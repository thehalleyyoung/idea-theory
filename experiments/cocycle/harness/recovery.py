"""
harness/recovery.py — LASSO estimator for E2 triple prediction.

Estimates the cocycle correction ĉ(a,b,d) from pair measurements using
a random-feature sketch of the 3-tensor:

    ĉ(a,b,d) ≈ Σ_k α_k · φ_k(a) · ψ_k(b) · ω_k(d)

where φ_k, ψ_k, ω_k are random ±1 hash functions over the feature index.
LASSO with 5-fold CV selects the regularisation strength.
"""
from __future__ import annotations

import json
import logging
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import numpy as np
import torch
from scipy import stats
from sklearn.linear_model import LassoCV, Lasso
from sklearn.model_selection import KFold

logger = logging.getLogger(__name__)

N_SKETCH = 5_000   # number of random features in the sketch


# ─── random feature sketch ────────────────────────────────────────────────────

def _make_hash_fns(n: int, m: int, seed: int) -> np.ndarray:
    """
    Returns hash_matrix of shape (3, m, n) with ±1 entries.
    hash_matrix[0, k, i] = φ_k(i), etc.
    """
    rng = np.random.default_rng(seed)
    return rng.choice([-1, 1], size=(3, m, n)).astype(np.float32)


def _design_row(ia: int, ib: int, id_: int, hash_matrix: np.ndarray) -> np.ndarray:
    """φ_k(a) · ψ_k(b) · ω_k(d)  for all k — shape (m,)."""
    return hash_matrix[0, :, ia] * hash_matrix[1, :, ib] * hash_matrix[2, :, id_]


def build_design_matrix(
    triples: List[Tuple[int, int, int]],  # (ia, ib, id_) index triples
    hash_matrix: np.ndarray,              # (3, m, n)
) -> np.ndarray:
    """Design matrix X[t, k] = φ_k(a_t) · ψ_k(b_t) · ω_k(d_t). Shape (T, m)."""
    rows = [_design_row(ia, ib, id_, hash_matrix) for ia, ib, id_ in triples]
    return np.stack(rows, axis=0)


# ─── LASSO fit ────────────────────────────────────────────────────────────────

def fit_lasso_cocycle(
    train_triples: List[Tuple[int, int, int]],
    RS: torch.Tensor,
    rs3_cache: Dict,
    n: int,
    seed: int,
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Fit LASSO estimator for ĉ.

    Target: y[t] = rs3(a,b,d) - RS[a,d] - RS[b,d]

    Returns:
        alpha: (m,) LASSO coefficients
        hash_matrix: (3, m, n) random hash matrix
    """
    m = min(N_SKETCH, len(train_triples))
    hash_matrix = _make_hash_fns(n, m, seed)

    X = build_design_matrix(train_triples, hash_matrix)   # (T, m)
    y = np.array([
        rs3_cache.get(_triple_key(ia, ib, id_), 0.0)
        - RS[ia, id_].item() - RS[ib, id_].item()
        for ia, ib, id_ in train_triples
    ], dtype=np.float32)

    logger.info("LASSO fit: X=%s, y=%s", X.shape, y.shape)

    # 5-fold CV with 10 alphas (fast on CPU)
    lasso = LassoCV(cv=5, n_alphas=10, max_iter=5000, random_state=seed, n_jobs=-1)
    lasso.fit(X, y)
    logger.info("LASSO best alpha=%.4e, n_nonzero=%d",
                lasso.alpha_, np.sum(lasso.coef_ != 0))
    return lasso.coef_, hash_matrix


def predict_triple(
    ia: int, ib: int, id_: int,
    RS: torch.Tensor,
    alpha: np.ndarray,
    hash_matrix: np.ndarray,
) -> float:
    """T_coc(a,b,d) = RS[a,d] + RS[b,d] + ĉ(a,b,d)."""
    phi = _design_row(ia, ib, id_, hash_matrix)
    c_hat = float(alpha @ phi)
    return RS[ia, id_].item() + RS[ib, id_].item() + c_hat


def _triple_key(ia: int, ib: int, id_: int) -> Tuple[int, int, int]:
    a, b = sorted((ia, ib))
    return (a, b, id_)


# ─── E2 experiment ────────────────────────────────────────────────────────────

def run_e2(
    RS: torch.Tensor,
    rs3_train: Dict,
    rs3_test: Dict,
    feature_indices: List[int],
    n_test: int,
    seed: int,
    results_dir: Path,
) -> Dict:
    """
    E2: Triple Interaction Prediction.

    Predicts ground-truth rs3(a,b,d) values on held-out test set using:
      - T_add(a,b,d) = RS[a,d] + RS[b,d]
      - T_coc(a,b,d) = RS[a,d] + RS[b,d] + ĉ(a,b,d)  [LASSO estimate]

    Returns summary with R², MAE, Spearman ρ.
    """
    n = len(feature_indices)
    rng = np.random.default_rng(seed)

    # Sample test triples
    test_triples = [(int(rng.integers(n)), int(rng.integers(n)), int(rng.integers(n)))
                    for _ in range(n_test)]

    # Ground truth
    T_gt = np.array([
        rs3_test.get(_triple_key(ia, ib, id_), 0.0)
        for ia, ib, id_ in test_triples
    ], dtype=np.float32)

    # Additive baseline
    T_add = np.array([
        RS[ia, id_].item() + RS[ib, id_].item()
        for ia, ib, id_ in test_triples
    ], dtype=np.float32)

    # Fit LASSO on training triples
    train_triples = list(rs3_train.keys())
    alpha, hash_matrix = fit_lasso_cocycle(train_triples, RS, rs3_train, n, seed)

    # Cocycle prediction
    T_coc = np.array([
        predict_triple(ia, ib, id_, RS, alpha, hash_matrix)
        for ia, ib, id_ in test_triples
    ], dtype=np.float32)

    def r_squared(y_true, y_pred):
        ss_res = np.sum((y_true - y_pred) ** 2)
        ss_tot = np.sum((y_true - y_true.mean()) ** 2)
        return float(1 - ss_res / max(ss_tot, 1e-10))

    def mae(y_true, y_pred):
        return float(np.mean(np.abs(y_true - y_pred)))

    # Welch t-test on squared errors
    sq_err_add = (T_gt - T_add) ** 2
    sq_err_coc = (T_gt - T_coc) ** 2
    _, p_welch = stats.ttest_ind(sq_err_add, sq_err_coc, equal_var=False)

    spearman_add = float(stats.spearmanr(T_gt, T_add).statistic)
    spearman_coc = float(stats.spearmanr(T_gt, T_coc).statistic)

    summary = {
        "n_test_triples": n_test,
        "R2_additive": r_squared(T_gt, T_add),
        "R2_cocycle": r_squared(T_gt, T_coc),
        "MAE_additive": mae(T_gt, T_add),
        "MAE_cocycle": mae(T_gt, T_coc),
        "spearman_additive": spearman_add,
        "spearman_cocycle": spearman_coc,
        "p_value_welch": float(p_welch),
        "delta_R2": r_squared(T_gt, T_coc) - r_squared(T_gt, T_add),
        "T_ground_truth": T_gt.tolist(),
        "T_additive": T_add.tolist(),
        "T_cocycle": T_coc.tolist(),
    }

    results_dir.mkdir(parents=True, exist_ok=True)
    out = results_dir / "e2_summary.json"
    log_keys = [k for k in summary if k not in ("T_ground_truth", "T_additive", "T_cocycle")]
    with open(out, "w") as f:
        json.dump({k: summary[k] for k in log_keys}, f, indent=2)
    logger.info("E2 results saved to %s", out)
    return summary
