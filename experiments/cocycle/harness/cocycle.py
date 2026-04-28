"""
harness/cocycle.py — Cocycle identity, Hochschild boundary, and E1.

The 3-cochain c(a, b, d) measures how much the joint ablation {a,b}
interacts with probe d beyond the sum of individual interactions:

    c(a, b, d)  =  rs3(a, b, d) - RS[a, d] - RS[b, d]

where:
  RS[i,j]       = rs(feature_i, feature_j)  (from precomputed 500×500 matrix)
  rs3(a, b, d)  = L(M_{abd}) - L(M_{ab}) - L(M_d) + L(M)

The Hochschild coboundary of this 3-cochain (trivial G-module):
    ∂c(a,b,d,e) = c(b,d,e) - c(a◦b,d,e) + c(a,b◦d,e) - c(a,b,d◦e) + c(a,b,d)

where (a◦b) in the first slot means the first argument to c is the
composed pair: c(a◦b, d, e) = rs4(a,b,d,e) - rs3(a,b,e) - RS[d,e].

For computational tractability we use the linear approximation:
    rs(a◦b, d◦e) ≈ rs3(a, b, d) + rs3(a, b, e) + ... [first-order terms]
but we report exact 4-way terms when available.
"""
from __future__ import annotations

import json
import logging
from collections import defaultdict
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import numpy as np
import scipy.stats
import torch

logger = logging.getLogger(__name__)


# ─── 3-cochain c ──────────────────────────────────────────────────────────────

def compute_c(
    ia: int, ib: int, id_: int,
    RS: torch.Tensor,                           # (n, n)
    rs3_cache: Dict[Tuple[int, int, int], float],
) -> float:
    """
    c(ia, ib, id_) = rs3(ia, ib, id_) - RS[ia, id_] - RS[ib, id_]

    All indices are positions in the feature_indices list (not raw SAE indices).
    """
    key = _triple_key(ia, ib, id_)
    rs3_val = rs3_cache.get(key, 0.0)
    return rs3_val - RS[ia, id_].item() - RS[ib, id_].item()


def _triple_key(ia: int, ib: int, id_: int) -> Tuple[int, int, int]:
    """Canonical key: first two sorted (composition is symmetric)."""
    a, b = sorted((ia, ib))
    return (a, b, id_)


# ─── Hochschild boundary ──────────────────────────────────────────────────────

def hochschild_boundary(
    ia: int, ib: int, id_: int, ie: int,
    RS: torch.Tensor,
    rs3_cache: Dict[Tuple[int, int, int], float],
    rs4_cache: Optional[Dict[Tuple[int, int, int, int], float]] = None,
) -> float:
    """
    Hochschild coboundary of 3-cochain c (trivial G-module):

        ∂c(a,b,d,e) = c(b,d,e) - c(a◦b,d,e) + c(a,b◦d,e) - c(a,b,d◦e) + c(a,b,d)

    Terms involving compositions a◦b (as first arg) require 4-way ablations.
    When rs4_cache is None, these are approximated as linear sums.

    Returns the boundary value (scalar float).
    """
    def c(x, y, z): return compute_c(x, y, z, RS, rs3_cache)

    # Term 1: c(b, d, e)
    t1 = c(ib, id_, ie)

    # Term 2: -c(a◦b, d, e)  — needs rs3(a◦b as composite, d, e)
    # = -(rs4(a,b,d,e) - rs3(a,b,e) - RS[d,e])
    t2 = -_c_composite_first(ia, ib, id_, ie, RS, rs3_cache, rs4_cache)

    # Term 3: +c(a, b◦d, e)
    # = +(rs4(a,b,d,e) - RS[a,e] - rs3(b,d,e))  [with b◦d composed]
    t3 = _c_composite_second(ia, ib, id_, ie, RS, rs3_cache, rs4_cache)

    # Term 4: -c(a, b, d◦e)
    # = -(rs3(a,b,d◦e) - RS[a,d◦e] - RS[b,d◦e])  — requires rs3 with composite probe
    t4 = -_c_composite_third(ia, ib, id_, ie, RS, rs3_cache, rs4_cache)

    # Term 5: +c(a, b, d)
    t5 = c(ia, ib, id_)

    return t1 + t2 + t3 + t4 + t5


def _c_composite_first(ia, ib, id_, ie, RS, rs3_cache, rs4_cache) -> float:
    """c(a◦b, d, e) = rs(joint_{a,b}, d_e) - rs3(a,b,e) - RS[d,e]"""
    rs3_abe = rs3_cache.get(_triple_key(ia, ib, ie), 0.0)
    rs4_abde = _get_rs4(ia, ib, id_, ie, rs4_cache, RS, rs3_cache)
    return rs4_abde - rs3_abe - RS[id_, ie].item()


def _c_composite_second(ia, ib, id_, ie, RS, rs3_cache, rs4_cache) -> float:
    """c(a, b◦d, e) = rs(joint_{a,b,d} against e) - RS[a,e] - rs3(b,d,e)"""
    rs3_bde = rs3_cache.get(_triple_key(ib, id_, ie), 0.0)
    rs4_abde = _get_rs4(ia, ib, id_, ie, rs4_cache, RS, rs3_cache)
    return rs4_abde - RS[ia, ie].item() - rs3_bde


def _c_composite_third(ia, ib, id_, ie, RS, rs3_cache, rs4_cache) -> float:
    """
    c(a, b, d◦e) = rs3(a,b,d◦e) - RS[a,d◦e] - RS[b,d◦e]

    Approximate using: rs(x, d◦e) ≈ rs3(x,d,e) + RS[x,d] + RS[x,e] - L_clean
    → use linear first-order approximation
    """
    # Approximate: RS[x, d◦e] ≈ RS[x,d] + RS[x,e]  (first-order, near-orthogonal features)
    rs_a_de = RS[ia, id_].item() + RS[ia, ie].item()
    rs_b_de = RS[ib, id_].item() + RS[ib, ie].item()
    # rs3(a,b,d◦e) ≈ rs3(a,b,d) + rs3(a,b,e)
    rs3_abd = rs3_cache.get(_triple_key(ia, ib, id_), 0.0)
    rs3_abe = rs3_cache.get(_triple_key(ia, ib, ie), 0.0)
    rs3_ab_de = rs3_abd + rs3_abe
    return rs3_ab_de - rs_a_de - rs_b_de


def _get_rs4(ia, ib, id_, ie, rs4_cache, RS, rs3_cache) -> float:
    """
    rs4(a,b,d,e) = L(M_{abde}) - L(M_{ab}) - L(M_d) + L(M)  [4-way ablation]

    Approximated as: rs3(a,b,d) + rs3(a,b,e) + RS[id_,ie] - (RS[ia,ie]+RS[ib,ie])
    when rs4_cache is not provided.
    """
    if rs4_cache is not None:
        key = tuple(sorted((ia, ib, id_, ie)))
        if key in rs4_cache:
            return rs4_cache[key]
    # Linear approximation (SAE near-orthogonality assumption)
    rs3_abd = rs3_cache.get(_triple_key(ia, ib, id_), 0.0)
    rs3_abe = rs3_cache.get(_triple_key(ia, ib, ie), 0.0)
    return rs3_abd + RS[id_, ie].item()


# ─── E1 experiment ────────────────────────────────────────────────────────────

def run_e1(
    RS: torch.Tensor,
    rs3_cache: Dict,
    feature_indices: List[int],
    n_quadruples: int,
    seed: int,
    results_dir: Path,
) -> Dict:
    """
    E1: Cocycle Identity Validation.

    Draw n_quadruples random (a,b,d,e) quadruples, compute Hochschild
    boundary, compare to permutation null. Returns summary dict.
    """
    n = len(feature_indices)
    rng = np.random.default_rng(seed)

    logger.info("E1: sampling %d quadruples (n_features=%d)…", n_quadruples, n)
    quadruples = [(int(rng.integers(n)), int(rng.integers(n)),
                   int(rng.integers(n)), int(rng.integers(n)))
                  for _ in range(n_quadruples)]

    # Empirical violations
    violations_emp = []
    per_feat_violations = defaultdict(list)
    for (ia, ib, id_, ie) in quadruples:
        bnd = hochschild_boundary(ia, ib, id_, ie, RS, rs3_cache)
        norm = (abs(compute_c(ia, ib, id_, RS, rs3_cache)) +
                abs(compute_c(ib, id_, ie, RS, rs3_cache)) + 1e-8)
        v = abs(bnd) / norm
        violations_emp.append(v)
        for fi in (ia, ib, id_, ie):
            per_feat_violations[feature_indices[fi]].append(abs(bnd))

    # Permutation null: column-permute RS
    perm_order = rng.permutation(n)
    RS_perm = RS[:, perm_order]
    violations_null = []
    for (ia, ib, id_, ie) in quadruples:
        bnd_n = hochschild_boundary(ia, ib, id_, ie, RS_perm, rs3_cache)
        norm_n = (abs(compute_c(ia, ib, id_, RS_perm, rs3_cache)) +
                  abs(compute_c(ib, id_, ie, RS_perm, rs3_cache)) + 1e-8)
        violations_null.append(abs(bnd_n) / norm_n)

    # Statistics
    t_stat, p_value = scipy.stats.ttest_ind(
        violations_emp, violations_null, alternative="less"
    )
    mu_emp = float(np.mean(violations_emp))
    mu_null = float(np.mean(violations_null))
    std_pool = float(np.std(violations_emp + violations_null))
    cohen_d = (mu_null - mu_emp) / max(std_pool, 1e-10)

    per_feat_V = {feat: float(np.mean(vals))
                  for feat, vals in per_feat_violations.items()}
    gini = _gini(list(per_feat_V.values()))
    top5 = _top_k_fraction(per_feat_V, 0.05)

    summary = {
        "n_quadruples": n_quadruples,
        "mean_violation_empirical": mu_emp,
        "mean_violation_null": mu_null,
        "ratio_emp_null": mu_emp / max(mu_null, 1e-10),
        "t_statistic": float(t_stat),
        "p_value": float(p_value),
        "cohen_d": float(cohen_d),
        "gini": float(gini),
        "top5pct_share": float(top5),
        "per_feature_V": per_feat_V,
    }

    results_dir.mkdir(parents=True, exist_ok=True)
    out = results_dir / "e1_summary.json"
    with open(out, "w") as f:
        json.dump({k: v for k, v in summary.items() if k != "per_feature_V"}, f, indent=2)
    logger.info("E1 results saved to %s", out)
    return summary


# ─── helpers ──────────────────────────────────────────────────────────────────

def _gini(values: List[float]) -> float:
    if not values:
        return 0.0
    arr = np.array(sorted(values), dtype=float)
    n = len(arr)
    idx = np.arange(1, n + 1)
    return float((2 * (idx * arr).sum() / (n * arr.sum()) - (n + 1) / n))


def _top_k_fraction(per_feat: Dict, frac: float) -> float:
    vals = sorted(per_feat.values(), reverse=True)
    k = max(1, int(len(vals) * frac))
    return sum(vals[:k]) / max(sum(vals), 1e-10)
