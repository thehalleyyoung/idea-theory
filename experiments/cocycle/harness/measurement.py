"""
harness/measurement.py — Compute rs(a,b) and rs3(a,b,d) interaction values.

rs(a, b) = E_x[L(M_{ab}(x)) - L(M_a(x)) - L(M_b(x)) + L(M(x))]
rs3(a, b, d) = E_x[L(M_{abd}(x)) - L(M_{ab}(x)) - L(M_d(x)) + L(M(x))]

All values are cached to activations/ so each ablation set is paid once.
Implements MPS constraints: fp32, batch ≤ 8, seq ≤ 128.
"""
from __future__ import annotations

import json
import logging
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import numpy as np
import torch
from tqdm import tqdm

logger = logging.getLogger(__name__)


# ─── cached single & pair losses ──────────────────────────────────────────────

def _cache_path(base_dir: Path, tag: str) -> Path:
    return base_dir / f"{tag}.pt"


def _get_or_compute_loss(
    wrapper,
    token_batches: List[torch.Tensor],
    ablation_set: tuple,        # sorted tuple of feature indices
    W_dec: torch.Tensor,
    mu: torch.Tensor,
    cache_dir: Path,
) -> float:
    """Return cached or freshly computed mean corpus loss for ablation_set."""
    tag = "loss_clean" if not ablation_set else f"loss_abl_{'_'.join(map(str, ablation_set))}"
    path = _cache_path(cache_dir, tag)
    if path.exists():
        return torch.load(path, weights_only=True).item()

    total, n = 0.0, 0
    for batch in token_batches:
        total += wrapper.compute_loss_batch(batch, list(ablation_set), W_dec, mu)
        n += 1
    val = total / max(n, 1)
    torch.save(torch.tensor(val), path)
    return val


# ─── rs pair computation ──────────────────────────────────────────────────────

def compute_rs_pair(
    wrapper,
    token_batches: List[torch.Tensor],
    feat_i: int,
    feat_j: int,
    W_dec: torch.Tensor,
    mu: torch.Tensor,
    cache_dir: Path,
) -> float:
    """rs(feat_i, feat_j) — Shapley-style ΔLoss interaction."""
    L_clean = _get_or_compute_loss(wrapper, token_batches, (), W_dec, mu, cache_dir)
    L_i = _get_or_compute_loss(wrapper, token_batches, (feat_i,), W_dec, mu, cache_dir)
    L_j = _get_or_compute_loss(wrapper, token_batches, (feat_j,), W_dec, mu, cache_dir)
    L_ij = _get_or_compute_loss(wrapper, token_batches,
                                 tuple(sorted((feat_i, feat_j))), W_dec, mu, cache_dir)
    return L_ij - L_i - L_j + L_clean


def build_rs_matrix(
    wrapper,
    token_batches: List[torch.Tensor],
    feature_indices: List[int],
    W_dec: torch.Tensor,
    mu: torch.Tensor,
    cfg: Dict,
) -> torch.Tensor:
    """
    Build the n×n symmetric rs matrix for feature_indices.
    Caches the full matrix and all intermediate ablation losses.

    Returns:
        RS: (n, n) float32 tensor
    """
    n = len(feature_indices)
    cache_dir = Path(cfg.get("paths", {}).get("activations_dir", "activations"))
    cache_dir.mkdir(parents=True, exist_ok=True)
    matrix_path = cache_dir / f"rs_matrix_{n}feat.pt"

    if matrix_path.exists():
        logger.info("Loading cached RS matrix from %s", matrix_path)
        return torch.load(matrix_path, weights_only=True)

    logger.info("Building %d×%d RS matrix (this may take a while)…", n, n)

    # Pre-compute all single-feature losses (amortised across all pairs)
    logger.info("  Pass 1/2: single-feature ablations…")
    for fi in tqdm(feature_indices, desc="single ablations"):
        _get_or_compute_loss(wrapper, token_batches, (fi,), W_dec, mu, cache_dir)
    _get_or_compute_loss(wrapper, token_batches, (), W_dec, mu, cache_dir)  # clean

    # Compute all pair losses
    logger.info("  Pass 2/2: pair ablations…")
    RS = torch.zeros(n, n, dtype=torch.float32)
    n_pairs = n * (n - 1) // 2
    with tqdm(total=n_pairs, desc="pair ablations") as pbar:
        for i in range(n):
            for j in range(i + 1, n):
                fi, fj = feature_indices[i], feature_indices[j]
                val = compute_rs_pair(wrapper, token_batches, fi, fj, W_dec, mu, cache_dir)
                RS[i, j] = val
                RS[j, i] = val
                pbar.update(1)

    torch.save(RS, matrix_path)
    logger.info("RS matrix saved to %s", matrix_path)
    return RS


# ─── rs3 triple computation ───────────────────────────────────────────────────

def compute_rs_triple(
    wrapper,
    token_batches: List[torch.Tensor],
    feat_a: int,
    feat_b: int,
    feat_d: int,
    W_dec: torch.Tensor,
    mu: torch.Tensor,
    cache_dir: Path,
) -> float:
    """
    rs3(a, b, d) = interaction of joint pair {a,b} against d.

    rs3(a, b, d) = L(M_{abd}) - L(M_{ab}) - L(M_d) + L(M)

    This measures how much jointly ablating {a,b} together differs from
    the sum of individual ablations w.r.t. probe d.
    """
    ab_set = tuple(sorted((feat_a, feat_b)))
    abd_set = tuple(sorted((feat_a, feat_b, feat_d)))
    L_clean = _get_or_compute_loss(wrapper, token_batches, (), W_dec, mu, cache_dir)
    L_ab = _get_or_compute_loss(wrapper, token_batches, ab_set, W_dec, mu, cache_dir)
    L_d = _get_or_compute_loss(wrapper, token_batches, (feat_d,), W_dec, mu, cache_dir)
    L_abd = _get_or_compute_loss(wrapper, token_batches, abd_set, W_dec, mu, cache_dir)
    return L_abd - L_ab - L_d + L_clean


def compute_rs_triple_batch(
    wrapper,
    token_batches: List[torch.Tensor],
    triples: List[Tuple[int, int, int]],   # (feat_a, feat_b, feat_d) as raw indices
    feature_indices: List[int],
    W_dec: torch.Tensor,
    mu: torch.Tensor,
    cfg: Dict,
) -> Dict[Tuple[int, int, int], float]:
    """
    Compute rs3 for a list of (ia, ib, id) index-triples (indices into feature_indices).
    Returns dict mapping (ia, ib, id) → rs3 value. Results are cached per ablation set.
    """
    cache_dir = Path(cfg.get("paths", {}).get("activations_dir", "activations"))
    cache_dir.mkdir(parents=True, exist_ok=True)

    # Deduplicate triples
    unique = set(triples)
    logger.info("Computing %d unique rs3 triples…", len(unique))

    rs3_cache: Dict[Tuple[int, int, int], float] = {}
    for (ia, ib, id_) in tqdm(unique, desc="rs3 triples"):
        fa, fb, fd = feature_indices[ia], feature_indices[ib], feature_indices[id_]
        rs3_cache[(ia, ib, id_)] = compute_rs_triple(
            wrapper, token_batches, fa, fb, fd, W_dec, mu, cache_dir
        )

    return rs3_cache
