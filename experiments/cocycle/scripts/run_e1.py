"""
scripts/run_e1.py — Experiment E1: Cocycle Identity Validation.

Usage:
    cd experiments/cocycle
    python -m scripts.run_e1 --config configs/gpt2_small.yaml
"""
from __future__ import annotations

import argparse
import logging
import sys
from pathlib import Path

import numpy as np
import torch
import yaml

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s  %(message)s")
logger = logging.getLogger("run_e1")

ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(ROOT))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", default="configs/gpt2_small.yaml")
    args = parser.parse_args()

    with open(args.config) as f:
        cfg = yaml.safe_load(f)

    from harness.model import load_model
    from harness.features import load_sae_weights, compute_mean_activations, tokenize_corpus
    from harness.measurement import build_rs_matrix, compute_rs_triple_batch
    from harness.cocycle import run_e1

    device = torch.device(cfg["device"].get("prefer", "mps")
                          if torch.backends.mps.is_available() else "cpu")
    cfg["device"]["prefer"] = str(device)

    results_dir = ROOT / cfg["paths"]["results_dir"]
    act_dir = ROOT / cfg["paths"]["activations_dir"]
    act_dir.mkdir(parents=True, exist_ok=True)
    cfg["paths"]["activations_dir"] = str(act_dir)
    cfg["paths"]["results_dir"] = str(results_dir)

    # ── Load components ────────────────────────────────────────────────────────
    wrapper = load_model(cfg)
    W_dec, _ = load_sae_weights(cfg)
    batches = tokenize_corpus(cfg, getattr(wrapper, "tokenizer", None))

    # ── Feature subset ─────────────────────────────────────────────────────────
    n_feat = cfg["experiments"]["n_features"]
    seed_feat = cfg["experiments"]["seed_features"]
    n_total = W_dec.shape[0]
    rng0 = np.random.default_rng(seed_feat)
    feature_indices = rng0.choice(n_total, size=n_feat, replace=False).tolist()
    logger.info("Feature subset: %d features sampled from %d (seed=%d)",
                n_feat, n_total, seed_feat)

    # ── Mean activations ───────────────────────────────────────────────────────
    mu = compute_mean_activations(wrapper, batches, W_dec, feature_indices, cfg)

    # ── Pair RS matrix ─────────────────────────────────────────────────────────
    RS = build_rs_matrix(wrapper, batches, feature_indices, W_dec, mu, cfg)
    logger.info("RS matrix: shape=%s, mean=%.4f", tuple(RS.shape), RS.mean().item())

    # ── Triple cache for E1 ────────────────────────────────────────────────────
    n_quad = cfg["experiments"]["n_quadruples"]
    seed_e1 = cfg["experiments"]["seed_e1_quadruples"]
    rng1 = np.random.default_rng(seed_e1)
    n = len(feature_indices)
    quadruples = [(int(rng1.integers(n)), int(rng1.integers(n)),
                   int(rng1.integers(n)), int(rng1.integers(n)))
                  for _ in range(n_quad)]

    # Unique triples needed
    triple_set = set()
    for (ia, ib, id_, ie) in quadruples:
        for t in [(ia, ib, id_), (ib, id_, ie), (ia, ib, ie),
                  (ia, ib, id_), (ib, id_, ie)]:
            a, b = sorted((t[0], t[1]))
            triple_set.add((a, b, t[2]))

    logger.info("Unique rs3 triples to compute: %d", len(triple_set))
    rs3_cache = compute_rs_triple_batch(
        wrapper, batches, list(triple_set), feature_indices, W_dec, mu, cfg
    )

    # ── Run E1 ─────────────────────────────────────────────────────────────────
    summary = run_e1(RS, rs3_cache, feature_indices, n_quad, seed_e1, results_dir)

    print("\n── E1 Results ───────────────────────────────────────")
    print(f"  n_quadruples       = {summary['n_quadruples']}")
    print(f"  mean_violation_emp = {summary['mean_violation_empirical']:.4f}")
    print(f"  mean_violation_null= {summary['mean_violation_null']:.4f}")
    print(f"  ratio emp/null     = {summary['ratio_emp_null']:.4f}")
    print(f"  p_value            = {summary['p_value']:.4e}")
    print(f"  cohen_d            = {summary['cohen_d']:.4f}")
    print(f"  gini               = {summary['gini']:.4f}")
    print(f"  top5%_share        = {summary['top5pct_share']:.2%}")
    print(f"  Saved → {results_dir}/e1_summary.json")
    return 0


if __name__ == "__main__":
    sys.exit(main())
