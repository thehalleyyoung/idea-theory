"""
scripts/run_e2.py — Experiment E2: Triple Interaction Prediction.

Requires E1 to have run first (RS matrix + rs3 cache).

Usage:
    cd experiments/cocycle
    python -m scripts.run_e2 --config configs/gpt2_small.yaml
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
logger = logging.getLogger("run_e2")

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
    from harness.recovery import run_e2

    device = torch.device(cfg["device"].get("prefer", "mps")
                          if torch.backends.mps.is_available() else "cpu")
    cfg["device"]["prefer"] = str(device)

    results_dir = ROOT / cfg["paths"]["results_dir"]
    act_dir = ROOT / cfg["paths"]["activations_dir"]
    act_dir.mkdir(parents=True, exist_ok=True)
    cfg["paths"]["activations_dir"] = str(act_dir)
    cfg["paths"]["results_dir"] = str(results_dir)

    wrapper = load_model(cfg)
    W_dec, _ = load_sae_weights(cfg)
    batches = tokenize_corpus(cfg, getattr(wrapper, "tokenizer", None))

    n_feat = cfg["experiments"]["n_features"]
    seed_feat = cfg["experiments"]["seed_features"]
    n_total = W_dec.shape[0]
    rng0 = np.random.default_rng(seed_feat)
    feature_indices = rng0.choice(n_total, size=n_feat, replace=False).tolist()

    mu = compute_mean_activations(wrapper, batches, W_dec, feature_indices, cfg)
    RS = build_rs_matrix(wrapper, batches, feature_indices, W_dec, mu, cfg)

    # Training triples — reuse E1 cache
    n = len(feature_indices)
    n_quad = cfg["experiments"]["n_quadruples"]
    seed_e1 = cfg["experiments"]["seed_e1_quadruples"]
    rng1 = np.random.default_rng(seed_e1)
    quadruples = [(int(rng1.integers(n)), int(rng1.integers(n)),
                   int(rng1.integers(n)), int(rng1.integers(n)))
                  for _ in range(n_quad)]
    train_triple_set = set()
    for (ia, ib, id_, ie) in quadruples:
        for t in [(ia, ib, id_), (ib, id_, ie), (ia, ib, ie)]:
            a, b = sorted((t[0], t[1]))
            train_triple_set.add((a, b, t[2]))

    rs3_train = compute_rs_triple_batch(
        wrapper, batches, list(train_triple_set), feature_indices, W_dec, mu, cfg
    )

    # Test triples (seed 2, disjoint intent)
    n_test = cfg["experiments"]["n_test_triples"]
    seed_e2 = cfg["experiments"]["seed_e2_test_triples"]
    rng2 = np.random.default_rng(seed_e2)
    test_triples_raw = [(int(rng2.integers(n)), int(rng2.integers(n)),
                         int(rng2.integers(n)))
                        for _ in range(n_test)]
    test_set = {(min(a,b), max(a,b), d) for a, b, d in test_triples_raw}

    rs3_test = compute_rs_triple_batch(
        wrapper, batches, list(test_set), feature_indices, W_dec, mu, cfg
    )

    summary = run_e2(RS, rs3_train, rs3_test, feature_indices, n_test, seed_e2, results_dir)

    print("\n── E2 Results ───────────────────────────────────────")
    print(f"  n_test_triples  = {summary['n_test_triples']}")
    print(f"  R2_additive     = {summary['R2_additive']:.4f}")
    print(f"  R2_cocycle      = {summary['R2_cocycle']:.4f}")
    print(f"  delta_R2        = {summary['delta_R2']:+.4f}")
    print(f"  MAE_additive    = {summary['MAE_additive']:.4f}")
    print(f"  MAE_cocycle     = {summary['MAE_cocycle']:.4f}")
    print(f"  spearman_add    = {summary['spearman_additive']:.4f}")
    print(f"  spearman_coc    = {summary['spearman_cocycle']:.4f}")
    print(f"  p_value_welch   = {summary['p_value_welch']:.4e}")
    print(f"  Saved → {results_dir}/e2_summary.json")
    return 0


if __name__ == "__main__":
    sys.exit(main())
