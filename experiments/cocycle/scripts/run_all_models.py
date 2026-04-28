"""
scripts/run_all_models.py — Run E1/E2/E3 for every model config in configs/.

Usage:
    cd experiments/cocycle
    python -m scripts.run_all_models                     # all configs
    python -m scripts.run_all_models --configs pythia_70m tinystories_33m
    python -m scripts.run_all_models --preflight-only    # just preflight

Results land in results/<model_name>/e{1,2,3}_summary.json.
"""
from __future__ import annotations

import argparse
import json
import logging
import sys
import time
import traceback
from pathlib import Path
from typing import List, Optional

import numpy as np
import torch
import yaml

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s  %(levelname)s  %(name)s  %(message)s",
    datefmt="%H:%M:%S",
)
logger = logging.getLogger("run_all_models")

HERE = Path(__file__).parent.parent
sys.path.insert(0, str(HERE))

# ─── per-model corpus helper ──────────────────────────────────────────────────

def tokenize_corpus_for_model(cfg: dict, wrapper) -> list:
    """
    Tokenize the corpus using the model's own tokenizer when available.
    Falls back to the base tokenize_corpus() for GPT-2-family models.
    """
    from harness.features import tokenize_corpus
    tokenizer = None
    if wrapper.tokenizer is not None:
        tokenizer = wrapper.tokenizer
    elif wrapper.backend == "transformer_lens":
        try:
            tokenizer_name = cfg.get("model", {}).get("tokenizer_name", "gpt2")
            from transformers import AutoTokenizer
            tokenizer = AutoTokenizer.from_pretrained(tokenizer_name)
            if tokenizer.pad_token is None:
                tokenizer.pad_token = tokenizer.eos_token
        except Exception:
            pass
    return tokenize_corpus(cfg, tokenizer)


# ─── single model run ─────────────────────────────────────────────────────────

def run_model(cfg_path: Path, preflight_only: bool = False) -> dict:
    """
    Run the full experiment suite for one model config.
    Returns a status dict.
    """
    with open(cfg_path) as f:
        cfg = yaml.safe_load(f)

    model_name = cfg["model"]["name"]
    results_dir = Path(cfg["paths"]["results_dir"])
    results_dir.mkdir(parents=True, exist_ok=True)

    status = {
        "config": str(cfg_path),
        "model": model_name,
        "feature_type": cfg.get("sae", {}).get("feature_type", "sae"),
        "steps_completed": [],
        "errors": [],
        "timing": {},
    }

    t_start = time.time()
    logger.info("=" * 60)
    logger.info("Model: %s  config: %s", model_name, cfg_path.name)

    # ── load model ────────────────────────────────────────────────────────────
    try:
        from harness.model_loader import load_model_for_config
        wrapper = load_model_for_config(cfg)
        status["backend"] = wrapper.backend
        status["device"] = str(wrapper.device)
        logger.info("Loaded: backend=%s device=%s", wrapper.backend, wrapper.device)
        status["steps_completed"].append("model_load")
    except Exception as e:
        status["errors"].append(f"model_load: {e}")
        logger.error("FAILED model_load: %s", e)
        return status

    # ── extract features ──────────────────────────────────────────────────────
    try:
        from harness.feature_extractor import get_features
        W_dec, feature_meta = get_features(cfg, wrapper)
        n_feat_total = W_dec.shape[0]
        logger.info("Features: %d total, type=%s", n_feat_total, feature_meta["feature_type"])
        status["n_features_total"] = n_feat_total
        status["feature_meta"] = feature_meta
        status["steps_completed"].append("feature_extraction")
    except Exception as e:
        status["errors"].append(f"feature_extraction: {e}")
        logger.error("FAILED feature_extraction: %s", traceback.format_exc())
        return status

    # ── tokenize corpus ───────────────────────────────────────────────────────
    try:
        token_batches = tokenize_corpus_for_model(cfg, wrapper)
        logger.info("Corpus: %d batches", len(token_batches))
        status["n_batches"] = len(token_batches)
        status["steps_completed"].append("corpus")
    except Exception as e:
        status["errors"].append(f"corpus: {e}")
        logger.error("FAILED corpus: %s", e)
        return status

    if preflight_only:
        logger.info("Preflight-only mode: stopping after corpus load.")
        return status

    # ── select feature subset ─────────────────────────────────────────────────
    exp_cfg = cfg.get("experiments", {})
    n_features = min(exp_cfg.get("n_features", 50), n_feat_total)
    rng = np.random.default_rng(exp_cfg.get("seed_features", 0))
    feature_indices = sorted(
        rng.choice(n_feat_total, size=n_features, replace=False).tolist()
    )
    logger.info("Feature subset: %d features selected", n_features)

    # ── compute mean activations ──────────────────────────────────────────────
    try:
        from harness.feature_extractor import compute_mean_activations_generic
        mu = compute_mean_activations_generic(
            wrapper, token_batches, W_dec, feature_indices, cfg
        )
        status["steps_completed"].append("mean_activations")
    except Exception as e:
        logger.warning("Mean activations failed (%s); using zeros.", e)
        mu = torch.zeros(len(feature_indices))
        status["errors"].append(f"mean_activations (non-fatal): {e}")

    # ── build RS matrix ───────────────────────────────────────────────────────
    try:
        t0 = time.time()
        from harness.measurement import build_rs_matrix
        RS = build_rs_matrix(wrapper, token_batches, feature_indices, W_dec, mu, cfg)
        status["timing"]["rs_matrix_sec"] = time.time() - t0
        status["steps_completed"].append("rs_matrix")
        logger.info("RS matrix built: %s in %.1fs", RS.shape, status["timing"]["rs_matrix_sec"])
    except Exception as e:
        status["errors"].append(f"rs_matrix: {e}")
        logger.error("FAILED rs_matrix: %s", traceback.format_exc())
        return status

    # ── sample triples for E2 ─────────────────────────────────────────────────
    n = len(feature_indices)
    n_train = exp_cfg.get("n_train_sketch", 5000)
    n_test = exp_cfg.get("n_test_triples", 500)
    rng2 = np.random.default_rng(exp_cfg.get("seed_e2_test_triples", 2))

    train_triples = [
        (int(rng2.integers(n)), int(rng2.integers(n)), int(rng2.integers(n)))
        for _ in range(n_train)
    ]
    test_triples = [
        (int(rng2.integers(n)), int(rng2.integers(n)), int(rng2.integers(n)))
        for _ in range(n_test)
    ]
    all_triples = list(set(train_triples + test_triples))

    # ── compute rs3 values ────────────────────────────────────────────────────
    try:
        t0 = time.time()
        from harness.measurement import compute_rs_triple_batch
        rs3_cache = compute_rs_triple_batch(
            wrapper, token_batches, all_triples, feature_indices, W_dec, mu, cfg
        )
        status["timing"]["rs3_sec"] = time.time() - t0
        status["steps_completed"].append("rs3_triples")
        logger.info("rs3 computed: %d values in %.1fs", len(rs3_cache),
                    status["timing"]["rs3_sec"])
    except Exception as e:
        status["errors"].append(f"rs3_triples: {e}")
        logger.error("FAILED rs3: %s", traceback.format_exc())
        return status

    rs3_train = {k: v for k, v in rs3_cache.items() if k in train_triples}
    rs3_test  = {k: v for k, v in rs3_cache.items() if k in test_triples}

    # ── E1: cocycle identity ──────────────────────────────────────────────────
    try:
        t0 = time.time()
        from harness.cocycle import run_e1
        e1 = run_e1(
            RS, rs3_cache, feature_indices,
            n_quadruples=exp_cfg.get("n_quadruples", 10000),
            seed=exp_cfg.get("seed_e1_quadruples", 1),
            results_dir=results_dir,
        )
        status["timing"]["e1_sec"] = time.time() - t0
        status["e1"] = {k: v for k, v in e1.items() if k != "per_feature_V"}
        status["steps_completed"].append("E1")
        logger.info(
            "E1: mean_violation=%.4f null=%.4f p=%.3e cohen_d=%.3f",
            e1["mean_violation_empirical"], e1["mean_violation_null"],
            e1["p_value"], e1["cohen_d"],
        )
    except Exception as e:
        status["errors"].append(f"E1: {e}")
        logger.error("FAILED E1: %s", traceback.format_exc())

    # ── E2: triple prediction ─────────────────────────────────────────────────
    try:
        t0 = time.time()
        from harness.recovery import run_e2
        e2 = run_e2(
            RS, rs3_train, rs3_test, feature_indices,
            n_test=exp_cfg.get("n_test_triples", 500),
            seed=exp_cfg.get("seed_lasso", 10),
            results_dir=results_dir,
        )
        status["timing"]["e2_sec"] = time.time() - t0
        status["e2"] = {k: v for k, v in e2.items()
                        if k not in ("T_ground_truth", "T_additive", "T_cocycle")}
        status["steps_completed"].append("E2")
        logger.info(
            "E2: R2_add=%.4f R2_coc=%.4f ΔR2=%.4f p_welch=%.3e",
            e2["R2_additive"], e2["R2_cocycle"],
            e2["delta_R2"], e2["p_value_welch"],
        )
    except Exception as e:
        status["errors"].append(f"E2: {e}")
        logger.error("FAILED E2: %s", traceback.format_exc())

    # ── E3: cluster / label stub ──────────────────────────────────────────────
    try:
        t0 = time.time()
        e3 = _run_e3_stub(RS, feature_indices, exp_cfg, results_dir, feature_meta)
        status["timing"]["e3_sec"] = time.time() - t0
        status["e3"] = e3
        status["steps_completed"].append("E3")
        logger.info("E3 (stub): %d clusters, top violation feature: %s",
                    e3["n_clusters"], e3.get("top_violation_feature_idx"))
    except Exception as e:
        status["errors"].append(f"E3: {e}")
        logger.error("FAILED E3: %s", traceback.format_exc())

    status["timing"]["total_sec"] = time.time() - t_start
    # Write per-model status JSON
    with open(results_dir / "run_status.json", "w") as f:
        json.dump(status, f, indent=2, default=str)
    logger.info("Total time: %.1fs  steps: %s",
                status["timing"]["total_sec"], status["steps_completed"])
    return status


def _run_e3_stub(RS, feature_indices, exp_cfg, results_dir: Path, feature_meta: dict) -> dict:
    """
    E3: Feature clustering stub.

    Groups features by their RS connectivity signature using k-means on the
    RS matrix rows. When feature_type='sae', this approximates Neuronpedia
    semantic clusters. For mlp_neuron/attn_head types, clusters reflect
    structural similarity in how features interact at the residual stream.
    """
    from sklearn.cluster import KMeans

    n = RS.shape[0]
    n_clusters = min(exp_cfg.get("n_clusters", 5), n)
    seed = exp_cfg.get("seed_kmeans", 99)

    X = RS.numpy()
    km = KMeans(n_clusters=n_clusters, random_state=seed, n_init=10)
    labels = km.fit_predict(X)

    cluster_sizes = {int(k): int((labels == k).sum()) for k in range(n_clusters)}

    # Top feature by mean |RS| column norm (proxy for most "interactive" feature)
    col_norms = RS.abs().mean(dim=0)
    top_idx = int(col_norms.argmax().item())

    summary = {
        "n_features": n,
        "n_clusters": n_clusters,
        "cluster_sizes": cluster_sizes,
        "top_violation_feature_idx": feature_indices[top_idx] if top_idx < len(feature_indices) else top_idx,
        "feature_type": feature_meta.get("feature_type", "unknown"),
        "feature_type_note": feature_meta.get("note", ""),
    }
    results_dir.mkdir(parents=True, exist_ok=True)
    with open(results_dir / "e3_summary.json", "w") as f:
        json.dump(summary, f, indent=2)
    return summary


# ─── main ─────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="Run E1/E2/E3 for all model configs.")
    parser.add_argument(
        "--configs", nargs="*",
        help="Config stem names (without .yaml). Default: all in configs/",
    )
    parser.add_argument(
        "--preflight-only", action="store_true",
        help="Only load model + tokenize corpus; skip experiments.",
    )
    args = parser.parse_args()

    configs_dir = HERE / "configs"
    if args.configs:
        cfg_paths = [configs_dir / f"{name}.yaml" for name in args.configs]
    else:
        cfg_paths = sorted(configs_dir.glob("*.yaml"))

    logger.info("Running %d model configs: %s", len(cfg_paths),
                [p.name for p in cfg_paths])

    all_status = {}
    for cfg_path in cfg_paths:
        if not cfg_path.exists():
            logger.warning("Config not found: %s — skipping.", cfg_path)
            continue
        model_key = cfg_path.stem
        try:
            all_status[model_key] = run_model(cfg_path, args.preflight_only)
        except Exception as e:
            all_status[model_key] = {"config": str(cfg_path), "errors": [str(e)]}
            logger.error("Unhandled error for %s: %s", model_key, e)

    # Write sweep summary
    summary_path = HERE / "results" / "sweep_status.json"
    summary_path.parent.mkdir(exist_ok=True)
    with open(summary_path, "w") as f:
        json.dump(all_status, f, indent=2, default=str)

    # Print quick report
    print("\n" + "=" * 60)
    print("SWEEP SUMMARY")
    print("=" * 60)
    for name, status in all_status.items():
        steps = status.get("steps_completed", [])
        errors = status.get("errors", [])
        ok = "✓" if not errors else "⚠"
        print(f"  {ok}  {name:30s}  steps={steps}  errors={len(errors)}")
    print(f"\nFull status: {summary_path}")


if __name__ == "__main__":
    main()
