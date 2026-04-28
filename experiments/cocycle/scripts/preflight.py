"""
scripts/preflight.py — Verify MPS availability and run a tiny baseline.

Verifiable in < 2 min. Falls back to CPU + stub model if transformer_lens
or sae_lens are not installed.

Usage:
    cd experiments/cocycle
    python -m scripts.preflight
    python -m scripts.preflight --config configs/gpt2_small.yaml
"""
from __future__ import annotations

import argparse
import json
import logging
import sys
import time
from pathlib import Path

import numpy as np
import torch
import yaml

logging.basicConfig(level=logging.INFO, format="%(levelname)s  %(message)s")
logger = logging.getLogger("preflight")

PASS = "✓"
FAIL = "✗"


def check(label: str, ok: bool, detail: str = "") -> bool:
    status = PASS if ok else FAIL
    print(f"  [{status}] {label}" + (f"  ({detail})" if detail else ""))
    return ok


def section(title: str):
    print(f"\n── {title} {'─'*(50-len(title))}")


# ─── checks ───────────────────────────────────────────────────────────────────

def check_device() -> torch.device:
    section("Device")
    mps_ok = torch.backends.mps.is_available()
    if mps_ok:
        dev = torch.device("mps")
        check("MPS available", True, "Apple Silicon GPU backend active")
    else:
        dev = torch.device("cpu")
        check("MPS available", False, "falling back to CPU")
        check("CPU fallback", True, "all experiments will run on CPU")
    print(f"     device = {dev}")
    return dev


def check_imports() -> dict:
    section("Imports")
    results = {}

    try:
        import transformer_lens  # noqa: F401
        check("transformer_lens", True, transformer_lens.__version__)
        results["transformer_lens"] = True
    except ImportError:
        check("transformer_lens", False, "NOT installed — using HuggingFace fallback")
        results["transformer_lens"] = False

    try:
        import sae_lens  # noqa: F401
        check("sae_lens", True, sae_lens.__version__)
        results["sae_lens"] = True
    except ImportError:
        check("sae_lens", False, "NOT installed — using random SAE stub")
        results["sae_lens"] = False

    try:
        import transformers
        check("transformers (HF fallback)", True, transformers.__version__)
        results["transformers"] = True
    except ImportError:
        check("transformers", False, "CRITICAL — cannot load GPT-2")
        results["transformers"] = False

    for pkg in ("scipy", "sklearn", "numpy", "yaml"):
        try:
            mod = __import__(pkg if pkg != "yaml" else "yaml")
            check(pkg, True, getattr(mod, "__version__", "ok"))
            results[pkg] = True
        except ImportError:
            check(pkg, False)
            results[pkg] = False

    return results


def build_stub_cfg(device: torch.device) -> dict:
    return {
        "model": {"name": "gpt2", "hook_layer": 8, "d_model": 768},
        "sae": {"n_features_total": 24576},
        "corpus": {"n_tokens": 200, "max_seq_len": 64, "seed": 42},
        "device": {"prefer": str(device), "batch_size": 4},
        "preflight": {"n_features": 5, "n_tokens": 200, "batch_size": 4},
        "paths": {"activations_dir": "activations_preflight", "results_dir": "results"},
    }


def run_model_check(device: torch.device, cfg: dict) -> bool:
    section("Model Loading")
    try:
        sys.path.insert(0, str(Path(__file__).parent.parent))
        from harness.model import load_model
        wrapper = load_model(cfg)
        check("load_model()", True, f"backend={wrapper.backend}, device={wrapper.device}")
        return True
    except Exception as e:
        check("load_model()", False, str(e)[:80])
        return False


def run_sae_check(cfg: dict) -> tuple:
    section("SAE / Feature Directions")
    try:
        from harness.features import load_sae_weights
        W_dec, sae_meta = load_sae_weights(cfg)
        shape_ok = W_dec.ndim == 2 and W_dec.shape[1] == cfg["model"]["d_model"]
        check("SAE weights loaded", True,
              f"shape={tuple(W_dec.shape)}, release={sae_meta.get('release','?')}")
        norm_ok = torch.allclose(W_dec.norm(dim=1).mean(), torch.tensor(1.0), atol=0.1)
        check("W_dec rows approx unit-norm", norm_ok,
              f"mean_norm={W_dec.norm(dim=1).mean():.4f}")
        return W_dec, True
    except Exception as e:
        check("SAE weights", False, str(e)[:80])
        d = cfg["model"]["d_model"]
        W_dec = torch.randn(100, d)
        W_dec = W_dec / W_dec.norm(dim=1, keepdim=True)
        return W_dec, False


def run_corpus_check(cfg: dict, wrapper) -> tuple:
    section("Corpus / Tokenisation")
    try:
        from harness.features import tokenize_corpus
        batches = tokenize_corpus(cfg, wrapper.tokenizer if hasattr(wrapper, "tokenizer") else None)
        ok = len(batches) > 0
        b0 = batches[0]
        check("corpus loaded", ok,
              f"{len(batches)} batches × {b0.shape} (batch,seq)")
        return batches, ok
    except Exception as e:
        check("corpus", False, str(e)[:80])
        # stub random batches
        bsz = cfg["device"]["batch_size"]
        seq = cfg["corpus"]["max_seq_len"]
        batches = [torch.randint(0, 50257, (bsz, seq))]
        check("random stub corpus", True, "using random tokens")
        return batches, False


def run_loss_check(wrapper, batches, W_dec, device: torch.device) -> bool:
    section("Forward Pass + ΔLoss")
    try:
        n_feat = W_dec.shape[0]
        n_subset = 5
        rng = np.random.default_rng(0)
        feat_idx = list(rng.choice(min(n_feat, 100), size=n_subset, replace=False).tolist())

        mu = torch.zeros(n_feat)   # stub mu = 0 (fast, no corpus sweep)
        W_dec_cpu = W_dec.cpu()

        t0 = time.time()
        L_clean = wrapper.corpus_loss(batches, [], W_dec_cpu, mu)
        check("clean forward pass", True, f"loss={L_clean:.4f}, {time.time()-t0:.1f}s")

        t1 = time.time()
        L_a0 = wrapper.corpus_loss(batches, [feat_idx[0]], W_dec_cpu, mu)
        check("single ablation", True, f"loss={L_a0:.4f}, {time.time()-t1:.1f}s")

        t2 = time.time()
        L_a01 = wrapper.corpus_loss(batches, feat_idx[:2], W_dec_cpu, mu)
        check("pair ablation", True, f"loss={L_a01:.4f}, {time.time()-t2:.1f}s")

        # rs(0, 1) — should be finite
        L_a1 = wrapper.corpus_loss(batches, [feat_idx[1]], W_dec_cpu, mu)
        rs_val = L_a01 - L_a0 - L_a1 + L_clean
        is_finite = np.isfinite(rs_val)
        check("rs(a,b) is finite", is_finite, f"rs={rs_val:.6f}")

        # 3-way ablation
        L_a012 = wrapper.corpus_loss(batches, feat_idx[:3], W_dec_cpu, mu)
        L_a2 = wrapper.corpus_loss(batches, [feat_idx[2]], W_dec_cpu, mu)
        rs3_val = L_a012 - L_a01 - L_a2 + L_clean
        check("rs3(a,b,d) is finite", np.isfinite(rs3_val), f"rs3={rs3_val:.6f}")

        # Cocycle math — cache single losses to avoid redundant forward passes
        from harness.cocycle import compute_c, hochschild_boundary
        L_single = {}
        for i in range(n_subset):
            L_single[i] = wrapper.corpus_loss(batches, [feat_idx[i]], W_dec_cpu, mu)

        RS = torch.zeros(n_subset, n_subset)
        L_pair = {}
        for i in range(n_subset):
            for j in range(i + 1, n_subset):
                Lij = wrapper.corpus_loss(batches, [feat_idx[i], feat_idx[j]],
                                          W_dec_cpu, mu)
                L_pair[(i, j)] = Lij
                val = Lij - L_single[i] - L_single[j] + L_clean
                RS[i, j] = val
                RS[j, i] = val

        rs3_cache = {}
        for ia in range(n_subset):
            for ib in range(ia + 1, n_subset):
                Lab = L_pair.get((ia, ib),
                      wrapper.corpus_loss(batches, [feat_idx[ia], feat_idx[ib]],
                                          W_dec_cpu, mu))
                for id_ in range(n_subset):
                    key = (ia, ib, id_)
                    Labd = wrapper.corpus_loss(
                        batches, [feat_idx[ia], feat_idx[ib], feat_idx[id_]],
                        W_dec_cpu, mu)
                    rs3_cache[key] = Labd - Lab - L_single[id_] + L_clean

        bnd = hochschild_boundary(0, 1, 2, 3, RS, rs3_cache)
        check("Hochschild boundary computes", np.isfinite(bnd), f"∂c={bnd:.6f}")

        print(f"\n  ΔLoss baseline: rs(a,b)={rs_val:.4f}  rs3(a,b,d)={rs3_val:.4f}")
        print(f"  Hochschild boundary |∂c| = {abs(bnd):.4f}")
        return True

    except Exception as e:
        import traceback
        check("forward pass", False, str(e)[:80])
        traceback.print_exc()
        return False


# ─── main ─────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="Cocycle experiments preflight check")
    parser.add_argument("--config", default="configs/gpt2_small.yaml")
    args = parser.parse_args()

    print("=" * 60)
    print("  Cocycle Experiments — Preflight Check")
    print("=" * 60)

    device = check_device()
    imports = check_imports()

    # Load or build config
    cfg_path = Path(args.config)
    if cfg_path.exists():
        with open(cfg_path) as f:
            cfg = yaml.safe_load(f)
        # Override with preflight-sized params
        pf = cfg.get("preflight", {})
        cfg["corpus"]["n_tokens"] = pf.get("n_tokens", 200)
        cfg["corpus"]["max_seq_len"] = min(cfg["corpus"].get("max_seq_len", 128), 64)
        cfg["device"]["batch_size"] = pf.get("batch_size", 4)
    else:
        cfg = build_stub_cfg(device)

    cfg["device"]["prefer"] = str(device)

    # Run checks
    model_ok = run_model_check(device, cfg)
    sys.path.insert(0, str(Path(__file__).parent.parent))
    from harness.model import load_model
    wrapper = load_model(cfg)

    W_dec, sae_ok = run_sae_check(cfg)
    batches, corpus_ok = run_corpus_check(cfg, wrapper)
    loss_ok = run_loss_check(wrapper, batches, W_dec, device)

    # Summary
    section("Summary")
    all_ok = model_ok and loss_ok
    if all_ok:
        print("\n  ✓  PREFLIGHT OK — ready to run experiments")
    else:
        print("\n  ✗  PREFLIGHT FAILED — see details above")
        if not imports.get("transformer_lens"):
            print("     → Install: pip install transformer_lens sae_lens")
        if not imports.get("transformers"):
            print("     → Install: pip install transformers")

    print()
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
