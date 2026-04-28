"""
scripts/run_e3.py — Experiment E3: Failure Localization.

Clusters features by cocycle-violation magnitude, cross-references with
Neuronpedia labels. Requires E1 results.

Usage:
    cd experiments/cocycle
    python -m scripts.run_e3 --config configs/gpt2_small.yaml
"""
from __future__ import annotations

import argparse
import json
import logging
import sys
from pathlib import Path

import numpy as np
import torch
import yaml

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s  %(message)s")
logger = logging.getLogger("run_e3")

ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(ROOT))


def run_e3(e1_summary: dict, RS: torch.Tensor, feature_indices: list,
           cfg: dict, results_dir: Path) -> dict:
    from sklearn.cluster import KMeans
    from scipy.stats import chisquare

    per_feat_V = e1_summary.get("per_feature_V", {})
    if not per_feat_V:
        logger.warning("per_feature_V empty — no E1 data for E3.")
        return {}

    # Rank features by violation score
    feat_ranking = sorted(per_feat_V.items(), key=lambda x: -x[1])
    n = len(feature_indices)

    # Build feature→index lookup
    feat_to_idx = {str(f): i for i, f in enumerate(feature_indices)}
    feat_to_idx.update({f: i for i, f in enumerate(feature_indices)})

    # Gini & concentration
    vals = [v for _, v in feat_ranking]
    total = max(sum(vals), 1e-10)
    k5 = max(1, int(len(vals) * 0.05))
    top5_share = sum(vals[:k5]) / total
    arr = np.array(sorted(vals), dtype=float)
    idx = np.arange(1, len(arr) + 1)
    gini = float((2 * (idx * arr).sum() / (len(arr) * arr.sum()) - (len(arr) + 1) / len(arr)))

    # k-means on RS rows (interaction profiles)
    n_clusters = cfg["experiments"].get("n_clusters", 5)
    seed_km = cfg["experiments"].get("seed_kmeans", 99)
    RS_np = RS.numpy()
    km = KMeans(n_clusters=n_clusters, random_state=seed_km, n_init=10)
    cluster_labels = km.fit_predict(RS_np)  # (n,)

    # Chi-square: do top-50 violators concentrate in fewer clusters?
    n_top = min(50, len(feat_ranking))
    top_fids = [fid for fid, _ in feat_ranking[:n_top]]
    top_idxs = [feat_to_idx.get(fid, feat_to_idx.get(str(fid), None)) for fid in top_fids]
    top_idxs = [i for i in top_idxs if i is not None]

    if top_idxs:
        from collections import Counter
        cluster_counts = Counter(cluster_labels[i] for i in top_idxs)
        obs = np.array([cluster_counts.get(c, 0) for c in range(n_clusters)], dtype=float)
        exp = np.full(n_clusters, len(top_idxs) / n_clusters)
        chi2_stat, chi2_p = chisquare(obs, exp)
    else:
        chi2_stat, chi2_p = 0.0, 1.0

    # Neuronpedia lookup (top-20 violators, graceful failure)
    top20_labels = _query_neuronpedia(top_fids[:20])

    # Build markdown table
    md_lines = [
        "# E3 Top Violators\n",
        "| Rank | Feature ID | Violation V | Cluster | Neuronpedia Label |",
        "|------|-----------|-------------|---------|-------------------|",
    ]
    for rank, (fid, v) in enumerate(feat_ranking[:20], 1):
        idx_k = feat_to_idx.get(fid, feat_to_idx.get(str(fid), None))
        cl = int(cluster_labels[idx_k]) if idx_k is not None else -1
        label = next((d.get("label", "—") for d in top20_labels
                      if str(d.get("feature_id")) == str(fid)), "—")
        md_lines.append(f"| {rank} | {fid} | {v:.4f} | {cl} | {label} |")

    results_dir.mkdir(parents=True, exist_ok=True)
    md_path = results_dir / "e3_top_violators.md"
    with open(md_path, "w") as f:
        f.write("\n".join(md_lines) + "\n")

    summary = {
        "gini": float(gini),
        "top5pct_share": float(top5_share),
        "n_features_ranked": len(feat_ranking),
        "chi2_statistic": float(chi2_stat),
        "chi2_pvalue": float(chi2_p),
        "cluster_labels": cluster_labels.tolist(),
        "top20_neuronpedia": top20_labels,
        "feature_ranking_top50": [(str(fid), float(v)) for fid, v in feat_ranking[:50]],
    }
    out = results_dir / "e3_summary.json"
    with open(out, "w") as f:
        json.dump({k: v for k, v in summary.items()
                   if k not in ("cluster_labels",)}, f, indent=2)
    logger.info("E3 results saved to %s", out)
    return summary


def _query_neuronpedia(feature_ids: list) -> list:
    """Query Neuronpedia API for feature labels (graceful failure)."""
    results = []
    try:
        import requests
        for fid in feature_ids:
            try:
                url = f"https://www.neuronpedia.org/api/feature/gpt2-small/8-res-jb/{fid}"
                resp = requests.get(url, timeout=5)
                if resp.ok:
                    data = resp.json()
                    results.append({
                        "feature_id": fid,
                        "label": data.get("description", "unlabeled"),
                        "top_examples": data.get("topActivations", [])[:3],
                    })
                else:
                    results.append({"feature_id": fid, "label": "api_error", "top_examples": []})
            except Exception:
                results.append({"feature_id": fid, "label": "lookup_failed", "top_examples": []})
    except ImportError:
        logger.warning("requests not installed — skipping Neuronpedia lookup.")
    return results


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", default="configs/gpt2_small.yaml")
    args = parser.parse_args()

    with open(args.config) as f:
        cfg = yaml.safe_load(f)

    results_dir = ROOT / cfg["paths"]["results_dir"]
    act_dir = ROOT / cfg["paths"]["activations_dir"]
    cfg["paths"]["activations_dir"] = str(act_dir)
    cfg["paths"]["results_dir"] = str(results_dir)

    # Load E1 results
    e1_path = results_dir / "e1_summary.json"
    if not e1_path.exists():
        logger.error("E1 results not found at %s — run run_e1 first.", e1_path)
        return 1
    with open(e1_path) as f:
        e1_summary = json.load(f)

    # Load RS matrix
    n_feat = cfg["experiments"]["n_features"]
    rs_path = act_dir / f"rs_matrix_{n_feat}feat.pt"
    if not rs_path.exists():
        logger.error("RS matrix not found at %s — run run_e1 first.", rs_path)
        return 1
    RS = torch.load(rs_path, weights_only=True)

    n_total = cfg["sae"]["n_features_total"]
    rng0 = np.random.default_rng(cfg["experiments"]["seed_features"])
    feature_indices = rng0.choice(n_total, size=n_feat, replace=False).tolist()

    summary = run_e3(e1_summary, RS, feature_indices, cfg, results_dir)

    print("\n── E3 Results ───────────────────────────────────────")
    print(f"  gini            = {summary.get('gini', '?'):.4f}")
    print(f"  top5%_share     = {summary.get('top5pct_share', 0):.2%}")
    print(f"  chi2_pvalue     = {summary.get('chi2_pvalue', '?'):.4e}")
    print(f"  Saved → {results_dir}/e3_summary.json")
    print(f"  Table → {results_dir}/e3_top_violators.md")
    return 0


if __name__ == "__main__":
    sys.exit(main())
