"""
scripts/aggregate_models.py — Aggregate E1/E2/E3 results across all models.

Reads results/<model>/e{1,2,3}_summary.json and produces:
  - results/cross_model_table.md    — Markdown table for the paper
  - results/cross_model_table.tex   — LaTeX tabular for \input{}
  - results/cross_model_summary.json — raw aggregated stats

Usage:
    cd experiments/cocycle
    python -m scripts.aggregate_models
    python -m scripts.aggregate_models --results-dir results
"""
from __future__ import annotations

import argparse
import json
import logging
from pathlib import Path
from typing import Dict, List, Optional

logger = logging.getLogger(__name__)
logging.basicConfig(level=logging.INFO, format="%(levelname)s  %(message)s")

HERE = Path(__file__).parent.parent


# ─── data loading ─────────────────────────────────────────────────────────────

def load_model_results(results_dir: Path) -> Dict[str, dict]:
    """
    Scan results_dir for per-model subdirectories containing e*_summary.json.
    Returns dict mapping model_name → {e1: ..., e2: ..., e3: ..., feature_type: ...}.
    """
    model_results = {}
    for model_dir in sorted(results_dir.iterdir()):
        if not model_dir.is_dir():
            continue
        model_name = model_dir.name
        entry: dict = {"model": model_name}

        for exp in ("e1", "e2", "e3"):
            p = model_dir / f"{exp}_summary.json"
            if p.exists():
                with open(p) as f:
                    entry[exp] = json.load(f)
            else:
                entry[exp] = None

        # Load run_status for feature_type
        status_p = model_dir / "run_status.json"
        if status_p.exists():
            with open(status_p) as f:
                st = json.load(f)
            entry["feature_type"] = (
                st.get("feature_meta", {}).get("feature_type")
                or st.get("feature_type", "?")
            )
            entry["backend"] = st.get("backend", "?")
            entry["n_features"] = st.get("n_features_total", "?")
        else:
            entry["feature_type"] = "?"
            entry["backend"] = "?"
            entry["n_features"] = "?"

        if any(entry[e] is not None for e in ("e1", "e2", "e3")):
            model_results[model_name] = entry
            logger.info("Loaded: %s (e1=%s, e2=%s, e3=%s)",
                        model_name,
                        "✓" if entry["e1"] else "–",
                        "✓" if entry["e2"] else "–",
                        "✓" if entry["e3"] else "–")

    return model_results


# ─── formatting helpers ───────────────────────────────────────────────────────

def _fmt(val, fmt=".4f", missing="–") -> str:
    if val is None:
        return missing
    try:
        return format(float(val), fmt)
    except (TypeError, ValueError):
        return str(val)


def _e1_row(e1: Optional[dict]) -> dict:
    if e1 is None:
        return {"mean_V": None, "null_V": None, "p_e1": None, "cohen_d": None}
    return {
        "mean_V": e1.get("mean_violation_empirical"),
        "null_V": e1.get("mean_violation_null"),
        "p_e1":   e1.get("p_value"),
        "cohen_d": e1.get("cohen_d"),
    }


def _e2_row(e2: Optional[dict]) -> dict:
    if e2 is None:
        return {"R2_add": None, "R2_coc": None, "delta_R2": None, "p_e2": None}
    return {
        "R2_add":   e2.get("R2_additive"),
        "R2_cocycle": e2.get("R2_cocycle"),
        "delta_R2": e2.get("delta_R2"),
        "p_e2":     e2.get("p_value_welch"),
    }


# ─── Markdown table ───────────────────────────────────────────────────────────

def build_markdown_table(model_results: Dict[str, dict]) -> str:
    lines = [
        "# Cross-Model Cocycle Experiment Results\n",
        "| Model | Feature type | # feat | "
        "E1 mean V | E1 null V | E1 p | E1 d | "
        "E2 R²(add) | E2 R²(coc) | E2 ΔR² | E2 p |",
        "|:------|:------------|-------:|"
        "----------:|----------:|-----:|-----:|"
        "----------:|----------:|-------:|-----:|",
    ]

    for name, entry in sorted(model_results.items()):
        e1 = _e1_row(entry.get("e1"))
        e2 = _e2_row(entry.get("e2"))
        ft = entry.get("feature_type", "?")
        nf = entry.get("n_features", "?")

        lines.append(
            f"| `{name}` | {ft} | {nf} | "
            f"{_fmt(e1['mean_V'])} | {_fmt(e1['null_V'])} | "
            f"{_fmt(e1['p_e1'], '.2e')} | {_fmt(e1['cohen_d'])} | "
            f"{_fmt(e2['R2_add'])} | {_fmt(e2['R2_cocycle'])} | "
            f"{_fmt(e2['delta_R2'])} | {_fmt(e2['p_e2'], '.2e')} |"
        )

    lines.append("")
    lines.append(
        "> **Feature type notes:** "
        "`sae` = pretrained SAE decoder directions; "
        "`mlp_neuron` = MLP output weight rows (no SAE available); "
        "`attn_head` = attention head W_O SVD directions (no SAE available). "
        "E1 and E2 are valid for all types; "
        "E3 clustering reflects neuron/head specialisation for non-SAE types."
    )
    return "\n".join(lines) + "\n"


# ─── LaTeX table ──────────────────────────────────────────────────────────────

def build_latex_table(model_results: Dict[str, dict]) -> str:
    rows = []
    for name, entry in sorted(model_results.items()):
        e1 = _e1_row(entry.get("e1"))
        e2 = _e2_row(entry.get("e2"))
        ft = entry.get("feature_type", "?").replace("_", "\\_")
        nf = entry.get("n_features", "?")
        model_label = name.replace("_", "\\_")

        rows.append(
            f"    \\texttt{{{model_label}}} & {ft} & {nf} & "
            f"{_fmt(e1['mean_V'])} & {_fmt(e1['null_V'])} & "
            f"{_fmt(e1['p_e1'], '.2e')} & {_fmt(e1['cohen_d'])} & "
            f"{_fmt(e2['R2_add'])} & {_fmt(e2['R2_cocycle'])} & "
            f"{_fmt(e2['delta_R2'])} & {_fmt(e2['p_e2'], '.2e')} \\\\"
        )

    cols = "l l r r r r r r r r r"
    header_a = (
        "Model & Feat.\\,type & $|\\mathcal{F}|$ & "
        "$\\bar{V}$ & $\\bar{V}_{\\text{null}}$ & $p_{\\text{E1}}$ & $d_{\\text{E1}}$ & "
        "$R^2_{\\text{add}}$ & $R^2_{\\text{coc}}$ & $\\Delta R^2$ & $p_{\\text{E2}}$"
    )
    lines = [
        "% Auto-generated by scripts/aggregate_models.py",
        "% \\input this file directly inside a table environment.",
        f"\\begin{{tabular}}{{{cols}}}",
        "  \\toprule",
        f"  {header_a} \\\\",
        "  \\midrule",
    ] + rows + [
        "  \\bottomrule",
        "\\end{tabular}",
        "",
        "% Feature type note:",
        "% sae = SAELens pretrained SAE decoder directions",
        "% mlp\\_neuron = MLP output weight rows (no SAE available)",
        "% attn\\_head = attention head W\\_O SVD directions (no SAE available)",
    ]
    return "\n".join(lines) + "\n"


# ─── main ─────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="Aggregate cross-model results.")
    parser.add_argument("--results-dir", default="results",
                        help="Directory containing per-model result subdirs.")
    args = parser.parse_args()

    results_dir = HERE / args.results_dir
    if not results_dir.exists():
        logger.error("Results directory not found: %s", results_dir)
        return

    model_results = load_model_results(results_dir)
    if not model_results:
        logger.error("No model results found in %s", results_dir)
        return

    logger.info("Aggregating %d models: %s", len(model_results), list(model_results))

    # Write outputs
    md_path = results_dir / "cross_model_table.md"
    md_path.write_text(build_markdown_table(model_results))
    logger.info("Markdown table: %s", md_path)

    tex_path = results_dir / "cross_model_table.tex"
    tex_path.write_text(build_latex_table(model_results))
    logger.info("LaTeX table: %s", tex_path)

    # Build raw summary JSON (drop large arrays)
    raw = {}
    for name, entry in model_results.items():
        raw[name] = {
            "model": entry["model"],
            "feature_type": entry.get("feature_type"),
            "backend": entry.get("backend"),
            "n_features": entry.get("n_features"),
            "e1": entry.get("e1"),
            "e2": {k: v for k, v in (entry.get("e2") or {}).items()
                   if k not in ("T_ground_truth", "T_additive", "T_cocycle")},
            "e3": entry.get("e3"),
        }

    summary_path = results_dir / "cross_model_summary.json"
    summary_path.write_text(json.dumps(raw, indent=2))
    logger.info("JSON summary: %s", summary_path)

    # Print table to stdout
    print("\n" + "=" * 70)
    print(build_markdown_table(model_results))


if __name__ == "__main__":
    main()
