# Cocycle Experiments — Apple Silicon MPS Harness

Empirical validation of the **cocycle identity** for higher-order feature
interactions in GPT-2-small SAE residual-stream features (layer 8).

---

## Requirements

| Requirement | Value |
|---|---|
| Python | ≥ 3.11 |
| PyTorch | ≥ 2.3 (MPS backend) |
| RAM | ≥ 16 GB (Apple Silicon unified memory) |
| Estimated wall-clock | E1: ~1–8 h (depends on `n_features`); E2+E3: ~1 h incremental |

---

## Installation

```bash
cd experiments/cocycle
pip install -r requirements.txt
```

`transformer_lens` and `sae_lens` are **optional** for the preflight — it
falls back to HuggingFace `transformers` + random SAE stub when they are
absent. For full experiments you need them:

```bash
pip install transformer_lens sae_lens datasets
```

---

## Preflight (verify setup, < 2 min)

```bash
cd experiments/cocycle
python -m scripts.preflight --config configs/gpt2_small.yaml
```

Expected output (MPS machine):
```
── Device ──────────────────────────────────────────────────
  [✓] MPS available  (Apple Silicon GPU backend active)
     device = mps
── Imports ─────────────────────────────────────────────────
  [✓] transformer_lens  (2.x.x)
  [✓] sae_lens          (3.x.x)
  ...
── Summary ──────────────────────────────────────────────────
  ✓  PREFLIGHT OK — ready to run experiments
```

### Fallback mode (no transformer_lens / sae_lens)

If the heavy deps are missing, the preflight runs a CPU/HF fallback:
- Uses `transformers.GPT2LMHeadModel` directly
- Generates random unit-norm SAE directions (stub)
- Verifies that the ΔLoss / cocycle math is numerically correct
- Still prints **PREFLIGHT OK**

---

## Running experiments

All scripts accept `--config configs/gpt2_small.yaml`.

### E1 — Cocycle Identity Validation

```bash
python -m scripts.run_e1 --config configs/gpt2_small.yaml
```

Outputs `results/e1_summary.json` with:
- `mean_violation_empirical`, `mean_violation_null`, `ratio_emp_null`
- `p_value`, `cohen_d` (one-sided t-test vs permutation null)
- `gini`, `top5pct_share` (violation concentration)
- `per_feature_V` (per-feature violation scores)

### E2 — Triple Interaction Prediction

```bash
python -m scripts.run_e2 --config configs/gpt2_small.yaml
```

Requires E1 to have run first (reuses cached RS matrix and rs3 triples).
Outputs `results/e2_summary.json` with:
- `R2_additive`, `R2_cocycle`, `delta_R2`
- `MAE_additive`, `MAE_cocycle`
- `spearman_additive`, `spearman_cocycle`
- `p_value_welch` (Welch t-test on squared errors)

### E3 — Failure Localization

```bash
python -m scripts.run_e3 --config configs/gpt2_small.yaml
```

Requires E1 results. Outputs:
- `results/e3_summary.json` — Gini, chi-square cluster test
- `results/e3_top_violators.md` — markdown table of top-20 violators with Neuronpedia labels

---

## Configuration (`configs/gpt2_small.yaml`)

Key parameters:

| Parameter | Default (MPS) | Full (A100) | Notes |
|---|---|---|---|
| `experiments.n_features` | 50 | 500 | Feature subset size |
| `corpus.n_tokens` | 10,000 | 500,000 | Tokens for corpus |
| `corpus.max_seq_len` | 128 | 256 | MPS constraint: ≤ 128 |
| `device.batch_size` | 8 | 32 | MPS constraint: ≤ 8 |
| `experiments.n_quadruples` | 10,000 | 10,000 | E1 quadruples |

To run a quick test with 10 features and 200 tokens, use the preflight config:
```yaml
preflight:
  n_features: 10
  n_tokens: 200
```

---

## Caching

All forward passes are cached under `activations/`:
- `loss_clean.pt` — clean corpus loss
- `loss_abl_<idx>.pt` — single-feature ablation losses
- `loss_abl_<i>_<j>.pt` — pair ablation losses
- `rs_matrix_<n>feat.pt` — full RS matrix
- `mean_activations_<n>feat.pt` — mean SAE activations

Delete these to force recomputation.

---

## MPS Constraints

| Constraint | Value | Reason |
|---|---|---|
| dtype | fp32 | MPS fp16 buggy in PyTorch < 2.5 |
| batch_size | ≤ 8 | Avoid OOM on 16 GB unified memory |
| seq_len | ≤ 128 | MPS attention kernel stability |
| Total wall-clock | ≤ 12 h | 50-feature run on M-series Mac |

---

## Mathematical Background

### Interaction kernel

`rs(a, b) = E_x[L(M_{ab}(x)) - L(M_a(x)) - L(M_b(x)) + L(M(x))]`

where `M_S(x)` is the forward pass with features S mean-ablated at layer 8.

### 3-cochain

`c(a, b, d) = rs3(a, b, d) - rs(a, d) - rs(b, d)`

where `rs3(a, b, d) = L(M_{abd}) - L(M_{ab}) - L(M_d) + L(M)`.

### Hochschild boundary (trivial G-module)

`∂c(a,b,d,e) = c(b,d,e) - c(a◦b,d,e) + c(a,b◦d,e) - c(a,b,d◦e) + c(a,b,d)`

**H₁:** `mean(|∂c|) < mean(|∂c_perm|)` — the identity constrains more than chance.

---

## Reproducing from scratch

```bash
git clone https://github.com/thehalleyyoung/idea-theory
cd idea-theory/experiments/cocycle

# 1. Install deps
pip install -r requirements.txt

# 2. Verify
python -m scripts.preflight

# 3. Run E1 (dominant cost)
python -m scripts.run_e1 --config configs/gpt2_small.yaml

# 4. Run E2 + E3
python -m scripts.run_e2 --config configs/gpt2_small.yaml
python -m scripts.run_e3 --config configs/gpt2_small.yaml
```

Results are written to `results/`. All random seeds are fixed:

| Seed | Purpose |
|---|---|
| 0 | Feature subset selection |
| 1 | E1 quadruples |
| 2 | E2 test triples |
| 7 | Stub SAE directions |
| 10 | LASSO CV |
| 42 | Corpus sampling |
| 99 | k-means |

---

## Multi-model reproduction

Runs E1/E2/E3 across **all** model configs, then aggregates into paper-ready tables.

### Supported models

| Config | Model | Feature source | d\_model |
|--------|-------|---------------|---------|
| `gpt2_small.yaml` | GPT-2-small | SAELens (`gpt2-small-res-jb`) | 768 |
| `pythia_70m.yaml` | Pythia-70m-deduped | SAELens (`pythia-70m-deduped-res-sm`) | 512 |
| `tinystories_33m.yaml` | TinyStories-33M | MLP neuron W\_out (no SAE) | 768 |
| `attn_only_2l.yaml` | attn-only-2l (TL toy) | Attn head W\_O SVD (no SAE) | 256 |

### Running the sweep

```bash
# Preflight all models first (fast — just loads model + tokenizes corpus)
python -m scripts.run_all_models --preflight-only

# Full sweep: E1/E2/E3 for every config
python -m scripts.run_all_models

# Specific models only
python -m scripts.run_all_models --configs pythia_70m tinystories_33m

# Aggregate into tables
python -m scripts.aggregate_models
```

Output files:

```
results/
  pythia_70m/
    e1_summary.json    e2_summary.json    e3_summary.json    run_status.json
  tinystories_33m/
    ...
  attn_only_2l/
    ...
  cross_model_table.md         # Markdown table for the paper
  cross_model_table.tex        # LaTeX tabular for \input{}
  cross_model_summary.json     # Raw aggregated stats
```

### Feature-type notes and E3 interpretation

**`sae` features** (GPT-2-small, Pythia-70m):
Pretrained SAE decoder directions from SAELens. E1, E2, and E3 are all
interpretable in the standard cocycle-identity framework.

**`mlp_neuron` features** (TinyStories-33M):
No pretrained SAE exists for this model. Features are MLP output weight rows
(W\_out[i] ∈ R^{d\_model}). MLP neurons are typically *polysemantic*, meaning
each neuron responds to multiple unrelated input patterns. E1 and E2 remain
fully valid. E3 clustering reflects MLP neuron connectivity structure
rather than semantically clean SAE clusters.

**`attn_head` features** (attn-only-2l):
Features are the leading SVD direction of W\_O for each attention head in each
layer (8 heads × 2 layers = 16 total directions). In small attention-only models,
these directions often correspond to interpretable circuits (induction heads,
bigram heads). E1 and E2 are fully valid; E3 clusters reflect head-level
functional specialisation.

### Adding a new model

1. Add `configs/<name>.yaml` following the existing templates.
2. Set `model.arch` to one of: `gpt2`, `gpt_neo`, `neox`, `tl_attn_only`.
3. Set `sae.feature_type` to `sae`, `mlp_neuron`, or `attn_head`.
4. Run `python -m scripts.preflight --config configs/<name>.yaml`.
5. If preflight passes, include it in the sweep.
