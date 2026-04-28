"""
harness/feature_extractor.py — Uniform feature direction extraction.

Returns a (W_dec, feature_meta) pair regardless of the underlying source:

  feature_type = "sae"          → SAELens pretrained decoder directions
  feature_type = "mlp_neuron"   → MLP W_out rows from a specified layer
  feature_type = "attn_head"    → W_O directions per attention head per layer

All W_dec tensors are float32, shape (n_features, d_model), with approximately
unit-norm rows (not enforced for mlp_neuron/attn_head, which may not be unit-norm
from the model weights directly).

IMPORTANT — E3 interpretation note:
  When feature_type != "sae", the "features" are not SAE features but structured
  weight directions. This affects E3 (feature clustering / Neuronpedia lookup):
  - mlp_neuron: features index individual MLP neurons; interpretability is lower
    than SAE features because MLP neurons are typically polysemantic.
  - attn_head: features index attention head output directions (W_O rows);
    these have cleaner interpretability in small models (e.g. induction heads).
  E1 and E2 are unaffected by this distinction — they only require a set of
  directions and a language model for computing ΔLoss interactions.
"""
from __future__ import annotations

import logging
from typing import Dict, List, Tuple

import torch

logger = logging.getLogger(__name__)


# ─── public API ───────────────────────────────────────────────────────────────

def get_features(
    cfg: Dict,
    wrapper,                    # GenericModelWrapper (from model_loader)
) -> Tuple[torch.Tensor, Dict]:
    """
    Return (W_dec, feature_meta) for the model described in cfg.

    W_dec: (n_features, d_model) float32 — one direction per feature.
    feature_meta: dict with 'feature_type', 'n_features', 'source', etc.
    """
    sae_cfg = cfg.get("sae", {})
    feature_type = sae_cfg.get("feature_type", "sae")

    if feature_type == "sae":
        return _load_sae_features(cfg, wrapper)
    elif feature_type == "mlp_neuron":
        return _extract_mlp_neurons(cfg, wrapper)
    elif feature_type == "attn_head":
        return _extract_attn_head_dirs(cfg, wrapper)
    else:
        raise ValueError(f"Unknown feature_type: {feature_type!r}")


# ─── residual extraction (hook_point-aware) ───────────────────────────────────

@torch.no_grad()
def extract_residuals(
    wrapper,
    tokens: torch.Tensor,           # (batch, seq)
    hook_point: str,
) -> torch.Tensor:
    """
    Extract residual stream activations at hook_point.
    Works for both TransformerLens and HuggingFace backends.
    Returns tensor of shape (batch, seq, d_model).
    """
    if wrapper.backend == "transformer_lens":
        _, cache = wrapper.model.run_with_cache(tokens, names_filter=hook_point)
        return cache[hook_point].float()

    # HF fallback: infer layer index from hook_point string
    # Supports patterns: "blocks.N.hook_resid_pre" or "blocks.N.hook_resid_post"
    import re
    m = re.search(r"blocks\.(\d+)", hook_point)
    layer_idx = int(m.group(1)) if m else wrapper.hook_layer

    residuals = []
    blocks = wrapper._block_accessor(wrapper.model) if wrapper._block_accessor else []
    block = blocks[layer_idx]

    def capture_hook(module, args):
        residuals.append(args[0].detach().float())
        return args

    handle = block.register_forward_pre_hook(capture_hook)
    try:
        wrapper.model(tokens)
    finally:
        handle.remove()

    d = wrapper.model.config.hidden_size
    return residuals[0] if residuals else torch.zeros(*tokens.shape, d)


@torch.no_grad()
def compute_mean_activations_generic(
    wrapper,
    token_batches: List[torch.Tensor],
    W_dec: torch.Tensor,            # (n_features, d_model)
    feature_indices: List[int],
    cfg: Dict,
) -> torch.Tensor:
    """
    µ_i = mean ReLU projection of residual stream onto W_dec[i].
    Returns (len(feature_indices),) float32 tensor.

    Uses the hook_point from wrapper.hook_point (GenericModelWrapper attribute)
    or falls back to the config value.
    """
    from pathlib import Path
    cache_dir = Path(cfg.get("paths", {}).get("activations_dir", "activations"))
    cache_dir.mkdir(parents=True, exist_ok=True)
    n = len(feature_indices)
    cache_path = cache_dir / f"mean_activations_{n}feat.pt"

    if cache_path.exists():
        logger.info("Loading cached mean activations from %s", cache_path)
        return torch.load(cache_path, weights_only=True)

    hook_pt = getattr(wrapper, "hook_point",
                      f"blocks.{wrapper.hook_layer}.hook_resid_pre")
    device = wrapper.device
    W_sub = W_dec[feature_indices].to(device, torch.float32)

    total_acts = torch.zeros(n, device=device)
    total_tokens = 0

    for batch in token_batches:
        batch = batch.to(device)
        res = extract_residuals(wrapper, batch, hook_pt)   # (b, s, d)
        acts = torch.einsum("bsd,nd->bsn", res, W_sub).clamp(min=0.0)
        total_acts += acts.sum(dim=(0, 1))
        total_tokens += batch.shape[0] * batch.shape[1]

    mu = total_acts / max(total_tokens, 1)
    torch.save(mu.cpu(), cache_path)
    return mu.cpu()


# ─── SAE features ─────────────────────────────────────────────────────────────

def _load_sae_features(cfg: Dict, wrapper) -> Tuple[torch.Tensor, Dict]:
    """Load SAE decoder weights via SAELens (with stub fallback)."""
    from harness.features import load_sae_weights
    W_dec, sae_meta = load_sae_weights(cfg)
    meta = {
        "feature_type": "sae",
        "n_features": W_dec.shape[0],
        "source": sae_meta.get("release", "unknown"),
        "sae_id": cfg.get("sae", {}).get("sae_id", "?"),
    }
    logger.info("SAE features: %d directions (d_model=%d)", *W_dec.shape)
    return W_dec, meta


# ─── MLP neuron features ──────────────────────────────────────────────────────

def _extract_mlp_neurons(cfg: Dict, wrapper) -> Tuple[torch.Tensor, Dict]:
    """
    Extract MLP output weight directions from one or more layers.

    In TransformerLens: model.blocks[l].mlp.W_out  shape (d_mlp, d_model)
    In HuggingFace GPT-2/GPT-Neo: model.transformer.h[l].mlp.c_proj.weight
        GPT-NeoX: model.gpt_neox.layers[l].mlp.dense_4h_to_h.weight
    Each row W_out[i] ∈ R^{d_model} is the output direction for neuron i.
    """
    sae_cfg = cfg.get("sae", {})
    source_layer = sae_cfg.get("source_layer",
                               cfg.get("model", {}).get("hook_layer", 0))

    W_out = _get_mlp_w_out(wrapper, source_layer)   # (d_mlp, d_model)
    W_dec = W_out.float()

    # Normalise rows so magnitudes don't dominate
    norms = W_dec.norm(dim=1, keepdim=True).clamp(min=1e-8)
    W_dec = W_dec / norms

    meta = {
        "feature_type": "mlp_neuron",
        "n_features": W_dec.shape[0],
        "source": f"mlp_layer_{source_layer}_W_out",
        "note": (
            "MLP neuron output directions, NOT SAE features. "
            "E1/E2 are valid; E3 clustering reflects neuron specialisation "
            "rather than polysemantic SAE features."
        ),
    }
    logger.info("MLP neuron features: %d neurons from layer %d", W_dec.shape[0], source_layer)
    return W_dec.cpu(), meta


def _get_mlp_w_out(wrapper, layer: int) -> torch.Tensor:
    """Return (d_mlp, d_model) MLP output weight tensor for the given layer."""
    if wrapper.backend == "transformer_lens":
        # TransformerLens: blocks[l].mlp.W_out  (d_mlp, d_model)
        return wrapper.model.blocks[layer].mlp.W_out.detach().cpu()

    # HuggingFace — architecture-specific
    arch = getattr(wrapper, "arch", "gpt2")
    if arch in ("gpt2", "gpt_neo"):
        # c_proj weight: GPT-2 stores (d_model, d_mlp) transposed
        w = wrapper.model.transformer.h[layer].mlp.c_proj.weight
        return w.detach().T.cpu()   # → (d_mlp, d_model)
    elif arch == "neox":
        # dense_4h_to_h: (d_mlp, d_model) already
        w = wrapper.model.gpt_neox.layers[layer].mlp.dense_4h_to_h.weight
        return w.detach().cpu()
    else:
        raise ValueError(f"MLP weight extraction not implemented for arch={arch!r}")


# ─── Attention head features ──────────────────────────────────────────────────

def _extract_attn_head_dirs(cfg: Dict, wrapper) -> Tuple[torch.Tensor, Dict]:
    """
    Extract W_O directions for each attention head in each specified layer.

    In TransformerLens: model.blocks[l].attn.W_O  shape (n_heads, d_head, d_model)
    Each slice W_O[h] ∈ R^{d_head × d_model}.
    We reduce to a single d_model direction per head by taking the leading
    singular vector of W_O[h] (a cleaner 1-D direction than e.g. the mean).

    Total features = n_heads × n_source_layers.
    """
    sae_cfg = cfg.get("sae", {})
    model_cfg = cfg.get("model", {})
    source_layers = sae_cfg.get("source_layers",
                                list(range(model_cfg.get("n_layers", 2))))
    n_heads = sae_cfg.get("n_heads", model_cfg.get("n_heads", 8))

    all_dirs = []
    for layer in source_layers:
        W_O = _get_attn_w_o(wrapper, layer)   # (n_heads, d_head, d_model)
        for h in range(W_O.shape[0]):
            # Leading left singular vector: shape (d_model,)
            U, _, _ = torch.linalg.svd(W_O[h].float(), full_matrices=False)
            all_dirs.append(U[:, 0])           # (d_model,)

    W_dec = torch.stack(all_dirs, dim=0)       # (n_heads * n_layers, d_model)

    meta = {
        "feature_type": "attn_head",
        "n_features": W_dec.shape[0],
        "source": f"attn_W_O_svd_layers_{'_'.join(map(str, source_layers))}",
        "note": (
            "Attention head output directions (leading SVD direction of W_O per head). "
            "NOT SAE features. E1/E2 are valid; E3 clustering reflects attention head "
            "specialisation (e.g. induction heads, positional heads) rather than "
            "polysemantic SAE features."
        ),
    }
    logger.info(
        "Attn-head features: %d directions from %d layers × %d heads",
        W_dec.shape[0], len(source_layers), n_heads,
    )
    return W_dec.cpu(), meta


def _get_attn_w_o(wrapper, layer: int) -> torch.Tensor:
    """Return (n_heads, d_head, d_model) W_O for the given layer."""
    if wrapper.backend == "transformer_lens":
        return wrapper.model.blocks[layer].attn.W_O.detach().cpu()

    arch = getattr(wrapper, "arch", "gpt2")
    if arch in ("gpt2", "gpt_neo"):
        # HF GPT-2: attn.c_proj.weight shape (d_model, d_model) — no per-head split
        # We split manually assuming equal head size
        d_model = wrapper.model.config.hidden_size
        n_heads = wrapper.model.config.num_attention_heads
        d_head = d_model // n_heads
        w = wrapper.model.transformer.h[layer].attn.c_proj.weight  # (d_model, d_model)
        # Reshape (d_model, n_heads, d_head) then transpose to (n_heads, d_head, d_model)
        return w.detach().T.reshape(n_heads, d_head, d_model).cpu()
    else:
        raise ValueError(f"Attn W_O extraction not implemented for arch={arch!r}")
