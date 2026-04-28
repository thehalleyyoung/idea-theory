"""
harness/model.py — Model loading and loss computation.

Supports two backends:
  1. TransformerLens (preferred): HookedTransformer with named hook points.
  2. HuggingFace transformers (fallback): GPT2LMHeadModel with manual hooks.

Both backends expose the same interface via ModelWrapper.
"""
from __future__ import annotations

import contextlib
import logging
from pathlib import Path
from typing import Dict, List, Optional, Sequence

import torch
import torch.nn.functional as F

logger = logging.getLogger(__name__)

# ─── device resolution ────────────────────────────────────────────────────────

def resolve_device(prefer: str = "mps") -> torch.device:
    if prefer == "mps" and torch.backends.mps.is_available():
        return torch.device("mps")
    return torch.device("cpu")


# ─── model wrapper ────────────────────────────────────────────────────────────

class ModelWrapper:
    """Unified interface for GPT-2 forward passes with mean-ablation hooks."""

    def __init__(self, backend: str, raw_model, tokenizer, device: torch.device,
                 hook_layer: int = 8, dtype: torch.dtype = torch.float32):
        self.backend = backend           # "transformer_lens" | "transformers"
        self.model = raw_model
        self.tokenizer = tokenizer
        self.device = device
        self.hook_layer = hook_layer
        self.dtype = dtype

    @torch.no_grad()
    def compute_loss_batch(
        self,
        tokens: torch.Tensor,           # (batch, seq)
        ablation_set: Sequence[int],    # feature indices to mean-ablate
        W_dec: torch.Tensor,            # (n_feat, d_model)
        mu: torch.Tensor,               # (n_feat,)  mean activations
    ) -> float:
        """Return mean per-token CE loss for one batch with optional ablation."""
        tokens = tokens.to(self.device)
        if self.backend == "transformer_lens":
            return self._loss_tl(tokens, ablation_set, W_dec, mu)
        return self._loss_hf(tokens, ablation_set, W_dec, mu)

    # ── TransformerLens backend ────────────────────────────────────────────────

    def _loss_tl(self, tokens, ablation_set, W_dec, mu) -> float:
        hook_pt = f"blocks.{self.hook_layer}.hook_resid_pre"
        if ablation_set:
            def hook_fn(value, hook):
                return _apply_ablation(value.float(), ablation_set, W_dec, mu)
            loss = self.model.run_with_hooks(
                tokens,
                fwd_hooks=[(hook_pt, hook_fn)],
                return_type="loss",
            )
        else:
            loss = self.model(tokens, return_type="loss")
        return loss.item()

    # ── HuggingFace transformers backend ──────────────────────────────────────

    def _loss_hf(self, tokens, ablation_set, W_dec, mu) -> float:
        handles = []
        if ablation_set:
            block = self.model.transformer.h[self.hook_layer]

            def pre_hook(module, args):
                hidden = args[0].float()
                hidden = _apply_ablation(hidden, ablation_set, W_dec, mu)
                return (hidden,) + args[1:]

            handles.append(block.register_forward_pre_hook(pre_hook))

        try:
            out = self.model(tokens, labels=tokens)
            loss = out.loss
        finally:
            for h in handles:
                h.remove()

        return loss.item()

    # ── corpus loss sweep ─────────────────────────────────────────────────────

    @torch.no_grad()
    def corpus_loss(
        self,
        token_batches: List[torch.Tensor],   # list of (batch, seq) tensors
        ablation_set: Sequence[int],
        W_dec: torch.Tensor,
        mu: torch.Tensor,
    ) -> float:
        """Mean CE loss over all batches."""
        total, count = 0.0, 0
        for batch in token_batches:
            total += self.compute_loss_batch(batch, ablation_set, W_dec, mu)
            count += 1
        return total / max(count, 1)


# ─── ablation primitive ───────────────────────────────────────────────────────

def _apply_ablation(
    hidden: torch.Tensor,           # (..., d_model)
    feature_set: Sequence[int],
    W_dec: torch.Tensor,            # (n_feat, d_model)
    mu: torch.Tensor,               # (n_feat,)
) -> torch.Tensor:
    """Mean-ablate features in feature_set from the hidden state."""
    W_dec = W_dec.to(hidden.device, hidden.dtype)
    mu = mu.to(hidden.device, hidden.dtype)
    for idx in feature_set:
        d = W_dec[idx]                              # (d_model,)
        proj = torch.einsum("...d,d->...", hidden, d).unsqueeze(-1) * d
        hidden = hidden - proj + mu[idx] * d
    return hidden


# ─── model loading ────────────────────────────────────────────────────────────

def load_model(cfg: Dict) -> ModelWrapper:
    """Load GPT-2-small, preferring TransformerLens, falling back to HF."""
    device = resolve_device(cfg.get("device", {}).get("prefer", "mps"))
    hook_layer = cfg.get("model", {}).get("hook_layer", 8)
    model_name = cfg.get("model", {}).get("name", "gpt2")

    try:
        from transformer_lens import HookedTransformer
        logger.info("Loading model via TransformerLens on %s", device)
        tl_model = HookedTransformer.from_pretrained(model_name, dtype="float32")
        tl_model.to(device)
        tl_model.eval()
        return ModelWrapper("transformer_lens", tl_model, None, device, hook_layer)
    except ImportError:
        pass

    logger.info("TransformerLens not available; falling back to HuggingFace on %s", device)
    from transformers import GPT2LMHeadModel, GPT2TokenizerFast
    hf_model = GPT2LMHeadModel.from_pretrained(model_name, dtype=torch.float32)
    hf_model.to(device)
    hf_model.eval()
    tokenizer = GPT2TokenizerFast.from_pretrained(model_name)
    tokenizer.pad_token = tokenizer.eos_token
    return ModelWrapper("transformers", hf_model, tokenizer, device, hook_layer)
