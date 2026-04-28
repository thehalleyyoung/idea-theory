"""
harness/model_loader.py — Multi-model dispatcher for cocycle experiments.

Extends the base ModelWrapper to support configurable hook points and
architecture-specific block accessors for non-GPT-2 models (Pythia/NeoX,
GPT-Neo, TransformerLens toy models, etc.).

Usage:
    from harness.model_loader import load_model_for_config
    wrapper = load_model_for_config(cfg)
"""
from __future__ import annotations

import logging
from typing import Dict, Optional

import torch

from harness.model import ModelWrapper, resolve_device

logger = logging.getLogger(__name__)

# ─── architecture → HF block accessor ────────────────────────────────────────
# Maps arch tag (from config model.arch) to a callable that returns the
# nn.Module list of transformer blocks given a loaded HF model.

_BLOCK_ACCESSORS = {
    "gpt2":        lambda m: m.transformer.h,
    "gpt_neo":     lambda m: m.transformer.h,       # GPT-Neo same as GPT-2
    "neox":        lambda m: m.gpt_neox.layers,     # GPT-NeoX (Pythia)
    "llama":       lambda m: m.model.layers,
    "tl_attn_only": None,                           # must use TransformerLens
}


# ─── extended wrapper with configurable hook point ────────────────────────────

class GenericModelWrapper(ModelWrapper):
    """
    Extends ModelWrapper with:
    - Configurable hook_point string (not just hook_layer + hardcoded "_resid_pre").
    - Architecture-aware block accessor for the HF ablation path.
    """

    def __init__(
        self,
        backend: str,
        raw_model,
        tokenizer,
        device: torch.device,
        hook_layer: int,
        hook_point: str,
        arch: str = "gpt2",
        dtype: torch.dtype = torch.float32,
    ):
        super().__init__(backend, raw_model, tokenizer, device, hook_layer, dtype)
        self.hook_point = hook_point
        self.arch = arch
        self._block_accessor = _BLOCK_ACCESSORS.get(arch, _BLOCK_ACCESSORS["gpt2"])

    # ── TransformerLens backend ────────────────────────────────────────────────

    def _loss_tl(self, tokens, ablation_set, W_dec, mu) -> float:
        if ablation_set:
            def hook_fn(value, hook):
                from harness.model import _apply_ablation
                return _apply_ablation(value.float(), ablation_set, W_dec, mu)
            loss = self.model.run_with_hooks(
                tokens,
                fwd_hooks=[(self.hook_point, hook_fn)],
                return_type="loss",
            )
        else:
            loss = self.model(tokens, return_type="loss")
        return loss.item()

    # ── HuggingFace fallback ───────────────────────────────────────────────────

    def _loss_hf(self, tokens, ablation_set, W_dec, mu) -> float:
        handles = []
        if ablation_set and self._block_accessor is not None:
            blocks = self._block_accessor(self.model)
            block = blocks[self.hook_layer]

            def pre_hook(module, args):
                from harness.model import _apply_ablation
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


# ─── loader ───────────────────────────────────────────────────────────────────

def load_model_for_config(cfg: Dict) -> GenericModelWrapper:
    """
    Load any supported model and return a GenericModelWrapper.

    Dispatch order:
      1. TransformerLens (preferred — uniform hook API)
      2. HuggingFace transformers (fallback — arch-specific block accessor)

    Raises RuntimeError if neither backend can load the model.
    """
    device = resolve_device(cfg.get("device", {}).get("prefer", "mps"))
    model_cfg = cfg.get("model", {})
    model_name = model_cfg.get("name", "gpt2")
    hook_layer = model_cfg.get("hook_layer", 0)
    hook_point = model_cfg.get(
        "hook_point",
        f"blocks.{hook_layer}.hook_resid_pre",
    )
    arch = model_cfg.get("arch", "gpt2")
    tokenizer_name = model_cfg.get("tokenizer_name", model_name)

    # ── TransformerLens ───────────────────────────────────────────────────────
    try:
        from transformer_lens import HookedTransformer
        logger.info("Trying TransformerLens for %s on %s", model_name, device)
        tl_model = HookedTransformer.from_pretrained(
            model_name,
            dtype="float32",
        )
        tl_model.to(device)
        tl_model.eval()
        logger.info("TransformerLens loaded: %s", model_name)
        return GenericModelWrapper(
            "transformer_lens", tl_model, None, device,
            hook_layer, hook_point, arch,
        )
    except ImportError:
        logger.warning("transformer_lens not installed; trying HuggingFace.")
    except Exception as tl_err:
        logger.warning("TransformerLens failed (%s); trying HuggingFace.", tl_err)

    # ── HuggingFace fallback ──────────────────────────────────────────────────
    if arch == "tl_attn_only":
        raise RuntimeError(
            f"Model '{model_name}' requires TransformerLens (arch=tl_attn_only) "
            "but transformer_lens is not installed or failed to load."
        )

    logger.info("Loading %s via HuggingFace (arch=%s) on %s", model_name, arch, device)
    try:
        from transformers import AutoModelForCausalLM, AutoTokenizer
        hf_model = AutoModelForCausalLM.from_pretrained(
            model_name,
            torch_dtype=torch.float32,
        )
        hf_model.to(device)
        hf_model.eval()
        tokenizer = AutoTokenizer.from_pretrained(tokenizer_name)
        if tokenizer.pad_token is None:
            tokenizer.pad_token = tokenizer.eos_token
        logger.info("HuggingFace loaded: %s", model_name)
        return GenericModelWrapper(
            "transformers", hf_model, tokenizer, device,
            hook_layer, hook_point, arch,
        )
    except Exception as hf_err:
        raise RuntimeError(
            f"Failed to load '{model_name}' via both TransformerLens and HuggingFace. "
            f"Last error: {hf_err}"
        ) from hf_err
