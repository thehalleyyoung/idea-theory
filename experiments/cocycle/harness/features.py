"""
harness/features.py — SAE loading, mean activations, corpus tokenization.

Provides:
  - load_sae_weights(): returns (W_dec, sae_cfg)
  - compute_mean_activations(): µ_i = mean SAE activation over corpus
  - tokenize_corpus(): returns list of (batch, seq) token tensors
  - stub_sae_weights(): random unit-norm directions for testing
"""
from __future__ import annotations

import logging
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np
import torch

logger = logging.getLogger(__name__)

# ─── SAE loading ──────────────────────────────────────────────────────────────

def load_sae_weights(cfg: Dict) -> Tuple[torch.Tensor, Dict]:
    """
    Load SAE decoder weights from SAELens.

    Returns:
        W_dec: (n_features, d_model) float32, unit-norm rows
        sae_cfg: dict of SAE metadata
    """
    sae_cfg = cfg.get("sae", {})
    release = sae_cfg.get("release", "gpt2-small-res-jb")
    sae_id = sae_cfg.get("sae_id", "blocks.8.hook_resid_pre_24576")

    try:
        from sae_lens import SAE
        logger.info("Loading SAE: release=%s, id=%s", release, sae_id)
        sae, cfg_dict, _ = SAE.from_pretrained(release=release, sae_id=sae_id)
        W_dec = sae.W_dec.float()          # (n_features, d_model)
        return W_dec, cfg_dict
    except ImportError:
        logger.warning("sae_lens not installed — using stub random SAE directions.")
        return stub_sae_weights(cfg)
    except Exception as e:
        logger.warning("SAE load failed (%s) — using stub.", e)
        return stub_sae_weights(cfg)


def stub_sae_weights(cfg: Dict, seed: int = 7) -> Tuple[torch.Tensor, Dict]:
    """Generate random unit-norm directions as a stub SAE (for testing)."""
    n = cfg.get("sae", {}).get("n_features_total", 24576)
    d = cfg.get("model", {}).get("d_model", 768)
    rng = np.random.default_rng(seed)
    W = torch.from_numpy(rng.standard_normal((n, d)).astype(np.float32))
    W = W / W.norm(dim=1, keepdim=True).clamp(min=1e-8)
    return W, {"release": "stub", "d_in": d, "d_sae": n}


# ─── mean activations ─────────────────────────────────────────────────────────

@torch.no_grad()
def compute_mean_activations(
    wrapper,                   # ModelWrapper
    token_batches: List[torch.Tensor],
    W_dec: torch.Tensor,       # (n_features, d_model)
    feature_indices: List[int],
    cfg: Dict,
) -> torch.Tensor:
    """
    Compute µ_i = mean activation of SAE feature i over the corpus.

    Activation of feature i at token x:
        act_i(x) = max(0, W_dec[i] @ resid(x))

    Returns:
        mu: (n_features,) float32
    """
    cache_dir = Path(cfg.get("paths", {}).get("activations_dir", "activations"))
    cache_dir.mkdir(parents=True, exist_ok=True)
    n = len(feature_indices)
    cache_path = cache_dir / f"mean_activations_{n}feat.pt"

    if cache_path.exists():
        logger.info("Loading cached mean activations from %s", cache_path)
        return torch.load(cache_path, weights_only=True)

    logger.info("Computing mean activations for %d features over %d batches",
                n, len(token_batches))

    hook_layer = cfg.get("model", {}).get("hook_layer", 8)
    device = wrapper.device
    W_sub = W_dec[feature_indices].to(device, torch.float32)  # (n, d_model)

    total_acts = torch.zeros(n, device=device)
    total_tokens = 0

    for batch in token_batches:
        batch = batch.to(device)
        residuals = _extract_residuals(wrapper, batch, hook_layer)
        # residuals: (batch, seq, d_model)
        acts = torch.einsum("bsd,nd->bsn", residuals.float(), W_sub)
        acts = acts.clamp(min=0.0)  # ReLU activation
        total_acts += acts.sum(dim=(0, 1))
        total_tokens += batch.shape[0] * batch.shape[1]

    mu = total_acts / max(total_tokens, 1)
    torch.save(mu.cpu(), cache_path)
    return mu.cpu()


def _extract_residuals(wrapper, tokens: torch.Tensor, hook_layer: int) -> torch.Tensor:
    """Extract residual-stream activations at hook_layer resid_pre."""
    residuals = []

    if wrapper.backend == "transformer_lens":
        hook_pt = f"blocks.{hook_layer}.hook_resid_pre"
        _, cache = wrapper.model.run_with_cache(tokens, names_filter=hook_pt)
        return cache[hook_pt]

    # HuggingFace fallback
    block = wrapper.model.transformer.h[hook_layer]

    def capture_hook(module, args):
        residuals.append(args[0].detach().float())
        return args

    handle = block.register_forward_pre_hook(capture_hook)
    try:
        wrapper.model(tokens)
    finally:
        handle.remove()

    return residuals[0] if residuals else torch.zeros(tokens.shape + (768,))


# ─── corpus tokenization ──────────────────────────────────────────────────────

def tokenize_corpus(cfg: Dict, tokenizer=None) -> List[torch.Tensor]:
    """
    Return a list of (batch_size, seq_len) int64 tensors.

    Falls back to random tokens if datasets or tokenizer unavailable.
    Guarantees at least one batch regardless of n_tokens setting.
    """
    n_tokens = cfg.get("corpus", {}).get("n_tokens", 10000)
    seq_len = cfg.get("corpus", {}).get("max_seq_len", 128)
    batch_size = cfg.get("device", {}).get("batch_size", 8)
    seed = cfg.get("corpus", {}).get("seed", 42)

    min_tokens = batch_size * seq_len
    n_tokens = max(n_tokens, min_tokens)

    raw_tokens = _load_tokens(cfg, tokenizer, n_tokens, seed)

    if len(raw_tokens) < min_tokens:
        # Pad with random tokens to fill at least one batch
        rng = np.random.default_rng(seed)
        pad = torch.from_numpy(rng.integers(0, 50257, size=min_tokens - len(raw_tokens),
                                            dtype=np.int64))
        raw_tokens = torch.cat([raw_tokens, pad])

    # Chunk into (batch, seq) tensors
    total = (len(raw_tokens) // (batch_size * seq_len)) * batch_size * seq_len
    raw_tokens = raw_tokens[:total]
    batches = raw_tokens.reshape(-1, batch_size, seq_len).unbind(0)
    logger.info("Corpus: %d tokens → %d batches of %d×%d",
                total, len(batches), batch_size, seq_len)
    return list(batches)


def _load_tokens(cfg: Dict, tokenizer, n_tokens: int, seed: int) -> torch.Tensor:
    """
    Try lightweight datasets first (wikitext-2), then fall back to random stub.

    For full experiments the config can set corpus.dataset = Skylion007/openwebtext
    but the preflight uses wikitext-2 which downloads in seconds.
    """
    # Try wikitext-2 (small, fast, no loading script)
    dataset_name = cfg.get("corpus", {}).get("dataset", "wikitext")
    try:
        from datasets import load_dataset
        if tokenizer is None:
            from transformers import GPT2TokenizerFast
            tokenizer = GPT2TokenizerFast.from_pretrained("gpt2")
            tokenizer.pad_token = tokenizer.eos_token

        if "openwebtext" in dataset_name:
            # openwebtext requires a loading script — use wikitext instead
            logger.warning(
                "openwebtext requires a custom loading script not supported by this "
                "datasets version. Using wikitext-2 fallback for corpus."
            )
            ds = load_dataset("wikitext", "wikitext-2-raw-v1", split="train")
        else:
            ds = load_dataset(dataset_name, "wikitext-2-raw-v1", split="train")

        logger.info("Loading corpus from wikitext-2-raw-v1 train")
        all_ids: list[int] = []
        for row in ds:
            text = row.get("text", "")
            if not text.strip():
                continue
            ids = tokenizer.encode(text)
            all_ids.extend(ids)
            if len(all_ids) >= n_tokens:
                break
        if all_ids:
            return torch.tensor(all_ids[:n_tokens], dtype=torch.long)

    except Exception as e:
        logger.warning("Corpus load failed (%s) — using random stub tokens.", e)

    rng = np.random.default_rng(seed)
    return torch.from_numpy(rng.integers(0, 50257, size=n_tokens, dtype=np.int64))
