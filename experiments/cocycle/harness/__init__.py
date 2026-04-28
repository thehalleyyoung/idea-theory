"""Cocycle experiments harness — public API re-exports."""

from harness.model import load_model, ModelWrapper
from harness.model_loader import load_model_for_config, GenericModelWrapper
from harness.features import load_sae_weights, compute_mean_activations
from harness.feature_extractor import (
    get_features,
    extract_residuals,
    compute_mean_activations_generic,
)
from harness.measurement import build_rs_matrix, compute_rs_triple_batch
from harness.cocycle import compute_c, hochschild_boundary, run_e1
from harness.recovery import run_e2

__all__ = [
    # base
    "load_model",
    "ModelWrapper",
    # multi-model
    "load_model_for_config",
    "GenericModelWrapper",
    # features
    "load_sae_weights",
    "compute_mean_activations",
    "get_features",
    "extract_residuals",
    "compute_mean_activations_generic",
    # measurement
    "build_rs_matrix",
    "compute_rs_triple_batch",
    # experiments
    "compute_c",
    "hochschild_boundary",
    "run_e1",
    "run_e2",
]
