"""Adapters that connect the model layer to existing SMT4ModPlant interfaces."""

from .recipe_to_legacy_dict import recipe_model_to_legacy_dict

__all__ = ["recipe_model_to_legacy_dict"]
