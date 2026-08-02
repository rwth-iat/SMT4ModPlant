"""Public entry points for model-based recipe and resource parsing."""

from .general_recipe_parser_model_based import parse_general_recipe_model
from .resource_description_parser_stub import parse_resource_description_model

__all__ = [
    "parse_general_recipe_model",
    "parse_resource_description_model",
]
