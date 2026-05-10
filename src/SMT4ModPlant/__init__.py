# src/SMT4ModPlant/__init__.py
from .AASxmlCapabilityParser import parse_capabilities_robust
from .GeneralRecipeParser import parse_general_recipe


def run_feasibility(*args, **kwargs):
    from .feasibility import run_feasibility as _run_feasibility

    return _run_feasibility(*args, **kwargs)

__all__ = [
    "parse_capabilities_robust",
    "parse_general_recipe",
    "run_feasibility",
]
