"""Public matching-rule types reserved for a later solver refactoring."""

from ..models.matching import MatchingRule
from .rules import (
    MaterialFlowRule,
    PreconditionRule,
    PropertyCompatibilityRule,
    SemanticCapabilityRule,
)

__all__ = [
    "MatchingRule",
    "MaterialFlowRule",
    "PreconditionRule",
    "PropertyCompatibilityRule",
    "SemanticCapabilityRule",
]
