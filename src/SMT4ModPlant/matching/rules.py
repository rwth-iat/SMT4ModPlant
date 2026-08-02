"""Placeholder rule definitions for future model-based matching behavior."""

from dataclasses import dataclass

from ..models.matching import MatchingRule


@dataclass(frozen=True)
class SemanticCapabilityRule(MatchingRule):
    """Describe semantic capability matching preferences."""

    allow_generalized_capabilities: bool = True

    @property
    def rule_type(self) -> str:
        return "semantic_capability"


@dataclass(frozen=True)
class PropertyCompatibilityRule(MatchingRule):
    """Describe property value and unit compatibility preferences."""

    require_matching_units: bool = True

    @property
    def rule_type(self) -> str:
        return "property_compatibility"


@dataclass(frozen=True)
class PreconditionRule(MatchingRule):
    """Describe how capability preconditions should be evaluated."""

    require_all_preconditions: bool = True

    @property
    def rule_type(self) -> str:
        return "precondition"


@dataclass(frozen=True)
class MaterialFlowRule(MatchingRule):
    """Describe the required material-flow consistency policy."""

    require_consistent_flow: bool = True

    @property
    def rule_type(self) -> str:
        return "material_flow"
