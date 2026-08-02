"""Solver-independent instance models produced from matching rules."""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Protocol

from .matching import MatchingRule
from .recipe import GeneralRecipe, ProcessElement
from .resources import ProvidedCapability, ResourceDescription


class ExpressionKind(str, Enum):
    """Supported solver-independent logical expression node types."""

    SYMBOL = "symbol"
    BOOLEAN = "boolean"
    NUMBER = "number"
    NOT = "not"
    AND = "and"
    OR = "or"
    IMPLIES = "implies"
    EQUALS = "equals"
    LESS_THAN = "less_than"
    LESS_EQUAL = "less_equal"
    GREATER_THAN = "greater_than"
    GREATER_EQUAL = "greater_equal"
    SUM = "sum"


@dataclass(frozen=True)
class ConstraintExpression:
    """A solver-independent logical expression tree."""

    kind: ExpressionKind
    value: str | bool | int | float | None = None
    operands: list[ConstraintExpression] = field(default_factory=list)


@dataclass(frozen=True)
class ConstraintOrigin:
    """Trace a generated constraint back to a rule and source objects."""

    rule_id: str
    source_references: list[str] = field(default_factory=list)
    description: str | None = None


@dataclass(frozen=True)
class AssignmentVariable:
    """A Boolean candidate assigning a process element to a capability."""

    variable_id: str
    process_element: ProcessElement
    resource: ResourceDescription
    capability: ProvidedCapability


@dataclass(frozen=True)
class LogicalConstraint:
    """One named logical assertion in the constraint instance model."""

    constraint_id: str
    expression: ConstraintExpression
    origin: ConstraintOrigin


@dataclass(frozen=True)
class ConstraintModel:
    """The complete solver-independent model passed to SMT serialization."""

    recipe: GeneralRecipe
    resources: list[ResourceDescription]
    rules: list[MatchingRule]
    assignment_variables: list[AssignmentVariable] = field(default_factory=list)
    constraints: list[LogicalConstraint] = field(default_factory=list)


class ConstraintModelBuilder(Protocol):
    """Build a solver-independent constraint model from domain models."""

    def build(
        self,
        recipe: GeneralRecipe,
        resources: list[ResourceDescription],
        rules: list[MatchingRule],
    ) -> ConstraintModel:
        """Transform recipe, resources, and rules into an instance model."""
