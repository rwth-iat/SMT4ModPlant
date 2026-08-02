"""Dataclasses representing the relevant BatchML General Recipe structures."""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from .material_flow import MaterialFlowGraph


def _first_description(descriptions: list[str | None]) -> str | None:
    return descriptions[0] if descriptions else None


class MaterialRole(str, Enum):
    """The explicit role of a material within a recipe formula."""

    INPUT = "Input"
    INTERMEDIATE = "Intermediate"
    OUTPUT = "Output"


@dataclass(frozen=True)
class ParameterValue:
    """A lexical BatchML value together with its type and semantic metadata."""

    value_string: str | None = None
    data_type: str | None = None
    unit_of_measure: str | None = None
    key: str | None = None


@dataclass(frozen=True)
class MaterialAmount:
    """The amount of a recipe material, including unit and quantity-kind IRIs."""

    quantity: str | None = None
    data_type: str | None = None
    unit_iri: str | None = None
    quantity_kind_iri: str | None = None


@dataclass(frozen=True)
class RecipeMaterial:
    """A material declared as an input, intermediate, or output."""

    role: MaterialRole
    recipe_material_id: str | None = None
    descriptions: list[str | None] = field(default_factory=list)
    material_id: str | None = None
    order: str | None = None
    amount: MaterialAmount | None = None

    @property
    def description(self) -> str | None:
        return _first_description(self.descriptions)


@dataclass(frozen=True)
class ProcessElementParameter:
    """A process parameter that may contain multiple BatchML Value elements."""

    parameter_id: str | None = None
    descriptions: list[str | None] = field(default_factory=list)
    parameter_type: str | None = None
    values: list[ParameterValue] = field(default_factory=list)
    child_parameters: list[ProcessElementParameter] = field(default_factory=list)

    @property
    def description(self) -> str | None:
        return _first_description(self.descriptions)


@dataclass(frozen=True)
class ResourceConstraintProperty:
    """A property nested below a BatchML resource constraint."""

    property_id: str | None = None
    descriptions: list[str | None] = field(default_factory=list)
    values: list[ParameterValue] = field(default_factory=list)

    @property
    def description(self) -> str | None:
        return _first_description(self.descriptions)


@dataclass(frozen=True)
class ResourceConstraint:
    """A recipe or process-level constraint on a required resource."""

    constraint_id: str | None = None
    descriptions: list[str | None] = field(default_factory=list)
    constraint_types: list[str | None] = field(default_factory=list)
    life_cycle_state: str | None = None
    ranges: list[ParameterValue] = field(default_factory=list)
    properties: list[ResourceConstraintProperty] = field(default_factory=list)

    @property
    def description(self) -> str | None:
        return _first_description(self.descriptions)


@dataclass(frozen=True)
class OtherInformation:
    """An extensible BatchML information entry with all of its values."""

    other_info_id: str | None = None
    descriptions: list[str | None] = field(default_factory=list)
    values: list[ParameterValue] = field(default_factory=list)

    @property
    def description(self) -> str | None:
        return _first_description(self.descriptions)


@dataclass(frozen=True)
class ProcessElement:
    """A recipe procedure step and its parameters, constraints, and semantics."""

    process_element_id: str | None = None
    descriptions: list[str | None] = field(default_factory=list)
    process_element_type: str | None = None
    life_cycle_state: str | None = None
    sequence_order: str | None = None
    sequence_path: str | None = None
    parameters: list[ProcessElementParameter] = field(default_factory=list)
    resource_constraints: list[ResourceConstraint] = field(default_factory=list)
    other_information: list[OtherInformation] = field(default_factory=list)
    child_process_elements: list[ProcessElement] = field(default_factory=list)
    semantic_description: str | None = None

    @property
    def description(self) -> str | None:
        return _first_description(self.descriptions)


@dataclass(frozen=True)
class DirectedLink:
    """A directed connection between material and process identifiers."""

    link_id: str | None = None
    descriptions: list[str | None] = field(default_factory=list)
    from_id: str | None = None
    to_id: str | None = None

    @property
    def description(self) -> str | None:
        return _first_description(self.descriptions)


@dataclass(frozen=True)
class RecipeFormula:
    """The formula section containing materials and formula-level parameters."""

    descriptions: list[str | None] = field(default_factory=list)
    inputs: list[RecipeMaterial] = field(default_factory=list)
    outputs: list[RecipeMaterial] = field(default_factory=list)
    intermediates: list[RecipeMaterial] = field(default_factory=list)
    parameters: list[ProcessElementParameter] = field(default_factory=list)

    @property
    def description(self) -> str | None:
        return _first_description(self.descriptions)


@dataclass(frozen=True)
class GeneralRecipe:
    """The complete model-based representation of a BatchML General Recipe."""

    material_flow_graph: MaterialFlowGraph
    recipe_id: str | None = None
    descriptions: list[str | None] = field(default_factory=list)
    recipe_type: str | None = None
    life_cycle_state: str | None = None
    formula: RecipeFormula | None = None
    process_procedure_id: str | None = None
    process_procedure_descriptions: list[str | None] = field(default_factory=list)
    process_procedure_type: str | None = None
    process_elements: list[ProcessElement] = field(default_factory=list)
    directed_links: list[DirectedLink] = field(default_factory=list)
    resource_constraints: list[ResourceConstraint] = field(default_factory=list)
    process_procedure_resource_constraints: list[ResourceConstraint] = field(
        default_factory=list
    )
    other_information: list[OtherInformation] = field(default_factory=list)
    process_procedure_other_information: list[OtherInformation] = field(
        default_factory=list
    )
    @property
    def description(self) -> str | None:
        return _first_description(self.descriptions)

    @property
    def inputs(self) -> list[RecipeMaterial]:
        return self.formula.inputs if self.formula is not None else []

    @property
    def outputs(self) -> list[RecipeMaterial]:
        return self.formula.outputs if self.formula is not None else []

    @property
    def intermediates(self) -> list[RecipeMaterial]:
        return self.formula.intermediates if self.formula is not None else []
