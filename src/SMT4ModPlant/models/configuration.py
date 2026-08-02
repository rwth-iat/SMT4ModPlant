"""Models for one executable plant configuration returned by a SAT result."""

from __future__ import annotations

from dataclasses import dataclass, field

from .material_flow import MaterialFlowEdge
from .recipe import (
    GeneralRecipe,
    ParameterValue,
    ProcessElement,
    ProcessElementParameter,
)
from .resources import (
    CapabilityProperty,
    ProvidedCapability,
    ResourceDescription,
)


@dataclass(frozen=True)
class ParameterBinding:
    """Bind a recipe parameter to a capability property and concrete values."""

    process_parameter: ProcessElementParameter
    capability_property: CapabilityProperty
    bound_values: list[ParameterValue] = field(default_factory=list)


@dataclass(frozen=True)
class Assignment:
    """Assign one recipe process element to one resource capability."""

    process_element: ProcessElement
    resource: ResourceDescription
    capability: ProvidedCapability
    parameter_bindings: list[ParameterBinding] = field(default_factory=list)


@dataclass(frozen=True)
class MaterialFlowAssignment:
    """Describe how one recipe material-flow edge is realized by resources."""

    edge: MaterialFlowEdge
    source_resource: ResourceDescription | None = None
    target_resource: ResourceDescription | None = None
    transport_capability: ProvidedCapability | None = None


@dataclass(frozen=True)
class PlantConfiguration:
    """A complete executable realization of one General Recipe."""

    configuration_id: str
    recipe: GeneralRecipe
    resources: list[ResourceDescription]
    assignments: list[Assignment]
    material_flow_assignments: list[MaterialFlowAssignment]

    def __post_init__(self) -> None:
        """Validate completeness and internal references of the configuration."""

        resource_ids = [resource.resource_id for resource in self.resources]
        if any(resource_id is None for resource_id in resource_ids):
            raise ValueError(
                "Every configured resource must have a stable ID."
            )
        if len(resource_ids) != len(set(resource_ids)):
            raise ValueError("Resource IDs must be unique.")

        process_ids = [
            element.process_element_id for element in self.recipe.process_elements
        ]
        if any(process_id is None for process_id in process_ids):
            raise ValueError(
                "Every configured process element must have a stable ID."
            )
        if len(process_ids) != len(set(process_ids)):
            raise ValueError("Process element IDs must be unique.")

        assigned_ids = [
            assignment.process_element.process_element_id
            for assignment in self.assignments
        ]
        if any(process_id is None for process_id in assigned_ids):
            raise ValueError(
                "Every assigned process element must have a stable ID."
            )
        if sorted(assigned_ids) != sorted(process_ids):
            raise ValueError(
                "A PlantConfiguration requires exactly one assignment "
                "for every recipe process element."
            )

        for assignment in self.assignments:
            if assignment.process_element not in self.recipe.process_elements:
                raise ValueError(
                    "Every assigned process element must belong to the recipe."
                )
            if assignment.resource not in self.resources:
                raise ValueError(
                    "Every assigned resource must belong to the configuration."
                )
            if assignment.capability not in assignment.resource.capabilities:
                raise ValueError(
                    "Every assigned capability must be provided by its resource."
                )
            if not assignment.capability.execution_reference:
                raise ValueError(
                    "Assigned capabilities require an execution reference."
                )
            self._validate_parameter_bindings(assignment)

        graph_edge_ids = [
            edge.edge_id for edge in self.recipe.material_flow_graph.edges
        ]
        assigned_edge_ids = [
            flow_assignment.edge.edge_id
            for flow_assignment in self.material_flow_assignments
        ]
        if sorted(assigned_edge_ids) != sorted(graph_edge_ids):
            raise ValueError(
                "A PlantConfiguration requires exactly one material-flow "
                "assignment for every graph edge."
            )

        for flow_assignment in self.material_flow_assignments:
            if flow_assignment.edge not in self.recipe.material_flow_graph.edges:
                raise ValueError(
                    "Every material-flow edge must belong to the recipe graph."
                )
            for resource in (
                flow_assignment.source_resource,
                flow_assignment.target_resource,
            ):
                if resource is not None and resource not in self.resources:
                    raise ValueError(
                        "Material-flow resources must belong to the "
                        "configuration."
                    )
            if flow_assignment.transport_capability is not None:
                candidate_resources = [
                    resource
                    for resource in (
                        flow_assignment.source_resource,
                        flow_assignment.target_resource,
                    )
                    if resource is not None
                ]
                if not any(
                    flow_assignment.transport_capability
                    in resource.capabilities
                    for resource in candidate_resources
                ):
                    raise ValueError(
                        "A transport capability must be provided by a "
                        "material-flow resource."
                    )
                if not flow_assignment.transport_capability.execution_reference:
                    raise ValueError(
                        "Transport capabilities require an execution reference."
                    )

    @staticmethod
    def _flatten_parameters(
        parameters: list[ProcessElementParameter],
    ) -> list[ProcessElementParameter]:
        flattened: list[ProcessElementParameter] = []
        for parameter in parameters:
            flattened.append(parameter)
            flattened.extend(
                PlantConfiguration._flatten_parameters(
                    parameter.child_parameters
                )
            )
        return flattened

    def _validate_parameter_bindings(self, assignment: Assignment) -> None:
        parameters = self._flatten_parameters(
            assignment.process_element.parameters
        )
        parameter_ids = [parameter.parameter_id for parameter in parameters]
        bound_parameter_ids = [
            binding.process_parameter.parameter_id
            for binding in assignment.parameter_bindings
        ]
        if any(parameter_id is None for parameter_id in parameter_ids):
            raise ValueError(
                "Every configured process parameter must have a stable ID."
            )
        if len(parameter_ids) != len(set(parameter_ids)):
            raise ValueError(
                "Process parameter IDs must be unique within an element."
            )
        if any(parameter_id is None for parameter_id in bound_parameter_ids):
            raise ValueError(
                "Every bound process parameter must have a stable ID."
            )
        if sorted(bound_parameter_ids) != sorted(parameter_ids):
            raise ValueError(
                "Every process parameter requires exactly one binding."
            )

        for binding in assignment.parameter_bindings:
            if binding.process_parameter not in parameters:
                raise ValueError(
                    "Every bound parameter must belong to the process element."
                )
            if (
                binding.capability_property
                not in assignment.capability.properties
            ):
                raise ValueError(
                    "Every bound property must belong to the capability."
                )
            if not binding.bound_values:
                raise ValueError(
                    "Every parameter binding requires at least one value."
                )
