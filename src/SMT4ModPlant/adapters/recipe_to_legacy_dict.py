"""Convert model-based recipes to the dictionary format used by the solver."""

from __future__ import annotations

from ..models.recipe import (
    GeneralRecipe,
    ParameterValue,
    ProcessElementParameter,
    RecipeMaterial,
)


def _value_to_legacy_dict(value: ParameterValue) -> dict:
    return {
        "ValueString": value.value_string,
        "DataType": value.data_type,
        "UnitOfMeasure": value.unit_of_measure,
        "Key": value.key,
    }


def _material_to_legacy_dict(material: RecipeMaterial) -> dict:
    amount = material.amount
    return {
        "ID": material.recipe_material_id,
        "Description": material.description,
        "Quantity": amount.quantity if amount is not None else None,
        "DataType": amount.data_type if amount is not None else None,
        "UnitOfMeasure": amount.unit_iri if amount is not None else None,
        "Key": amount.quantity_kind_iri if amount is not None else None,
    }


def _flatten_parameters(
    parameters: list[ProcessElementParameter],
) -> list[ProcessElementParameter]:
    flattened: list[ProcessElementParameter] = []
    for parameter in parameters:
        flattened.append(parameter)
        flattened.extend(_flatten_parameters(parameter.child_parameters))
    return flattened


def _parameter_to_legacy_dict(parameter: ProcessElementParameter) -> dict:
    first_value = parameter.values[0] if parameter.values else None
    # TODO: Replace the first-value compatibility fields with explicit range
    # handling when the legacy feasibility workflow supports value intervals.
    return {
        "ID": parameter.parameter_id,
        "Description": parameter.description,
        "ValueString": (
            first_value.value_string if first_value is not None else None
        ),
        "DataType": first_value.data_type if first_value is not None else None,
        "UnitOfMeasure": (
            first_value.unit_of_measure if first_value is not None else None
        ),
        "Key": first_value.key if first_value is not None else None,
        "Values": [
            _value_to_legacy_dict(value) for value in parameter.values
        ],
    }


def recipe_model_to_legacy_dict(recipe: GeneralRecipe) -> dict:
    """Create the recipe dictionary expected by ``run_feasibility``."""

    return {
        "ID": recipe.recipe_id,
        "Description": recipe.description,
        "Inputs": [
            _material_to_legacy_dict(material) for material in recipe.inputs
        ],
        "Outputs": [
            _material_to_legacy_dict(material) for material in recipe.outputs
        ],
        "Intermediates": [
            _material_to_legacy_dict(material)
            for material in recipe.intermediates
        ],
        "ProcessElements": [
            {
                "ID": process_element.process_element_id,
                "Description": process_element.description,
                "Parameters": [
                    _parameter_to_legacy_dict(parameter)
                    for parameter in _flatten_parameters(
                        process_element.parameters
                    )
                ],
                "SemanticDescription": (
                    process_element.semantic_description
                ),
            }
            for process_element in recipe.process_elements
        ],
        "DirectedLinks": [
            {
                "ID": link.link_id,
                "FromID": link.from_id,
                "ToID": link.to_id,
            }
            for link in recipe.directed_links
        ],
    }
