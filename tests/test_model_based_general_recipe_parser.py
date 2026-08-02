"""Tests for model-based BatchML parsing and graph generation."""

from pathlib import Path

from SMT4ModPlant.models import MaterialRole
from SMT4ModPlant.models.material_flow import MaterialNode, ProcessNode
from SMT4ModPlant.parsing import parse_general_recipe_model


FIXTURE = (
    Path(__file__).parent
    / "fixtures"
    / "general_recipe"
    / "2026-04-26_BatchML_Verfahrensrezept1.xml"
)


def _process_element(recipe, process_element_id):
    return next(
        element
        for element in recipe.process_elements
        if element.process_element_id == process_element_id
    )


def test_parse_complete_general_recipe_model():
    recipe = parse_general_recipe_model(FIXTURE)

    assert recipe.recipe_id == "testID"
    assert recipe.description is None
    assert len(recipe.inputs) == 2
    assert len(recipe.intermediates) == 2
    assert len(recipe.outputs) == 1
    assert all(material.role is MaterialRole.INPUT for material in recipe.inputs)
    assert all(
        material.role is MaterialRole.INTERMEDIATE
        for material in recipe.intermediates
    )
    assert all(
        material.role is MaterialRole.OUTPUT for material in recipe.outputs
    )
    assert len(recipe.process_elements) == 3
    assert len(recipe.directed_links) == 7

    expected_semantics = {
        "MixingOfLiquids001": (
            "http://css.iat.rwth-aachen.de/"
            "OntoProCap#MixingOfLiquids"
        ),
        "Dosing001": (
            "http://css.iat.rwth-aachen.de/OntoProCap#Dosing"
        ),
        "HeatingOfLiquids001": (
            "http://css.iat.rwth-aachen.de/"
            "OntoProCap#HeatingOfLiquids"
        ),
    }
    for process_element_id, semantic_description in expected_semantics.items():
        assert (
            _process_element(recipe, process_element_id).semantic_description
            == semantic_description
        )

    mixing = _process_element(recipe, "MixingOfLiquids001")
    rotation_speed = next(
        parameter
        for parameter in mixing.parameters
        if parameter.parameter_id == "RotationSpeed001"
    )
    assert [
        value.value_string for value in rotation_speed.values
    ] == [">=50", "<=300"]
    assert all(
        value.unit_of_measure
        == "http://qudt.org/vocab/unit/REV-PER-MIN"
        for value in rotation_speed.values
    )

    assert recipe.inputs[0].amount is not None
    assert (
        recipe.inputs[0].amount.unit_iri
        == "http://si-digital-framework.org/SI/units/litre"
    )
    assert (
        recipe.inputs[0].amount.quantity_kind_iri
        == "http://qudt.org/vocab/quantitykind/LiquidVolume"
    )

    dosing = _process_element(recipe, "Dosing001")
    heating = _process_element(recipe, "HeatingOfLiquids001")
    assert len(dosing.resource_constraints) == 1
    assert dosing.resource_constraints[0].ranges[0].value_string == ">0.0"
    assert len(heating.resource_constraints) == 3


def test_material_flow_graph_contains_recipe_nodes_and_links():
    recipe = parse_general_recipe_model(FIXTURE)
    graph = recipe.material_flow_graph

    assert graph.graph_id == "testID:material-flow"
    assert graph.recipe_id == "testID"
    assert len(graph.nodes) == 8
    assert len(graph.edges) == 7
    assert len([node for node in graph.nodes if isinstance(node, MaterialNode)]) == 5
    assert len([node for node in graph.nodes if isinstance(node, ProcessNode)]) == 3
    assert graph.balances == []
    assert {
        edge.source_directed_link_id for edge in graph.edges
    } == {
        f"DirectedLink_Root_{index}" for index in range(1, 8)
    }
    assert all(edge.is_material_transfer for edge in graph.edges)


def test_parser_handles_namespace_free_xml_and_missing_optional_elements(
    tmp_path,
):
    recipe_path = tmp_path / "minimal_recipe.xml"
    recipe_path.write_text(
        """\
<?xml version="1.0" encoding="UTF-8"?>
<GRecipe>
  <ID>minimal</ID>
  <Description/>
  <Formula>
    <ProcessInputs>
      <Material>
        <ID>Input1</ID>
        <Description/>
      </Material>
    </ProcessInputs>
  </Formula>
  <ProcessProcedure>
    <ProcessElement>
      <ID>Step1</ID>
      <Description/>
      <ProcessElementParameter>
        <ID>OptionalValue</ID>
      </ProcessElementParameter>
    </ProcessElement>
  </ProcessProcedure>
</GRecipe>
""",
        encoding="utf-8",
    )

    recipe = parse_general_recipe_model(recipe_path)

    assert recipe.recipe_id == "minimal"
    assert recipe.description is None
    assert recipe.recipe_type is None
    assert len(recipe.inputs) == 1
    assert recipe.inputs[0].description is None
    assert recipe.inputs[0].amount is None
    assert recipe.outputs == []
    assert recipe.intermediates == []
    assert len(recipe.process_elements) == 1
    assert recipe.process_elements[0].description is None
    assert recipe.process_elements[0].parameters[0].values == []
    assert recipe.process_elements[0].semantic_description is None
    assert recipe.directed_links == []
    assert len(recipe.material_flow_graph.nodes) == 2
    assert recipe.material_flow_graph.edges == []
