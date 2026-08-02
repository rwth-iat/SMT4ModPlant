"""Tests for adapting recipe dataclasses to the existing solver dictionary."""

from pathlib import Path

import pytest

from SMT4ModPlant.adapters import recipe_model_to_legacy_dict
from SMT4ModPlant.feasibility import run_feasibility
from SMT4ModPlant.parsing import (
    parse_general_recipe_model,
    parse_resource_description_model,
)


FIXTURE = (
    Path(__file__).parent
    / "fixtures"
    / "general_recipe"
    / "2026-04-26_BatchML_Verfahrensrezept1.xml"
)


def test_legacy_adapter_preserves_expected_shape_and_all_values():
    recipe = parse_general_recipe_model(FIXTURE)
    legacy = recipe_model_to_legacy_dict(recipe)

    assert set(legacy) == {
        "ID",
        "Description",
        "Inputs",
        "Outputs",
        "Intermediates",
        "ProcessElements",
        "DirectedLinks",
    }
    assert legacy["ID"] == "testID"
    assert legacy["Description"] is None
    assert len(legacy["Inputs"]) == 2
    assert len(legacy["Intermediates"]) == 2
    assert len(legacy["Outputs"]) == 1
    assert len(legacy["ProcessElements"]) == 3
    assert len(legacy["DirectedLinks"]) == 7

    assert legacy["Inputs"][0] == {
        "ID": "Educt001",
        "Description": "Water",
        "Quantity": "5.0",
        "DataType": "double",
        "UnitOfMeasure": (
            "http://si-digital-framework.org/SI/units/litre"
        ),
        "Key": "http://qudt.org/vocab/quantitykind/LiquidVolume",
    }

    mixing = next(
        element
        for element in legacy["ProcessElements"]
        if element["ID"] == "MixingOfLiquids001"
    )
    rotation_speed = next(
        parameter
        for parameter in mixing["Parameters"]
        if parameter["ID"] == "RotationSpeed001"
    )
    assert rotation_speed["ValueString"] == ">=50"
    assert [value["ValueString"] for value in rotation_speed["Values"]] == [
        ">=50",
        "<=300",
    ]
    assert (
        mixing["SemanticDescription"]
        == "http://css.iat.rwth-aachen.de/"
        "OntoProCap#MixingOfLiquids"
    )


def test_legacy_adapter_output_is_accepted_by_feasibility_solver():
    recipe = parse_general_recipe_model(FIXTURE)
    legacy = recipe_model_to_legacy_dict(recipe)

    gui_results, json_solutions, debug = run_feasibility(
        legacy,
        {},
        log_callback=lambda _message: None,
        generate_json=True,
    )

    assert gui_results == []
    assert json_solutions == []
    assert debug["step_count"] == 3
    assert debug["resource_count"] == 0


def test_resource_model_parser_remains_an_explicit_stub(tmp_path):
    with pytest.raises(
        NotImplementedError,
        match="Model-based resource parsing will be implemented",
    ):
        parse_resource_description_model(tmp_path / "resource.xml")
