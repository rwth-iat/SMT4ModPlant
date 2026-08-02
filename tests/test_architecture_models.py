"""Tests for the constraint, solver, and executable configuration models."""

from dataclasses import replace
from pathlib import Path

import pytest

from SMT4ModPlant.matching import (
    MaterialFlowRule,
    PreconditionRule,
    PropertyCompatibilityRule,
    SemanticCapabilityRule,
)
from SMT4ModPlant.models import (
    Assignment,
    AssignmentVariable,
    CapabilityProperty,
    ConfigurationSolution,
    ConstraintExpression,
    ConstraintModel,
    ConstraintOrigin,
    Explanation,
    ExpressionKind,
    FeasibilityResult,
    LogicalConstraint,
    MaterialFlowAssignment,
    ParameterBinding,
    PlantConfiguration,
    ProvidedCapability,
    ResourceDescription,
    SmtLibProgram,
    SolverResult,
    SolverStatus,
)
from SMT4ModPlant.parsing import parse_general_recipe_model


FIXTURE = (
    Path(__file__).parent
    / "fixtures"
    / "general_recipe"
    / "2026-04-26_BatchML_Verfahrensrezept1.xml"
)


def _configuration_fixture():
    recipe = parse_general_recipe_model(FIXTURE)
    capabilities = []

    for process_element in recipe.process_elements:
        properties = [
            CapabilityProperty(property_id=parameter.parameter_id)
            for parameter in process_element.parameters
        ]
        capabilities.append(
            ProvidedCapability(
                capability_id=f"cap:{process_element.process_element_id}",
                name=process_element.description,
                semantic_id=process_element.semantic_description,
                execution_reference=(
                    f"opcua://module/"
                    f"{process_element.process_element_id}"
                ),
                properties=properties,
            )
        )

    resource = ResourceDescription(
        resource_id="module-1",
        name="Module 1",
        capabilities=capabilities,
    )
    assignments = []
    for process_element, capability in zip(
        recipe.process_elements, capabilities
    ):
        bindings = [
            ParameterBinding(
                process_parameter=parameter,
                capability_property=property_model,
                bound_values=parameter.values,
            )
            for parameter, property_model in zip(
                process_element.parameters, capability.properties
            )
        ]
        assignments.append(
            Assignment(
                process_element=process_element,
                resource=resource,
                capability=capability,
                parameter_bindings=bindings,
            )
        )

    material_flow_assignments = [
        MaterialFlowAssignment(
            edge=edge,
            source_resource=resource,
            target_resource=resource,
        )
        for edge in recipe.material_flow_graph.edges
    ]
    configuration = PlantConfiguration(
        configuration_id="configuration-1",
        recipe=recipe,
        resources=[resource],
        assignments=assignments,
        material_flow_assignments=material_flow_assignments,
    )
    return recipe, resource, configuration


def test_plant_configuration_contains_executable_object_references():
    recipe, resource, configuration = _configuration_fixture()

    assert configuration.recipe is recipe
    assert configuration.resources == [resource]
    assert len(configuration.assignments) == len(recipe.process_elements)
    assert all(
        assignment.process_element in recipe.process_elements
        for assignment in configuration.assignments
    )
    assert all(
        assignment.capability.execution_reference
        for assignment in configuration.assignments
    )
    assert len(configuration.material_flow_assignments) == len(
        recipe.material_flow_graph.edges
    )


def test_plant_configuration_rejects_incomplete_assignments():
    recipe, resource, configuration = _configuration_fixture()

    with pytest.raises(ValueError, match="exactly one assignment"):
        PlantConfiguration(
            configuration_id="incomplete",
            recipe=recipe,
            resources=[resource],
            assignments=configuration.assignments[:-1],
            material_flow_assignments=configuration.material_flow_assignments,
        )


def test_constraint_and_solver_models_represent_the_processing_chain():
    recipe, resource, configuration = _configuration_fixture()
    rules = [
        SemanticCapabilityRule(rule_id="semantic"),
        PropertyCompatibilityRule(rule_id="properties"),
        PreconditionRule(rule_id="preconditions"),
        MaterialFlowRule(rule_id="material-flow"),
    ]
    variable = AssignmentVariable(
        variable_id="assign_MixingOfLiquids001_module_1",
        process_element=recipe.process_elements[0],
        resource=resource,
        capability=resource.capabilities[0],
    )
    constraint = LogicalConstraint(
        constraint_id="exactly-one-MixingOfLiquids001",
        expression=ConstraintExpression(
            kind=ExpressionKind.EQUALS,
            operands=[
                ConstraintExpression(
                    kind=ExpressionKind.SYMBOL,
                    value=variable.variable_id,
                ),
                ConstraintExpression(
                    kind=ExpressionKind.BOOLEAN,
                    value=True,
                ),
            ],
        ),
        origin=ConstraintOrigin(
            rule_id=rules[0].rule_id,
            source_references=["MixingOfLiquids001", "module-1"],
        ),
    )
    constraint_model = ConstraintModel(
        recipe=recipe,
        resources=[resource],
        rules=rules,
        assignment_variables=[variable],
        constraints=[constraint],
    )
    smt_lib = SmtLibProgram(
        text="(assert (= assign_MixingOfLiquids001_module_1 true))",
        constraint_ids=[constraint.constraint_id],
    )
    solver_result = SolverResult(
        status=SolverStatus.SAT,
        model_values={variable.variable_id: True},
    )
    solution = ConfigurationSolution(
        solution_id=1,
        solver_result=solver_result,
        plant_configuration=configuration,
        explanation=Explanation(summary="Solution 1 is feasible."),
    )
    second_configuration = replace(
        configuration,
        configuration_id="configuration-2",
    )
    second_solution = ConfigurationSolution(
        solution_id=2,
        solver_result=SolverResult(
            status=SolverStatus.SAT,
            model_values={variable.variable_id: True},
        ),
        plant_configuration=second_configuration,
        explanation=Explanation(summary="Solution 2 is feasible."),
    )
    result = FeasibilityResult(
        constraint_model=constraint_model,
        smt_lib_program=smt_lib,
        status=SolverStatus.SAT,
        solutions=[solution, second_solution],
        explanation=Explanation(
            summary="Two feasible plant configurations were found."
        ),
    )

    assert [rule.rule_type for rule in rules] == [
        "semantic_capability",
        "property_compatibility",
        "precondition",
        "material_flow",
    ]
    assert result.status is SolverStatus.SAT
    assert len(result.solutions) == 2
    assert result.solutions[0].plant_configuration is configuration
    assert (
        result.solutions[1].plant_configuration is second_configuration
    )
    assert result.solutions[0].solver_result.status is SolverStatus.SAT


def test_solution_and_result_enforce_enumeration_contracts():
    recipe, resource, configuration = _configuration_fixture()
    constraint_model = ConstraintModel(
        recipe=recipe,
        resources=[resource],
        rules=[],
    )
    smt_lib = SmtLibProgram(text="")
    explanation = Explanation(summary="No assignment is possible.")

    with pytest.raises(ValueError, match="requires a SAT"):
        ConfigurationSolution(
            solution_id=1,
            solver_result=SolverResult(status=SolverStatus.UNSAT),
            plant_configuration=configuration,
            explanation=explanation,
        )

    with pytest.raises(ValueError, match="at least one solution"):
        FeasibilityResult(
            constraint_model=constraint_model,
            smt_lib_program=smt_lib,
            status=SolverStatus.SAT,
            solutions=[],
            explanation=explanation,
        )

    solution = ConfigurationSolution(
        solution_id=1,
        solver_result=SolverResult(status=SolverStatus.SAT),
        plant_configuration=configuration,
        explanation=Explanation(summary="Solution 1 is feasible."),
    )
    with pytest.raises(ValueError, match="cannot contain solutions"):
        FeasibilityResult(
            constraint_model=constraint_model,
            smt_lib_program=smt_lib,
            status=SolverStatus.UNSAT,
            solutions=[solution],
            explanation=explanation,
        )

    with pytest.raises(ValueError, match="contiguous sequence"):
        FeasibilityResult(
            constraint_model=constraint_model,
            smt_lib_program=smt_lib,
            status=SolverStatus.SAT,
            solutions=[replace(solution, solution_id=2)],
            explanation=Explanation(summary="Invalid numbering."),
        )

    unsat_result = FeasibilityResult(
        constraint_model=constraint_model,
        smt_lib_program=smt_lib,
        status=SolverStatus.UNSAT,
        solutions=[],
        explanation=explanation,
    )
    assert unsat_result.solutions == []
