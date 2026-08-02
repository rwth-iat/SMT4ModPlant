"""Parse BatchML General Recipes into dataclasses and a material-flow graph."""

from __future__ import annotations

from pathlib import Path
import xml.etree.ElementTree as ET

from ..models.material_flow import (
    MaterialFlowEdge,
    MaterialFlowGraph,
    MaterialNode,
    ProcessNode,
)
from ..models.recipe import (
    DirectedLink,
    GeneralRecipe,
    MaterialAmount,
    MaterialRole,
    OtherInformation,
    ParameterValue,
    ProcessElement,
    ProcessElementParameter,
    RecipeFormula,
    RecipeMaterial,
    ResourceConstraint,
    ResourceConstraintProperty,
)


def _local_name(tag: str) -> str:
    return tag.rsplit("}", 1)[-1] if "}" in tag else tag


def _children(element: ET.Element | None, name: str) -> list[ET.Element]:
    if element is None:
        return []
    return [child for child in element if _local_name(child.tag) == name]


def _child(element: ET.Element | None, name: str) -> ET.Element | None:
    children = _children(element, name)
    return children[0] if children else None


def _text(element: ET.Element | None) -> str | None:
    if element is None or element.text is None:
        return None
    text = element.text.strip()
    return text or None


def _child_text(element: ET.Element | None, name: str) -> str | None:
    return _text(_child(element, name))


def _descriptions(element: ET.Element | None) -> list[str | None]:
    return [_text(description) for description in _children(element, "Description")]


def _parse_parameter_value(
    element: ET.Element | None,
    value_element_name: str = "ValueString",
) -> ParameterValue:
    return ParameterValue(
        value_string=_child_text(element, value_element_name),
        data_type=_child_text(element, "DataType"),
        unit_of_measure=_child_text(element, "UnitOfMeasure"),
        key=_child_text(element, "Key"),
    )


def _parse_material_amount(element: ET.Element | None) -> MaterialAmount | None:
    if element is None:
        return None
    return MaterialAmount(
        quantity=_child_text(element, "QuantityString"),
        data_type=_child_text(element, "DataType"),
        unit_iri=_child_text(element, "UnitOfMeasure"),
        quantity_kind_iri=_child_text(element, "Key"),
    )


def _parse_material(element: ET.Element, role: MaterialRole) -> RecipeMaterial:
    return RecipeMaterial(
        recipe_material_id=_child_text(element, "ID"),
        descriptions=_descriptions(element),
        material_id=_child_text(element, "MaterialID"),
        order=_child_text(element, "Order"),
        amount=_parse_material_amount(_child(element, "Amount")),
        role=role,
    )


def _parse_material_group(
    formula_element: ET.Element | None,
    group_name: str,
    role: MaterialRole,
) -> list[RecipeMaterial]:
    group = _child(formula_element, group_name)
    if group is None:
        return []
    return [_parse_material(material, role) for material in _children(group, "Material")]


def _parse_process_parameter(element: ET.Element) -> ProcessElementParameter:
    return ProcessElementParameter(
        parameter_id=_child_text(element, "ID"),
        descriptions=_descriptions(element),
        parameter_type=_child_text(element, "ProcessElementParameterType"),
        values=[
            _parse_parameter_value(value)
            for value in _children(element, "Value")
        ],
        child_parameters=[
            _parse_process_parameter(parameter)
            for parameter in _children(element, "ProcessElementParameter")
        ],
    )


def _parse_constraint_property(element: ET.Element) -> ResourceConstraintProperty:
    return ResourceConstraintProperty(
        property_id=_child_text(element, "ID"),
        descriptions=_descriptions(element),
        values=[
            _parse_parameter_value(value)
            for value in _children(element, "Value")
        ],
    )


def _parse_resource_constraint(element: ET.Element) -> ResourceConstraint:
    return ResourceConstraint(
        constraint_id=_child_text(element, "ConstraintID"),
        descriptions=_descriptions(element),
        constraint_types=[
            _text(constraint_type)
            for constraint_type in _children(element, "ConstraintType")
        ],
        life_cycle_state=_child_text(element, "LifeCycleState"),
        ranges=[
            _parse_parameter_value(value)
            for value in _children(element, "Range")
        ],
        properties=[
            _parse_constraint_property(property_element)
            for property_element in _children(
                element, "ResourceConstraintProperty"
            )
        ],
    )


def _parse_other_information(element: ET.Element) -> OtherInformation:
    return OtherInformation(
        other_info_id=_child_text(element, "OtherInfoID"),
        descriptions=_descriptions(element),
        values=[
            _parse_parameter_value(value)
            for value in _children(element, "OtherValue")
        ],
    )


def _semantic_description(
    other_information: list[OtherInformation],
) -> str | None:
    for information in other_information:
        info_id = (information.other_info_id or "").strip().casefold()
        if info_id != "semanticdescription":
            continue
        for value in information.values:
            if value.value_string is not None:
                return value.value_string
    return None


def _parse_process_element(element: ET.Element) -> ProcessElement:
    other_information = [
        _parse_other_information(info)
        for info in _children(element, "OtherInformation")
    ]
    return ProcessElement(
        process_element_id=_child_text(element, "ID"),
        descriptions=_descriptions(element),
        process_element_type=_child_text(element, "ProcessElementType"),
        life_cycle_state=_child_text(element, "LifeCycleState"),
        sequence_order=_child_text(element, "SequenceOrder"),
        sequence_path=_child_text(element, "SequencePath"),
        parameters=[
            _parse_process_parameter(parameter)
            for parameter in _children(element, "ProcessElementParameter")
        ],
        resource_constraints=[
            _parse_resource_constraint(constraint)
            for constraint in _children(element, "ResourceConstraint")
        ],
        other_information=other_information,
        child_process_elements=[
            _parse_process_element(child)
            for child in _children(element, "ProcessElement")
        ],
        semantic_description=_semantic_description(other_information),
    )


def _flatten_process_elements(
    process_elements: list[ProcessElement],
) -> list[ProcessElement]:
    flattened: list[ProcessElement] = []
    for process_element in process_elements:
        flattened.append(process_element)
        flattened.extend(
            _flatten_process_elements(process_element.child_process_elements)
        )
    return flattened


def _parse_directed_link(element: ET.Element) -> DirectedLink:
    return DirectedLink(
        link_id=_child_text(element, "ID"),
        descriptions=_descriptions(element),
        from_id=_child_text(element, "FromID"),
        to_id=_child_text(element, "ToID"),
    )


def _collect_directed_links(element: ET.Element | None) -> list[DirectedLink]:
    if element is None:
        return []
    links = [
        _parse_directed_link(link)
        for link in _children(element, "DirectedLink")
    ]
    for process_element in _children(element, "ProcessElement"):
        links.extend(_collect_directed_links(process_element))
    return links


def _parse_formula(element: ET.Element | None) -> RecipeFormula | None:
    if element is None:
        return None
    return RecipeFormula(
        descriptions=_descriptions(element),
        inputs=_parse_material_group(
            element, "ProcessInputs", MaterialRole.INPUT
        ),
        outputs=_parse_material_group(
            element, "ProcessOutputs", MaterialRole.OUTPUT
        ),
        intermediates=_parse_material_group(
            element,
            "ProcessIntermediates",
            MaterialRole.INTERMEDIATE,
        ),
        parameters=[
            _parse_process_parameter(parameter)
            for parameter in _children(element, "ProcessElementParameter")
        ],
    )


def _build_material_flow_graph(
    recipe_id: str | None,
    formula: RecipeFormula | None,
    process_elements: list[ProcessElement],
    directed_links: list[DirectedLink],
) -> MaterialFlowGraph:
    recipe_key = recipe_id or "general-recipe"
    graph_id = f"{recipe_key}:material-flow"
    nodes: list[MaterialNode | ProcessNode] = []
    material_nodes: dict[str, MaterialNode] = {}

    materials = []
    if formula is not None:
        materials = formula.inputs + formula.intermediates + formula.outputs
    for index, material in enumerate(materials, start=1):
        node_id = material.recipe_material_id or f"{graph_id}:material:{index}"
        node = MaterialNode(
            node_id=node_id,
            label=material.description or material.recipe_material_id,
            material_node_id=node_id,
            recipe_material_id=material.recipe_material_id or node_id,
            material_id=material.material_id,
            description=material.description,
            role=material.role,
            amount=material.amount,
        )
        nodes.append(node)
        material_nodes[node_id] = node

    for index, process_element in enumerate(process_elements, start=1):
        node_id = (
            process_element.process_element_id
            or f"{graph_id}:process:{index}"
        )
        nodes.append(
            ProcessNode(
                node_id=node_id,
                label=process_element.description
                or process_element.process_element_id,
                process_element_id=node_id,
                capability_iri=process_element.semantic_description,
            )
        )

    edges: list[MaterialFlowEdge] = []
    for index, link in enumerate(directed_links, start=1):
        source_material = material_nodes.get(link.from_id or "")
        target_material = material_nodes.get(link.to_id or "")
        amount_source = source_material or target_material
        edges.append(
            MaterialFlowEdge(
                edge_id=link.link_id or f"{graph_id}:edge:{index}",
                source_id=link.from_id,
                target_id=link.to_id,
                source_directed_link_id=link.link_id,
                is_material_transfer=amount_source is not None,
                amount=amount_source.amount if amount_source is not None else None,
            )
        )

    return MaterialFlowGraph(
        graph_id=graph_id,
        recipe_id=recipe_id,
        nodes=nodes,
        edges=edges,
        balances=[],
    )


def parse_general_recipe_model(file_path: str | Path) -> GeneralRecipe:
    """Parse a BatchML General Recipe XML file into the model layer."""

    root = ET.parse(Path(file_path)).getroot()
    formula = _parse_formula(_child(root, "Formula"))
    process_procedure = _child(root, "ProcessProcedure")
    root_process_elements = [
        _parse_process_element(element)
        for element in _children(process_procedure, "ProcessElement")
    ]
    process_elements = _flatten_process_elements(root_process_elements)
    directed_links = _collect_directed_links(process_procedure)
    recipe_id = _child_text(root, "ID")
    material_flow_graph = _build_material_flow_graph(
        recipe_id=recipe_id,
        formula=formula,
        process_elements=process_elements,
        directed_links=directed_links,
    )

    return GeneralRecipe(
        material_flow_graph=material_flow_graph,
        recipe_id=recipe_id,
        descriptions=_descriptions(root),
        recipe_type=_child_text(root, "GRecipeType"),
        life_cycle_state=_child_text(root, "LifeCycleState"),
        formula=formula,
        process_procedure_id=_child_text(process_procedure, "ID"),
        process_procedure_descriptions=_descriptions(process_procedure),
        process_procedure_type=_child_text(
            process_procedure, "ProcessElementType"
        ),
        process_elements=process_elements,
        directed_links=directed_links,
        resource_constraints=[
            _parse_resource_constraint(constraint)
            for constraint in _children(root, "ResourceConstraint")
        ],
        process_procedure_resource_constraints=[
            _parse_resource_constraint(constraint)
            for constraint in _children(
                process_procedure, "ResourceConstraint"
            )
        ],
        other_information=[
            _parse_other_information(info)
            for info in _children(root, "OtherInformation")
        ],
        process_procedure_other_information=[
            _parse_other_information(info)
            for info in _children(process_procedure, "OtherInformation")
        ],
    )
