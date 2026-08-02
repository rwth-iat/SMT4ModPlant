"""Dataclasses for the UML-derived material-flow graph representation."""

from __future__ import annotations

from dataclasses import dataclass, field

from .recipe import MaterialAmount, MaterialRole


@dataclass(frozen=True)
class FlowNode:
    """A node shared by material and process graph elements."""

    node_id: str
    label: str | None


@dataclass(frozen=True)
class MaterialNode(FlowNode):
    """A graph node representing one recipe material."""

    material_node_id: str
    recipe_material_id: str
    material_id: str | None = None
    description: str | None = None
    role: MaterialRole = MaterialRole.INPUT
    amount: MaterialAmount | None = None


@dataclass(frozen=True)
class ProcessNode(FlowNode):
    """A graph node representing one recipe process element."""

    process_element_id: str
    capability_iri: str | None = None


@dataclass(frozen=True)
class MaterialFlowEdge:
    """A graph edge derived from one BatchML DirectedLink."""

    edge_id: str
    source_id: str | None
    target_id: str | None
    source_directed_link_id: str | None
    is_material_transfer: bool
    amount: MaterialAmount | None = None


@dataclass(frozen=True)
class MaterialBalanceConstraint:
    """A future material-balance expression associated with a graph."""

    constraint_id: str
    balance_scope: str
    expression: str


@dataclass(frozen=True)
class MaterialFlowGraph:
    """A material-flow graph generated from one General Recipe."""

    graph_id: str
    recipe_id: str | None
    nodes: list[FlowNode] = field(default_factory=list)
    edges: list[MaterialFlowEdge] = field(default_factory=list)
    balances: list[MaterialBalanceConstraint] = field(default_factory=list)
