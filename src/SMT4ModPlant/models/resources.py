"""Placeholder models for future model-based resource description parsing."""

from __future__ import annotations

from dataclasses import dataclass, field


@dataclass(frozen=True)
class CapabilityConstraint:
    """A constraint attached to a provided capability property."""

    constraint_id: str | None = None
    constraint_type: str | None = None
    value: str | None = None
    unit: str | None = None


@dataclass(frozen=True)
class CapabilityProperty:
    """A semantic property of a capability offered by a resource."""

    property_id: str | None = None
    name: str | None = None
    value: str | None = None
    unit: str | None = None
    constraints: list[CapabilityConstraint] = field(default_factory=list)


@dataclass(frozen=True)
class ProvidedCapability:
    """A capability exposed by a resource description."""

    capability_id: str | None = None
    name: str | None = None
    semantic_id: str | None = None
    execution_reference: str | None = None
    properties: list[CapabilityProperty] = field(default_factory=list)


@dataclass(frozen=True)
class ResourceDescription:
    """The future model-based representation of one plant resource."""

    resource_id: str | None = None
    name: str | None = None
    capabilities: list[ProvidedCapability] = field(default_factory=list)
