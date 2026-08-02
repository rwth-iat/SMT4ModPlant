"""Trace models for explaining SAT, UNSAT, and UNKNOWN solver outcomes."""

from __future__ import annotations

from dataclasses import dataclass, field


@dataclass(frozen=True)
class ConstraintTrace:
    """Explain the outcome of one generated logical constraint."""

    constraint_id: str
    rule_id: str
    message: str
    source_references: list[str] = field(default_factory=list)
    satisfied: bool | None = None


@dataclass(frozen=True)
class Explanation:
    """A human-readable and machine-traceable solver explanation."""

    summary: str
    traces: list[ConstraintTrace] = field(default_factory=list)
    unsat_core: list[str] = field(default_factory=list)
    diagnostics: list[str] = field(default_factory=list)
