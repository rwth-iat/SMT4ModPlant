"""Models for SMT-LIB serialization, solver output, and feasibility results."""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Protocol

from .configuration import PlantConfiguration
from .constraints import ConstraintModel
from .explanation import Explanation


class SolverStatus(str, Enum):
    """The normalized outcome of an SMT solver execution."""

    SAT = "SAT"
    UNSAT = "UNSAT"
    UNKNOWN = "UNKNOWN"


@dataclass(frozen=True)
class SmtLibProgram:
    """Serialized SMT-LIB text and its originating constraint identifiers."""

    text: str
    constraint_ids: list[str] = field(default_factory=list)


@dataclass(frozen=True)
class SolverResult:
    """The normalized raw result returned by an SMT solver."""

    status: SolverStatus
    model_values: dict[str, bool | int | float | str] = field(
        default_factory=dict
    )
    unsat_core: list[str] = field(default_factory=list)
    diagnostics: list[str] = field(default_factory=list)


class SmtLibSerializer(Protocol):
    """Serialize a solver-independent constraint model to SMT-LIB."""

    def serialize(self, constraint_model: ConstraintModel) -> SmtLibProgram:
        """Return the SMT-LIB representation of a constraint model."""


class SmtSolver(Protocol):
    """Enumerate all SAT models for an SMT-LIB program."""

    def solve_all(self, program: SmtLibProgram) -> list[SolverResult]:
        """Return every SAT model found by iterative model blocking."""


@dataclass(frozen=True)
class ConfigurationSolution:
    """One SAT solver model and its executable plant configuration."""

    solution_id: int
    solver_result: SolverResult
    plant_configuration: PlantConfiguration
    explanation: Explanation

    def __post_init__(self) -> None:
        """Enforce the contract for one enumerated SAT solution."""

        if self.solution_id < 1:
            raise ValueError("A solution ID must be a positive integer.")
        if self.solver_result.status is not SolverStatus.SAT:
            raise ValueError(
                "A ConfigurationSolution requires a SAT SolverResult."
            )


@dataclass(frozen=True)
class FeasibilityResult:
    """The complete result of enumerating feasible plant configurations."""

    constraint_model: ConstraintModel
    smt_lib_program: SmtLibProgram
    status: SolverStatus
    solutions: list[ConfigurationSolution]
    explanation: Explanation

    def __post_init__(self) -> None:
        """Enforce aggregate status and solution-enumeration invariants."""

        if self.status is SolverStatus.SAT and not self.solutions:
            raise ValueError("A SAT result requires at least one solution.")
        if self.status is not SolverStatus.SAT and self.solutions:
            raise ValueError(
                "UNSAT and UNKNOWN results cannot contain solutions."
            )

        solution_ids = [solution.solution_id for solution in self.solutions]
        if len(solution_ids) != len(set(solution_ids)):
            raise ValueError("Solution IDs must be unique.")
        if sorted(solution_ids) != list(range(1, len(solution_ids) + 1)):
            raise ValueError(
                "Solution IDs must form a contiguous sequence starting at 1."
            )

        configuration_ids = [
            solution.plant_configuration.configuration_id
            for solution in self.solutions
        ]
        if len(configuration_ids) != len(set(configuration_ids)):
            raise ValueError(
                "PlantConfiguration IDs must be unique within a result."
            )
