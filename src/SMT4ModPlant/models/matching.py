"""Base model for future recipe-to-resource matching rules."""

from abc import ABC, abstractmethod
from dataclasses import dataclass


@dataclass(frozen=True)
class MatchingRule(ABC):
    """Metadata shared by future matching-rule implementations."""

    rule_id: str
    description: str | None = None

    @property
    @abstractmethod
    def rule_type(self) -> str:
        """Return the stable type identifier used for constraint tracing."""
