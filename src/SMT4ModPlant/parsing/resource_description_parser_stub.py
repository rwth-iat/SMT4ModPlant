"""Declare the future model-based resource parser without replacing legacy code."""

from pathlib import Path

from ..models.resources import ResourceDescription


def parse_resource_description_model(
    file_path: str | Path,
) -> ResourceDescription:
    """Reserve the public API for a later resource-parsing implementation."""

    raise NotImplementedError(
        "Model-based resource parsing will be implemented in a later task."
    )
