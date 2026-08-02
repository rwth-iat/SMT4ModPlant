"""BaSyx-backed AASX loading and package-reference validation.

This loader intentionally does not replace the existing capability parser. It
only exposes BaSyx stores and diagnostics for current AASX input files.
"""

from __future__ import annotations

import importlib.metadata
import logging
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from basyx.aas import model
from basyx.aas.adapter import aasx
from basyx.aas.util import traversal

from SMT4ModPlant.validation.aasx_package import (
    PackageDiagnosticSeverity,
    validate_aasx_package,
)


class BasyxAasxValidationError(RuntimeError):
    """Raised when package or post-deserialization validation fails."""


class _DiagnosticHandler(logging.Handler):
    def __init__(self) -> None:
        super().__init__(level=logging.WARNING)
        self.records: list[dict[str, str]] = []

    def emit(self, record: logging.LogRecord) -> None:
        self.records.append(
            {
                "logger": record.name,
                "level": record.levelname,
                "message": record.getMessage(),
            }
        )


@dataclass(frozen=True)
class BasyxAasxLoadResult:
    """Loaded BaSyx object stores and their validation diagnostics."""

    path: Path
    identifiable_store: model.DictIdentifiableStore
    supplementary_file_container: aasx.DictSupplementaryFileContainer
    read_identifiers: frozenset[model.Identifier]
    diagnostics: dict[str, Any]

    @property
    def asset_administration_shells(self) -> tuple[model.AssetAdministrationShell, ...]:
        return tuple(
            item
            for item in self.identifiable_store
            if isinstance(item, model.AssetAdministrationShell)
        )

    @property
    def submodels(self) -> tuple[model.Submodel, ...]:
        return tuple(
            item
            for item in self.identifiable_store
            if isinstance(item, model.Submodel)
        )


def _load_with_captured_diagnostics(
    path: Path,
    identifiable_store: model.DictIdentifiableStore,
    file_container: aasx.DictSupplementaryFileContainer,
    *,
    failsafe: bool,
) -> tuple[set[model.Identifier], list[dict[str, str]]]:
    handler = _DiagnosticHandler()
    logger_names = (
        "basyx.aas.adapter.aasx",
        "basyx.aas.adapter.xml.xml_deserialization",
    )
    states: list[tuple[logging.Logger, int, bool]] = []
    try:
        for logger_name in logger_names:
            logger = logging.getLogger(logger_name)
            states.append((logger, logger.level, logger.propagate))
            logger.addHandler(handler)
            logger.setLevel(logging.WARNING)
            logger.propagate = False
        with aasx.AASXReader(path, failsafe=failsafe) as reader:
            identifiers = reader.read_into(identifiable_store, file_container)
    finally:
        for logger, level, propagate in states:
            logger.removeHandler(handler)
            logger.setLevel(level)
            logger.propagate = propagate
    return identifiers, handler.records


def _file_diagnostics(
    submodels: tuple[model.Submodel, ...],
    file_container: aasx.DictSupplementaryFileContainer,
) -> list[dict[str, Any]]:
    references: list[dict[str, Any]] = []
    for submodel in submodels:
        for element in traversal.walk_submodel(submodel):
            if not isinstance(element, model.File) or element.value is None:
                continue
            references.append(
                {
                    "submodel_id": str(submodel.id),
                    "submodel_id_short": submodel.id_short,
                    "file_id_short": element.id_short,
                    "value": element.value,
                    "content_type": element.content_type,
                    "exists_in_supplementary_file_container": (
                        element.value in file_container
                    ),
                }
            )
    return references


def load_aasx(
    path: str | Path,
    *,
    failsafe: bool = True,
    require_clean_package: bool = True,
) -> BasyxAasxLoadResult:
    """Load an AASX file into BaSyx stores and validate internal files.

    BaSyx's failsafe XML mode defaults to ``True`` because the supplied AAS 3.1
    documents contain pre-existing metamodel diagnostics outside package-level
    validation (for example empty optional multilingual fields). Every such
    BaSyx diagnostic is captured and returned; package-reference validation is
    strict independently of this setting.
    """

    package_path = Path(path).resolve()
    package = validate_aasx_package(package_path)
    package_errors = [
        diagnostic
        for diagnostic in package.diagnostics
        if diagnostic.severity is PackageDiagnosticSeverity.ERROR
    ]
    package_failures = {
        "zip_integrity": not package.zip_integrity_ok,
        "missing_file_targets": bool(package.missing_file_targets),
        "orphan_relationships": bool(package.orphan_relationships),
        "duplicate_relationship_ids": bool(package.duplicate_relationship_ids),
        "duplicate_zip_parts": bool(package.duplicate_parts),
        "package_error_codes": [diagnostic.code for diagnostic in package_errors],
    }
    if require_clean_package and package_errors:
        raise BasyxAasxValidationError(
            f"AASX package validation failed for {package_path.name}: "
            + ", ".join(diagnostic.code for diagnostic in package_errors)
        )

    identifiable_store = model.DictIdentifiableStore()
    file_container = aasx.DictSupplementaryFileContainer()
    identifiers, basyx_messages = _load_with_captured_diagnostics(
        package_path,
        identifiable_store,
        file_container,
        failsafe=failsafe,
    )
    shells = tuple(
        item
        for item in identifiable_store
        if isinstance(item, model.AssetAdministrationShell)
    )
    submodels = tuple(
        item for item in identifiable_store if isinstance(item, model.Submodel)
    )
    file_references = _file_diagnostics(submodels, file_container)
    unresolved = [
        item
        for item in file_references
        if not item["exists_in_supplementary_file_container"]
    ]
    if unresolved:
        raise BasyxAasxValidationError(
            f"BaSyx loaded {package_path.name}, but internal File references "
            f"are unresolved: {[item['value'] for item in unresolved]}"
        )

    supplementary_files = [
        {
            "name": name,
            "content_type": file_container.get_content_type(name),
            "sha256": file_container.get_sha256(name).hex(),
        }
        for name in file_container
    ]
    diagnostics: dict[str, Any] = {
        "path": str(package_path),
        "basyx_version": importlib.metadata.version("basyx-python-sdk"),
        "basyx_failsafe": failsafe,
        "package_validation_passed": package.is_valid,
        "package_failures": package_failures,
        "package_diagnostics": [
            {
                "code": diagnostic.code,
                "severity": diagnostic.severity.value,
                "message": diagnostic.message,
                "package_part": diagnostic.package_part,
                "related_value": diagnostic.related_value,
            }
            for diagnostic in package.diagnostics
        ],
        "aas_namespace": list(package.namespaces),
        "identifiable_count": len(identifiable_store),
        "read_identifier_count": len(identifiers),
        "asset_administration_shell_count": len(shells),
        "asset_administration_shells": [
            {"id_short": shell.id_short, "id": str(shell.id)} for shell in shells
        ],
        "submodel_count": len(submodels),
        "submodels": [
            {"id_short": submodel.id_short, "id": str(submodel.id)}
            for submodel in submodels
        ],
        "internal_file_references": file_references,
        "unresolved_internal_file_references": unresolved,
        "supplementary_file_count": len(file_container),
        "supplementary_files": supplementary_files,
        "basyx_diagnostic_count": len(basyx_messages),
        "basyx_diagnostics": basyx_messages,
        "deserialization_succeeded": True,
    }
    return BasyxAasxLoadResult(
        path=package_path,
        identifiable_store=identifiable_store,
        supplementary_file_container=file_container,
        read_identifiers=frozenset(identifiers),
        diagnostics=diagnostics,
    )
