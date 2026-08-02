"""Read-only regression checks for the canonical AASX system inputs.

Package-level validity and successful BaSyx failsafe loading do not imply full
AAS metamodel conformance. The pre-existing BaSyx diagnostics remain visible,
and strict loading is tested separately.
"""

from __future__ import annotations

import hashlib
from functools import lru_cache
from pathlib import Path

import pytest

from SMT4ModPlant.parsing.basyx_aasx_loader import load_aasx
from SMT4ModPlant.validation.aasx_package import (
    AAS_NAMESPACE_3_1,
    AAS_SUPPLEMENTARY_RELATIONSHIP,
    PackageDiagnosticSeverity,
    validate_aasx_package,
)


FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "aas" / "aasx" / "V3.1"
EXPECTED_SUBMODELS = (
    "CapabilityDescription",
    "TechnicalData",
    "ProcessEquipmentAssembly",
    "ModuleTypePackage",
    "Nameplate",
    "SimulationModels",
)
CASES = (
    (
        "HC10",
        "3beb1222068b442f47740d0adcabf2372f79ee9ab5c96bbc2f6860f7e2098785",
        9,
        8,
    ),
    (
        "HC20",
        "da9e3618aa92dae7490191aabf6f9401738c7698f770882d74745fa47ce86863",
        6,
        5,
    ),
    (
        "HC30",
        "8adc27a993f6135bff00c42b188e20d1bf601318164c18be94c93f7be83c97b0",
        2,
        1,
    ),
)


def _path(resource: str) -> Path:
    return FIXTURE_ROOT / f"2026-08-02_{resource}_V3.1.aasx"


@lru_cache(maxsize=None)
def _validated(resource: str):
    return validate_aasx_package(_path(resource))


@lru_cache(maxsize=None)
def _loaded(resource: str):
    return load_aasx(_path(resource), failsafe=True)


@pytest.mark.parametrize(
    ("resource", "expected_sha256", "supplementary_count", "fmu_count"),
    CASES,
)
def test_canonical_input_hash_and_package_integrity(
    resource,
    expected_sha256,
    supplementary_count,
    fmu_count,
):
    path = _path(resource)
    package = _validated(resource)

    assert hashlib.sha256(path.read_bytes()).hexdigest() == expected_sha256
    assert package.zip_integrity_ok
    assert package.is_valid
    assert not package.duplicate_parts
    assert len(package.aas_xml_parts) == 1
    assert package.namespaces == (AAS_NAMESPACE_3_1,)
    assert not package.missing_file_targets
    assert not package.orphan_relationships
    assert not package.duplicate_relationship_ids
    assert not any(
        diagnostic.severity is PackageDiagnosticSeverity.ERROR
        for diagnostic in package.diagnostics
    )


@pytest.mark.parametrize(
    ("resource", "expected_sha256", "supplementary_count", "fmu_count"),
    CASES,
)
def test_internal_files_have_complete_opc_relationships(
    resource,
    expected_sha256,
    supplementary_count,
    fmu_count,
):
    package = _validated(resource)
    internal_references = [
        reference
        for reference in package.file_references
        if reference.is_internal
    ]
    fmu_references = [
        reference
        for reference in internal_references
        if (reference.resolved_part or "").casefold().endswith(".fmu")
    ]
    supplementary_targets = {
        relationship.resolved_part
        for relationship in package.relationships
        if relationship.relationship_type == AAS_SUPPLEMENTARY_RELATIONSHIP
    }

    assert len(internal_references) == supplementary_count
    assert len(fmu_references) == fmu_count
    assert all(reference.target_exists for reference in internal_references)
    assert {
        reference.resolved_part for reference in internal_references
    } == supplementary_targets


@pytest.mark.parametrize(
    ("resource", "expected_sha256", "supplementary_count", "fmu_count"),
    CASES,
)
def test_basyx_deserializes_current_input_with_visible_diagnostics(
    resource,
    expected_sha256,
    supplementary_count,
    fmu_count,
):
    result = _loaded(resource)
    diagnostics = result.diagnostics
    submodel_names = tuple(submodel.id_short for submodel in result.submodels)

    assert diagnostics["basyx_version"] == "2.1.0"
    assert diagnostics["basyx_failsafe"] is True
    assert diagnostics["package_validation_passed"] is True
    assert diagnostics["deserialization_succeeded"] is True
    assert diagnostics["asset_administration_shell_count"] == 2
    assert diagnostics["submodel_count"] == 6
    assert submodel_names == EXPECTED_SUBMODELS
    assert not any("optim" in name.casefold() for name in submodel_names)
    assert diagnostics["supplementary_file_count"] == supplementary_count
    assert len(result.supplementary_file_container) == supplementary_count
    assert not diagnostics["unresolved_internal_file_references"]
    assert all(
        reference["exists_in_supplementary_file_container"]
        for reference in diagnostics["internal_file_references"]
    )
    assert diagnostics["basyx_diagnostic_count"] > 0
    assert diagnostics["basyx_diagnostics"]


@pytest.mark.parametrize(
    ("resource", "expected_sha256", "supplementary_count", "fmu_count"),
    CASES,
)
def test_current_input_still_requires_basyx_failsafe(
    resource,
    expected_sha256,
    supplementary_count,
    fmu_count,
):
    with pytest.raises(ValueError):
        load_aasx(_path(resource), failsafe=False)

