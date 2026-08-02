"""Read-only validation of AASX ZIP and OPC package structures.

The validator reads package metadata and XML structures without extracting or
rewriting any package part. A valid result covers package-level consistency;
it does not assert full AAS metamodel conformance.
"""

from __future__ import annotations

import posixpath
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from urllib.parse import unquote, urlsplit
from xml.etree import ElementTree as ET
from zipfile import BadZipFile, ZipFile


AAS_NAMESPACE_3_1 = "https://admin-shell.io/aas/3/1"
AAS_SUPPLEMENTARY_RELATIONSHIP = (
    "http://admin-shell.io/aasx/relationships/aas-suppl"
)


class PackageDiagnosticSeverity(str, Enum):
    """Severity of a package-level validation diagnostic."""

    INFO = "info"
    WARNING = "warning"
    ERROR = "error"


@dataclass(frozen=True)
class PackageDiagnostic:
    """One structured AASX package diagnostic."""

    code: str
    severity: PackageDiagnosticSeverity
    message: str
    package_part: str | None = None
    related_value: str | None = None


@dataclass(frozen=True)
class FileReference:
    """An AAS ``File.value`` reference and its resolved package target."""

    aas_xml_part: str
    element_path: str
    value: str
    resolved_part: str | None
    is_internal: bool
    target_exists: bool | None


@dataclass(frozen=True)
class OpcRelationship:
    """An OPC relationship and its resolved package target."""

    relationship_part: str
    source_part: str
    relationship_id: str | None
    relationship_type: str | None
    target: str
    target_mode: str | None
    resolved_part: str | None
    target_exists: bool | None


@dataclass(frozen=True)
class DuplicateRelationshipId:
    """A relationship ID repeated within one ``.rels`` part."""

    relationship_part: str
    relationship_id: str


@dataclass(frozen=True)
class AasxPackageValidationResult:
    """Complete result of read-only AASX package validation."""

    path: Path
    zip_integrity_ok: bool
    duplicate_parts: tuple[str, ...]
    aas_xml_parts: tuple[str, ...]
    namespaces: tuple[str, ...]
    file_references: tuple[FileReference, ...]
    relationships: tuple[OpcRelationship, ...]
    missing_file_targets: tuple[FileReference, ...]
    orphan_relationships: tuple[OpcRelationship, ...]
    duplicate_relationship_ids: tuple[DuplicateRelationshipId, ...]
    diagnostics: tuple[PackageDiagnostic, ...]

    @property
    def is_valid(self) -> bool:
        """Whether no package-level error diagnostic was found."""

        return not any(
            diagnostic.severity is PackageDiagnosticSeverity.ERROR
            for diagnostic in self.diagnostics
        )


class _InvalidInternalTarget(ValueError):
    pass


def _local_name(tag: str) -> str:
    return tag.rsplit("}", 1)[-1]


def _namespace(tag: str) -> str:
    return tag[1:].split("}", 1)[0] if tag.startswith("{") else ""


def _is_external_reference(reference: str) -> bool:
    return reference.startswith("//") or ":" in reference.split("/", 1)[0]


def _resolve_internal_target(reference: str, source_part: str) -> str | None:
    if not reference or _is_external_reference(reference):
        return None
    parsed = urlsplit(reference)
    if parsed.scheme or parsed.netloc:
        return None
    target_path = unquote(parsed.path).replace("\\", "/")
    if target_path.startswith("/"):
        combined = target_path.lstrip("/")
    else:
        combined = posixpath.join(posixpath.dirname(source_part), target_path)
    normalized = posixpath.normpath(combined)
    if normalized in ("", ".", "..") or normalized.startswith("../"):
        raise _InvalidInternalTarget(
            f"Target {reference!r} from {source_part!r} escapes the package root"
        )
    return normalized.lstrip("/")


def _relationship_source_part(relationship_part: str) -> str:
    normalized = relationship_part.lstrip("/")
    if normalized == "_rels/.rels":
        return ""
    directory, marker, filename = normalized.rpartition("/_rels/")
    if not marker or not filename.endswith(".rels"):
        raise ValueError(f"Invalid OPC relationship part: {relationship_part}")
    return posixpath.join(directory, filename[: -len(".rels")])


def _relationship_part_for(source_part: str) -> str:
    directory, filename = posixpath.split(source_part)
    return posixpath.join(directory, "_rels", f"{filename}.rels")


def _element_path(root: ET.Element, target: ET.Element) -> str:
    parents = {child: parent for parent in root.iter() for child in parent}
    parts: list[str] = []
    current = target
    while True:
        name = _local_name(current.tag)
        parent = parents.get(current)
        if parent is not None:
            peers = [child for child in parent if _local_name(child.tag) == name]
            if len(peers) > 1:
                name += f"[{peers.index(current) + 1}]"
        parts.append(name)
        if parent is None:
            break
        current = parent
    return "/" + "/".join(reversed(parts))


def _invalid_zip_result(path: Path, message: str) -> AasxPackageValidationResult:
    return AasxPackageValidationResult(
        path=path,
        zip_integrity_ok=False,
        duplicate_parts=(),
        aas_xml_parts=(),
        namespaces=(),
        file_references=(),
        relationships=(),
        missing_file_targets=(),
        orphan_relationships=(),
        duplicate_relationship_ids=(),
        diagnostics=(
            PackageDiagnostic(
                code="ZIP_INVALID",
                severity=PackageDiagnosticSeverity.ERROR,
                message=message,
            ),
        ),
    )


def validate_aasx_package(path: str | Path) -> AasxPackageValidationResult:
    """Validate an AASX package without mutating it or any contained part."""

    package_path = Path(path).resolve()
    try:
        with ZipFile(package_path, "r") as archive:
            infos = archive.infolist()
            part_names = [info.filename for info in infos if not info.is_dir()]
            duplicate_parts = tuple(
                sorted({name for name in part_names if part_names.count(name) > 1})
            )
            package_parts = set(part_names)
            data: dict[str, bytes] = {}
            for info in infos:
                if info.is_dir() or info.filename in data:
                    continue
                with archive.open(info, "r") as stream:
                    data[info.filename] = stream.read()
            try:
                bad_part = archive.testzip()
            except Exception as exc:
                return _invalid_zip_result(package_path, str(exc))
    except (BadZipFile, OSError) as exc:
        return _invalid_zip_result(package_path, str(exc))

    diagnostics: list[PackageDiagnostic] = []
    if bad_part is not None:
        diagnostics.append(
            PackageDiagnostic(
                code="ZIP_INTEGRITY_ERROR",
                severity=PackageDiagnosticSeverity.ERROR,
                message=f"ZIP integrity check failed at {bad_part}",
                package_part=bad_part,
            )
        )
    for duplicate in duplicate_parts:
        diagnostics.append(
            PackageDiagnostic(
                code="ZIP_PART_DUPLICATE",
                severity=PackageDiagnosticSeverity.ERROR,
                message=f"Duplicate ZIP part: {duplicate}",
                package_part=duplicate,
            )
        )

    aas_xml_parts = tuple(
        name for name in part_names if name.casefold().endswith(".aas.xml")
    )
    if not aas_xml_parts:
        diagnostics.append(
            PackageDiagnostic(
                code="AAS_XML_PART_MISSING",
                severity=PackageDiagnosticSeverity.ERROR,
                message="No AAS XML package part was found",
            )
        )

    namespaces: list[str] = []
    file_references: list[FileReference] = []
    readable_aas_parts: list[str] = []
    for aas_part in aas_xml_parts:
        try:
            root = ET.fromstring(data[aas_part])
        except ET.ParseError as exc:
            diagnostics.append(
                PackageDiagnostic(
                    code="AAS_XML_INVALID",
                    severity=PackageDiagnosticSeverity.ERROR,
                    message=str(exc),
                    package_part=aas_part,
                )
            )
            continue
        readable_aas_parts.append(aas_part)
        namespace = _namespace(root.tag)
        namespaces.append(namespace)
        if namespace != AAS_NAMESPACE_3_1:
            diagnostics.append(
                PackageDiagnostic(
                    code="AAS_NAMESPACE_UNSUPPORTED",
                    severity=PackageDiagnosticSeverity.ERROR,
                    message=(
                        f"Expected {AAS_NAMESPACE_3_1}, found {namespace!r}"
                    ),
                    package_part=aas_part,
                    related_value=namespace,
                )
            )
        file_tag = f"{{{namespace}}}file"
        value_tag = f"{{{namespace}}}value"
        for file_element in root.iter(file_tag):
            value_element = file_element.find(value_tag)
            if value_element is None or value_element.text is None:
                continue
            value = value_element.text
            try:
                resolved = _resolve_internal_target(value, aas_part)
            except _InvalidInternalTarget as exc:
                resolved = None
                diagnostics.append(
                    PackageDiagnostic(
                        code="FILE_TARGET_INVALID",
                        severity=PackageDiagnosticSeverity.ERROR,
                        message=str(exc),
                        package_part=aas_part,
                        related_value=value,
                    )
                )
                file_references.append(
                    FileReference(
                        aas_xml_part=aas_part,
                        element_path=_element_path(root, value_element),
                        value=value,
                        resolved_part=None,
                        is_internal=True,
                        target_exists=False,
                    )
                )
                continue
            file_references.append(
                FileReference(
                    aas_xml_part=aas_part,
                    element_path=_element_path(root, value_element),
                    value=value,
                    resolved_part=resolved,
                    is_internal=resolved is not None,
                    target_exists=(
                        resolved in package_parts if resolved is not None else None
                    ),
                )
            )

    missing_file_targets = tuple(
        reference
        for reference in file_references
        if reference.is_internal and not reference.target_exists
    )
    for reference in missing_file_targets:
        diagnostics.append(
            PackageDiagnostic(
                code="FILE_TARGET_MISSING",
                severity=PackageDiagnosticSeverity.ERROR,
                message=f"Internal File.value target is missing: {reference.value}",
                package_part=reference.aas_xml_part,
                related_value=reference.value,
            )
        )

    relationships: list[OpcRelationship] = []
    duplicate_relationship_ids: list[DuplicateRelationshipId] = []
    for relationship_part in (
        name for name in part_names if name.casefold().endswith(".rels")
    ):
        try:
            source_part = _relationship_source_part(relationship_part)
            root = ET.fromstring(data[relationship_part])
        except (ET.ParseError, ValueError) as exc:
            diagnostics.append(
                PackageDiagnostic(
                    code="RELATIONSHIP_PART_INVALID",
                    severity=PackageDiagnosticSeverity.ERROR,
                    message=str(exc),
                    package_part=relationship_part,
                )
            )
            continue
        ids: list[str] = []
        for element in root:
            relationship_id = element.attrib.get("Id")
            if relationship_id is not None:
                ids.append(relationship_id)
            target = element.attrib.get("Target", "")
            target_mode = element.attrib.get("TargetMode")
            try:
                resolved = (
                    None
                    if target_mode == "External"
                    else _resolve_internal_target(target, source_part)
                )
            except _InvalidInternalTarget as exc:
                resolved = None
                diagnostics.append(
                    PackageDiagnostic(
                        code="RELATIONSHIP_TARGET_INVALID",
                        severity=PackageDiagnosticSeverity.ERROR,
                        message=str(exc),
                        package_part=relationship_part,
                        related_value=target,
                    )
                )
            relationships.append(
                OpcRelationship(
                    relationship_part=relationship_part,
                    source_part=source_part,
                    relationship_id=relationship_id,
                    relationship_type=element.attrib.get("Type"),
                    target=target,
                    target_mode=target_mode,
                    resolved_part=resolved,
                    target_exists=(
                        resolved in package_parts if resolved is not None else None
                    ),
                )
            )
        for duplicate_id in sorted(
            {relationship_id for relationship_id in ids if ids.count(relationship_id) > 1}
        ):
            duplicate_relationship_ids.append(
                DuplicateRelationshipId(relationship_part, duplicate_id)
            )
            diagnostics.append(
                PackageDiagnostic(
                    code="RELATIONSHIP_ID_DUPLICATE",
                    severity=PackageDiagnosticSeverity.ERROR,
                    message=f"Duplicate relationship ID: {duplicate_id}",
                    package_part=relationship_part,
                    related_value=duplicate_id,
                )
            )

    orphan_relationships = tuple(
        relationship
        for relationship in relationships
        if relationship.target_mode != "External"
        and relationship.resolved_part is not None
        and not relationship.target_exists
    )
    for relationship in orphan_relationships:
        diagnostics.append(
            PackageDiagnostic(
                code="RELATIONSHIP_TARGET_MISSING",
                severity=PackageDiagnosticSeverity.ERROR,
                message=(
                    f"Relationship {relationship.relationship_id!r} targets "
                    f"missing part {relationship.target!r}"
                ),
                package_part=relationship.relationship_part,
                related_value=relationship.target,
            )
        )

    supplementary_targets_by_source: dict[str, set[str]] = {}
    for relationship in relationships:
        if (
            relationship.relationship_type == AAS_SUPPLEMENTARY_RELATIONSHIP
            and relationship.resolved_part is not None
            and relationship.target_mode != "External"
        ):
            supplementary_targets_by_source.setdefault(
                relationship.source_part, set()
            ).add(relationship.resolved_part)
    for reference in file_references:
        if not reference.is_internal or not reference.target_exists:
            continue
        related_targets = supplementary_targets_by_source.get(
            reference.aas_xml_part, set()
        )
        if reference.resolved_part not in related_targets:
            diagnostics.append(
                PackageDiagnostic(
                    code="SUPPLEMENTARY_RELATIONSHIP_MISSING",
                    severity=PackageDiagnosticSeverity.ERROR,
                    message=(
                        "No aas-suppl relationship references the internal "
                        f"file {reference.resolved_part}"
                    ),
                    package_part=_relationship_part_for(reference.aas_xml_part),
                    related_value=reference.value,
                )
            )

    if not any(
        diagnostic.severity is PackageDiagnosticSeverity.ERROR
        for diagnostic in diagnostics
    ):
        diagnostics.append(
            PackageDiagnostic(
                code="PACKAGE_VALIDATION_OK",
                severity=PackageDiagnosticSeverity.INFO,
                message=(
                    f"Validated {len(readable_aas_parts)} AAS XML part(s), "
                    f"{len(file_references)} File reference(s), and "
                    f"{len(relationships)} OPC relationship(s)"
                ),
            )
        )

    return AasxPackageValidationResult(
        path=package_path,
        zip_integrity_ok=bad_part is None,
        duplicate_parts=duplicate_parts,
        aas_xml_parts=aas_xml_parts,
        namespaces=tuple(namespaces),
        file_references=tuple(file_references),
        relationships=tuple(relationships),
        missing_file_targets=missing_file_targets,
        orphan_relationships=orphan_relationships,
        duplicate_relationship_ids=tuple(duplicate_relationship_ids),
        diagnostics=tuple(diagnostics),
    )

