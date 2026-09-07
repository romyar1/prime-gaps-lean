#!/usr/bin/env python3
"""Verify portable source records, optionally against the original collection.

This checks bytes and metadata-only normalization. It does not evaluate the
integral inequalities or discharge any Lean theorem hypothesis.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Any


SOURCE_BUNDLE = "prime_gaps_20260903/"
SOURCE_PREFIX = re.compile(r'/(?:[^/"\\\r\n]+/)*prime_gaps_20260903/')
HOST_PATH = re.compile(r'/(?:Users|home|private|tmp|var)/')


class JSONNumber(str):
    """Retain the exact spelling of each JSON numeric token."""


def decode(text: str) -> Any:
    return json.loads(text, parse_int=JSONNumber, parse_float=JSONNumber)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def normalize_text(text: str) -> tuple[str, int]:
    """Replace only an absolute prefix ending in the fixed source-bundle name."""
    return SOURCE_PREFIX.subn(SOURCE_BUNDLE, text)


def logical_string(value: str) -> str:
    return normalize_text(value)[0]


def pointer_part(value: str) -> str:
    return logical_string(value).replace("~", "~0").replace("/", "~1")


def non_path_payload(text: str) -> tuple[str, int]:
    """Canonical typed non-path leaves, preserving all numeric token spellings.

    JSON pointers use logical source identifiers for any provenance keys.
    Only path-valued string leaves are omitted. Every other leaf, including
    bounds encoded as decimal/rational/interval strings, contributes to the
    SHA256. The byte-normalization check separately protects the path leaves.
    """
    leaves: list[list[Any]] = []

    def walk(value: Any, pointer: str) -> None:
        if isinstance(value, dict):
            for key in sorted(value, key=logical_string):
                walk(value[key], pointer + "/" + pointer_part(key))
        elif isinstance(value, list):
            for index, item in enumerate(value):
                walk(item, pointer + "/" + str(index))
        elif isinstance(value, JSONNumber):
            leaves.append([pointer, "number", str(value)])
        elif isinstance(value, str):
            if SOURCE_BUNDLE not in value:
                leaves.append([pointer, "string", value])
        elif isinstance(value, bool):
            leaves.append([pointer, "boolean", value])
        elif value is None:
            leaves.append([pointer, "null", None])
        else:
            raise ValueError(f"Unexpected JSON type at {pointer}: {type(value).__name__}")

    walk(decode(text), "")
    canonical = json.dumps(leaves, ensure_ascii=False, separators=(",", ":"))
    return digest(canonical.encode("utf-8")), len(leaves)


def path_changes(text: str) -> list[dict[str, str]]:
    """Record changed JSON key/value locations without recording host paths."""
    changes: list[dict[str, str]] = []

    def walk(value: Any, pointer: str) -> None:
        if isinstance(value, dict):
            normalized_keys = [logical_string(key) for key in value]
            if len(set(normalized_keys)) != len(normalized_keys):
                raise ValueError(f"Path normalization collides at {pointer}")
            for key, item in value.items():
                location = pointer + "/" + pointer_part(key)
                if logical_string(key) != key:
                    changes.append({"kind": "key", "location": location})
                walk(item, location)
        elif isinstance(value, list):
            for index, item in enumerate(value):
                walk(item, pointer + "/" + str(index))
        elif isinstance(value, str) and not isinstance(value, JSONNumber):
            if logical_string(value) != value:
                changes.append({"kind": "value", "location": pointer})

    walk(decode(text), "")
    return changes


def source_references(text: str) -> set[str]:
    refs: set[str] = set()

    def walk(value: Any) -> None:
        if isinstance(value, dict):
            for key, item in value.items():
                walk(key)
                walk(item)
        elif isinstance(value, list):
            for item in value:
                walk(item)
        elif isinstance(value, str) and not isinstance(value, JSONNumber):
            logical = logical_string(value)
            if logical.startswith(SOURCE_BUNDLE):
                refs.add(logical)

    walk(decode(text))
    return refs


def ensure(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def verify(repo: Path, source_dir: Path | None) -> dict[str, Any]:
    manifest_path = repo / "provenance/data_manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    ensure(manifest["schema_version"] == 1, "Unsupported manifest schema")
    ensure(manifest["numerical_premises_discharged"] is False, "Incorrect numerical proof status")
    ensure(manifest["type_iii_proved"] is False, "Incorrect Type III proof status")
    records = manifest["files"]
    expected = {record["published_path"] for record in records}
    ensure(len(expected) == len(records), "Duplicate manifest file records")
    actual = {str(path.relative_to(repo)) for path in
              (repo / "inputs/source_certificates").rglob("*.json")}
    ensure(expected == actual, "Source-certificate file inventory mismatch")
    all_references: set[str] = set()
    source_ids: dict[str, str] = {}
    total_bytes = 0
    replacement_count = 0
    for record in records:
        path = repo / record["published_path"]
        data = path.read_bytes()
        text = data.decode("utf-8")
        ensure(digest(data) == record["published_sha256"], f"Published digest mismatch: {path.name}")
        ensure(len(data) == record["published_bytes"], f"Published size mismatch: {path.name}")
        ensure(not HOST_PATH.search(text), f"Absolute host path remains: {path.name}")
        ensure(normalize_text(text)[1] == 0, f"Unnormalized source prefix remains: {path.name}")
        payload_hash, leaf_count = non_path_payload(text)
        ensure(payload_hash == record["canonical_non_path_payload_sha256"],
               f"Non-path payload mismatch: {path.name}")
        ensure(leaf_count == record["canonical_non_path_leaf_count"],
               f"Non-path leaf count mismatch: {path.name}")
        ensure(record["non_path_payload_unchanged"] is True,
               f"Non-path payload not marked unchanged: {path.name}")
        source_ids[record["source_identifier"]] = record["published_path"]
        all_references.update(source_references(text))
        total_bytes += len(data)
        replacement_count += record["path_prefix_replacements"]
        if source_dir is not None:
            original = source_dir / record["source_relative_path"]
            original_data = original.read_bytes()
            original_text = original_data.decode("utf-8")
            ensure(digest(original_data) == record["original_sha256"],
                   f"Original digest mismatch: {original.name}")
            ensure(len(original_data) == record["original_bytes"],
                   f"Original size mismatch: {original.name}")
            normalized, count = normalize_text(original_text)
            ensure(normalized == text, f"Change beyond path normalization: {path.name}")
            ensure(count == record["path_prefix_replacements"],
                   f"Path replacement count mismatch: {path.name}")
            ensure(path_changes(original_text) == record["changed_json_locations"],
                   f"Changed field inventory mismatch: {path.name}")
            ensure(non_path_payload(original_text) == (payload_hash, leaf_count),
                   f"Original non-path payload mismatch: {path.name}")
    expected_refs = []
    for ref in sorted(all_references):
        published = source_ids.get(ref)
        expected_refs.append({
            "source_identifier": ref,
            "availability": ("included_after_path_normalization" if published else
                             "provenance_only_not_in_repository"),
            "published_path": published,
        })
    ensure(expected_refs == manifest["source_references"], "Source reference inventory mismatch")
    ensure(len(records) == manifest["file_count"], "Manifest file count mismatch")
    ensure(total_bytes == manifest["published_total_bytes"], "Manifest total size mismatch")
    ensure(sum(record["original_bytes"] for record in records) == manifest["original_total_bytes"],
           "Manifest original size total mismatch")
    ensure(replacement_count == manifest["path_prefix_replacements"],
           "Manifest total replacement count mismatch")
    return {
        "status": "PASS_DATA_INTEGRITY_ONLY",
        "files_checked": len(records),
        "published_bytes": total_bytes,
        "original_comparison_performed": source_dir is not None,
        "numerical_premises_discharged": False,
        "type_iii_proved": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path,
                        help="Optional original source_certificates directory for read-only comparison")
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    try:
        result = verify(repo, args.source_dir)
    except (OSError, ValueError, KeyError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
