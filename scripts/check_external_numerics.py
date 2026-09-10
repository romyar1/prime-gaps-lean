#!/usr/bin/env python3
"""Check the frozen external numerical release and its repository copies offline.

This is an integrity check of an already completed run, not a numerical rerun
or a Lean proof. Python 3.11+; no third-party packages, downloads or extraction.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import zipfile

ROOT = Path(__file__).resolve().parents[1]
DATA = Path("research/numerical_182")
PASS = "PASS_COMPLETE_EXTERNAL_NUMERICAL_RECOMPUTATION"
NEGATIVE_CASES = {"negative_denominator", "missing_inner_bin", "changed_trial",
                  "obsolete_fft_runtime"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def require_materialized(path):
    require(not getattr(path.stat(), "st_flags", 0) & 0x40000000,
            "Online-only file refused: " + str(path))


def read_json(path):
    require_materialized(path)
    return json.loads(path.read_text())


def digest_file(path):
    require_materialized(path)
    with path.open("rb") as stream:
        return digest_stream(stream)


def digest_stream(stream):
    result = hashlib.sha256()
    for block in iter(lambda: stream.read(1024 * 1024), b""):
        result.update(block)
    return result.hexdigest()


def safe_relative(name):
    path = PurePosixPath(name)
    require(bool(path.parts) and not path.is_absolute() and ".." not in path.parts
            and "\\" not in name and path.as_posix() == name,
            "Invalid relative path: " + name)
    return path


def check_repository(root=ROOT):
    data = root / DATA
    asset = read_json(data / "asset.json")
    manifest_path = data / "package-manifest.json"
    require(digest_file(manifest_path) == asset["archive"]["manifest_sha256"],
            "Package manifest differs from the pinned release")
    manifest = read_json(manifest_path)
    require(manifest["status"] == PASS, "Release lacks completed acceptance")
    require(len(manifest["files"]) == asset["archive"]["manifest_files"] == 913,
            "Incomplete release manifest")
    for name in manifest["files"]:
        safe_relative(name)
    for name, record in asset["repository_copies"].items():
        safe_relative(name)
        source = record["archive_path"]
        require(manifest["files"][source] == {k: record[k] for k in ("bytes", "sha256")},
                "Repository copy disagrees with release manifest: " + name)
        path = data / name
        require(path.stat().st_size == record["bytes"]
                and digest_file(path) == record["sha256"], "Changed review file: " + name)
    receipt = read_json(data / "evidence/verification.json")
    require(receipt["status"] == PASS and receipt["all_262_recomputed"] is True
            and receipt["target_inequalities"] == 262
            and receipt["production_stages"] == receipt["audit_stages"] == 14
            and receipt["lean_numerical_premises_discharged"] == 0
            and receipt["type_iii_proved"] is False, "Unexpected acceptance scope")
    require(len(receipt["target_files"]) == 5, "Incomplete Lean target inventory")
    for name, expected in receipt["target_files"].items():
        safe_relative(name)
        require(digest_file(root / "formal" / name) == expected,
                "Lean numerical target differs from the verified release: " + name)
    for name, expected in receipt["package_tools"].items():
        safe_relative(name)
        require(digest_file(data / "verifier" / name) == expected,
                "Verifier differs from acceptance receipt: " + name)
    negative = read_json(data / "evidence/negative-controls.json")
    require(negative["status"] == "PASS" and len(negative["cases"]) == 4
            and {case["case"] for case in negative["cases"]} == NEGATIVE_CASES
            and all(case["rejected"] is True for case in negative["cases"]),
            "Expected negative controls did not all reject their invalid inputs")
    return asset, manifest


def check_archive(path, asset, manifest):
    expected = asset["archive"]
    require(path.stat().st_size == expected["bytes"], "Archive size differs")
    require(digest_file(path) == expected["sha256"], "Archive SHA256 differs")
    prefix = str(safe_relative(expected["root"])) + "/"
    inventory = {prefix + name: record for name, record in manifest["files"].items()}
    inventory[prefix + "package-manifest.json"] = {
        "sha256": expected["manifest_sha256"]}
    with zipfile.ZipFile(path) as archive:
        names = archive.namelist()
        require(len(names) == len(set(names)) and set(names) == set(inventory),
                "Archive contains missing, extra, or duplicate entries")
        for name, record in inventory.items():
            safe_relative(name)
            info = archive.getinfo(name)
            require((info.external_attr >> 16) & 0o170000 == 0o100000,
                    "Archive entry is not a regular file: " + name)
            if "bytes" in record:
                require(info.file_size == record["bytes"], "Entry size differs: " + name)
            with archive.open(info) as stream:
                require(digest_stream(stream) == record["sha256"],
                        "Entry SHA256 differs: " + name)
    return len(inventory)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, help="Downloaded release ZIP; never extracted")
    args = parser.parse_args()
    asset, manifest = check_repository()
    entries = check_archive(args.archive, asset, manifest) if args.archive else 0
    print(json.dumps({
        "status": "PASS_EXTERNAL_PACKAGE_INTEGRITY",
        "repository_copies": len(asset["repository_copies"]),
        "lean_target_files": 5, "archive_entries_checked": entries,
        "integrations_repeated": False, "lean_proof_run": False,
    }, indent=2))


if __name__ == "__main__":
    main()
