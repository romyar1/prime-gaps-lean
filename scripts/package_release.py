#!/usr/bin/env python3
"""Package a checked source snapshot without Git history or local build state."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import posixpath
import re
import stat
import zipfile

ROOT = Path(__file__).resolve().parents[1]
PASS = "PASS_CONDITIONAL_DEVELOPMENT_AND_TYPE_III_SUPPORT"
PATTERNS = (
    "README.md", "STATUS.md", "CITATION.md", "NOTICE.md", ".gitignore", ".gitattributes",
    "lean-toolchain", "lakefile.toml", "lake-manifest.json", "verify.sh",
    ".github/workflows/*.yml", "docs/*.md", "formal/*.lean", "formal/LICENSE",
    "diagnostics/*.lean", "scripts/*.py", "scripts/ci_verify.sh",
    "scripts/ci_prepare_memory.sh", "provenance/*.json",
    "provenance/check_data.py", "provenance/release_checks/**/*",
    "vendor/primegaps186/*", "inputs/source_certificates/**/*.json",
    "research/numerical_182/**/*",
    "research/type_iii/geometry/*.md", "research/type_iii/published_inputs/*.md",
    "research/type_iii/contractions/*.md", "research/type_iii/contractions/*.py",
    "research/type_iii/contractions/*.json", "research/type_iii/numerics/*.md",
    "research/type_iii/numerics/*.py", "research/type_iii/numerics/*.json",
)
UPSTREAM_README_TARGETS = {
    "prime_gap_186_certificate.py", "comparator/main.json", "Challenge.lean",
    "comparator/README.md", "formalization.yaml",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    receipt_path = args.receipt.resolve()
    receipt = json.loads(receipt_path.read_text())
    require(receipt["status"] == PASS, "A completed full verification receipt is required.")
    require(not args.output.exists(), "Output already exists; use a new snapshot filename.")

    expected = {}
    for field in ("manifest_files", "preserved_files", "driver_files"):
        expected.update(receipt[field])
    expected.update(receipt["data_integrity"]["input_fingerprints"])
    expected.update({r["path"]: r["sha256"] for r in receipt["source_manifest"].values()})
    for relative, digest in expected.items():
        path = ROOT / relative
        require(path.is_file() and sha(path.read_bytes()) == digest,
                f"Source snapshot differs from the successful audit: {relative}")
    actual_modules = {p.stem for p in (ROOT / "formal").glob("*.lean")}
    require(actual_modules == set(receipt["source_manifest"]),
            "Formal module inventory differs from the successful audit.")

    files = {}
    modes = {}
    for pattern in PATTERNS:
        for path in sorted(ROOT.glob(pattern)):
            if not path.is_file():
                continue
            require(not path.is_symlink(), f"Symlink is not a release source: {path.name}")
            relative = path.relative_to(ROOT).as_posix()
            require("__pycache__" not in path.parts, "Cache selected for release.")
            files[relative] = path.read_bytes()
            modes[relative] = 0o755 if path.stat().st_mode & stat.S_IXUSR else 0o644
    require(set(expected) <= set(files), "A verified source or data file is missing from the archive.")
    require(all(len(data) < 25 * 1024 * 1024 for data in files.values()),
            "A selected file exceeds the documented browser upload limit.")
    require(all(re.search(rb"/Users/[A-Za-z0-9_.-]+/", data) is None for data in files.values()),
            "A selected file retains an absolute host path.")

    local_links = 0
    upstream_links = []
    upstream = json.loads(files["vendor/primegaps186/upstream.json"])
    for relative, data in files.items():
        if not relative.endswith(".md"):
            continue
        for target in re.findall(r"\]\(([^\s)]+)\)", data.decode("utf-8")):
            if target.startswith(("http:", "https:", "mailto:", "#")):
                continue
            target = target.split("#", 1)[0].strip("<>")
            if relative == "vendor/primegaps186/README.md" and target in UPSTREAM_README_TARGETS:
                # The unchanged upstream README describes files outside the
                # vendored subset. UPSTREAM.md explicitly records this scope.
                upstream_links.append(upstream["repository"] + "/blob/" + upstream["commit"] + "/" + target)
                continue
            resolved = posixpath.normpath(posixpath.join(posixpath.dirname(relative), target))
            require(resolved in files or any(p.startswith(resolved.rstrip("/") + "/") for p in files),
                    f"Missing archive link: {relative} -> {target}")
            local_links += 1

    manifest = {
        "schema_version": 1,
        "scope": "Source archive integrity; mathematical scope is the included conditional receipt.",
        "verification_status": receipt["status"],
        "verification_finished_utc": receipt["finished_utc"],
        "receipt_sha256": sha(receipt_path.read_bytes()),
        "formal_modules": len(actual_modules),
        "audited_declarations": receipt["distinct_audited_declarations"],
        "checked_local_markdown_links": local_links,
        "upstream_readme_links_resolved_by_UPSTREAM_note": upstream_links,
        "files": {p: {"bytes": len(data), "sha256": sha(data)} for p, data in sorted(files.items())},
    }
    files["provenance/upload_manifest.json"] = (json.dumps(manifest, indent=2) + "\n").encode()
    modes["provenance/upload_manifest.json"] = 0o644
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(args.output, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for relative, data in sorted(files.items()):
            info = zipfile.ZipInfo("prime-gaps-lean/" + relative, date_time=(2026, 9, 5, 0, 0, 0))
            info.create_system = 3
            info.external_attr = (stat.S_IFREG | modes[relative]) << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, data, compresslevel=9)
    with zipfile.ZipFile(args.output) as archive:
        require(archive.testzip() is None, "ZIP checksum failure.")
        require(len(archive.infolist()) == len(files), "Archive inventory mismatch.")
        for relative, data in files.items():
            require(sha(archive.read("prime-gaps-lean/" + relative)) == sha(data),
                    f"Archive byte mismatch: {relative}")
    result = {
        "status": "PASS_UPLOAD_ARCHIVE_INTEGRITY",
        "archive": args.output.name,
        "sha256": sha(args.output.read_bytes()),
        "archive_bytes": args.output.stat().st_size,
        "uncompressed_bytes": sum(map(len, files.values())),
        "files": len(files),
        "formal_modules": len(actual_modules),
        "audited_declarations": receipt["distinct_audited_declarations"],
        "checked_local_markdown_links": local_links,
        "mathematical_verification_status": receipt["status"],
        "type_iii_proved": False,
        "numerical_premises_fully_discharged": False,
        "unconditional_182": False,
    }
    check_path = args.output.with_suffix(".check.json")
    check_path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
