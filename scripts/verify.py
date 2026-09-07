#!/usr/bin/env python3
"""Check the portable Lake development and print its actual theorem premises.

The default build uses Lake's rehashed dependency traces. --fresh also removes
this package's build products, leaving dependency caches intact. Neither mode
claims to prove the still explicit numerical, finite-field, or Type III inputs.
Python 3.11+, Git, and the project-pinned Lean/Lake toolchain are required.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time
import tomllib

from lean_text import (
    APPROVED_BASELINE_WRAPPER_AXIOMS, LEAN_NAME, MODULE_NAME, SourceCheckError,
    axiom_requests, imports, parse_axiom_reports, source_scan,
    strip_lean_comments_and_strings,
)

if not __debug__:
    raise RuntimeError("verification must run without Python -O")

ROOT = Path(__file__).resolve().parents[1]
SOURCE_MANIFEST = ROOT / "provenance/source_manifest.json"
REGISTRY = ROOT / "provenance/audit_declarations.json"
PACKAGE = "primeGapsLean"
DEVELOPMENT = "PrimeGapsDevelopment"
BASELINE_SOURCE = "vendor/primegaps186/PrimeGaps186.lean"
BASELINE_SHA256 = "fd7d9296871d276f7cd950ebf88d38627ff326abdf214a1facabc52fb6794d27"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
BASELINE_AXIOMS = (
    "PrimeGap186.kloosterman3_bound",
    "PrimeGap186.kloosterman2_correlation_bound",
    "PrimeGap186.physical_integral_bounds",
)
TERMINALS = (
    "PrimeGap182Audit.incidenceSecondaryFamily182_of_rank_four",
    "PrimeGap182Audit.trialOrderThreeBilinear182_of_rank_four",
    "PrimeGap182.trialShiftedSourceEstimates182_of_local_inputs",
    "PrimeGap182.primeGapLiminf_le_182_of_local_inputs",
    "PrimeGap182.infinite_integer_translates182_of_local_inputs",
    "PrimeGap182.infinite_consecutive_prime_pairs182_of_local_inputs",
)
PREMISES = (
    "PrimeGap182.PhysicalCapBounds182",
    "PrimeGap182.PhysicalSourceBounds182",
    "PrimeGap182Analytic.PublicPrimeLocalBounds182",
    "PrimeGap182Audit.IncidenceRankFourBound",
    "PrimeGap182Audit.AllIncidenceRankFourBounds",
    "PrimeGap182.TypeIII.BaselineLocalInputs",
    "PrimeGap182.TypeIII.FiniteExceptionalFourierBound",
    "PrimeGap182.TypeIII.CurveExceptionalFourierBound",
    "PrimeGap182.TypeIII.LocalFourierHypothesis",
    "PrimeGap182.TypeIII.HasFiniteExceptionalTypeIIIInput",
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SourceCheckError(message)


def utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def relative(path: Path) -> str:
    return path.resolve().relative_to(ROOT).as_posix()


def local_path(value: str) -> Path:
    path = Path(value)
    require(not path.is_absolute() and ".." not in path.parts, f"unsafe repository path: {value}")
    path = ROOT / path
    require(path.resolve().is_relative_to(ROOT), f"path escapes repository: {value}")
    return path


def atomic_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + f".tmp.{os.getpid()}")
    temporary.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    temporary.replace(path)


def clean_environment() -> dict[str, str]:
    env = dict(os.environ)
    for name in ("LEAN_PATH", "LEAN_SRC_PATH", "PYTHONOPTIMIZE"):
        env.pop(name, None)
    env.update(PYTHONDONTWRITEBYTECODE="1", GIT_OPTIONAL_LOCKS="0")
    # Lake invokes `git` itself even while loading an environment. Keep its
    # executable consistent with the one used by our preceding read-only checks.
    selected_git = env.get("PRIME_GAPS_GIT")
    if selected_git and (Path(selected_git).is_absolute() or "/" in selected_git):
        git_path = Path(selected_git).resolve()
        require(git_path.name == "git" and git_path.is_file(), "PRIME_GAPS_GIT must identify an executable named git")
        env["PATH"] = str(git_path.parent) + os.pathsep + env.get("PATH", "")
    return env


def capture(command: list[str], env: dict[str, str], timeout: float = 120) -> str:
    result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
    require(result.returncode == 0,
            f"command failed ({result.returncode}): {command[0]} {' '.join(command[1:3])}\n"
            + result.stderr.strip())
    return result.stdout


def run(command: list[str], env: dict[str, str], log: Path, timeout: float) -> dict:
    started = time.monotonic()
    with log.open("w", encoding="utf-8") as stream:
        process = subprocess.Popen(command, cwd=ROOT, env=env, stdout=stream,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        heartbeat = started + 30
        try:
            while process.poll() is None:
                now = time.monotonic()
                if timeout and now - started > timeout:
                    raise TimeoutError(f"timeout after {timeout:g}s; see {relative(log)}")
                if now >= heartbeat:
                    print(f"  checking ({now - started:.0f}s): {relative(log)}", flush=True)
                    heartbeat = now + 30
                time.sleep(0.2)
        except BaseException:
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            raise
    # Machine-specific commands are kept in the local log, not the portable receipt.
    record = {"exit_code": process.returncode, "elapsed_seconds": round(time.monotonic() - started, 3),
              "log": relative(log), "log_sha256": digest(log)}
    require(process.returncode == 0, f"Lean/Lake failed; see {relative(log)}")
    require(not re.search(r"(?m)^.*:\d+:\d+: (?:error|warning):", log.read_text()),
            f"unexpected Lean diagnostic; see {relative(log)}")
    return record


def read_sources(manifest: dict, registry: dict, *, permit_changes: bool = False) -> tuple[dict, list[str]]:
    require(manifest.get("schema_version") == registry.get("schema_version") == 1, "unsupported manifest schema")
    require(manifest.get("type_iii_proposition_proved") is False and registry.get("target_proved") is False,
            "proof-status policy changed: the Type III proposition has not been discharged by this verifier")
    records = manifest["files"]
    require(records and len(records) == manifest["formal_module_count"], "empty or inconsistent source manifest")
    recorded = {record["module"]: record for record in records}
    require(len(recorded) == len(records), "duplicate source module record")
    actual = {path.stem: path for path in sorted((ROOT / "formal").glob("*.lean"))}
    require(set((ROOT / "formal").rglob("*.lean")) == set(actual.values()), "only flat formal modules are supported")
    if not permit_changes:
        require(set(actual) == set(recorded) == set(registry["modules"]), "source/manifest/audit module inventory mismatch")
    require(actual and "PrimeGaps182Analytic" in actual and "TypeIIILocalProgress" in actual,
            "required analytic and Type III entries are missing")
    for artifact in (ROOT / "formal").rglob("*.olean*"):
        raise SourceCheckError(f"compiled source-tree object can shadow Lake output: {relative(artifact)}")
    data = {}
    for name, path in actual.items():
        require(MODULE_NAME.fullmatch(name) is not None, f"invalid module name: {name}")
        require(path.resolve().is_relative_to(ROOT / "formal"), f"source escapes formal/: {name}")
        raw = path.read_bytes()
        code = strip_lean_comments_and_strings(raw.decode("utf-8"))
        source_scan(code)
        requests = axiom_requests(code)
        h = hashlib.sha256(raw).hexdigest()
        if not permit_changes:
            record, audit = recorded[name], registry["modules"][name]
            require(record["path"] == relative(path), f"manifest path does not identify module: {name}")
            require(record["sha256"] == audit["source_sha256"] == h and record["bytes"] == len(raw),
                    f"source fingerprint changed: {name}; review it and use --refresh-manifests")
            require(requests == [r["requested"] for r in audit["requests"]], f"axiom request coverage changed: {name}")
            for item in audit["requests"]:
                require(LEAN_NAME.fullmatch(item["declaration"]) is not None, f"invalid canonical name in {name}")
                requested = item["requested"].removeprefix("_root_.")
                require(item["declaration"] == requested or item["declaration"].endswith("." + requested),
                        f"canonical name does not resolve its source request: {name}")
        data[name] = {"path": relative(path), "sha256": h, "bytes": len(raw),
                      "imports": imports(code), "axiom_requests": requests}
    active, seen, order = set(), set(), []

    def visit(name: str) -> None:
        require(name not in active, f"cyclic project import: {name}")
        if name in seen:
            return
        active.add(name)
        for dep in data[name]["imports"]:
            require(dep not in {"BaselineAxioms", "BaselineLowerOrderAxioms"}, "diagnostic imported by proof development")
            if dep in data:
                visit(dep)
        active.remove(name)
        seen.add(name)
        order.append(name)

    for name in data:
        visit(name)
    return data, order


def check_preserved_files(manifest: dict) -> dict[str, str]:
    result = {}
    for record in manifest["vendored_files"] + manifest["diagnostic_files"]:
        path = local_path(record["path"])
        require(path.is_file() and digest(path) == record["sha256"] and path.stat().st_size == record["bytes"],
                f"preserved source changed: {record['path']}")
        result[record["path"]] = record["sha256"]
    require(digest(ROOT / BASELINE_SOURCE) == BASELINE_SHA256, "public baseline source fingerprint changed")
    # This immutable 10 MB source has already matched the fixed upstream hash.
    # Avoid rescanning it with the conservative development-source lexer.
    baseline_code = (ROOT / BASELINE_SOURCE).read_text()
    declared = re.findall(r"(?m)^axiom\s+(\S+)\s*:", baseline_code)
    require(declared == list(BASELINE_AXIOMS), "public baseline mathematical axiom declarations changed")
    return result


def check_configuration(registry: dict, sources: dict, *, permit_changes: bool = False) -> dict:
    for path, expected in registry["configuration_sha256"].items():
        if not permit_changes or path != "lakefile.toml":
            require(digest(local_path(path)) == expected, f"pinned configuration changed: {path}")
    require((ROOT / "lean-toolchain").read_text().strip() == registry["toolchain"], "toolchain file changed")
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    fixed_fields = json.loads(json.dumps(config))
    for library in fixed_fields.get("lean_lib", []):
        if library.get("name") == DEVELOPMENT:
            library.pop("roots", None)
            library.pop("globs", None)
    require(fixed_fields == registry["lake_configuration_fixed_fields"],
            "Lake configuration changed beyond the development module inventory; review the pinned verification policy separately")
    require(config["name"] == PACKAGE and config.get("fixedToolchain") is True, "unexpected Lake package configuration")
    require(config.get("leanOptions", {}).get("autoImplicit") is False and
            config["leanOptions"].get("warningAsError") is True, "strict Lean options are required")
    libraries = {lib["name"]: lib for lib in config["lean_lib"]}
    development = libraries[DEVELOPMENT]
    require(development["srcDir"] == "formal", "incorrect formal source directory")
    require(set(development["roots"]) == set(sources) and len(development["roots"]) == len(sources),
            "Lake library does not enumerate every formal source exactly once")
    require(set(development.get("globs", development["roots"])) == set(sources), "Lake globs omit or add formal modules")
    baseline = libraries["PrimeGaps186"]
    require(baseline["srcDir"] == "vendor/primegaps186" and baseline["roots"] == ["PrimeGaps186"],
            "public baseline library is shadowed or relocated")
    lock = json.loads((ROOT / "lake-manifest.json").read_text())
    require(lock["name"] == PACKAGE and lock["packagesDir"] == ".lake/packages", "unexpected Lake manifest layout")
    packages = lock["packages"]
    actual = {p["name"]: p["rev"] for p in packages}
    require(len(actual) == len(packages) and actual == registry["package_revisions"], "dependency lockfile pins changed")
    require(all(p["type"] == "git" and p.get("subDir") is None for p in packages), "unexpected dependency kind")
    require(all(re.fullmatch(r"[0-9a-f]{40}", p["rev"]) for p in packages), "dependency is not pinned to a full commit")
    require(actual.get("mathlib") == "bbcd1968ee6950abe88b85dba6995da346c4b2a8", "Mathlib pin changed")
    return lock


def check_dependency_checkouts(lock: dict, env: dict[str, str]) -> list[dict]:
    """Read-only checks, deliberately usable before and after any Lake call."""
    git = os.environ.get("PRIME_GAPS_GIT", "git")
    capture([git, "--version"], env)
    packages = []
    for package in lock["packages"]:
        name = package["name"]
        require(MODULE_NAME.fullmatch(name) is not None, "invalid dependency name")
        directory = local_path(f".lake/packages/{name}")
        require(directory.is_dir(), f"dependency checkout missing: {name}; first run lake exe cache get")
        head = capture([git, "-C", str(directory), "rev-parse", "HEAD"], env).strip()
        require(head == package["rev"], f"dependency checkout revision mismatch: {name}")
        origin = capture([git, "-C", str(directory), "config", "--get", "remote.origin.url"], env).strip()
        require(origin == package["url"], f"dependency origin differs from lockfile: {name}; repair it before running Lake")
        dirty = capture([git, "-C", str(directory), "-c", "core.fsmonitor=false", "status",
                         "--porcelain=v1", "--untracked-files=no", "--ignore-submodules=none"], env)
        require(not dirty.strip(), f"tracked dependency sources are modified: {name}")
        packages.append({"name": name, "revision": head, "origin": origin, "tracked_sources_clean": True})
    return packages


def check_environment(registry: dict, lock: dict, env: dict[str, str], lake: str) -> tuple[dict, list[Path]]:
    # Lake may fetch/replace a checkout when Git fails or its origin differs.
    # Check these conditions before asking Lake to load the project at all.
    packages = check_dependency_checkouts(lock, env)
    version = capture([lake, "env", "lean", "--version"], env).strip()
    require("version 4.34.0-rc2," in version and f"commit {registry['lean_commit']}," in version,
            f"unexpected Lean compiler: {version}")
    raw_env = capture([lake, "env"], env)
    lake_env = dict(line.split("=", 1) for line in raw_env.splitlines() if "=" in line)
    roots = [Path(value).resolve() for value in lake_env.get("LEAN_PATH", "").split(os.pathsep) if value]
    sysroot = Path(lake_env["LEAN_SYSROOT"]).resolve()
    allowed = [ROOT / ".lake/build/lib/lean"] + [ROOT / ".lake/packages" / p["name"] / ".lake/build/lib/lean"
                                                         for p in lock["packages"]]
    allowed = [p.resolve() for p in allowed]
    require(ROOT / ".lake/build/lib/lean" in roots, "Lake environment omits local compiled library")
    require(all(p in allowed or p.is_relative_to(sysroot) for p in roots), "unexpected external Lean search path")
    roots.append(sysroot / "lib/lean")
    require(check_dependency_checkouts(lock, env) == packages, "dependency checkout changed while Lake loaded the environment")
    return {"lean_version": version, "packages": packages,
            "inherited_lean_paths_cleared": True, "lean_search_path_checked": True}, list(dict.fromkeys(roots))


def data_fingerprints() -> dict[str, str]:
    """Snapshot every published numerical input, not just its manifest."""
    manifest = json.loads((ROOT / "provenance/data_manifest.json").read_text())
    require(manifest.get("numerical_premises_discharged") is False and manifest.get("type_iii_proved") is False,
            "numerical data metadata incorrectly claims a mathematical proof")
    records = manifest["files"]
    require(records and len(records) == manifest["file_count"], "empty or inconsistent numerical data inventory")
    result = {path: digest(ROOT / path) for path in ("provenance/check_data.py", "provenance/data_manifest.json")}
    expected_paths = set()
    for record in records:
        path = local_path(record["published_path"])
        require(path.is_relative_to(ROOT / "inputs/source_certificates"), "numerical input is outside its declared collection")
        require(record["published_path"] not in expected_paths, "duplicate numerical input record")
        expected_paths.add(record["published_path"])
        require(path.is_file() and path.stat().st_size == record["published_bytes"] and
                digest(path) == record["published_sha256"], f"numerical input fingerprint mismatch: {record['published_path']}")
        result[record["published_path"]] = record["published_sha256"]
    actual_paths = {relative(path) for path in (ROOT / "inputs/source_certificates").rglob("*.json")}
    require(actual_paths == expected_paths, "numerical data inventory differs from manifest")
    return result


def check_imports(sources: dict, roots: list[Path], env: dict[str, str], *, compiled: bool) -> dict:
    expected_modules = set(sources) | {"PrimeGaps186"}
    local_lib = ROOT / ".lake/build/lib/lean"
    permitted_artifacts = expected_modules | {"BaselineAxioms", "BaselineLowerOrderAxioms"}
    for artifact in local_lib.rglob("*.olean"):
        name = ".".join(artifact.relative_to(local_lib).with_suffix("").parts)
        require(name in permitted_artifacts, f"orphan compiled project module: {name}")
    external = {}
    for name in expected_modules:
        suffix = Path(*name.split(".")).with_suffix(".olean")
        require(not any((root / suffix).exists() for root in roots if root != local_lib),
                f"project module is shadowed by dependency object: {name}")
    for name, record in sources.items():
        for dep in record["imports"]:
            if dep in expected_modules:
                continue
            if dep in external:
                continue
            suffix = Path(*dep.split(".")).with_suffix(".olean")
            candidates = [root / suffix for root in roots if (root / suffix).is_file()]
            if not candidates and not compiled:
                continue
            require(len(candidates) == 1, f"external import is missing or shadowed: {dep} in {name}")
            require(not candidates[0].is_relative_to(local_lib), f"orphan compiled import: {dep}")
            path = candidates[0]
            record_path = relative(path) if path.is_relative_to(ROOT) else "<lean-toolchain>/lib/lean/" + suffix.as_posix()
            external[dep] = {"artifact": record_path, "sha256": digest(path), "bytes": path.stat().st_size}
            if path.is_relative_to(ROOT / ".lake/packages"):
                package_name = path.relative_to(ROOT / ".lake/packages").parts[0]
                package_root = ROOT / ".lake/packages" / package_name
                source = package_root / suffix.with_suffix(".lean")
                require(source.is_file(), f"external compiled import has no matching source: {dep}")
                git = os.environ.get("PRIME_GAPS_GIT", "git")
                tracked = capture([git, "-C", str(package_root), "ls-files", "--error-unmatch", "--",
                                   source.relative_to(package_root).as_posix()], env)
                require(tracked.strip() == source.relative_to(package_root).as_posix(),
                        f"external import source is not tracked by its pinned package: {dep}")
                external[dep].update(source=relative(source), source_sha256=digest(source), tracked_source=True)
    return external


def module_trace_reports(name: str, requests: list[str]) -> list[dict]:
    path = ROOT / ".lake/build/lib/lean" / f"{name}.trace"
    trace = json.loads(path.read_text())
    require(trace.get("synthetic") is False, f"synthetic build trace for project module: {name}")
    messages = []
    for entry in trace.get("log", []):
        require(entry["level"] not in {"warning", "error"}, f"diagnostic in Lake trace: {name}")
        if entry["level"] == "info":
            messages.append(re.sub(r"^[^\n]*:\d+:\d+: ", "", entry["message"], count=1))
    return parse_axiom_reports("\n".join(messages), requests,
                               allow_namespace_abbreviations=True, allow_approved_baseline_wrappers=True)


def canonical_names(registry: dict) -> list[str]:
    names = sorted({r["declaration"] for module in registry["modules"].values() for r in module["requests"]})
    require(names and set(TERMINALS) <= set(names), "terminal declarations missing from canonical audit")
    require(set(APPROVED_BASELINE_WRAPPER_AXIOMS) <= set(names), "documented baseline wrapper missing from audit")
    return names


def check_type_output(output: str, names: list[str]) -> None:
    # `#check @name` can retain its leading @, and the pretty printer wraps
    # long lists of universe parameters across lines. Accept only parameter
    # names in that suffix, while matching the canonical declaration exactly.
    parameter = r"(?:[^\W\d]|_)[\w']*"
    universes = rf"(?:\.\{{\s*{parameter}(?:\s*,\s*{parameter})*\s*\}})?"
    for name in names:
        pattern = rf"(?m)^@?{re.escape(name)}{universes}\s*:"
        require(len(re.findall(pattern, output)) == 1, f"missing or duplicate full theorem type: {name}")


def refresh_manifests(manifest: dict, registry: dict, sources: dict, observed: dict) -> None:
    """Update reviewed working sources; never relabel historical bytes as verified."""
    old = {r["module"]: r for r in manifest["files"]}
    changed = []
    records = []
    for name, source in sources.items():
        record = dict(old.get(name, {}))
        if record.get("sha256") != source["sha256"]:
            changed.append(name)
            if record:
                record.setdefault("origin_sha256", record["sha256"])
                record.setdefault("origin_bytes", record["bytes"])
                record.setdefault("origin_audit_status", record.get("prior_audit_status"))
            record.update(module=name, path=source["path"], sha256=source["sha256"], bytes=source["bytes"],
                          prior_audit_status="CHANGED_AFTER_INITIAL_IMPORT_REQUIRES_CURRENT_VERIFICATION")
            record.pop("individual_check", None)
            record.setdefault("source_project", "prime-gaps-lean")
            record.setdefault("source_path", source["path"])
        records.append(record)
    removed = sorted(set(old) - set(sources))
    if removed:
        manifest.setdefault("retired_source_records", []).extend(old[name] for name in removed)
    manifest.update(files=records, formal_module_count=len(records), type_iii_proposition_proved=False)
    manifest["working_manifest_updated_utc"] = utc()
    manifest["scope"] = "Current working sources. Original provenance fingerprints are retained when sources change; verification is recorded separately."
    registry["modules"] = {name: {"source_sha256": sources[name]["sha256"], "requests": [
        {"requested": r["requested"], "declaration": r["declaration"]} for r in observed[name]]} for name in sources}
    registry["configuration_sha256"]["lakefile.toml"] = digest(ROOT / "lakefile.toml")
    registry["updated_utc"] = utc()
    canonical_names(registry)
    atomic_json(SOURCE_MANIFEST, manifest)
    atomic_json(REGISTRY, registry)
    print(f"Refreshed {len(changed)} changed/new module records; {len(removed)} retired. A new audit is required.", flush=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fresh", action="store_true", help="clean only this package before building")
    parser.add_argument("--preflight", action="store_true", help="check sources/pins only; do not build or certify proofs")
    parser.add_argument("--refresh-manifests", action="store_true",
                        help="after reviewing source changes, build and regenerate source/canonical-name manifests; never change proof-status claims")
    parser.add_argument("--timeout", type=float, default=7200, help="seconds per build/probe; zero disables timeout")
    args = parser.parse_args()
    require(args.timeout >= 0 and math.isfinite(args.timeout), "timeout must be finite and nonnegative")
    require(not (args.preflight and (args.fresh or args.refresh_manifests)), "preflight cannot clean or refresh")
    env = clean_environment()
    lake = os.environ.get("PRIME_GAPS_LAKE", "lake")
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + f"_{os.getpid()}"
    run_dir = ROOT / "verification/runs" / stamp
    run_dir.mkdir(parents=True, exist_ok=False)
    started = time.monotonic()
    receipt = {"schema_version": 1, "status": "RUNNING", "started_utc": utc(),
               "run_directory": relative(run_dir), "fresh_project_rebuild_requested": args.fresh,
               "type_iii_proposition_proved": False, "numerical_premises_discharged": False,
               "unconditional_182_formalization": False,
               "scope": "Current Lean declarations with their explicit hypotheses; pinned dependency artifacts may be reused.",
               "axiom_policy": {"standard": sorted(STANDARD_AXIOMS), "approved_nonterminal_wrappers": {
                   name: sorted(axioms) for name, axioms in APPROVED_BASELINE_WRAPPER_AXIOMS.items()},
                   "public_baseline_axiom_declarations": list(BASELINE_AXIOMS),
                   "terminal_declarations_standard_only": True,
                   "axiom_checks_do_not_discharge_explicit_premises": True}}

    def save() -> None:
        receipt["elapsed_seconds"] = round(time.monotonic() - started, 3)
        atomic_json(run_dir / "receipt.json", receipt)
        atomic_json(ROOT / "verification/latest.json", receipt)

    lock_fd = None
    lock_path = ROOT / "verification/verifier.lock"
    try:
        try:
            lock_fd = os.open(lock_path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
        except FileExistsError as exc:
            raise SourceCheckError("another verifier holds verification/verifier.lock; inspect it before removing a stale lock") from exc
        os.write(lock_fd, (str(os.getpid()) + "\n").encode())
        manifest, registry = json.loads(SOURCE_MANIFEST.read_text()), json.loads(REGISTRY.read_text())
        driver_paths = ["scripts/verify.py", "scripts/lean_text.py", "verify.sh", "lakefile.toml", "lake-manifest.json", "lean-toolchain"]
        drivers = {path: digest(ROOT / path) for path in driver_paths}
        receipt["manifest_files"] = {relative(path): digest(path) for path in (SOURCE_MANIFEST, REGISTRY)}
        sources, order = read_sources(manifest, registry, permit_changes=args.refresh_manifests)
        preserved = check_preserved_files(manifest)
        pins = check_configuration(registry, sources, permit_changes=args.refresh_manifests)
        data_inputs = data_fingerprints()
        receipt["data_integrity"] = run([sys.executable, "-B", "provenance/check_data.py"], env,
                                         run_dir / "data_integrity.log", args.timeout)
        data_result = json.loads((run_dir / "data_integrity.log").read_text())
        require(data_result["status"] == "PASS_DATA_INTEGRITY_ONLY" and
                data_result["numerical_premises_discharged"] is False and data_result["type_iii_proved"] is False,
                "numerical data checker did not report an integrity-only pass")
        receipt["data_integrity"].update(result=data_result, input_fingerprints=data_inputs)
        receipt["environment"], roots = check_environment(registry, pins, env, lake)
        for path, expected in {**drivers, **receipt["manifest_files"]}.items():
            require(digest(ROOT / path) == expected, f"verification input changed while loading environment: {path}")
        check_configuration(registry, sources, permit_changes=args.refresh_manifests)
        check_imports(sources, roots, env, compiled=False)
        receipt.update(source_manifest=sources, preserved_files=preserved, driver_files=drivers,
                       formal_module_count=len(sources), topological_order=order)
        print(f"Sources and pins checked: {len(sources)} formal modules. Type III remains an explicit premise.", flush=True)
        save()
        if args.preflight:
            receipt["status"] = "PASS_PREFLIGHT_NO_PROOF_BUILD"
        else:
            if args.fresh:
                receipt["clean"] = run([lake, "clean", PACKAGE], env, run_dir / "clean.log", args.timeout)
            receipt["build"] = run([lake, "--no-cache", "--rehash", "build", DEVELOPMENT], env,
                                    run_dir / "build.log", args.timeout)
            observed = {name: module_trace_reports(name, sources[name]["axiom_requests"]) for name in order}
            if args.refresh_manifests:
                for path, expected in {**drivers, **receipt["manifest_files"]}.items():
                    require(digest(ROOT / path) == expected, f"verification input changed before intentional refresh: {path}")
                refresh_manifests(manifest, registry, sources, observed)
                receipt["manifest_files"] = {relative(path): digest(path) for path in (SOURCE_MANIFEST, REGISTRY)}
            for name in order:
                expected = registry["modules"][name]["requests"]
                actual = [{"requested": r["requested"], "declaration": r["declaration"]} for r in observed[name]]
                require(actual == expected, f"current build trace resolves different declaration names: {name}")
            names = canonical_names(registry)
            receipt["external_imports"] = check_imports(sources, roots, env, compiled=True)
            artifacts = {}
            for name in ["PrimeGaps186", *order]:
                base = ROOT / ".lake/build/lib/lean" / name
                paths = [base.with_suffix(".olean"), base.with_suffix(".trace")]
                paths.extend(p for p in (base.with_suffix(".olean.private"), base.with_suffix(".olean.server")) if p.is_file())
                require(all(p.is_file() for p in paths), f"compiled proof/trace missing: {name}")
                artifacts[name] = {relative(path): digest(path) for path in paths}
            receipt["compiled_artifacts"] = artifacts
            probe = run_dir / "TheoremTypes.lean"
            probe.write_text("\n".join(f"import {name}" for name in sorted(sources)) +
                             "\n\nset_option pp.fullNames true\nset_option pp.universes true\n\n" +
                             "\n".join(f"#check @{name}\n#print axioms {name}" for name in names) + "\n")
            probe_hash = digest(probe)
            log = run_dir / "theorem_types.log"
            receipt["canonical_audit"] = run([lake, "env", "lean", "-j2", "-DautoImplicit=false", "-DwarningAsError=true",
                                               str(probe.relative_to(ROOT))], env, log, args.timeout)
            output = log.read_text()
            require(digest(probe) == probe_hash, "canonical probe changed during checking")
            reports = parse_axiom_reports(output, names, allow_approved_baseline_wrappers=True)
            require(all(r["declaration"] == n for r, n in zip(reports, names, strict=True)), "noncanonical declaration name")
            check_type_output(output, names)
            terminals = [r for r in reports if r["declaration"] in TERMINALS]
            require(len(terminals) == len(TERMINALS) and all(set(r["axioms"]) <= STANDARD_AXIOMS for r in terminals),
                    "terminal theorem used a mathematical axiom")
            receipt["canonical_audit"].update(probe=relative(probe), probe_sha256=probe_hash,
                                              declarations=names, reports=reports,
                                              distinct_declarations=len(names), terminal_reports=terminals)
            premise_probe = run_dir / "ExplicitPremises.lean"
            premise_probe.write_text("import PrimeGaps182Analytic\nimport TypeIIILocalProgress\n\n"
                                     "set_option pp.fullNames true\nset_option pp.universes true\n\n" +
                                     "\n".join(f"#print {name}\n#print axioms {name}" for name in PREMISES) +
                                     "\n\n" + "\n".join(f"#print {name}" for name in BASELINE_AXIOMS) + "\n")
            premise_hash = digest(premise_probe)
            premise_log = run_dir / "explicit_premises.log"
            receipt["explicit_premises"] = run([lake, "env", "lean", "-j2", "-DautoImplicit=false", "-DwarningAsError=true",
                                                 str(premise_probe.relative_to(ROOT))], env, premise_log, args.timeout)
            premise_output = premise_log.read_text()
            require(digest(premise_probe) == premise_hash, "explicit-premise probe changed during checking")
            receipt["explicit_premises"].update(probe=relative(premise_probe), probe_sha256=premise_hash,
                                               declarations=list(PREMISES),
                                               reports=parse_axiom_reports(premise_output, list(PREMISES)))
            require("LocalFourierHypothesis" in premise_output and "PhysicalSourceBounds182" in premise_output,
                    "explicit mathematical premise output is missing")
            for group in artifacts.values():
                for path, expected in group.items():
                    require(digest(ROOT / path) == expected, f"compiled proof changed during audit: {path}")
            receipt["status"] = "PASS_CONDITIONAL_DEVELOPMENT_AND_TYPE_III_SUPPORT"
            receipt["distinct_audited_declarations"] = len(names)
            require(check_imports(sources, roots, env, compiled=True) == receipt["external_imports"],
                    "external imported source or object changed during verification")
        require(check_dependency_checkouts(pins, env) == receipt["environment"]["packages"],
                "dependency checkout changed during verification")
        check_configuration(registry, sources)
        for name, record in sources.items():
            require(digest(ROOT / record["path"]) == record["sha256"], f"source changed during verification: {name}")
        require(check_preserved_files(manifest) == preserved, "preserved source changed during verification")
        for path, expected in {**drivers, **receipt["manifest_files"], **data_inputs}.items():
            require(digest(ROOT / path) == expected, f"verification input changed during run: {path}")
        receipt["finished_utc"] = utc()
        save()
        print(f"{receipt['status']}: {relative(run_dir / 'receipt.json')}", flush=True)
        return 0
    except (Exception, KeyboardInterrupt) as error:
        receipt.update(status="FAIL", error=f"{type(error).__name__}: {error}", finished_utc=utc())
        save()
        print(f"FAIL: {error}", file=sys.stderr, flush=True)
        return 1
    finally:
        if lock_fd is not None:
            os.close(lock_fd)
            lock_path.unlink(missing_ok=True)


if __name__ == "__main__":
    raise SystemExit(main())
