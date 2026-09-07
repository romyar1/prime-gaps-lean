"""Focused false-pass regressions for the verification boundary."""
from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import verify
from lean_text import (
    APPROVED_BASELINE_WRAPPER_AXIOMS, SourceCheckError, axiom_requests,
    imports, parse_axiom_reports, source_scan, strip_lean_comments_and_strings,
)


class LeanTextTests(unittest.TestCase):
    def test_nested_comments_literals_and_false_requests(self):
        text = 'import A /- axiom /- sorry -/ -/\n-- #print axioms forged\n' \
               'def text := "sorry"\n#print axioms actual\n'
        code = strip_lean_comments_and_strings(text)
        self.assertEqual(code.count("\n"), text.count("\n"))
        self.assertEqual(imports(code), ["A"])
        self.assertEqual(axiom_requests(code), ["actual"])
        source_scan(code)

    def test_forbidden_proof_shortcuts(self):
        for token in ("sorry", "sorryAx", "admit", "axiom", "native_decide", "unsafe"):
            with self.subTest(token=token), self.assertRaises(SourceCheckError):
                source_scan(f"theorem t : True := by {token}\n")
        source_scan("def sorry_count := 1\n")

    def test_incomplete_comments_strings_and_interpolation(self):
        for text in ('/- unfinished', 'def x := "unfinished', 's!"{by sorry}"',
                     's! /- intervening comment -/ "{3}"', 's! /- comment -/ r#"{3}"#'):
            with self.subTest(text=text), self.assertRaises(SourceCheckError):
                strip_lean_comments_and_strings(text)

    def test_diagnostic_forgery_is_rejected(self):
        for text in ('#eval "fake"', '#guard_msgs in\n#print axioms t',
                     'set_option debug.skipKernelTC true', 'macro "fake" : command => x',
                     'set_option pp.universes true in #eval IO.println "fake"',
                     'namespace N macro "fake" : command => x\nend N',
                     '@[command_elab Lean.Parser.Command.check] def auditDemo : CommandElab :=\n'
                     '  fun _ => logInfo "audit output changed"',
                     '@[app_delab Some.name] def displayed : Delab := custom',
                     'run_elab logInfo "audit output changed"',
                     'run_meta logInfo "audit output changed"',
                     '@[builtin_formatter parserName] def changed := handler',
                     '@[builtin_category_parenthesizer command] def changed := handler'):
            with self.subTest(text=text), self.assertRaises(SourceCheckError):
                source_scan(strip_lean_comments_and_strings(text))

    def test_late_import_is_rejected(self):
        for text in ("import A\nnamespace N\nimport B\n", "import\nLean\n#check True\n"):
            with self.subTest(text=text), self.assertRaises(SourceCheckError):
                imports(text)

    def test_incomplete_duplicate_or_extra_reports_fail(self):
        bad = (
            "'N.t' depends on axioms: [propext,",
            "'N.t' depends on axioms: [propext, propext]\n",
            "'N.t' depends on axioms: [newAxiom]\n",
            "'N.t' does not depend on any axioms\n'N.other' does not depend on any axioms\n",
        )
        for output in bad:
            with self.subTest(output=output), self.assertRaises(SourceCheckError):
                parse_axiom_reports(output, ["N.t"])

    def test_wrapper_permission_is_name_and_exact_set_specific(self):
        name, axioms = next(iter(APPROVED_BASELINE_WRAPPER_AXIOMS.items()))
        output = f"'{name}' depends on axioms: [{', '.join(sorted(axioms))}]\n"
        with self.assertRaises(SourceCheckError):
            parse_axiom_reports(output, [name])
        reports = parse_axiom_reports(output, [name], allow_approved_baseline_wrappers=True)
        self.assertEqual(reports[0]["classification"], "approved_baseline_wrapper")
        for changed in (axioms | {"sorryAx"}, axioms - {"PrimeGap186.kloosterman3_bound"}):
            forged = f"'{name}' depends on axioms: [{', '.join(sorted(changed))}]\n"
            with self.assertRaises(SourceCheckError):
                parse_axiom_reports(forged, [name], allow_approved_baseline_wrappers=True)
        renamed = "Other." + name
        with self.assertRaises(SourceCheckError):
            parse_axiom_reports(output.replace(name, renamed), [renamed], allow_approved_baseline_wrappers=True)

    def test_abbreviated_axioms_need_independent_canonical_audit(self):
        output = "'N.t' depends on axioms: [propext, choice, sound]\n"
        with self.assertRaises(SourceCheckError):
            parse_axiom_reports(output, ["N.t"])
        self.assertTrue(parse_axiom_reports(output, ["N.t"], allow_namespace_abbreviations=True)[0]
                        ["requires_canonical_name_audit"])

    def test_printed_universes_preserve_exact_axiom_identity(self):
        output = "'N.t' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]\n"
        report = parse_axiom_reports(output, ["N.t"])[0]
        self.assertEqual(report["axioms"], ["propext", "Classical.choice", "Quot.sound"])
        self.assertEqual(report["printed_axioms"], ["propext", "Classical.choice.{u}", "Quot.sound.{u}"])
        self.assertEqual(report["classification"], "standard_only")
        wrapper, expected = next(iter(APPROVED_BASELINE_WRAPPER_AXIOMS.items()))
        displayed = [name + ".{u}" if name in {"Classical.choice", "Quot.sound"} else name
                     for name in sorted(expected)]
        output = f"'{wrapper}' depends on axioms: [{', '.join(displayed)}]\n"
        with self.assertRaises(SourceCheckError):
            parse_axiom_reports(output, [wrapper])
        report = parse_axiom_reports(output, [wrapper], allow_approved_baseline_wrappers=True)[0]
        self.assertEqual(set(report["axioms"]), expected)
        self.assertEqual(report["classification"], "approved_baseline_wrapper")

    def test_universe_syntax_cannot_hide_axioms_or_duplicates(self):
        malformed = (
            "Classical.choice.{u", "Classical.choice.{u}trailing", "Classical.choice.{u},",
            "Classical.choice.{}", "Classical.choice.{u,}", "Classical.choice.{u, v}",
            "Classical.choice.{u newAxiom}", "Classical.choice.{u.{v}}", "propext.{u}",
            "Classical.choice.{u}, Classical.choice", "newAxiom.{u, v}",
            "Classical.choice.{u}, newAxiom.{v}", "Classical.choice.{u}, sorryAx",
        )
        for axioms in malformed:
            output = f"'N.t' depends on axioms: [{axioms}]\n"
            with self.subTest(axioms=axioms), self.assertRaises(SourceCheckError):
                parse_axiom_reports(output, ["N.t"])


class VerifierBoundaryTests(unittest.TestCase):
    def test_inherited_lean_search_paths_are_removed(self):
        with patch.dict(verify.os.environ, {"LEAN_PATH": "/stale", "LEAN_SRC_PATH": "/stale", "PYTHONOPTIMIZE": "1"}):
            env = verify.clean_environment()
        for name in ("LEAN_PATH", "LEAN_SRC_PATH", "PYTHONOPTIMIZE"):
            self.assertNotIn(name, env)

    def test_repository_paths_cannot_escape(self):
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(verify, "ROOT", Path(directory).resolve()):
                for path in ("../other.lean", "/tmp/other.lean"):
                    with self.subTest(path=path), self.assertRaises(SourceCheckError):
                        verify.local_path(path)
                self.assertEqual(verify.local_path("formal/A.lean"), Path(directory).resolve() / "formal/A.lean")

    def test_broken_git_fails_before_any_lake_operation(self):
        with patch.object(verify, "capture", side_effect=SourceCheckError("Git unavailable")) as run:
            with self.assertRaises(SourceCheckError):
                verify.check_environment({}, {"packages": []}, {}, "lake")
        self.assertEqual(len(run.call_args_list), 1)
        self.assertEqual(run.call_args.args[0][-1], "--version")
        self.assertNotIn("lake", run.call_args.args[0])

    def test_vacuous_canonical_manifest_is_rejected(self):
        with self.assertRaises(SourceCheckError):
            verify.canonical_names({"modules": {}})

    def test_missing_duplicate_or_wrong_theorem_type_fails(self):
        verify.check_type_output("N.t.{u_1, u_2} : True\n", ["N.t"])
        verify.check_type_output("@N.t.{u_1, u_2} : True\n", ["N.t"])
        for output in ("", "Other.N.t : True\n", "@Other.N.t : True\n",
                       "N.t : True\nN.t : False\n", "@N.t : True\nN.t : False\n",
                       "N.t.{u_1,\n    } : True\n", "N.t.{u_1\n    hidden} : True\n"):
            with self.subTest(output=output), self.assertRaises(SourceCheckError):
                verify.check_type_output(output, ["N.t"])

    def test_explicit_type_header_with_wrapped_universes(self):
        name = "PrimeGap182.TypeIII.CurveOpen.exists_nonradial_regular_point_avoiding_charP"
        output = f"@{name}.{{u_1,\n    u_2}} : ∀ {{k : Type u_1}}, True\n"
        verify.check_type_output(output, [name])
        with self.assertRaises(SourceCheckError):
            verify.check_type_output(output + output, [name])

    def test_initial_source_manifest_and_request_mapping(self):
        manifest = json.loads(verify.SOURCE_MANIFEST.read_text())
        registry = json.loads(verify.REGISTRY.read_text())
        sources, order = verify.read_sources(manifest, registry)
        self.assertEqual(set(sources), set(order))
        self.assertGreater(len(verify.canonical_names(registry)), 1000)
        name = next(n for n, r in registry["modules"].items() if r["requests"])
        changed = copy.deepcopy(registry)
        changed["modules"][name]["requests"].pop()
        with self.assertRaises(SourceCheckError):
            verify.read_sources(manifest, changed)
        changed = copy.deepcopy(registry)
        changed["modules"][name]["source_sha256"] = hashlib.sha256(b"other").hexdigest()
        with self.assertRaises(SourceCheckError):
            verify.read_sources(manifest, changed)

    def test_status_cannot_be_silently_promoted(self):
        manifest = json.loads(verify.SOURCE_MANIFEST.read_text())
        registry = json.loads(verify.REGISTRY.read_text())
        manifest["type_iii_proposition_proved"] = True
        with self.assertRaises(SourceCheckError):
            verify.read_sources(manifest, registry)

    def test_missing_or_changed_numerical_input_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "provenance").mkdir()
            (root / "inputs/source_certificates").mkdir(parents=True)
            (root / "provenance/check_data.py").write_text("# checker fixture\n")
            source = root / "inputs/source_certificates/bound.json"
            source.write_text('{"bound":"1/3"}')
            manifest = {"numerical_premises_discharged": False, "type_iii_proved": False, "file_count": 1,
                        "files": [{"published_path": "inputs/source_certificates/bound.json",
                                   "published_bytes": source.stat().st_size,
                                   "published_sha256": verify.digest(source)}]}
            (root / "provenance/data_manifest.json").write_text(json.dumps(manifest))
            with patch.object(verify, "ROOT", root):
                self.assertEqual(len(verify.data_fingerprints()), 3)
                source.write_text('{"bound":"1/2"}')
                with self.assertRaises(SourceCheckError):
                    verify.data_fingerprints()
                source.unlink()
                with self.assertRaises(SourceCheckError):
                    verify.data_fingerprints()


if __name__ == "__main__":
    unittest.main()
