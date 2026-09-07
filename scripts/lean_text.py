"""Conservative lexical checks for this project's ordinary Lean modules.

Lean remains the parser and proof checker. This helper preserves line numbers,
removes nested comments and literal strings, and refuses unsupported interpolated
strings rather than silently hiding embedded Lean terms from the source scan.
It does not infer whether a theorem's explicit premises have been discharged.
"""
from __future__ import annotations

import re

if not __debug__:
    raise RuntimeError("validation must run with Python assertions enabled")


class SourceCheckError(ValueError):
    pass


MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
LEAN_NAME = re.compile(r"[\w']+(?:\.[\w']+)*\Z", re.UNICODE)
FORBIDDEN = {
    "sorry", "sorryAx", "admit", "axiom", "native_decide", "unsafe",
    "elab", "elab_rules", "macro", "macro_rules", "initialize",
    "builtin_initialize", "run_cmd", "run_elab", "run_meta", "run_tac", "run_conv",
    "command_elab", "builtin_command_elab", "term_elab", "builtin_term_elab",
    "tactic", "builtin_tactic", "doElem_elab", "builtin_doElem_elab",
    "builtin_macro", "app_delab", "delab", "builtin_delab",
    "app_unexpander", "builtin_app_unexpander", "unexpander", "builtin_unexpander",
    "combinator_formatter", "combinator_parenthesizer", "implemented_by",
    "formatter", "builtin_formatter", "parenthesizer", "builtin_parenthesizer",
    "category_parenthesizer", "builtin_category_parenthesizer",
}

# This imported convenience theorem deliberately instantiates the two original
# public local axioms. It is unused by the conditional final endpoints. Its
# classification is exact in both declaration name and complete axiom set;
# callers must opt in, and terminal entry/type checks never do so.
APPROVED_BASELINE_WRAPPER_AXIOMS = {
    "PrimeGap182.TypeIII.kernel_norm_le_from_public_inputs": frozenset({
        "propext", "Classical.choice", "Quot.sound",
        "PrimeGap186.kloosterman3_bound", "PrimeGap186.kloosterman2_correlation_bound",
    }),
}


def _blank(text: str) -> str:
    return "".join("\n" if c == "\n" else " " for c in text)


def strip_lean_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i, n = 0, len(text)
    while i < n:
        start = i
        if text.startswith("/-", i):
            i += 2
            depth = 1
            while i < n and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise SourceCheckError("unterminated Lean block comment")
            out.append(_blank(text[start:i]))
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = n if end < 0 else end
            out.append(_blank(text[start:i]))
        elif text[i] == "r" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'")) \
                and (m := re.match(r'r(#+)"', text[i:])):
            if "".join(out).rstrip().endswith("!"):
                raise SourceCheckError("interpolated strings require an explicit lexer extension")
            hashes = m.group(1)
            opening_end = i + m.end()
            end = text.find('"' + hashes, opening_end)
            if end < 0:
                raise SourceCheckError("unterminated Lean raw string")
            i = end + 1 + len(hashes)
            out.append(_blank(text[start:i]))
        elif text[i] == '"':
            # Comments are legal between an interpolation marker and its
            # string, so examine the already stripped prefix, not raw text.
            if "".join(out).rstrip().endswith("!"):
                raise SourceCheckError("interpolated strings require an explicit lexer extension")
            i += 1
            closed = False
            while i < n:
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    closed = True
                    break
                else:
                    i += 1
            if not closed:
                raise SourceCheckError("unterminated Lean string")
            out.append(_blank(text[start:i]))
        elif text[i] == "'" and (m := re.match(r"'(?:\\(?:u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|.)|[^'\n\\])'", text[i:])):
            i += m.end()
            out.append(_blank(text[start:i]))
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def source_scan(code: str) -> None:
    for m in re.finditer(r"[\w']+", code, re.UNICODE):
        if m.group() in FORBIDDEN:
            line = code.count("\n", 0, m.start()) + 1
            raise SourceCheckError(f"forbidden Lean token {m.group()!r} on line {line}")
    # These commands can suppress diagnostics or manufacture audit-like output.
    # They are not used by the mathematical source modules in this development.
    # Do not anchor this check: `set_option ... in #eval ...` and commands on
    # the same line as a namespace are also executable audit-output forgeries.
    bad = re.search(r"#\s*(?:eval|guard_msgs|exit)\b", code)
    if bad:
        raise SourceCheckError("unsupported metaprogramming/diagnostic command in audited source")
    if re.search(r"\b(?:debug\.skipKernelTC|trustCompiler|ofReduceBool|ofReduceNat)\b", code):
        raise SourceCheckError("compiler-trust or skipped-kernel option in audited source")


def imports(code: str) -> list[str]:
    result: list[str] = []
    header = True
    for number, line in enumerate(code.splitlines(), 1):
        line = line.strip()
        if not line:
            continue
        if header and line in {"prelude", "module"}:
            continue
        m = re.fullmatch(r"(?:(?:public|private)\s+)?(?:meta\s+)?import\s+(.+)", line)
        if m:
            if not header:
                raise SourceCheckError(f"import outside the ordinary module header on line {number}")
            names = m.group(1).split()
            if not names or any(not MODULE_NAME.fullmatch(name) for name in names):
                raise SourceCheckError(f"unsupported import syntax on line {number}")
            result.extend(names)
        else:
            # Lean accepts multiline `import\nModule`; our ordinary-header
            # reader deliberately fails closed rather than missing that edge.
            if re.search(r"\bimport\b", line):
                raise SourceCheckError(f"unsupported import layout on line {number}")
            header = False
    return list(dict.fromkeys(result))


def axiom_requests(code: str) -> list[str]:
    result: list[str] = []
    for number, line in enumerate(code.splitlines(), 1):
        if re.match(r"^\s*#print\s+axioms\b", line):
            m = re.fullmatch(r"\s*#print\s+axioms\s+(\S+)\s*", line)
            if not m or not LEAN_NAME.fullmatch(m.group(1)):
                raise SourceCheckError(f"unsupported #print axioms request on line {number}")
            result.append(m.group(1))
    return result


def parse_printed_axioms(raw: str, declaration: str) -> tuple[list[str], list[str]]:
    """Parse entire axiom tokens, retaining validated printed universe suffixes.

    With pp.universes enabled, Lean prints declarations such as
    Classical.choice.{u}. Universes instantiate the same axiom declaration;
    they are not part of its canonical name. Commas inside a universe list
    must not split an axiom token. No suffix or trailing input is discarded.
    #print axioms uses universe *parameter* names, not arbitrary Lean terms.
    """
    if not raw:
        return [], []
    parameter = r"(?:[^\W\d]|_)[\w']*"
    token = re.compile(
        r"\s*([\w']+(?:\.[\w']+)*)"
        rf"(?:\.\{{\s*({parameter}(?:\s*,\s*{parameter})*)\s*\}})?"
        r"\s*(,|$)", re.UNICODE,
    )
    arities = {"propext": 0, "Classical.choice": 1, "Quot.sound": 1,
               "choice": 1, "sound": 1}
    for expected in APPROVED_BASELINE_WRAPPER_AXIOMS.values():
        for name in expected:
            if name.startswith("PrimeGap186."):
                arities[name] = 0
    names, printed = [], []
    offset = 0
    while offset < len(raw):
        match = token.match(raw, offset)
        if match is None:
            raise SourceCheckError(f"malformed axiom list for {declaration}")
        name, parameters, separator = match.groups()
        if not LEAN_NAME.fullmatch(name):
            raise SourceCheckError(f"malformed axiom name for {declaration}")
        if parameters is not None:
            levels = [level.strip() for level in parameters.split(",")]
            if name in arities and len(levels) != arities[name]:
                raise SourceCheckError(f"unexpected universe arity for axiom {name} in {declaration}")
            displayed = name + ".{" + ", ".join(levels) + "}"
        else:
            displayed = name
        names.append(name)
        printed.append(displayed)
        offset = match.end()
        if separator and not raw[offset:].strip():
            raise SourceCheckError(f"trailing comma in axiom list for {declaration}")
    return names, printed


def parse_axiom_reports(output: str, requested: list[str], *,
                        allow_namespace_abbreviations: bool = False,
                        allow_approved_baseline_wrappers: bool = False) -> list[dict]:
    pattern = re.compile(
        r"^'([^\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)\s*$",
        re.MULTILINE,
    )
    matches = list(pattern.finditer(output))
    if len(matches) != len(requested):
        raise SourceCheckError(f"expected {len(requested)} complete axiom reports, found {len(matches)}")
    reports = []
    for req, m in zip(requested, matches, strict=True):
        name = m.group(1)
        normalized = req.removeprefix("_root_.")
        if not LEAN_NAME.fullmatch(name) or not (name == normalized or name.endswith("." + normalized)):
            raise SourceCheckError(f"axiom report for {name!r} does not match requested {req!r}")
        raw_axioms = "" if m.group(2) is None else m.group(2).strip()
        axioms, printed_axioms = parse_printed_axioms(raw_axioms, name)
        if len(axioms) != len(set(axioms)):
            raise SourceCheckError(f"duplicate axiom in report for {name}")
        abbreviated = set(axioms) & {"choice", "sound"}
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        if allow_namespace_abbreviations:
            allowed |= {"choice", "sound"}
        classification = "standard_only"
        if allow_approved_baseline_wrappers and name in APPROVED_BASELINE_WRAPPER_AXIOMS:
            expected = APPROVED_BASELINE_WRAPPER_AXIOMS[name]
            actual = set(axioms)
            if actual != expected:
                raise SourceCheckError(f"approved baseline wrapper axiom set changed in {name}: "
                                       f"missing={sorted(expected - actual)}, extra={sorted(actual - expected)}")
            classification = "approved_baseline_wrapper"
        else:
            unexpected = set(axioms) - allowed
            if unexpected:
                raise SourceCheckError(f"nonstandard axioms in {name}: {sorted(unexpected)}")
        reports.append({"requested": req, "declaration": name, "axioms": axioms,
                        "printed_axioms": printed_axioms,
                        "classification": classification,
                        "requires_canonical_name_audit": bool(abbreviated)})
    return reports
