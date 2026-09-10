# Reading this project if you are new to Lean

A Lean file can contain mathematical definitions, theorem statements and
proofs. Lean checks that the proof establishes the stated theorem from its
stated assumptions. It does not decide whether an assumption has been proved
elsewhere, whether a numerical experiment justifies it, or whether the theorem
is a new result.

## Three kinds of evidence

| Item | What it establishes |
| --- | --- |
| A checked Lean theorem with no outstanding mathematical premises | The precise mathematical conclusion in that theorem. |
| A checked Lean theorem that takes hypotheses | The implication from those hypotheses to its conclusion. |
| A numerical computation or saved certificate | Computational evidence; its reliability and scope depend on the method and the checks performed. |

For example, proving in Lean that hypotheses A, B and C imply a prime-gap
bound does not prove A, B or C. They remain visible in the theorem's type.
This repository's [assumptions guide](assumptions.md) gives the exact list.

The 262 numerical premises are inequalities for specific mathematical
integrals. Their definitions already exist in Lean. Saved JSON files contain
supporting calculations, but Lean currently does not derive the integral
inequalities from those files. A full external recomputation has now passed
all 262 target comparisons, 14 audits and four deliberate rejection tests.
That gives reproducible computational evidence; the three formal proof steps
below are still needed to discharge the Lean premises.

## What a certificate needs

An approximate decimal is different from an interval proved to contain an
integral. An interval computation can provide rigorous mathematical evidence
when it controls rounding, discretization and every omitted term.

To discharge a Lean premise, we also need a checked argument connecting the
certificate to the original integral. That usually has three parts:

1. Prove that the integral is bounded by a finite calculation, including all
   approximation errors.
2. Check that finite calculation with exact arithmetic or a formally justified
   interval checker.
3. Compare the resulting rational bounds with the exact constants in the
   theorem statement.

Checking only a stored decimal comparison, or checking a file's SHA256 hash,
does not establish the first part. A hash establishes which bytes were used.

## Sharing unfinished work

You can publish Lean proofs and computations in the same repository. Include
programs, inputs, outputs, versions and reproduction commands where available,
and label their roles clearly. Contributors can then inspect the computations
while extending the formal proof. No special central registry is required to
publish a standalone Lean project.

This package keeps the checked sources in `formal/` and the saved integral
calculations in `inputs/source_certificates/`. The
[numerical-data guide](numerical-data.md) explains the unchanged provenance
records, while the [external package](../research/numerical_182/README.md)
provides full-run receipts and reproduction commands for its tested macOS runtime. Small finite experiments in `research/type_iii/` are separate
from the integral certificates and from the Lean proof.

## Interpreting a successful build

`lake build` checks that the Lean source compiles. `./verify.sh` adds the
repository's source, dependency, theorem-type and axiom audit. Read its status
together with the theorem premises. In particular, this project's successful
conditional-verification status is not an unconditional proof of the bound 182.

Ordinary mathematical inputs are kept as explicit theorem arguments. The
audit's standard logical axioms, such as classical choice, are distinct from
those outstanding mathematical inputs; an axiom report alone is not a list
of all assumptions in a theorem statement.
