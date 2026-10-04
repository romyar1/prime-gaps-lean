# Prime gaps in Lean

**GPT-6 Astra (OpenAI), prompted by Romyar Sharifi.**

A Lean development of the analytic and sieve argument for prime gaps at most
182, with supporting work on its Type III local Fourier input.

**The result is conditional.** The final theorem still assumes 262 fixed
integral inequalities, three established finite-field estimates, and the
Type III local Fourier proposition. The repository does not contain an
unconditional Lean proof of the bound 182.

The September 18 Type III derivation supplies that local Fourier input from
precisely stated published general theorem interfaces on one common adic
theory. The joint interpretation of those interfaces remains external; the
262 numerical inequalities remain hypotheses. See the
[cited derivation](docs/type-iii-published-general-application.md) and
[verification status](STATUS.md).

## Start here

- [Reading this project](docs/reading-this-project.md) explains proofs,
  hypotheses, numerical certificates and build results for readers new to Lean.
- [Assumptions](docs/assumptions.md) lists the exact outstanding premises.
- [Verification status](STATUS.md) identifies the checked source snapshot.
- [Numerical computations and data](docs/numerical-data.md) describes what is
  included and which computations still need a formal connection to the integrals.
- [Completed external numerical package](research/numerical_182/README.md) supplies
  the verifier tools, full-run results, and reproduction instructions.
- [Type III statement and code map](docs/type-iii.md) describes the local target.
- [Type III from published general theorems](docs/type-iii-published-general-application.md)
  records the September 18 derivation and its exact common-theory assumptions.
- [Earlier published-input route](research/type_iii/published_inputs/README.md)
  explains the support and trace arguments used in that derivation.
- [Citation](CITATION.md) and [attribution](NOTICE.md) preserve the authorship
  and existing notices of this project and its dependencies.

The main entry is [PrimeGaps182Analytic.lean](formal/PrimeGaps182Analytic.lean).
Its theorem
`PrimeGap182.infinite_consecutive_prime_pairs182_of_local_inputs`
proves that infinitely many consecutive primes have gap at most 182,
**if its displayed mathematical premises hold**. The analytic, incidence,
distribution and sieve deductions from those premises are checked in Lean.

[TypeIIILocalProgress.lean](formal/TypeIIILocalProgress.lean) collects the
Type III supporting results. The original finite sums and uniform local
Fourier statement are unchanged. The development includes exact finite-sum
identities, phase algebra, support arguments, a conditional route using
published geometric theorems, and a separate partial development of the
étale and adic foundations. The September 18 entry
[TypeIIICoherentUniformApplicationsFromGeneralStandardTheory03.lean](formal/TypeIIICoherentUniformApplicationsFromGeneralStandardTheory03.lean)
constructs `HasFiniteExceptionalTypeIIIInput` from the common general-theorem
interfaces, with uniform constants chosen before the prime. It does not prove
the existence or adic interpretation of that common theory. The numerical
package supplies computational evidence for the separate integral premises.

## What is included

| Directory | Contents and scope |
| --- | --- |
| `formal/` | Lean definitions and checked theorems; every module is in the default build. |
| `inputs/source_certificates/` | Saved numerical evidence for the integral inequalities; these JSON files are not Lean proofs. |
| `provenance/` | Source/data fingerprints, the declaration registry, and a data-integrity checker. |
| `research/numerical_182/` | External numerical verifier drivers, all 262 comparison records, and a pinned full release attachment. |
| `research/type_iii/` | Mathematical notes and separately labelled finite computational checks. |
| `docs/` | Explanations of assumptions, verification, numerical data and CI. |
| `vendor/primegaps186/` | The unchanged public baseline, with its license and source identity. |
| `diagnostics/` | Optional inspection of the baseline's explicit axioms. |
| `.github/workflows/` | A workflow that runs the pinned verifier on GitHub. |

The source archive excludes unfinished working files, generated proof objects,
dependency caches and Git history. On **9 September 2026**, the full external
numerical recomputation passed **262 target comparisons, 14 implementation
audits, and four deliberate rejection tests**. The verified bundle includes
programs, inputs, the tested runtime, fresh outputs and receipts. Full numerical
reproduction is tested on Apple Silicon macOS; Linux and Windows are not yet
tested. See the [package guide](research/numerical_182/README.md).

This is external computational verification. It supplies no new Lean proof
terms for the integral inequalities and does not prove the Type III premise.

## Reproduce the Lean checks

The project pins Lean **4.34.0-rc2** and Mathlib commit
`bbcd1968ee6950abe88b85dba6995da346c4b2a8`.
With Elan, Git and Python **3.11 or later** installed, run from this directory:

```sh
lake exe cache get
./verify.sh
```

The first command downloads compiled dependencies. The verifier builds the
development, checks source/data integrity, and prints the actual theorem types
and their axiom dependencies. It writes fresh receipts and logs under
`verification/`.

For a build without the additional audit:

```sh
lake build PrimeGapsDevelopment
```

See [verification instructions](docs/verification.md) for a fresh project build,
the exact audit policy and adding new modules. A successful build checks the
stated implications; it does not remove their hypotheses.

The integrated September 18 sources passed full local verification on
3 October 2026: 918 development modules and 6,128 audited declarations, plus
30 regression tests. See the [current evidence](provenance/release_checks/20261003/README.md).

The GitHub workflow runs the same verifier. A [fresh hosted verification](https://github.com/romyar1/prime-gaps-lean/actions/runs/34143288525)
passed on 7 September 2026, checking all 638 modules and 4,916 declarations
with their explicit hypotheses. [CI notes](docs/ci.md) record the result,
resource settings and earlier shutdowns.

## Updating this repository

The full verified numerical bundle and checksum are available in the
[external-numerics-20260909 release](https://github.com/romyar1/prime-gaps-lean/releases/tag/external-numerics-20260909).
See [the upload guide](docs/uploading-to-github.md) for the source-update and
release workflow. Keep the scope and attribution with both the code and
numerical evidence.

This is a standalone project depending on Mathlib, not a contribution already
accepted into Mathlib. The public
[OpenAI PrimeGaps186 development](https://github.com/openai/PrimeGaps186)
is vendored unchanged; its three mathematical axioms are disclosed separately.
The conditional 182 endpoints use only Lean's standard logical axioms and
retain the mathematical inputs as explicit theorem arguments.
