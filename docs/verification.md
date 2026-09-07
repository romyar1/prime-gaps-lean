# Reproducing the verification

Install Elan, Git, and Python 3.11 or later. Run these commands from the
repository root:

```sh
lake exe cache get
./verify.sh
```

The toolchain and every dependency revision are pinned by `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`. The first command fetches the pinned
Mathlib cache. The verifier checks Git availability, each dependency's exact
revision and origin, and clean tracked dependency sources before asking Lake
to load the project. It clears inherited `LEAN_PATH` and `LEAN_SRC_PATH` so
objects from another proof project cannot enter the build.

The default verification runs:

```sh
lake --no-cache --rehash build PrimeGapsDevelopment
```

Lake checks dependency traces and rebuilds stale modules. To force a fresh
build of the project and its vendored public baseline, use:

```sh
./verify.sh --fresh
```

This runs `lake clean primeGapsLean` first. It preserves dependency caches.
Do not replace it with unqualified `lake clean`, which also cleans dependencies.
The baseline is large, so allow time for this build.

The package and audit probes use `-j1 -DElab.async=false -DmaxHeartbeats=2000000 -M30000`: one frontend
worker, synchronous elaboration, a two-million-heartbeat elaboration budget,
and a 30000 MiB Lean allocation limit. Set
`LEAN_NUM_THREADS=1` in the invoking environment to limit Lake's worker pool
as well. The package uses `weakLeanArgs`, which the pinned Lake implementation
excludes from proof artifact cache keys. See [CI notes](ci.md) for the resource
limits and their scope. Set `PRIME_GAPS_LIVE_LOGS=1` to stream verifier logs.

For a source, dependency, and numerical-data integrity check without a proof
build or axiom audit:

```sh
./verify.sh --preflight
```

The preflight result is labeled `PASS_PREFLIGHT_NO_PROOF_BUILD`. A full pass is
labeled `PASS_CONDITIONAL_DEVELOPMENT_AND_TYPE_III_SUPPORT`.

## What a full pass checks

- Every `formal/*.lean` file appears in the source manifest, Lake library,
  import graph, and canonical declaration registry. Source bytes match their
  recorded fingerprints. Orphan or shadowing compiled imports are rejected.
- The unchanged vendored baseline has its recorded fingerprint and exactly
  its three documented mathematical axiom declarations. Optional diagnostic
  modules remain outside the default proof library.
- New proof sources contain no unfinished-proof tokens, new axioms, native
  decision shortcuts, or unsupported commands that can manufacture audit
  output or bypass the kernel. Builds treat warnings as errors.
- Every source `#print axioms` request resolves to its recorded canonical
  declaration in the current build. An independent generated Lean file imports
  all project modules and prints each declaration's full type and axiom set.
  The final 182 declarations must use only `propext`, `Classical.choice`, and
  `Quot.sound`. The one documented nonterminal baseline convenience wrapper
  receives its own exact axiom classification.
- The premise definitions are printed separately, including the numerical
  inequalities, established finite-field estimates, and the full uniform
  quantifiers in `LocalFourierHypothesis`.
- `provenance/check_data.py` checks all published numerical source records,
  their inventory, numeric payload fingerprints, and the limited provenance
  path normalization. The checker, manifests, numerical records, Lean sources,
  and compiled proof fingerprints are checked for changes during verification.

A pass certifies the Lean declarations **with their displayed hypotheses**.
It does not establish the numerical integral inequalities or the Type III
local Fourier proposition. Official pinned Mathlib/Lean dependency artifacts
may be reused; `--fresh` rebuilds this project's proof sources, not all of
Mathlib. The public baseline's three axioms are disclosed separately and must
not appear in the conditional 182 endpoint's axiom report.

## Output

Each run writes `verification/runs/<UTC timestamp>_<process id>/receipt.json`.
`verification/latest.json` points to the latest result by recording the same
receipt content. Its status distinguishes failure, preflight, and full proof
checking. These generated files are ignored by Git.

A full run also writes `build.log`, `data_integrity.log`, `TheoremTypes.lean`,
`theorem_types.log`, `ExplicitPremises.lean`, and `explicit_premises.log` in that
run directory. The receipt records the hashes, source inventory, declaration
counts, axiom reports, and their precise scope. Counts describe the current
run; they are not a substitute for inspecting the theorem premises.

Run focused verifier regression tests with:

```sh
python3 -B -m unittest discover -s scripts -p 'test_verifier.py' -v
```

## Extending the development

Edit the working files in `formal/`. For a new module, add its exact module
name to the `PrimeGapsDevelopment` roots in `lakefile.toml`. Lake currently
uses those roots as its default globs; if an explicit `globs` array is present,
update that array too so both inventories include every module. Give exported
results explicit `#print axioms` requests. Keep the conditional final theorem
and the remaining-problem descriptions accurate as mathematical work advances.

Ordinary verification rejects changed sources until their manifest entries
are refreshed. After reviewing the changes, run:

```sh
./verify.sh --refresh-manifests
```

This builds the current library, resolves every source request from the
current module's Lean reports, updates source fingerprints and the canonical
name registry, and performs the independent full audit. Changed files retain
their original provenance hashes; their previous audit status is invalidated.
A refresh does not change `target_proved: false` or discharge any hypothesis.
If the audit subsequently fails, the refreshed registry is still only a
registry, and the failure receipt remains the verification result. Dependency,
compiler, baseline, or other Lake configuration changes require separate
review of the pinned verification policy. Only development module inventory
changes are accepted by automatic refresh.

Review the source and manifest diff together before committing. Include newly
proved mathematics, the matching registry changes, and any warranted status
documentation changes in the same commit. Do not commit generated objects or
reuse an older successful receipt as evidence for changed source bytes.

`PRIME_GAPS_PYTHON`, `PRIME_GAPS_LAKE`, and `PRIME_GAPS_GIT` can select installed
executables. A path-valued `PRIME_GAPS_GIT` must name an executable called `git`;
its directory is also supplied to Lake through `PATH`. Machine-specific
executable paths belong in the invoking environment, not the checked-in
configuration. `--timeout SECONDS` sets the limit for each build or probe;
the default is 7200 seconds, and zero disables the limit.
