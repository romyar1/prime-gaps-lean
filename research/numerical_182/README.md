# External verification of the 262 numerical bounds

The full external recomputation completed on **9 September 2026 at 07:57 UTC**.
All **262 rational target comparisons**, **14 production stages** (including
affine preparation), **14 implementation audits**, and **four negative
controls** passed. Production took approximately **1 hour 44 minutes** of wall
time with three workers on the tested machine. Summed production-stage time
was about 3 hours 31 minutes; that sum is not elapsed wall time.

The authoritative [acceptance receipt](evidence/verification.json) reports
`PASS_COMPLETE_EXTERNAL_NUMERICAL_RECOMPUTATION`. It records 328,936 source
geometry equalities, exact agreement of all 20 fresh affine arrays, and no
reads of historical production outputs during production. The
[coverage record](evidence/coverage.json) lists all 262 comparisons.

## Proof status

**Proved in Lean:** the precise conditional theorems in
[`formal/`](../../formal/), including
`PrimeGap182.infinite_consecutive_prime_pairs182_of_local_inputs`.
This update changes no Lean source, theorem statement, proof, or dependency pin.

**Remaining hypotheses:** Lean still takes the 262 integral inequalities as
explicit premises. It also takes the three established finite-field estimates
and the separate Type III local Fourier proposition. This external package
discharges **zero** Lean numerical premises and does **not** prove Type III.
See the [exact assumptions](../../docs/assumptions.md). The ordinary mathematical
arguments connecting the numerical algorithms to those integrals still need
review; the finite implementation audits do not prove every analytic reduction.

**Computational evidence:** the frozen interval programs were rerun on the
exact trial, their fresh mathematical payloads matched the reference records,
and every required rational comparison passed. See [the method](METHOD.md),
[implementation audits](evidence/audits-result.json), and
[payload comparisons](evidence/payload-comparisons.json).

## What the four negative tests mean

A negative test deliberately supplies an invalid input and requires rejection.
These are successful safeguard tests, not four failed inequalities in the
accepted run. Each uses a disposable copy.

| Deliberate problem | Required response | Result |
| --- | --- | --- |
| Make the denominator lower bound negative | Reject the cap target | Rejected |
| Remove a required inner bin | Reject incomplete coverage | Rejected |
| Append a newline to the exact trial file | Reject its changed hash | Rejected |
| Substitute the obsolete FLINT library with the signed-FFT bug | Fail the signed-convolution regression | Rejected |

The [negative-control receipt](evidence/negative-controls.json) records these
results; detailed logs are in the full archive. These test specific safeguards,
not every possible bug. The new repository attachment tests are a separate suite.

## Complete runnable package

Download the complete runnable package from the
[external-numerics-20260909 release](https://github.com/romyar1/prime-gaps-lean/releases/tag/external-numerics-20260909)
in the **existing** `romyar1/prime-gaps-lean` repository. Release assets:

`prime-gaps-external-182-verified-20260909.zip` — 244,843,318 bytes

SHA256:

```text
2960729efa8996538731820ce6cadc202831c8e98b2c0bdb14cfd19f33726f3b
```

[`asset.json`](asset.json) pins its identity, base commit, and review copies.
The archive contains 914 regular files: 913 covered by
[`package-manifest.json`](package-manifest.json), plus that manifest itself.
These include 793 unchanged research inputs and runtime files, fresh outputs,
full audit evidence, the exact Lean target snapshot, and the drivers.
Original provenance bytes, including historical host paths, remain in the
frozen archive. These are provenance, not portable path instructions; workers
relocate them in memory. Native libraries and upstream sources retain licenses.

This repository directory contains a **review subset**: byte-for-byte driver
and checker copies in `verifier/`, method/runtime notes, and compact evidence.
Integrator sources, arrays and native runtime are in the archive. Run the full
package from its extracted root; `verifier/` alone is incomplete.

From the repository root, check the review copies and five current Lean target
files with Python 3.11+ (standard library only):

```sh
python3 -B scripts/check_external_numerics.py
```

After obtaining the ZIP, also check its SHA256 and every archived file:

```sh
python3 -B scripts/check_external_numerics.py \
  --archive /path/to/prime-gaps-external-182-verified-20260909.zip
```

This offline check does not extract files and refuses online-only inputs.
Its `PASS_EXTERNAL_PACKAGE_INTEGRITY` verifies stored evidence and file identity;
it is not a new integration run. The separate GitHub integrity job checks the
repository subset without downloading the attachment. The existing Lean job
continues to check the conditional development.

## Repeat the computation

Extract the verified ZIP into a new local directory. The tested runtime is
**Apple Silicon macOS, Python 3.12, NumPy 2.3.5**, with bundled python-flint 0.9.0
and FLINT 3.6.0 including the signed-FFT repair. See [`RUNTIME.md`](RUNTIME.md)
for the fixed library hash and upstream commit. This release has no tested
Linux or Windows numerical installer.

Run from the extracted `prime-gaps-external-182/` directory, using fresh working
directories outside Dropbox. These directories must not already exist:

```sh
python3.12 -B check_package.py
python3.12 -B audit.py --work /tmp/pg182-audits
python3.12 -B test_rejection.py --work /tmp/pg182-negative
python3.12 -B verify.py --work /tmp/pg182-production --jobs 3
python3.12 -B finish.py --work /tmp/pg182-production \
  --audits /tmp/pg182-audits --negative /tmp/pg182-negative \
  --export /tmp/pg182-evidence
```

Use `--jobs 1` when memory is limited. Do not use Python `-O`. The archive's
README gives resume behavior and acceptance conditions. The final
`verification.json`, rather than a partial stage result or `run.json`, determines
full acceptance. The measured time is specific to the tested machine.

The source target was commit `78e052bd50e64a34f58866b8b306844b72926c60`.
The [trial comparison](evidence/trial-comparison.json) checks all 726 coefficients,
26 knots, 11 signatures, three caps, 12 shells and 13 scalar parameters
against the literal Lean data. Target hashes are checked again by the
attachment checker. No unfinished Lean work is included here.
