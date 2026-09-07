# Continuous verification

The workflow downloads the pinned Mathlib dependency cache, cleans this
package with `verify.sh --fresh`, rebuilds its proofs, and audits the same
canonical declarations and explicit hypotheses as local verification. It does
not change the mathematical sources or dependency pins.

[GitHub Actions run 34143288525](https://github.com/romyar1/prime-gaps-lean/actions/runs/34143288525) passed on
7 September 2026 at 19:16 UTC, for commit
`73d33fe6451d1054cc569943eadad83c906a9551`. The job took 2h 49m 23s. Its
receipt records `PASS_CONDITIONAL_DEVELOPMENT_AND_TYPE_III_SUPPORT` and
`fresh_project_rebuild_requested: true`, with 638 formal modules and 4,916
audited declarations. All 25 verifier regression tests also passed. The
run artifact `lean-verification-34143288525-1` contains the receipt, build
log, theorem-type and explicit-premise audits, and resource measurements.
The numerical inequalities and Type III hypotheses remain undischarged.

The revised workflow uses the standard public `ubuntu-24.04-arm` image. Its
published software inventory is smaller than the x64 image's (for example,
Android SDK and CodeQL are absent), which makes it a candidate for providing
swap headroom without deleting installed software. This is not a guarantee of
free space: the workflow checks actual capacity after fetching dependencies.
Lean `v4.34.0-rc2` provides an official Linux aarch64 release.

The first two hosted attempts at commit `c2f3d7f` ended with runner shutdowns
and exit code 143, about 51 and 45 minutes into the build. Neither reached the
180-minute job deadline. The available logs do not establish the shutdown's
cause. An earlier uncapped local build of the 10 MB public baseline exceeded
25 GiB RSS, so memory demand is a specific concern on the standard public
Ubuntu runner's 16 GB of RAM.

A local test with one worker, synchronous elaboration and `-M12000` failed
after 508 seconds with `lean::memory_exception` in the interpreter. This
confirms that even these reduced concurrency settings need a larger allocation
budget; it does not prove why GitHub terminated the earlier runners.

The revised resource settings use `LEAN_NUM_THREADS=1` for Lake and
`weakLeanArgs = ["-j1", "-DElab.async=false", "-DmaxHeartbeats=2000000", "-M30000"]` for project compilers.
The 200,000-heartbeat default was insufficient for three category-theory
modules during a local build with synchronous elaboration. Raising this finite
work budget does not skip proof checking.
Synchronous elaboration avoids accumulating concurrent theorem elaborations;
the memory cap requests a Lean error if its allocation limit is reached.
The direct audit probes use the same limits. The workflow first adds a unique
24 GiB swap file to its disposable Linux VM, after checking that 30 GiB of disk
space is free following the Mathlib cache download. This reserves 6 GiB for
build outputs. If the workspace has that 6 GiB reserve and an additional `/mnt`
temporary disk has 30 GiB free, swap can use that disk instead. If space is
insufficient it fails with a capacity message; it
does not delete existing files or installed software. The setup script refuses
to run outside a GitHub-hosted Linux runner. This cap is not an operating-system
limit on total resident memory or all subprocesses. These settings leave kernel
checking and the verifier's source, dependency, declaration and axiom checks
in place. The audit registry records the reviewed configuration change.

`PRIME_GAPS_LIVE_LOGS=1` streams new verifier log contents to the Actions console.
Lake may still buffer a compiler's diagnostics until that module finishes, so
`scripts/ci_verify.sh` also prints memory, disk and process information every
30 seconds. GNU time records resource statistics in `verification/time.txt`.
The wrapper's 210-minute deadline sends SIGINT so the verifier can stop its
children and record failure, leaving time for artifact upload within the
240-minute job. This extra timing headroom accommodates the conservative
single-worker build; it is not an explanation of the earlier shutdowns.
A runner that disappears abruptly can still skip artifact
upload; the console diagnostics are therefore essential.

The verifier retains `--no-cache --rehash`. In the pinned Lake version,
`--no-cache` prevents build-cache downloads during that command; it does not
delete existing dependency artifacts. `--rehash` hashes file contents instead
of trusting saved `.hash` files. The deliberate package clean is what requires
fresh project proof objects on CI.

The successful hosted run rebuilt the public baseline in 4,052 seconds and
completed the verifier in 2h 47m 9s. GNU time reported maximum process RSS of
14,057,908 KiB. These are measurements of this run, not a guarantee for every
runner. If a future compiler reports its memory limit, or telemetry shows
excessive total memory, address the resource requirement while preserving
all audits and the fresh project build.

References: [pinned Lake CLI](https://github.com/leanprover/lean4/blob/v4.34.0-rc2/src/lake/Lake/CLI/Help.lean),
[elaboration option](https://github.com/leanprover/lean4/blob/v4.34.0-rc2/src/Lean/CoreM.lean),
[weak arguments](https://github.com/leanprover/lean4/blob/v4.34.0-rc2/src/lake/Lake/Config/LeanConfig.lean),
[ARM image inventory](https://github.com/actions/runner-images/blob/main/images/ubuntu/Ubuntu2404-Arm64-Readme.md),
[pinned Lean release](https://github.com/leanprover/lean4/releases/tag/v4.34.0-rc2),
and [GitHub runner specifications](https://docs.github.com/en/actions/reference/runners/github-hosted-runners).
