# Continuous verification

The GitHub Actions workflow runs the same `verify.sh` as local verification.
It downloads the pinned Mathlib dependency cache, rebuilds the project's proof
objects, and preserves verification receipts and logs as run artifacts even
when a check fails. It does not update dependency pins. The job timeout is
180 minutes; the verifier receives `--timeout 10800`.

There are two distinct concurrency settings. `LEAN_NUM_THREADS=2` limits Lake's
normal runtime worker pool. The package's `weakLeanArgs = ["-j2"]` passes the
supported thread option to each Lean compiler process; the verifier also uses
that option for its direct Lean probes. Weak arguments do not enter Lake's
build-result trace, so changing this resource setting does not invalidate the
Mathlib cache. These behaviors are documented in the pinned
[Lean frontend](https://github.com/leanprover/lean4/blob/v4.34.0-rc2/src/Lean/Shell.lean),
[runtime](https://github.com/leanprover/lean4/blob/v4.34.0-rc2/src/runtime/object.cpp),
and [Lake configuration](https://github.com/leanprover/lean4/blob/v4.34.0-rc2/src/lake/Lake/Config/LeanConfig.lean).

An uncapped local compilation of the monolithic public baseline used over
25 GiB of resident memory. The peak with `-j2` has not yet been measured.
Standard Ubuntu GitHub runners currently provide 16 GB for public repositories
and 8 GB for private repositories, according to the
[official runner specifications](https://docs.github.com/en/actions/how-tos/write-workflows/choose-where-workflows-run/choose-the-runner-for-a-job).
The workflow therefore still needs a completed hosted run to establish its
memory and timing requirements. No successful GitHub Actions run is asserted
by the local verification records.
