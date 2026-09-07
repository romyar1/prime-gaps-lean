# Continuous verification

The workflow downloads the pinned Mathlib dependency cache, cleans this
package with `verify.sh --fresh`, rebuilds its proofs, and audits the same
canonical declarations and explicit hypotheses as local verification. It does
not change the mathematical sources or dependency pins.

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
`weakLeanArgs = ["-j1", "-DElab.async=false", "-M30000"]` for project compilers.
Synchronous elaboration avoids accumulating concurrent theorem elaborations;
the memory cap requests a Lean error if its allocation limit is reached.
The direct audit probes use the same limits. The workflow first adds a unique
24 GiB swap file to its disposable Linux VM, after checking that 30 GiB of disk
space is free following the Mathlib cache download. This reserves 6 GiB for
build outputs. If space is insufficient it fails with a capacity message; it
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

A successful local run does not establish a successful Linux hosted run.
The revised workflow must complete on GitHub before hosted verification is
reported as passing. If the compiler reports its memory limit, or the telemetry
shows excessive total memory, the resource requirement must be addressed rather
than skipping any audit or reusing unverified project proof objects.

References: [pinned Lake CLI](https://github.com/leanprover/lean4/blob/v4.34.0-rc2/src/lake/Lake/CLI/Help.lean),
[elaboration option](https://github.com/leanprover/lean4/blob/v4.34.0-rc2/src/Lean/CoreM.lean),
[weak arguments](https://github.com/leanprover/lean4/blob/v4.34.0-rc2/src/lake/Lake/Config/LeanConfig.lean),
[ARM image inventory](https://github.com/actions/runner-images/blob/main/images/ubuntu/Ubuntu2404-Arm64-Readme.md),
[pinned Lean release](https://github.com/leanprover/lean4/releases/tag/v4.34.0-rc2),
and [GitHub runner specifications](https://docs.github.com/en/actions/reference/runners/github-hosted-runners).
