# External numerical verification for the conditional 182 development

Release: [external-numerics-20260909](https://github.com/romyar1/prime-gaps-lean/releases/tag/external-numerics-20260909).

All 262 rational target comparisons, 14 production stages, 14 implementation
audits, and four deliberate rejection tests passed in a full external
recomputation of the fixed trial. The run took approximately 1 hour 44 minutes
on the tested Apple Silicon Mac with three workers.

The archive supplies unchanged numerical programs and inputs, the tested
arithmetic runtime, fresh outputs, complete receipts and logs, and reproduction
commands. The repository includes verifier drivers and compact evidence for
review, plus an offline attachment-integrity checker. Full numerical
reproduction is tested on Apple Silicon macOS, Python 3.12 and NumPy 2.3.5.

**Proof scope is unchanged.** The Lean theorem remains conditional on its
262 integral inequalities, three established finite-field estimates, and Type
III local Fourier proposition. No Lean premise is discharged by this release;
Type III remains separate. The analytic justification of the numerical
algorithms still requires mathematical review. See the
[numerical package guide](../research/numerical_182/README.md) and
[exact assumptions](assumptions.md).

Release assets in `romyar1/prime-gaps-lean`:

- `prime-gaps-external-182-verified-20260909.zip`
- `prime-gaps-external-182-verified-20260909.zip.sha256`

Archive size: 244,843,318 bytes. SHA256:

```text
2960729efa8996538731820ce6cadc202831c8e98b2c0bdb14cfd19f33726f3b
```

Check a downloaded asset from the updated repository root with:

```sh
python3 -B scripts/check_external_numerics.py --archive /path/to/the.zip
```

This updates the existing project. Lean sources and dependency pins are unchanged
from posted commit `78e052bd50e64a34f58866b8b306844b72926c60`.
