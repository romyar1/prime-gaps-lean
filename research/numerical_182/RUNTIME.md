# Runtime provenance

The acceptance run uses Python 3.12.14, NumPy 2.3.5, python-flint 0.9.0 and
FLINT 3.6.0 with the upstream signed-FFT correction
`7ad753d51c82fdec115cb179b41d0e581f1cb0ec`.

The corrected library is
`snapshot/prime_gaps_20260903/runtime/flint/.dylibs/libflint.24.0.dylib`.
Its SHA-256 is
`0658f28b8b28dcf7f58c5204492709feb755dafe047430d007837eccee2fdd39`.
The unchanged 186 numerical engine has SHA-256
`7f71bdefcfe3bb5ca76a143929b3cb3f4156c21dc483253cda3077420f1e5de4`.

The local build recipe, upstream patch, deployment receipt, configuration
logs and tests are preserved under `experiments/runtime_fix/`. The historical
recipe refers to its original Xcode installation and source build tree; it
is provenance, not a newly tested cross-platform installer. The operational
reproduction route for this package uses the included macOS ARM64 libraries.

`audit.py` starts with `check_certificate_runtime.py`. In addition to the
engine's required environment checks, it compares 24 deterministic signed
polynomial products and truncations against Python arbitrary-precision
integers. Version strings alone do not establish that the repair is present.
`test_rejection.py` also tests that the old library is rejected.

Library licenses are included under
`runtime/python_flint-0.9.0.dist-info/licenses/`. The original 186 source
license is preserved under `sources/PrimeGaps186/LICENSE`.
