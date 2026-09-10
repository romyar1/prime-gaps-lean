# Numerical dependency chain and review boundary

1. The fixed rational trial has 39 coordinates, 393,216 grid intervals,
   393,177 retained radial indices, and 726 independent spline coefficients.
   Its SHA-256 is
   `3ebae41700a7839f2d7a7b3fe068b11ed364a7542aab110173bbcdbd66645952`.
   Optimisation and floating candidate searches are not rerun: they selected
   this trial, but their output is now fixed exact input.

2. `certify_independent_fragment_cap.py` combines the signed independent cap
   components before squaring, retaining their cross terms. The inherited
   face integration calculates the denominator, J0, Jplus, and outside-C
   tail enclosures. The implementation is frozen by source hashes and
   checked against small exact rational cases in
   `audit_independent_fragment_cap.py`.

3. `prepare_fine_source_affines.py` constructs signed marginal prefixes on
   blocks of 48 original grid cells. Reference and variation arrays are
   stored together. `FineSourceContext` verifies the trial, full normaliser,
   mesh, array archive, dimensions, and retained-maximum prefix coverage.
   The block grouping does not substitute a different coarse trial.

4. Rank-two and high source programs contract the original source kernels
   with the appropriate root or retained-coordinate envelopes. Low-source
   programs use the recorded tilted kernels and directed bounds for the
   high-count tail. `stages.json` fixes every producer and bin selection.
   The independent finite audits check signed-prefix composition, normalising
   powers, count factors, and positive-kernel majorants on explicit small
   examples. Production-scale arithmetic is rerun separately.

5. Each outer row supplies a raw root bound R and weighted face bound QL.
   The historical ledger normalises them as A = R/(39 D_lower) and
   M = rho_star² QL/D_lower. Each inner row supplies a raw face bound U,
   normalised as B = rho_star × coefficient × U/D_lower. The coverage checker
   compares R, QL and U directly with the published raw Lean thresholds,
   avoiding a change of normalisation during the target comparison.

6. The frozen exact scalar ledger checks all event inventories, tuple
   admissibility, rational square-root upper bounds and the positive
   restoration margin. Acceptance requires the fresh production payloads to
   match the frozen inputs to that ledger. Dependency hashes are not rewritten
   to make old receipts accept new data.

This package makes the numerical claim reproducible and reviewable. Its
trusted computation base includes Python, NumPy, python-flint/FLINT, the
native libraries and hardware. The algorithm-to-integral arguments embodied
in the source comments and audits are ordinary mathematics, not newly
kernel-checked Lean endpoint proofs. A mathematical reviewer should check
those arguments and the Type III derivation separately before describing an
unconditional bounded-prime-gap theorem.
