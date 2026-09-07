# Audit accompanying the 5 September 2026 upload snapshot

These are unchanged portable outputs from the full local verifier run
`20260905T081655Z_6176`, completed at 08:21:25 UTC.

- `receipt.json`: source, configuration, dependency, artifact and data hashes,
  with the full declaration/axiom inventory.
- `theorem_types.log` and `TheoremTypes.lean`: the actual types and axiom reports
  of the 4,916 audited declarations and the generated query that produced them.
- `explicit_premises.log` and `ExplicitPremises.lean`: the mathematical premises
  retained by the endpoint, including the original integral inequalities.
- `data_integrity.log`: the numerical-record integrity check. It is not an
  interval recomputation or a proof of those inequalities.

The receipt reports 638 formal modules and a conditional-verification pass.
It does not assert an unconditional proof of Type III or of the bound 182.
It reused pinned dependency objects and valid existing project artifacts,
rebuilding changed sources.

Paths inside the receipt refer to the original run layout. Local build logs
and compiled objects are not distributed. To produce all outputs in their
original layout, run the [repository verifier](../../../docs/verification.md).
The supplied source files and manifests can be checked against the hashes in
this receipt without accessing the producing machine.
