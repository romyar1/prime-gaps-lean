# Lean interface audit for conditional Type III

This is a source-level audit of the unchanged `LocalFourierHypothesis` and
the arithmetic, phase, and support lemmas used by the published-input route.
The conditional deductions are checked; the actual sheaf realization remains
explicit application data. The companion literature audits give the primary
theorem statements and their hypotheses.

## 1. What the existing assembly actually proves

`TypeIIIFiniteAssembly.finiteExceptionalFourierBound_of_actual_core_bounds`
combines fifteen bounds for the **actual** corrected subproducts. Given core
constant `C`, physical-complement bound `2*Dphys*p`, and exceptional cardinality
`Dcore`, its output is the original finite branch with constant

```
81 + 175*C + 13122*Dphys
```

and exceptional cardinality at most `15*Dcore`. The coefficients 81 and 175
come from the exact four-factor expansion and `coreCorrection = 1+1/p+1/p²`.
The raw boundary estimate uses the explicit `BaselineLocalInputs`.

The fifteen `hcore` inequalities are not established by that assembly. Calling
them published trace-theorem assumptions would obscure the main problem.

`TypeIIIRepeatedReduction` proves the exact transpose and reduces repeated
columns to repeated rows. Its `curveExceptional_of_nonzero_frequencies`
handles the origin from the baseline `6561*p⁴` estimate, but its remaining
nonzero-frequency hypothesis is still the desired estimate. The new
`TypeIIIStalkAssembly` instead derives that branch from stalk spectra,
weights and supports, as described below.

## 2. The smallest useful arithmetic interface

Separate the numerical implication from its geometric realization. For each
nonempty corrected subproduct, provide actual finite Frobenius spectra in
ordinary degrees `-2,-1,0` for a physical complex `P` and transformed complex
`Q`. The records should carry eigenvalues with multiplicity and their
alternating traces; they should not carry a Fourier norm bound.

The explicit obligations are:

1. The physical trace equals the original corrected subproduct on `U`.
2. `trace Q(h,k) = fourier₂ p (trace P) h k`, with the existing positive,
   unnormalized Fourier convention.
3. Every block has dimension at most one prime-independent integer `B`.
4. Physical eigenvalues in degrees `-2,-1,0` have bounds
   `p²`, `p²*sqrt p`, `p³`. Physical degree zero vanishes; physical degree
   minus one is supported on a set of cardinality at most `Rphys`.
5. Transformed eigenvalues have bounds `p³`, `p³*sqrt p`, `p⁴`.
6. In the distinct branch, transformed degree zero vanishes and degree
   minus one has finite support of cardinality at most `Dcore`.
7. In the repeated branch, transformed degree zero is supported at the
   origin and degree minus one on the zero set of an actual nonzero
   polynomial of degree at most `Dcore`.
8. The complement of `U` has at most `2*Dphys*p` rational points.

These imply, by finite-sum inequalities alone, a core constant
`B*(1+2*Dphys+Rphys)`. The sparse physical degree-minus-one support is
essential: finitely many physical boundary stalks may have size `p^(5/2)`.
The existing aggregate boundary theorem accounts for them correctly.

The new root-owned `TypeIIIFrobeniusTraceBounds` realizes the numerical
records and derives trace envelopes. `TypeIIIStalkAssembly` now derives the
actual restricted-core and raw envelopes from the explicit obligations above;
its strict check passed all fourteen declarations with standard axioms only.
These are conditional arithmetic theorems, not claims that the geometric
obligations themselves have been proved. The final endpoints are
`finiteExceptionalFourierBound_of_surface_stalks` and
`curveExceptionalFourierBound_of_surface_stalks`, with the same raw constant
`81 + 175*B*(1+2*Dphys+Rphys) + 13122*Dphys` and cardinality/degree bound
`15*Dcore`.

## 3. What may honestly be a published general input

An abstract sheaf interface must distinguish operations/data from theorems
about them. At minimum it needs meaningful lisse objects, inertia data,
intermediate extension, Fourier transform, ordinary stalk spectra, simple
constituent supports, and complexity. Its generic theorem hypotheses may
then state the following independently useful facts, with precise published
locators confirmed by the literature audit:

* The geometric trace formula for the actual compact direct image, including
  alternating signs and Tate twists.
* The rank-three Kloosterman construction, purity, zero monodromy, and
  infinity monodromy, with its normalization.
* Purity of the curve parabolic image and of intermediate extension;
  Fourier perversity, inversion, linear-map compatibility, and weights.
* The strict boundary condition of a full-support intermediate extension.
  This is stronger than generic lissity or full support of the entire object.
* Uniform complexity bounds for the specified operations, simple
  constituents, stalk dimensions, and support degrees/cardinalities.
* The precise local Fourier/stationary-phase decomposition, with its
  hypotheses and **exhaustion/rank** assertion. Exhibiting some phases is
  insufficient to exclude a hidden tame or zero-phase summand.
* Coefficient-change compatibility and preservation of support. This is a
  statement about geometric stalks, not invariance of complex absolute values.

The manuscript's Section 4 and the existing geometry audit notes identify
candidate sources: SGA 4½, Katz, BBD, Laumon, Katz–Laumon, Fu, and quantitative
sheaf theory. The actual rank-six family, the scalar covariance of that
family, and the exclusion of its proper Fourier constituents are **not**
generic published theorem statements. They must be derived using the general
inputs, or separately retained and named as unproved family-specific
obligations. A structure silently postulating those conclusions is not a
formal derivation from published results alone.

## 4. Existing family-specific deductions that can be reused

The following are already exact Lean theorems, not sheaf assumptions.

| Existing API | What it supplies | What it does not supply |
| --- | --- | --- |
| `TypeIIIGeometricAssembly.actual_fourCycle_core_expansion` and `actual_fourCycle_fourier_core_expansion` | Exact corrected/raw four-factor expansion | A trace realization or purity |
| `TypeIIIBaselineBridge.correlation_zero` | The full correction `1+1/p+1/p²` in the actual zero-frequency correlation | The corrected rank-six image sheaf |
| `TypeIIIFiniteFieldCovariance` | Exact changes of variables over arbitrary finite extensions; one coefficient automorphism for all extensions | Support invariance of a perverse Fourier transform or norm invariance |
| `CoefficientSheafSupport.stalkSupport_changeCoefficients` | Support preservation for the actual module-sheaf coefficient equivalence | An adic/perverse Fourier identification |
| `ScalingSupport.eight_invariant_finite_support` | A finite eight-invariant support of size at most `D` lies at the origin when `p>8^D` | Its invariance or its cardinality bound |
| `ScalingLines.eight_invariant_subset_line_cover` | A bounded-degree eight-invariant subset lies in at most `D+1` origin lines | That an individual support is an irreducible closed curve |
| `PhaseObstruction.rectanglePhaseAmplitude_ne_zero` | Noncancellation in every nonempty grouped rectangle phase for distinct rows/columns, including opposite-corner coincidences | Exhaustiveness of those phases in actual inertia |
| `PhaseObstruction.algebraicDistinctRectanglePhase_ne_linearReciprocalSqrt` | Every allowed phase differs from `d/sqrt(a+bz)`, `d≠0` | The support-to-descent inference for the actual transform |
| `AlgebraicDescent.rescaled_distinctRectanglePhase_infinite_orbit` | The corresponding coefficient has infinite orbit over the constant field | A geometric descent statement for a sheaf |
| `AlgebraicDescent.poleOneClass_finite_orbit_iff_constant` | The same obstruction for actual pole-one Artin–Schreier quotient classes | A local-inertia decomposition |
| `TypeIIIBoundary.physicalBoundaryFourier_norm_le_surface_weights` | Correct aggregate physical-boundary estimate | Weight and support premises |

The curve support lemma gives containment in a finite union of origin lines.
To conclude that a one-dimensional simple-constituent support is one whole
line, the interface must also provide actual closedness, irreducibility, and
dimension, or an equivalent generic support theorem. Containment alone is
not that conclusion.

## 5. The family bridge and its current proof boundary

The shortest coherent route uses the actual rank-six family on the entire
parameter torus, as described in `geometry/relative_core_lissity.md` and
`geometry/core_covariance_and_finite_support_audit.md`:

1. **Physical image.** `TypeIIIPublishedParabolicTrace` proves rank six and
   the signed trace from supplied exact cohomology maps, compact rank nine,
   and the compact trace formula. `TypeIIICoreTraceCoordinates` proves the
   literal parameter substitution and reindexing. Identifying those spaces
   and maps with `im(R¹f! F → R¹f* F)`, and applying whole-torus lissity and
   purity, remain actual-family data. Over `q=p^d` the trace is
   `(-1)^(d+1)(C_q+κ_q)`, not the unsigned prime-field expression.
2. **Conjugated factors.** The geometric phase calculation uses actual
   dual representations, with the original four-cycle orientation. The
   sheaf realization must use `H∨(-1)` to preserve weight one and the
   trace normalization; the Tate twist has trivial geometric inertia.
3. **Covariance.** `TypeIIICorrectedTraceCovariance` proves the literal
   all-extension identity. `TypeIIIPublishedCovarianceRules` applies the
   generic Chebotarev and Fourier laws to derive `τP ≅ s_(1/4)*P` and
   `τQ ≅ s_8*Q`. The whole-torus intermediate-extension realization and
   its all-extension trace identification are explicit inputs.
4. **Exhaustive radial phases.** `TypeIIIPublishedPhaseApplication` derives
   the complete profile, tensor and subquotient containment from Fu's
   general cubic rule and the supplied Mackey and finite-origin maps.
   The same arrow `H → V` is proved bijective by exactness and rank.
   `TypeIIIPublishedApplicationBridge` checks the four-cycle orientation.
   These maps must still be identified with those of the physical family.
   The generic angular parameter `λ=m/(nz³)` avoids 1; the specialization
   `λ=1` can have a tame remainder and is not asserted to have six wild phases.
5. **Proper-support exclusion.** `TypeIIIPublishedFourierRules` derives
   the absence of punctual and origin-line constituents from the generic
   inverse-Fourier and inertia-descent laws and the exact scalar phase
   obstructions. `TypeIIIInvariantSupportComponents` supplies the
   irreducible-curve step. The exclusion is a conclusion, not an input.
6. **Repeated indices.** The union of punctual supports is finite and
   invariant under dilation by eight. Its bounded cardinality and the
   characteristic cutoff put it at the origin. This route does not require
   a separate radial-infinity tameness hypothesis.
7. **Ordinary supports and weights.** The BBD/QST rules are applied to
   every simple constituent. `TypeIIIPublishedStalkSupport` and
   `TypeIIIPublishedStalkCertificate` derive the required rational supports,
   dimensions, weights and trace identities. `TypeIIIPublishedTypeIII`
   combines these with the proved exclusion to obtain both original bounds.
8. **Uniformity.** The final constants are quantified before the prime
   and residue parameters, with a safe cutoff dominating `8^D`. The
   bounds on the published complexity functions at the actual family
   objects are still application data. Bounded rank alone does not supply
   them, and no monotonicity of those functions is assumed.

The remaining work is therefore the actual-family realization and its
uniform complexity applications, as specified in the
[published-input guide](README.md). The conditional deductions above do not
provide an instance of the unfinished foundational geometric theory.

## 6. Scope of the conditional endpoint

A correct final implication can have the form

```
published_general_theorems -> proved_family_deductions ->
explicit_stalk_data -> LocalFourierHypothesis C D p0.
```

Some family identifications remain hypotheses in the current endpoint, so
it is not yet a derivation from established published results alone. The
original target and finite sums are unchanged.
