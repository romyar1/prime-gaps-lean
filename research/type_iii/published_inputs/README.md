# Checking Type III from published results

The present route treats established geometric theorems as explicit Lean
hypotheses and checks their consequences for the original Type III estimate.
It does not continue the construction of the full étale and adic foundations.
Type III work is paused at the upload snapshot while the numerical integral
premises are investigated.
The original finite sums and the original `LocalFourierHypothesis` are unchanged.

The support exclusion and the passage from stalks to the two Fourier estimates
are formal deductions. The physical construction also derives the rank-six
image, purity and corrected trace from explicit general cohomological laws
and the rank-three arithmetic local model. **A deduction from published
theorems alone is not yet complete:** the source recipe, its uniform complexity,
and the identification of the local representations with that same physical
family remain application obligations.

Every imported rule is an ordinary parameter of a Lean theorem or structure.
There are no new global axioms. An axiom audit using only `propext`,
`Classical.choice`, and `Quot.sound` checks the implication, not its parameters.

## What the conditional argument proves

For a nonempty subset of the four corrected factors, let `P` denote its
intermediate extension from the unit torus to the plane, and let
`Q = FT(P)`. Fourier transform uses the positive additive character, the
cohomological shift `[2]`, and no Tate normalization.

1. **Coefficient symmetry.** The literal corrected trace is checked over every
   finite extension. At degree `d`, each factor has sign `(-1)^(d+1)` and
   correction `1+q⁻¹+q⁻²`. A single coefficient automorphism sending the
   prime-field character `ψ(t)` to `ψ(2t)` changes the physical arguments to
   `(x/4,y/4)`. A precise Chebotarev hypothesis, with geometric semisimplicity
   and intermediate extension, converts this all-extension identity into a
   geometric isomorphism. Generic Fourier functoriality then gives
   `coefficient(Q) ≅ [8]*Q`.
2. **Reduction of proper supports.** The union of proper simple-constituent
   supports is invariant under dilation by eight. Published complexity bounds
   put it inside the zero set of a polynomial of bounded degree `D`. For
   `p > 8^D`, the proved polynomial argument puts every curve component in an
   origin line. The analogous finite-orbit argument puts punctual components
   at the origin. Individual constituents need not be fixed by dilation.
3. **Distinct rows and columns.** Radial inertia is taken at `t=0`; after
   `t=T²` the characters have the form `AS(β/T)`. The checked radical-phase calculation excludes
   zero and every coefficient `c/sqrt(a+bz)` with `c≠0`. Generic Fourier
   inversion and restriction rules show that a punctual or origin-line Fourier
   constituent would supply exactly such a phase. Thus all simple constituents
   of `Q` have full surface support. This is a proved exclusion, not a field
   of the imported theorem record.
4. **Stalks and estimates.** BBD's strict support rules now make ordinary
   `H⁻¹(Q)` finitely supported and `H⁰(Q)=0`. With repeated indices, the
   permitted support is a curve in degree `−1` and the origin in degree `0`.
   Deligne's weights and quantitative sheaf bounds give the trace envelopes.
   The exact corrected-product expansion and physical boundary estimates then
   recover both bounds for the original four-cycle.

The numerical endpoint fixes every constant before choosing the prime and
the five residue parameters. For uniform stalk bound `B`, physical exceptional
cardinality `R`, and core exceptional bound `D`, use of the whole physical
torus gives

```
C = 81 + 175 B (3 + R) + 13122,     exceptional bound = 15 D.
```

The constant is positive even if `B=0`. Its size is immaterial to the
existence statement. The uniform characteristic cutoff must dominate both
the proper-support degree and the punctual-support cardinality cutoffs.

## Imported results and their precise role

| Published input | Role in the Lean interfaces |
| --- | --- |
| Deligne, [Weil II](https://publications.ias.edu/sites/default/files/Number40.pdf), Corollary 3.3.6 and §§6.2.2–6.2.4 | Purity of the parabolic image; the upper weight of ordinary degree `i` is the complex weight plus `i`. |
| Beilinson–Bernstein–Deligne, [Faisceaux pervers](https://publications.ias.edu/sites/default/files/Faisceaux%20pervers.pdf), Corollaries 1.4.24–25 and 5.3.2, Theorems 4.3.1 and 5.3.8 | Intermediate extension, simple supports, strict boundary support, and geometric semisimplicity. |
| Laumon, [Transformation de Fourier](https://www.numdam.org/article/PMIHES_1987__65__131_0.pdf), §§1.2–1.3, §2.3.2 and Theorem 2.4.3 | Fourier equivalence and linear-map compatibility; the finite-origin exact sequence and local Fourier theory. |
| Katz–Laumon, [Transformation de Fourier et majoration de sommes exponentielles](https://www.numdam.org/article/PMIHES_1985__62__145_0.pdf), Theorem 2.2.1 | The unnormalized shifted plane transform adds two to the pure weight. |
| Fu, [Calculation of ℓ-adic local Fourier transformations](https://arxiv.org/pdf/math/0702436v5), Proposition 0.8 and Theorem 0.1(iii) | Kloosterman local models and the monomial local transform, here with `r=3,s=1,p>3`. |
| Chebotarev and geometric semisimplicity, as used in Katz, [Moments, Monodromy, and Perversity, §6.7.10](https://web.math.princeton.edu/~nmk/mmp/chpt6midconv78.pdf#page=46) | All-extension traces identify arithmetic semisimplifications; geometric semisimplicity and intermediate-extension uniqueness give the required geometric isomorphism. |
| Sawin–Forey–Fresán–Kowalski, [Quantitative sheaf theory](https://arxiv.org/pdf/2101.00635v4), Theorems 6.8, 6.15, 6.23; Proposition 6.24 and 7.18 | Uniform complexity, constituent, ordinary-support, and Fourier bounds. Monotonicity of their bound functions is not assumed. |
| Grothendieck's trace formula, Deligne's [SGA 4½, Rapport](https://publications.ias.edu/sites/default/files/Number32.pdf), Theorem 3.2 | The trace of the actual positive-kernel Fourier transform is the unnormalized finite Fourier sum. |

The [support and weight audit](support_and_weights_audit.md) and
[local-monodromy audit](local_monodromy_audit.md) give the hypotheses and
application checks, including the coefficient scope of Laumon's lissity
theorem. The [covariance audit](covariance_audit.md) gives the precise
Chebotarev and normal-base semisimplicity locators. The finite-origin sequence points **from the actual core to the local
Fourier contribution**; the checked rank argument inverts that map after
proving it bijective.

## Remaining actual-family identifications

The imported general theorems do not, by themselves, name the arithmetic
objects used in the paper. Three groups of application data remain visible:

- **The starting geometric realization:** the cohomology operations, original
  three input traces and rank-three arithmetic boundary model must describe
  the specified Kl3/AS construction. From these data and generic laws, Lean
  constructs the actual categorical image and proves its rank, lissity,
  purity and signed trace, followed by physical pullbacks, tensors and IC.
  The literal universal source recipe and its uniform complexity cap remain.
- **The local representations:** generic cubic-cover Mackey laws and the
  finite-origin exact sequence now construct the local input from the
  infinity model and generic rank. That perverse object and its natural maps
  must still be identified with the same physical family. Fu's formula,
  exactness, rank exhaustion and the radical calculation then give the
  complete phase list.
- **Compatibility of the interfaces:** the coefficient action, Fourier functor,
  inertia restriction, geometric dimensions, and rational Frobenius spectra
  must describe the same objects. The current abstract records do not silently
  assert an instance in the unfinished foundational development.

In particular, the all-extension trace formula and local realization are not
being replaced by assumptions that already assert the Fourier bound or the
absence of its exceptional constituents. The
[whole-torus construction note](../geometry/relative_core_lissity.md) supplies
the mathematical derivation of the physical family; it is not yet an
instantiation of all these records in Lean.

The arithmetic stalks are indexed by chosen Weil structures. Arbitrary
geometric constituents are not assumed to have Frobenius operators over the
prime field. The all-extension trace and prime-field stalk trace belong to
the same Weil lift. Local Fourier is defined only on its specified admissible
representation category, with a nonzero scale; no functor on all abstract
representations is assumed.

The physical torus is an actual integral reduced scheme, proved equivalent
to the spectrum of a two-variable Laurent polynomial ring. The physical
map is an actual morphism with a proved degree-six polynomial presentation.
QST Proposition 6.21 therefore gives its morphism-complexity bound. Separately,
the uniform-complexity module derives all seven numerical support/stalk
bounds from one physical complexity cap and shared published bound functions.
That cap is still to be deduced from the fixed source construction; bounded
rank alone does not supply it.

## Code map

| File | Checked deduction |
| --- | --- |
| [Corrected trace covariance](../../../formal/TypeIIICorrectedTraceCovariance.lean) | Literal finite sums, correction, extension sign, and a fixed coefficient action over all extensions. |
| [Parabolic exact sequence](../../../formal/TypeIIIPublishedParabolicTrace.lean), [actual trace coordinates](../../../formal/TypeIIICoreTraceCoordinates.lean) | Rank six and the signed corrected trace from the supplied cohomology maps; literal reindexing and physical parameter substitution. |
| [Published covariance rules](../../../formal/TypeIIIPublishedCovarianceRules.lean) | Geometric coefficient/Fourier covariance from the trace identification and generic rules. |
| [Local phase sets](../../../formal/TypeIIIPublishedLocalPhases.lean), [Fu coordinates](../../../formal/TypeIIIFuPhaseCoordinates.lean), [tensor application](../../../formal/TypeIIIFuTensorApplication.lean) | Finite phase sets, exactness/rank exhaustion, and the scalar substitution and sum laws. |
| [Local representation application](../../../formal/TypeIIIPublishedPhaseApplication.lean) | Actual finite-dimensional representations, finite-origin maps, Fu's general rule, rank exhaustion, tensor products, duals and subquotients. |
| [Mackey construction](../../../formal/TypeIIIPublishedMackey.lean), [local construction](../../../formal/TypeIIIPublishedLocalConstruction.lean) | The correlation decomposition and original finite-origin maps from generic laws on admissible representations. |
| [Physical construction](../../../formal/TypeIIIPublishedPhysicalConstruction.lean) | Literal categorical image, rank six, lissity, purity, arithmetic correction, actual physical pullback, tensor products and IC outputs. |
| [Physical scheme morphism](../../../formal/TypeIIIPhysicalTorusMorphism.lean), [Laurent identification](../../../formal/TypeIIIPhysicalTorusLaurent.lean), [polynomial complexity](../../../formal/TypeIIIPublishedPolynomialComplexity.lean) | Genuine torus and morphism, reducedness and integral structure, degree-six presentation and its generic QST application. |
| [Line-phase descent](../../../formal/TypeIIILinePhaseDescent.lean) | The finite invariant rescaled phase set produces a forbidden constant-field coefficient. |
| [Support components](../../../formal/TypeIIIInvariantSupportComponents.lean), [published Fourier rules](../../../formal/TypeIIIPublishedFourierRules.lean) | Origin-line reduction and the novel exclusion of proper Fourier constituents. |
| [Published support rules](../../../formal/TypeIIIPublishedSupportRules.lean), [rational support](../../../formal/TypeIIIPublishedStalkSupport.lean) | Ordinary-cohomology support and the actual prime-field cardinality restriction. |
| [Common stalk certificate](../../../formal/TypeIIIPublishedStalkCertificate.lean) | Torus boundary, physical support, dimensions, weights, and Fourier trace. |
| [Stalk assembly](../../../formal/TypeIIIStalkAssembly.lean), [uniform criterion](../../../formal/TypeIIIUniformStalkCriterion.lean) | Both original Fourier estimates, with all constants uniformly quantified. |
| [Combined Type III theorem](../../../formal/TypeIIIPublishedTypeIII.lean), [application bridge](../../../formal/TypeIIIPublishedApplicationBridge.lean) | The original uniform Type III conclusion; its phase and covariance fields supplied by the preceding deductions. |
| [Uniform complexity](../../../formal/TypeIIIPublishedUniformComplexity.lean) | All seven numerical application bounds from a single physical complexity cap, without assuming monotonicity of the QST functions. |

Use the repository's [verification guide](../../../docs/verification.md) and
[current receipt](../../../STATUS.md) for the checked snapshot and reproduction
command. No claim here discharges the numerical integral premises of the
prime-gap theorem or asserts an unconditional Lean proof of the bound 182.
