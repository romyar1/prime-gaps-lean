# Verification status

## September 18 Type III integration — 3 October 2026

The September 18 source packet has been integrated into this existing
repository: 280 new formal modules and one updated existing module, for
918 development modules. The entry
[`computedTypeIIIInput`](formal/TypeIIICoherentUniformApplicationsFromGeneralStandardTheory03.lean)
derives the original `HasFiniteExceptionalTypeIIIInput` from the explicit
common general-theorem interfaces described in the
[cited derivation](docs/type-iii-published-general-application.md).

**Full local verification passed**, with status
`PASS_CONDITIONAL_DEVELOPMENT_AND_TYPE_III_SUPPORT`: all 918 development
modules and the unchanged baseline were freshly compiled, and 6,128 distinct
declarations were audited. All seven required terminal declarations, including
`computedTypeIIIInput`, use only standard logical axioms. One documented
nonterminal convenience wrapper retains its approved baseline estimates.

All 30 regression tests, the 16 numerical-input integrity checks, and the
external numerical-package attachment checks passed. The complete local run
took about 91 minutes. The [verification evidence](provenance/release_checks/20261003/README.md),
[full receipt](provenance/release_checks/20261003/receipt.json), and
[explicit premises](provenance/release_checks/20261003/explicit_premises.log)
are retained in the repository.

This verifies an identical isolated build copy on Apple Silicon macOS. The
refreshed source and declaration manifests are integrated here. No new hosted
Linux/GitHub Actions verification result is claimed by this local receipt.
The earlier receipts below remain historical.

The common continuous-adic interpretation and applicability of the published
theorem interfaces remain external mathematical inputs. The 262 numerical
inequalities and the three established finite-field estimates remain explicit
premises. This update does not claim an unconditional Lean proof of 182.

## External numerical package update — 9 September 2026

The [external acceptance receipt](research/numerical_182/evidence/verification.json)
reports `PASS_COMPLETE_EXTERNAL_NUMERICAL_RECOMPUTATION`: all 262 target
comparisons, 14 production stages, 14 implementation audits and four deliberate
rejection controls passed. The full production run took approximately 1 hour
44 minutes with three workers on the tested Apple Silicon Mac. See the
[package guide](research/numerical_182/README.md) for programs, evidence,
runtime limitations and reproduction commands.

This source update preserves every Lean source file and dependency pin from
posted commit `78e052bd50e64a34f58866b8b306844b72926c60`. It adds documentation,
external numerical tools and evidence, and attachment-integrity checks.
**No fresh full Lean build is claimed for this documentation/tool update.**
The hosted Lean verification below applies to the earlier audited snapshot;
its receipts remain historical records. The new integrity job checks stored
numerical evidence and target identity without repeating integrations.

**Lean numerical premises discharged: 0. Type III proved: no.** The ordinary
mathematical reduction from these numerical algorithms to the named integrals
also remains subject to review. The conditional theorem's scope is unchanged.

## Prior hosted Lean verification

The prior hosted repository snapshot passed a fresh verification on
**7 September 2026 (UTC)** at commit
`73d33fe6451d1054cc569943eadad83c906a9551`, with
status `PASS_CONDITIONAL_DEVELOPMENT_AND_TYPE_III_SUPPORT`.

- Lake freshly rebuilt all 638 development modules and the vendored
  `PrimeGaps186` baseline. Pinned dependency objects were reused; project proof
  objects were rebuilt after cleaning this package.
- The independent declaration audit checked the full types and axiom sets of
  4,916 distinct declarations. Of these, 4,915 use only standard logical axioms;
  one explicitly identified convenience wrapper uses two public baseline
  estimates. Both conditional 182 endpoints use only standard logical axioms.
- All 16 supporting numerical-data records passed the provenance and payload
  integrity checks. These checks do not prove the integral inequalities.
- All 25 verifier regression tests passed.

The verifier checked that the sources, configuration, dependencies, numerical
records, and proof artifacts remained unchanged during the audit. See the
[verification guide](docs/verification.md) for reproduction commands and the
scope of the checks. The [successful hosted run](https://github.com/romyar1/prime-gaps-lean/actions/runs/34143288525)
finished at **19:16:07 UTC**, after 2h 49m 23s. Its artifact
`lean-verification-34143288525-1` contains the fresh-build receipt and logs.
Resource settings and measurements are described in the [CI guide](docs/ci.md).

The earlier local [receipt](provenance/release_checks/20260905/receipt.json)
from 5 September, with its [theorem-type audit](provenance/release_checks/20260905/theorem_types.log)
and [explicit premises](provenance/release_checks/20260905/explicit_premises.log),
is retained as historical verification evidence.
This snapshot includes the
[derivation from published geometric inputs](research/type_iii/published_inputs/README.md).
The general trace, weight, perverse-support, Fourier, local-monodromy and
complexity laws are explicit hypotheses. Lean derives the corrected
all-extension covariance, the local phase calculation from supplied exact
maps, exclusion of proper Fourier supports in the distinct case, and both
original Type III estimates with uniformly quantified constants.

This is not yet a deduction from published theorems alone. The physical
construction derives the categorical image, rank six, lissity, purity and
signed trace from generic cohomological laws and the rank-three arithmetic
boundary model. The literal starting source recipe, its uniform complexity
cap, and the identification of the local representations with that same
physical family remain application obligations. Weil structures are kept
separate from geometric objects; local Fourier is restricted to its
admissible representation category. These are explicit mathematical inputs,
separate from the checked consequences.
The [application bridge](formal/TypeIIIPublishedApplicationBridge.lean) and
[combined theorem](formal/TypeIIIPublishedTypeIII.lean) record the exact boundary.
The Type III results described here belong to that audited source snapshot;
the external numerical update does not add a new Type III proof.

The audited foundational work includes the actual Artin–Schreier character
sheaf over commutative coefficient rings in which `p` is invertible.
Its actual geometric stalk is free of rank one, its geometric Frobenius
trace is `ψ(Tr(f(K)))`, and it becomes constant on the actual cover.
The finite cyclotomic coefficient levels, primitive characters, and
surjective reductions are constructed. Their actual sheaf maps satisfy
identity and composition and form an inverse system of additive sheaves.
The canonical extension-of-scalars comparison is an isomorphism,
including for every finite reduction, and its adjoint is the original
coefficient map.
The coefficient-ring inverse limit has its universal property and compact
Hausdorff, totally disconnected topology. It is finite free of rank `p−1`
over `Z_ell`, with its original finite projections inducing the proved
quotient identifications modulo `(ell^(n+1))`. The existing topology is
`(ell)`-adic; the ring is Noetherian, complete and separated for this ideal.
The actual limit-coefficient sheaf has canonical tensor comparisons to
the finite sheaves, whose restrictions form an inverse system of
limit-ring module sheaves with a compatible cone.
The actual extension-by-zero
functor preserves short exact sequences. All these declarations use only
standard logical axioms. The fixed affine phase family and its exact
normalized Kloosterman trace-sum identity remain included in the audit.
The same phase family now has an actual dense open immersion into the
projective plane over its parameter line, with a proper projection,
the unchanged projection and phase identities, and exact extension by
zero along that immersion.
The actual small-étale direct image is additive and left exact. Genuine
injective resolutions construct its right derived functors, including
`R^n barπ_*(j!F)` for this fixed compactification, with the canonical
degree-zero comparison.
Actual inverse image is constructed from the original direct-image
adjunction. Its geometric-stalk comparison proves exactness. The
canonical derived base-change map is constructed from the actual
ordinary mate and an exact-source resolution comparison; its degree-zero
component agrees with the original mate. For monomorphic étale base
change, that same map is an isomorphism in every degree, including for
the unchanged compactification and its original extension by zero.
The original finite-level tower in the fixed coefficient-limit module
category gives an inverse system under each derived-image functor.
Every level remains annihilated by its stated power of `ell`.
Extension by zero now commutes with arbitrary scheme inverse image.
Actual global sections and their right derived functors identify the
target of the geometric-point comparison with cohomology of the literal
fiber. The degree-zero comparison agrees with the original ordinary
mate through both canonical zero isomorphisms. For the fixed phase
family, the pulled-back open is identified with the original phase
projection fiber, and the same comparison respects the original finite
coefficient reductions and torsion exponents.
Every specified residue-field homomorphism of an arbitrary étale algebra
over a Henselian local ring lifts uniquely through the actual residue
map. The standard étale presentation is obtained by localization. The
same lifting theorem holds for arbitrary étale schemes, without an affine
or separated hypothesis. Over a strictly henselian local base, the
original closed-point stalk is global sections. This proves exactness of
global sections and vanishing of positive cohomology. For any scheme
over this base the closed-point stalk of its relative derived image is
the cohomology of the whole source; comparison with its closed fiber
remains separate. For a universally closed map to a local base, an open
containing the actual closed fiber is the whole source. In particular,
étale sections are determined by their closed-fiber restrictions.
The original closed-fiber restriction on global sections of every module
sheaf is also injective. A finite étale map to a proper scheme over a
local base is an isomorphism exactly when its actual closed-fiber base
change is an isomorphism. Idempotents lift uniquely across henselian
pairs, and coprime monic factorizations of prescribed ordered degrees
lift uniquely across the residue map of a henselian local ring. The
original coefficient reductions are retained.
Finite-module Cayley–Hamilton and the actual coprime-factorization
theorem now prove unique lifting of idempotents in finite algebras over
the henselian local base. Finite descent of the ideal-membership witness
extends this to every integral algebra. The original quotient `A → A/mA`
is bijective on idempotents, and its actual prime-spectrum pullback is an
order isomorphism on clopens. The inverse agrees with the unique lifted
idempotent. The integral algebra need not be finite, nonzero, free, local
or henselian. The original affinization of a proper scheme over an
affine base is proper and surjective, and its original structure-sheaf
map is an isomorphism. Pullback across a nilpotent quotient is bijective
on global idempotents. An idempotent on the zeroth infinitesimal
neighborhood determines a unique compatible family on all the actual
neighborhoods, with their original restriction maps. Separately, a
linear map out of an adic completion has the same range on the original
module if an ideal power annihilates its target and the ideal is
finitely generated. The original section restrictions now construct the
canonical map from completed global sections to compatible sections of
the actual infinitesimal schemes. Its coordinates and normalization are
proved. For affine schemes, the original restriction is surjective with
the expected ideal-power kernel, and this same completion map is a linear
equivalence without finite-generation or Noetherian hypotheses. The
original idempotent family then has a completed preimage. For a general
proper scheme, surjectivity of the comparison remains unproved.
Global idempotents and clopens descend from a given cofiltered limit of
qcqs schemes with affine transition maps, and equal representatives agree
at a common later stage. All maps are the original limit projections and
section restrictions. This does not construct proper Noetherian models
or prove proper nonaffine clopen lifting.
The existing ordinary right derived functors are naturally identified
with bounded-below derived-category cohomology, using the same injective
resolutions. Their degree-zero comparison agrees with the actual
derived-functor unit. The bounded-below functor is triangulated, and actual
short exact sequences give natural connecting maps and the long exact
sequence for the original ordinary derived functors. The actual comparison
for a resolution by acyclic objects is a quasi-isomorphism after applying
the left exact functor. Consequently the same derived base-change map is
invertible if its ordinary mate is invertible and the exact source functor
sends injectives to objects acyclic for the target functor. These
geometric hypotheses remain explicit.

The actual skyscraper functors and their small products are exact and
have zero positive global cohomology. Products at actual geometric
points also have zero positive relative derived direct image along every
scheme morphism. The original stalk-adjunction units give a canonical
Godement embedding, and every injective sheaf is an actual retract of
that same product. Coefficient restriction is exact and commutes with
the original skyscrapers and products through their actual projections.
These results prove acyclicity of restricted injectives, so the original
global and relative derived coefficient comparisons are isomorphisms
for arbitrary ring homomorphisms. Their original section identities and
degree-zero augmentation squares are retained. The actual coefficient
coextension adjunction also proves the comparison for the original
extension by zero. Consequently the unchanged composite
`R^n barπ_*(j!F)` commutes with coefficient restriction, with its original
forward map and full degree-zero square. At each finite torsion level,
the derived image computed in that finite coefficient category restricts
to the corresponding object of the existing common-coefficient tower.
The original derived comparisons satisfy composition and transformation
laws, using the original resolution homotopies and homology comparisons.
Transitions defined directly from the finite sheaf reductions and
inverse coefficient comparisons satisfy composition within the finite
coefficient categories. After the original scalar restrictions, the
levelwise comparisons form an isomorphism with the original inverse
system, respecting every reduction map.

Powers of `ell` act injectively on the original coefficient limit. The
original finite coefficient reductions have their stated power-ideal
kernels. The projected identity sections prove the coefficient-map
square on actual geometric stalks. These facts give the original
Artin–Schreier short exact sequence, with multiplication by `ell^(n+1)`
and the unchanged limit-to-finite reduction. The original exact `j!`
and derived projection give the Bockstein long exact sequence, including
the objects computed in their actual finite coefficient categories.
The original reductions and canonical connecting maps form natural
transformations of inverse systems, and all three consecutive triples
are exact in that functor category. The next-degree ordinary terms have
the complementary-power transitions `ell^(n-m)`. No inverse limit is
taken in this construction. Cohomology through the inverse limit and
the required adic comparisons remain unproved; see the
[coefficient note](research/type_iii/geometry/coefficient_bockstein_scope.md).

The earlier centering estimate remains checked: for distinct row indices,
subtracting the row-pair means changes the original coefficient by at most
`32p³` at every frequency. The remaining centered coefficient is not estimated.
Invertibility of the constructed proper stalk-to-fiber cohomology map
remains unproved, including the needed geometric acyclicity and existence
of étale section extensions from the closed fiber. The foundational adic and
trace comparisons, normalized rank-three Kloosterman sheaf, and purity
remain unproved. The new conditional Type III derivation does not instantiate
these objects or discharge its separate family application data. Further working modules require
their own completed audit before inclusion in the snapshot counts above.
The hypotheses and limits are recorded in the
[Type III progress map](docs/type-iii.md).

## Mathematical scope

The endpoint in [PrimeGaps182Analytic.lean](formal/PrimeGaps182Analytic.lean) is
conditional on:

1. 262 fixed physical integral inequalities;
2. the established rank-three Kloosterman bound and rank-two correlation bound;
3. the established scalar rank-four Kloosterman bound;
4. the Type III local Fourier hypothesis, with constants uniform in the prime
   and residue parameters.

The first three categories are explicit premises. The fourth has a conditional
derivation from the published-rule interfaces and actual-family application
data, but those inputs have not all been discharged. The precise statements
and numerical count appear in
[the assumptions guide](docs/assumptions.md).

No status reported here asserts an unconditional formal proof of the
prime-gap bound 182. In particular, standard-only logical axiom reports do
not prove a theorem's mathematical premises.

## Package scope

- Lean: `leanprover/lean4:v4.34.0-rc2`.
- Mathlib: `bbcd1968ee6950abe88b85dba6995da346c4b2a8`.
- Current audited development: 918 Lean modules, plus the vendored `PrimeGaps186` baseline.
- Diagnostics: two separate baseline inspection modules.
- Supporting numerical data: 16 JSON records, with original and published
  hashes and a canonical check of the preserved non-path payload.

The current target `PrimeGap182.TypeIII.HasFiniteExceptionalTypeIIIInput` is
derived by `CoherentUniformApplicationsFromGeneralStandardTheory03.computedTypeIIIInput`
from the common general-theorem interfaces. The joint continuous-adic
interpretation remains external, so this is a conditional derivation.
See the [cited derivation](docs/type-iii-published-general-application.md)
and [Type III progress map](docs/type-iii.md) for the exact scope.
