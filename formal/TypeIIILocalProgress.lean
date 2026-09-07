import TypeIIILocalAlgebra
import TypeIIIBoundary
import TypeIIIExactSpectrum
import TypeIIIRepeatedReduction
import TypeIIIRepeatedRadial
import TypeIIIFiniteAssembly
import TypeIIITraceIdentity
import TypeIIICoefficientCovariance
import TypeIIIScalingLines
import TypeIIICorrelationGram
import TypeIIIFiniteFieldCovariance
import TypeIIICenteredFourier
import TypeIIICoefficientSheafSupport
import TypeIIIArtinSchreierSchemeBaseChange
import TypeIIIArtinSchreierSchemeTorsor
import TypeIIIArtinSchreierCharacterStalk
import TypeIIIArtinSchreierSheafTrace
import TypeIIIArtinSchreierPointFiber
import TypeIIIArtinSchreierPointTrace
import TypeIIIArtinSchreierLocalTriviality
import TypeIIIArtinSchreierTorsionSheaf
import TypeIIIArtinSchreierTorsionTower
import TypeIIIArtinSchreierTorsionBaseChange
import TypeIIIArtinSchreierLimitSheaf
import TypeIIITorsionCoefficientLimit
import TypeIIITorsionCoefficientLimitTopology
import TypeIIITorsionCoefficientComplete
import TypeIIIEtaleExtensionExact
import TypeIIIEtaleDerivedDirectImage
import TypeIIIEtaleInverseImageStalk
import TypeIIIEtaleInverseImageComposition
import TypeIIIExactFunctorResolution
import TypeIIIDerivedBaseChangeIso
import TypeIIIEtaleDerivedBaseChangeZero
import TypeIIIEtaleDerivedOpenBaseChange
import TypeIIIEtaleRestrictionInverseImage
import TypeIIIEtaleInjectiveImages
import TypeIIIKloostermanTorsionDerivedTower
import TypeIIIKloostermanPhasePoints
import TypeIIIKloostermanCompactification
import TypeIIIKloostermanTorsionFiberTower
import TypeIIIEtaleGeometricFiberCohomologyZero
import TypeIIIHenselianEtaleLifting
import TypeIIIRightDerivedPlusComparison
import TypeIIIDerivedBaseChangeAcyclic
import TypeIIIStrictHenselianEtaleCohomology
import TypeIIIProperLocalClosedFiber
import TypeIIIEtaleDerivedAcyclicBaseChange
import TypeIIIProperFiniteEtaleDetection
import TypeIIIProperLocalSectionsInjective
import TypeIIIHenselianIdempotentLifting
import TypeIIIHenselianFactorizationLifting
import TypeIIIEtaleCoefficientDerivedDirectImage
import TypeIIIFiniteAlgebraClopenLifting
import TypeIIIIntegralAlgebraClopenLifting
import TypeIIIKloostermanTorsionCoefficientComparison
import TypeIIIKloostermanFiniteCoefficientComposition
import TypeIIIProperAffinizationStructureSheaf
import TypeIIIInfinitesimalIdempotentTower
import TypeIIIAdicCompletionRangeDescent
import TypeIIIInfinitesimalAffineCompletion
import TypeIIIAffineLimitIdempotentDescent
import TypeIIIKloostermanBocksteinSystem
import TypeIIIKloostermanDerivedTowerCohomology
import TypeIIIHomogeneousCoordinateIntersection
import TypeIIIPublishedApplicationBridge
import TypeIIIPublishedLocalConstruction
import TypeIIIPublishedPhysicalConstruction
import TypeIIIPublishedPolynomialComplexity
import TypeIIIPublishedUniformComplexity

#check PrimeGap182.TypeIII.PublishedTypeIII.UniformApplications.localFourierHypothesis
#check PrimeGap182.TypeIII.PublishedTypeIII.UniformApplications.hasFiniteExceptionalTypeIIIInput
#print axioms PrimeGap182.TypeIII.PublishedTypeIII.UniformApplications.localFourierHypothesis
#print axioms PrimeGap182.TypeIII.PublishedTypeIII.UniformApplications.hasFiniteExceptionalTypeIIIInput
#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.applicationOfTraceAndLocalData

/-!
# Checked progress toward the Type III local Fourier proposition

This entry collects the local algebra, exact finite-sum and Gram identities,
the actual Fourier centering error bound, boundary estimates, parameter and
coefficient symmetries over finite extensions, elementary support rigidity,
and conditional assembly results. The target remains the unchanged
`PrimeGap182.TypeIII.HasFiniteExceptionalTypeIIIInput`.

The published-input route proves the original Type III conclusion from explicit
generic BBD, Deligne, Laumon, Fu, Chebotarev and quantitative-sheaf laws, together
with separate actual-family realization data. It derives coefficient covariance
from all-extension traces, the radial phases from the supplied local maps, and
the proper-support exclusion and both uniform Fourier estimates. This is not a
closed proof of the target: actual geometric/cohomological identifications and
uniform complexity applications remain explicit. An axiom report for the
conditional theorem does not discharge these mathematical premises.
The complex coefficient automorphisms do not preserve absolute values in
general; their exact covariance does not by itself prove invariance of the
norm-based exceptional sets. The scaling lemmas require their stated
invariance and bounded-degree hypotheses.
The centering theorem removes an error of at most `32 p³` for distinct row
indices, but does not estimate the remaining centered Fourier coefficient.
The actual Artin--Schreier quotient is finite étale, with its torsor
trivialization and an actual character module sheaf over an arbitrary
affine base. The character average is an idempotent with an actual split
image. When `p` is invertible in the commutative coefficient ring, the
geometric stalk is the free rank-one character module, and restriction to
the actual cover is isomorphic to the categorical constant rank-one sheaf.
At a finite field-valued point, the trace of the point-induced geometric
Frobenius is the positive additive trace character of the specialized
phase. All stalk comparisons retain the original affine base.
Actual finite cyclotomic coefficient rings and their surjective reductions
carry compatible primitive additive characters. The corresponding sheaves
are locally trivial, and their actual Frobenius traces commute with
reduction. The actual coefficient maps satisfy identity and composition
and give an inverse system of additive sheaves on the same site.
The canonical extension-of-scalars comparison is an isomorphism for
character-compatible coefficient maps, including every finite reduction.
This follows from the actual free-sheaf comparison and split character
projectors; no flatness premise is required.
The coefficient-ring inverse limit is constructed as a compact Hausdorff,
totally disconnected topological ring with the actual coordinate universal
property. Its actual Padic scalar map gives a finite free module of rank
p-1, and its original level-n projection has kernel (ell^(n+1)) and is
surjective. The canonical quotient equivalence commutes with that same
projection. The existing topology is (ell)-adic and the ring is Noetherian,
complete and separated for this ideal.
The actual character sheaf over this ring has canonical tensor comparisons
with the finite sheaves. Its reduction maps give a compatible cone to the
original finite levels viewed as an inverse system of limit-ring modules.
The extension-by-zero functor on the actual small étale sites
has its inside and outside stalk formulas and preserves short exact
sequences for arbitrary coefficient rings.
The single affine phase family has all its field-valued points and its
projection fibers parametrized by the actual Laurent universal property.
Summing its character-sheaf stalk traces gives the original rank-three
Kloosterman function with the existing normalization.
The original phase family is the dense open chart D₊(XYZ) in the projective
plane over F_p[t]. Its unchanged projection factors through the actual
proper projection, and the homogeneous fraction (X²Y+XY²+tZ³)/(XYZ)
is identified with the original phase. The same embedding carries the
actual exact extension-by-zero functor with its geometric stalk formulas.
The actual direct image for any scheme morphism is additive and left exact.
Genuine injective resolutions give its right derived functors, including
R^n barπ_*(j!F) for this fixed compactification, as sheaves on the original
parameter line. The canonical degree-zero comparison is an isomorphism.
The actual inverse image is constructed from the direct-image adjunction.
Its geometric stalk is the stalk at the composed geometric point, and
conservativity of those points proves exactness. Actual scheme pullbacks
give direct-image composition isomorphisms and the ordinary base-change
map. An exact functor maps a genuine injective resolution to an exact
augmented complex; its comparison to the chosen resolution is natural
up to homotopy, without assuming that the mapped terms are injective.
It defines the derived base-change map for the actual commuting square.
In degree zero, this is the original ordinary mate under the canonical
identifications. If the ordinary map is an isomorphism and the exact
functor on its source sends injectives to objects acyclic for the target
functor, the same derived map is an isomorphism. The original comparison
chain map is proved a quasi-isomorphism under this explicit acyclicity
hypothesis; no homotopy equivalence is required.
For base change along an étale monomorphism, the actual ordinary mate is
proved invertible. The pulled-back inverse image preserves injectives,
so the same derived map is invertible in every degree. This result
includes the unchanged compactification, with its original j! retained.
The actual direct image preserves injectives by its exact left adjoint,
and restriction to an open object preserves injectives by exact extension
by zero. This restriction is identified with actual inverse image through
the proved site adjunction, including unit and counit compatibility.
The actual derived functors are additive. Applying the fixed
compactified derived functor to the original finite coefficient tower
gives an inverse system in every degree, still annihilated at level n
by ell^(n+1). This system is constructed in the fixed limit-ring module
category; no comparison with other coefficient categories is implicit.
Extension by zero commutes with arbitrary scheme inverse image. Actual
global sections and their right derived functors identify the target of
the geometric-point comparison with cohomology on the literal fiber.
In degree zero, the transported map agrees with the original ordinary
mate through the canonical zero isomorphisms on both sides.
For the unchanged compactification, the pulled-back phase open is
identified with the fiber of the original phase projection. The same
comparison maps the relative derived-image stalks to cohomology of the
actual proper fiber with this pulled-back extension by zero. It respects
the original finite coefficient reductions and their torsion exponents.
For an arbitrary étale algebra over a Henselian local ring, every
specified residue-field homomorphism lifts uniquely through the original
residue map. The standard étale presentation is obtained by localization;
it is not supplied as a hypothesis. Uniqueness already holds over a local
base ring. The lifting result also holds for arbitrary étale schemes.
Over a strictly henselian local ring the actual closed-point stalk is
global sections, so this global-sections functor is exact and its positive
cohomology vanishes. For any scheme over this base the same stalk of its
relative derived image is the cohomology of the whole source scheme.
This does not yet identify it with cohomology of the closed fiber.
For a universally closed morphism to a local base, an open containing the
actual closed fiber is the whole source. Consequently étale sections are
determined by their restrictions to that fiber. The actual closed-fiber
restriction on global sections of every module sheaf is also injective.
A finite étale map to a proper scheme over a local base is an isomorphism
exactly when its actual closed-fiber base change is an isomorphism.
Idempotents lift uniquely across a henselian pair, and coprime monic
factorizations with prescribed factor degrees lift uniquely across the
residue map of a henselian local ring. These are actual coefficient
reductions. Finite-module Cayley--Hamilton, coprime factorization and an
actual Bezout identity prove unique lifting of idempotents in every
finite commutative algebra over that henselian local base. Retaining the
finite ideal-membership witness descends the problem in any integral
algebra to a finite subalgebra. Thus the original quotient A -> A/mA is
bijective on idempotents for arbitrary integral A, and its actual
prime-spectrum inverse image is an order isomorphism on clopens.
There is no finiteness, nonzero, free, local or henselian hypothesis on A
in the integral result. Proper nonaffine clopen lifting and existence of
general proper closed-fiber section extensions remain to be proved.
The original proper affinization X -> Spec Γ(X) is proper and
surjective, its second factor is integral, and the original structure
sheaf map is an isomorphism. Global idempotents classify actual clopens.
The original restriction on global idempotents through a nilpotent
thickening is bijective. For every ideal I and scheme over Spec R,
an idempotent on X_0 has a unique compatible family on the literal
X_n = X × Spec(R/I^(n+1)), through the original section maps.
An original linear map out of an adic completion has the same range
on the original module when a power of its finitely generated ideal
annihilates the target. The original section restrictions now define
the canonical map from completed global sections to compatible sections
of the actual infinitesimal schemes. Its coordinates and normalization
are proved. For affine X it is a linear equivalence, without FG or
Noetherian hypotheses, and the original idempotent family has a
completed preimage. Surjectivity for general proper X remains unproved.
Given a cofiltered limit of qcqs schemes with affine transition maps,
actual global idempotents and clopens descend to a stage. Equal
representatives agree after restriction to a common stage. This uses
the original limit projections and does not construct proper Noetherian
models or prove proper formal functions.
The existing right derived functors are naturally identified with
cohomology of the bounded-below derived functor on objects concentrated
in degree zero. The comparison uses the same injective resolutions, and
its degree-zero map intertwines the original augmentation with the
actual derived-functor unit. The bounded-below derived functor is proved
triangulated, giving natural connecting maps and the long exact sequence
for the original ordinary right derived functors. These exact sequences
prove that the original comparison for a resolution by acyclic objects
computes the same derived functors.
The original skyscraper functors and their small products are exact.
These actual products have zero positive global cohomology. Products
at geometric points also have zero positive relative derived direct
image along every scheme morphism.
The canonical product of stalk-adjunction units is a monomorphism,
detected by the proved conservative geometric-point family. Every
injective sheaf is therefore an actual retract of this Godement product.
Restriction along any coefficient-ring homomorphism preserves these
products and the original projections. This proves acyclicity of
restricted injectives and makes the original coefficient comparison
an isomorphism for global cohomology and relative derived direct images.
The original section identities and degree-zero augmentations are
retained; no flatness or injective-preservation premise is required.
The actual coefficient coextension adjunction also proves that
restriction commutes with the original extension by zero. Composing
these comparisons gives the original coefficient comparison for
R^n barπ_*(j!F), with its full degree-zero augmentation square. At each
finite torsion level the actual derived image in that finite coefficient
category restricts to the same object of the original common-coefficient
tower. The original derived comparisons satisfy pasting and
transformation laws, and both original coefficient comparisons respect
composition of ring maps. The finite-category transitions are defined
directly by applying the original derived functor to the original
finite sheaf reduction, then the original inverse coefficient comparison.
They compose with the original scalar-composition maps. After actual
restriction to the common coefficient ring, these transitions form an
inverse system and the original levelwise comparisons give an isomorphism
with the existing tower, respecting every reduction map.
Regularity of ell on the original coefficient limit and the exact
kernels of its original finite projections give the original
Artin--Schreier coefficient short exact sequence. The actual projected
identity generators prove its stalk square, so no extra stalk-exactness
premise is supplied. Extension by the original j! and the original
derived projection give the Bockstein long exact sequence. The original
coefficient comparisons give its finite-category torsion term, retaining
all three exact triples. The original sequence transitions give the
complementary power ell^(n-m) in connecting-map naturality.
The original scalar, finite reduction, and connecting maps form natural
transformations of the actual inverse systems. All three consecutive
triples are exact in the functor category. The next-degree terms use
the proved complementary-power transitions. That exact-sequence
construction does not take an inverse limit.
Separately, the actual category of sheaf-valued towers is Grothendieck
abelian. The original categorical limit and pointwise direct image
preserve injectives, by their original adjunctions and the exactness of
their left adjoints. The ordinary limit/direct-image comparison gives
the original total-derived comparison Rq_* Rlim_X = Rlim_S RQ, with the
same ordinary map and the same derived units. The Kloosterman input is
the actual tower extended by j! before resolving it. Its full derived
objects have an original resolution presentation and respect the
independently constructed finite-coefficient extended tower.
Evaluation is exact and preserves injectives. Its original derived
comparison is natural in the coefficient index. Consequently the full
derived tower has the existing finite-coefficient systems as its
cohomology towers, including every original reduction map. The full
complex remains the input to the derived limit; cohomology has not
been interchanged with that limit or identified with adic cohomology.
An elementary homogeneous-coordinate intersection theorem also gives
the unique scalar represented by compatible coordinate fractions,
over arbitrary commutative rings. It does not yet identify global
sections of the original projective-plane model.
Invertibility of the proper geometric base-change map, including its
actual geometric acyclicity input, adic and trace comparisons, rank,
purity, and the Type III estimate remain unproved. Ordinary module-sheaf
cohomology does not by itself supply those missing comparisons.
-/

#check PrimeGap182.TypeIII.HasFiniteExceptionalTypeIIIInput
#print PrimeGap182.TypeIII.HasFiniteExceptionalTypeIIIInput
#print PrimeGap182.TypeIII.LocalFourierHypothesis

#print axioms PrimeGap182.TypeIII.exact_fourCycle_fourier_explicit
#print axioms PrimeGap182.TypeIII.physicalBoundaryFourier_norm_le_surface_weights
#print axioms PrimeGap182.TypeIII.raw_fourCycle_polynomialBoundary_norm_le
#print axioms PrimeGap182.TypeIII.actual_fourCycle_fourier_core_expansion
#print axioms PrimeGap182.TypeIII.finiteExceptionalFourierBound_of_actual_core_bounds
#print axioms PrimeGap182.TypeIII.curveExceptional_of_nonzero_frequencies
#print axioms PrimeGap182.TypeIII.kernel_radial_positive_fourier_norm_le_baseline_inputs
#print axioms PrimeGap182.TypeIII.fourier₂_fourCycle_normalize_parameters
#print axioms PrimeGap182.TypeIII.exact_fourCycle_fourier_origin_split
#print axioms PrimeGap182.TypeIII.exact_fourCycle_fourier_origin_of_coprime
#print axioms PrimeGap182.TypeIII.exists_fourCycle_fourier_coefficient_automorphism
#print axioms PrimeGap182.TypeIII.fourCycle_fourier_zero_iff_cubic_dilation
#print axioms PrimeGap182.TypeIII.ScalingSupport.eight_invariant_finite_support
#print axioms PrimeGap182.TypeIII.ScalingLines.eight_invariant_subset_line_cover
#print axioms PrimeGap182.TypeIII.correlation_column_contraction
#print axioms PrimeGap182.TypeIII.correlation_gram_entry
#print axioms PrimeGap182.TypeIII.correlation_row_energy
#print axioms PrimeGap182.TypeIII.correlationUnitMatrix_norm_le
#print axioms PrimeGap182.TypeIII.FiniteFieldSums.exists_uniform_trace_fourier_coefficient_automorphism
#print axioms PrimeGap182.TypeIII.FiniteFieldSums.fourier₂_fourCycle_prime
#print axioms PrimeGap182.TypeIII.correlationGramVector_sum_norm_sq
#print axioms PrimeGap182.TypeIII.correlationRowMean_sum_norm_le
#print axioms PrimeGap182.TypeIII.exactUnitTorusMap_fiber_card_le_three
#print axioms PrimeGap182.TypeIII.fourier₂_fourCycle_sub_centeredTypeIIIFourier
#print axioms PrimeGap182.TypeIII.fourier₂_fourCycle_sub_centered_norm_le
#print axioms PrimeGap182.TypeIII.CoefficientSheafSupport.stalkSupport_changeCoefficients
#print axioms PrimeGap182.TypeIII.artinSchreierCover_finite_free_etale
#print axioms PrimeGap182.TypeIII.artinSchreierEtaleToBase_covering
#print axioms PrimeGap182.TypeIII.artinSchreierCover_torsorEquiv_tmul
#print axioms PrimeGap182.TypeIII.artinSchreierSchemeTorsorIso
#print axioms PrimeGap182.TypeIII.artinSchreierSchemeTorsorIso_fst
#print axioms PrimeGap182.TypeIII.artinSchreierSchemeTorsorIso_snd
#print axioms PrimeGap182.TypeIII.artinSchreierSchemeBaseChangeIso_over
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterProjection_isProj
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterSheafAverage_stalk
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterStalkEquiv
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterStalk_finrank
#print axioms PrimeGap182.TypeIII.artinSchreierFreeSheaf_stalk_fieldAutomorphism
#print axioms PrimeGap182.TypeIII.artinSchreierSheafGeometricFrobenius_trace
#print axioms PrimeGap182.TypeIII.artinSchreierSheafGeometricFrobenius_prime_trace
#print axioms PrimeGap182.TypeIII.artinSchreierPointSiteEquivRoots
#print axioms PrimeGap182.TypeIII.artinSchreierPointSiteFiber_card
#print axioms PrimeGap182.TypeIII.artinSchreierPointFreeEquivFunctions_deck
#print axioms PrimeGap182.TypeIII.artinSchreierPointCharacterStalkEquiv
#print axioms PrimeGap182.TypeIII.artinSchreierPointCharacterStalk_finrank
#print axioms PrimeGap182.TypeIII.artinSchreierPointSheafGeometricFrobenius_trace
#print axioms PrimeGap182.TypeIII.artinSchreierPointSheafGeometricFrobenius_prime_trace
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterSheafAverage_idempotent
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterImageSheafRetract
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterLocalTrivialization
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterImageSheaf_over_isConstant
#print axioms PrimeGap182.TypeIII.artinSchreierRingCharacterSheafAverage_idempotent
#print axioms PrimeGap182.TypeIII.artinSchreierRingCharacterImageSheafRetract
#print axioms PrimeGap182.TypeIII.artinSchreierRingPointCharacterStalkEquiv
#print axioms PrimeGap182.TypeIII.artinSchreierRingPointCharacterStalk_free
#print axioms PrimeGap182.TypeIII.artinSchreierRingPointCharacterStalk_finrank
#print axioms PrimeGap182.TypeIII.artinSchreierRingPointSheafGeometricFrobenius_trace
#print axioms PrimeGap182.TypeIII.artinSchreierRingCharacterLocalTrivialization
#print axioms PrimeGap182.TypeIII.torsionCoefficientRing_card
#print axioms PrimeGap182.TypeIII.torsionCoefficientChar_isPrimitive
#print axioms PrimeGap182.TypeIII.torsionCoefficientReduce_surjective
#print axioms PrimeGap182.TypeIII.torsionCoefficientReduce_comp_char
#print axioms PrimeGap182.TypeIII.torsionArtinSchreierLocalTrivialization
#print axioms PrimeGap182.TypeIII.torsionArtinSchreierTrace_eq
#print axioms PrimeGap182.TypeIII.torsionArtinSchreierTrace_reduce
#print axioms PrimeGap182.TypeIII.artinSchreierRingCharacterSheafCoefficientMap_inclusion
#print axioms PrimeGap182.TypeIII.artinSchreierRingCharacterSheafCoefficientMap_comp
#print axioms PrimeGap182.TypeIII.torsionArtinSchreierAbTower
#print axioms PrimeGap182.TypeIII.artinSchreierRingCharacterSheafCoefficientExtensionIso
#print axioms PrimeGap182.TypeIII.artinSchreierRingCharacterSheafCoefficientExtensionIso_mate
#print axioms PrimeGap182.TypeIII.artinSchreierRingCharacterSheafCoefficientExtension_isIso
#print axioms PrimeGap182.TypeIII.torsionArtinSchreierReductionIso
#print axioms PrimeGap182.TypeIII.torsionArtinSchreierReductionIso_mate
#print axioms PrimeGap182.TypeIII.torsionCoefficientLimitLift_unique
#print axioms PrimeGap182.TypeIII.torsionCoefficientLimitChar_isPrimitive
#print axioms PrimeGap182.TypeIII.torsionCoefficientLimitProfinite
#print axioms PrimeGap182.TypeIII.torsionCoefficientLimitProjection_continuous
#print axioms PrimeGap182.TypeIII.torsionCoefficientLimitEquivFun
#print axioms PrimeGap182.TypeIII.torsionCoefficientLimitEquivFun_projection
#print axioms PrimeGap182.TypeIII.torsionCoefficientLimit_finrank
#print axioms PrimeGap182.TypeIII.torsionCoefficientLimitProjection_surjective
#print axioms PrimeGap182.TypeIII.torsionCoefficientLimitProjection_ker
#print axioms PrimeGap182.TypeIII.torsionCoefficientLimitQuotientEquiv_comp_mk
#print axioms PrimeGap182.TypeIII.torsionCoefficientLimitKernel_hasBasis
#print axioms PrimeGap182.TypeIII.torsionCoefficientLimit_isAdic
#print axioms PrimeGap182.TypeIII.torsionCoefficientLimit_isNoetherianRing
#print axioms PrimeGap182.TypeIII.torsionCoefficientLimit_isAdicComplete
#print axioms PrimeGap182.TypeIII.limitArtinSchreierLocalTrivialization
#print axioms PrimeGap182.TypeIII.limitArtinSchreierReductionIso
#print axioms PrimeGap182.TypeIII.limitArtinSchreierReductionIso_mate
#print axioms PrimeGap182.TypeIII.torsionArtinSchreierLimitModuleTower
#print axioms PrimeGap182.TypeIII.limitArtinSchreierCone
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.adjunction
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.stalk_isZero
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.stalkIso
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.map_shortExact
#print axioms PrimeGap182.TypeIII.kloostermanPhaseTrace_sum
#print axioms PrimeGap182.TypeIII.kloostermanPhaseTrace_sum_prime
#print axioms PrimeGap182.TypeIII.kloostermanPhaseRingHomEquiv
#print axioms PrimeGap182.TypeIII.kloostermanPhaseSchemePointEquiv
#print axioms PrimeGap182.TypeIII.kloostermanPhaseSchemeFiberEquiv
#print axioms PrimeGap182.TypeIII.projectiveTorusChartEquiv
#print axioms PrimeGap182.TypeIII.kloostermanCompactificationProjection_isProper
#print axioms PrimeGap182.TypeIII.kloostermanCompactificationOpenImmersion_isOpenImmersion
#print axioms PrimeGap182.TypeIII.kloostermanCompactificationOpenImmersion_denseRange
#print axioms PrimeGap182.TypeIII.kloostermanCompactificationOpenImmersion_toBase
#print axioms PrimeGap182.TypeIII.kloostermanCompactificationChartPhase_eq_phaseFunction
#print axioms PrimeGap182.TypeIII.kloostermanPhaseExtensionByZeroAdjunction
#print axioms PrimeGap182.TypeIII.kloostermanPhaseExtensionByZero_map_shortExact
#print axioms PrimeGap182.TypeIII.kloostermanPhaseExtensionByZero_stalkIso
#print axioms PrimeGap182.TypeIII.kloostermanPhaseExtensionByZero_stalk_isZero
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.baseChange_coverPreserving
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.functor_obj_obj
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.functor_preservesFiniteLimits
#print axioms PrimeGap182.TypeIII.EtaleDerivedDirectImage.hasInjectiveResolutions
#print axioms PrimeGap182.TypeIII.EtaleDerivedDirectImage.functor_eq_resolution_homology
#print axioms PrimeGap182.TypeIII.EtaleDerivedDirectImage.zeroIso
#print axioms PrimeGap182.TypeIII.kloostermanCompactifiedDerivedImage
#print axioms PrimeGap182.TypeIII.kloostermanCompactifiedDerivedImage_objIsoHomology
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.adjunction
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.stalkIso
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.map_shortExact
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.compIso
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.pullbackBaseChangeMap
#print axioms PrimeGap182.TypeIII.exactFunctorResolutionComparison
#print axioms PrimeGap182.TypeIII.exactFunctorResolutionNatTrans
#print axioms PrimeGap182.TypeIII.exactFunctorResolutionNatTrans_isIso
#print axioms PrimeGap182.TypeIII.derivedBaseChangeMap_factors
#print axioms PrimeGap182.TypeIII.derivedBaseChangeMap_zero
#print axioms PrimeGap182.TypeIII.derivedBaseChangeMap_isIso
#print axioms PrimeGap182.TypeIII.EtaleDerivedBaseChange.pullbackBaseChangeMap
#print axioms PrimeGap182.TypeIII.EtaleDerivedBaseChange.baseChangeMap_zero_eq
#print axioms PrimeGap182.TypeIII.kloostermanCompactifiedDerivedBaseChange
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.functor_preservesInjectiveObjects
#print axioms PrimeGap182.TypeIII.EtaleRestrictionInverseImage.iso
#print axioms PrimeGap182.TypeIII.EtaleRestrictionInverseImage.inverseImage_preservesInjectiveObjects_of_etale_mono
#print axioms PrimeGap182.TypeIII.rightDerived_additive
#print axioms PrimeGap182.TypeIII.kloostermanTorsionDerivedTower
#print axioms PrimeGap182.TypeIII.kloostermanTorsionDerivedTower_nsmul_section
#print axioms PrimeGap182.TypeIII.EtaleOpenBaseChange.pullbackBaseChangeMap_isIso
#print axioms PrimeGap182.TypeIII.EtaleDerivedOpenBaseChange.pullbackBaseChangeMap_isIso
#print axioms PrimeGap182.TypeIII.kloostermanCompactifiedDerivedOpenBaseChangeIso_hom
#print axioms PrimeGap182.TypeIII.EtaleOpenExtensionBaseChange.iso_conjugate_hom
#print axioms PrimeGap182.TypeIII.EtaleCompactSupportBaseChange.map
#print axioms PrimeGap182.TypeIII.EtaleCohomology.gammaIso
#print axioms PrimeGap182.TypeIII.EtaleCohomology.directImageIso
#print axioms PrimeGap182.TypeIII.EtaleClosedFieldSections.stalkIso
#print axioms PrimeGap182.TypeIII.rightDerivedPostcomposeIso
#print axioms PrimeGap182.TypeIII.EtaleGeometricFiberCohomology.baseChangeMap
#print axioms PrimeGap182.TypeIII.EtaleGeometricFiberCohomology.baseChangeMap_zero_eq
#print axioms PrimeGap182.TypeIII.kloostermanPhaseFiberOpenIso
#print axioms PrimeGap182.TypeIII.kloostermanFiberBaseChange_app_original
#print axioms PrimeGap182.TypeIII.kloostermanTorsionFiberBaseChange_reduction
#print axioms PrimeGap182.TypeIII.kloostermanTorsionFiberCohomologyTower_nsmul
#print axioms PrimeGap182.TypeIII.HenselianEtaleLifting.reduction_bijective
#print axioms PrimeGap182.TypeIII.HenselianEtaleLifting.residueEquiv_symm_spec
#print axioms PrimeGap182.TypeIII.rightDerivedPlusComparisonIso
#print axioms PrimeGap182.TypeIII.rightDerivedPlusComparisonIso_zero_unit
#print axioms PrimeGap182.TypeIII.rightDerivedFunctorPlus_isTriangulated
#print axioms PrimeGap182.TypeIII.shortExactPlusTriangle_distinguished
#print axioms PrimeGap182.TypeIII.rightDerivedConnectingHom_naturality
#print axioms PrimeGap182.TypeIII.rightDerivedLongExact_exact₁
#print axioms PrimeGap182.TypeIII.rightDerivedLongExact_exact₂
#print axioms PrimeGap182.TypeIII.rightDerivedLongExact_exact₃
#print axioms PrimeGap182.TypeIII.exactFunctorResolutionComparison_quasiIso
#print axioms PrimeGap182.TypeIII.exactFunctorResolutionComparison_map_quasiIso_of_acyclic
#print axioms PrimeGap182.TypeIII.derivedBaseChangeMap_isIso_of_acyclic
#print axioms PrimeGap182.TypeIII.derivedBaseChangeAcyclicIso_zero
#print axioms PrimeGap182.TypeIII.HenselianEtaleScheme.existsUnique_section
#print axioms PrimeGap182.TypeIII.StrictHenselianEtaleSections.stalkIso
#print axioms PrimeGap182.TypeIII.StrictHenselianEtaleSections.sections_preservesHomology
#print axioms PrimeGap182.TypeIII.StrictHenselianEtaleCohomology.isZero_cohomology_succ
#print axioms PrimeGap182.TypeIII.StrictHenselianEtaleCohomology.stalkIso
#print axioms PrimeGap182.TypeIII.StrictHenselianEtaleCohomology.stalkIso_zero_eq
#print axioms PrimeGap182.TypeIII.ProperLocalClosedFiber.closedFiberι_range
#print axioms PrimeGap182.TypeIII.ProperLocalClosedFiber.open_eq_top_of_closedFiber_subset
#print axioms PrimeGap182.TypeIII.ProperLocalClosedFiber.sections_ext_of_closedFiber
#print axioms PrimeGap182.TypeIII.EtaleDerivedAcyclicBaseChange.pullbackBaseChangeMap_isIso_of_acyclic
#print axioms PrimeGap182.TypeIII.EtaleDerivedAcyclicBaseChange.pullbackBaseChangeIso_zero
#print axioms PrimeGap182.TypeIII.EtaleSectionsRestriction.map
#print axioms PrimeGap182.TypeIII.ProperLocalSectionsInjective.restriction_injective
#print axioms PrimeGap182.TypeIII.ProperFiniteEtaleDetection.isIso_iff_closedFiber
#print axioms PrimeGap182.TypeIII.HenselianIdempotentLifting.idempotentReduction_bijective
#print axioms PrimeGap182.TypeIII.HenselianIdempotentLifting.clopenReductionOrderIso
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.factorizationReduction_bijective
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.lift_fst_reduction
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.lift_snd_reduction
#print axioms PrimeGap182.TypeIII.EtaleSkyscraperFamily.adjunction
#print axioms PrimeGap182.TypeIII.EtaleSkyscraperFamily.functor_preservesHomology
#print axioms PrimeGap182.TypeIII.EtaleSkyscraperFamily.isZero_cohomology_succ
#print axioms PrimeGap182.TypeIII.EtaleGodement.unit_mono
#print axioms PrimeGap182.TypeIII.EtaleGodement.injectiveRetract
#print axioms PrimeGap182.TypeIII.EtaleCoefficientRestriction.skyscraperIso
#print axioms PrimeGap182.TypeIII.EtaleCoefficientRestriction.isZero_cohomology_succ_restrict_injective
#print axioms PrimeGap182.TypeIII.EtaleCoefficientRestriction.cohomologyIso
#print axioms PrimeGap182.TypeIII.EtaleCoefficientRestriction.cohomologyIso_zero
#print axioms PrimeGap182.TypeIII.EtaleSkyscraperDirectImage.iso
#print axioms PrimeGap182.TypeIII.EtaleSkyscraperFamilyDirectImage.algebraicClosure_isZero_derived_succ
#print axioms PrimeGap182.TypeIII.EtaleCoefficientRestriction.isZero_derived_succ_restrict_injective
#print axioms PrimeGap182.TypeIII.EtaleCoefficientRestriction.derivedDirectImageIso
#print axioms PrimeGap182.TypeIII.EtaleCoefficientRestriction.derivedDirectImageIso_zero
#print axioms PrimeGap182.TypeIII.CoprimeIdempotentLifting.exists_lift_of_powers
#print axioms PrimeGap182.TypeIII.FiniteAlgebraAnnihilator.exists_positive_monicDegreeEq_annihilator
#print axioms PrimeGap182.TypeIII.FiniteAlgebraJacobson.maximalIdeal_map_le_jacobson
#print axioms PrimeGap182.TypeIII.FiniteAlgebraIdempotentLifting.idempotentReduction_bijective
#print axioms PrimeGap182.TypeIII.FiniteAlgebraClopenLifting.clopenReductionOrderIso
#print axioms PrimeGap182.TypeIII.IntegralAlgebraFiniteDescent.exists_finite_subalgebra
#print axioms PrimeGap182.TypeIII.IntegralAlgebraIdempotentLifting.idempotentReduction_bijective
#print axioms PrimeGap182.TypeIII.IntegralAlgebraClopenLifting.clopenReductionOrderIso
#print axioms PrimeGap182.TypeIII.EtaleCoefficientRestriction.restrictionCoextensionAdjunction
#print axioms PrimeGap182.TypeIII.EtaleExtensionCoefficientRestriction.iso
#print axioms PrimeGap182.TypeIII.EtaleCompactSupportCoefficientRestriction.iso
#print axioms PrimeGap182.TypeIII.EtaleCompactSupportCoefficientRestriction.iso_hom_app
#print axioms PrimeGap182.TypeIII.EtaleCompactSupportCoefficientRestriction.iso_zero
#print axioms PrimeGap182.TypeIII.kloostermanFiniteCoefficientToTowerIso
#print axioms PrimeGap182.TypeIII.kloostermanFiniteCoefficientToTowerIso_hom_original
#print axioms PrimeGap182.TypeIII.kloostermanFiniteCoefficientToTowerIso_zero
#print axioms PrimeGap182.TypeIII.exactFunctorMapHomologyIso_comp
#print axioms PrimeGap182.TypeIII.exactFunctorResolutionComparisonCompHomotopy
#print axioms PrimeGap182.TypeIII.exactFunctorResolutionComparisonTransformationHomotopy
#print axioms PrimeGap182.TypeIII.derivedBaseChangeMap_comp
#print axioms PrimeGap182.TypeIII.derivedBaseChangeMap_transformation
#print axioms PrimeGap182.TypeIII.EtaleCoefficientRestriction.compIso
#print axioms PrimeGap182.TypeIII.EtaleExtensionCoefficientRestriction.iso_comp'
#print axioms PrimeGap182.TypeIII.EtaleCoefficientRestriction.derivedDirectImageMap_comp'
#print axioms PrimeGap182.TypeIII.EtaleCompactSupportCoefficientRestriction.iso_comp'
#print axioms PrimeGap182.TypeIII.torsionArtinSchreierLimitModuleReduction_eq_restrictScalars
#print axioms PrimeGap182.TypeIII.kloostermanFiniteCoefficientRestrictedReduction_toTower
#print axioms PrimeGap182.TypeIII.kloostermanFiniteCoefficientDerivedTowerIso
#print axioms PrimeGap182.TypeIII.kloostermanFiniteCoefficientReduction_comp
#print axioms PrimeGap182.TypeIII.SchemeIdempotentClopens.globalIdempotentClopenEquiv
#print axioms PrimeGap182.TypeIII.ProperAffinization.factorization
#print axioms PrimeGap182.TypeIII.ProperAffinization.toAffinization_isProper
#print axioms PrimeGap182.TypeIII.ProperAffinization.toAffinization_surjective
#print axioms PrimeGap182.TypeIII.ProperAffinizationStructureSheaf.structureMap_isIso
#print axioms PrimeGap182.TypeIII.ProperAffinizationStructureSheaf.structureMap_isIso_of_proper
#print axioms PrimeGap182.TypeIII.NilpotentThickeningIdempotents.existsUnique_idempotent_lift
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.transition_isHomeomorph
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.lift_compatible_appTop
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.existsUnique_compatible_lifts
#print axioms PrimeGap182.TypeIII.adicCompletion_exists_original_preimage
#print axioms PrimeGap182.TypeIII.adicCompletion_range_comp_of_eq
#print axioms PrimeGap182.TypeIII.torsionCoefficientLimit_mul_ell_pow_injective
#print axioms PrimeGap182.TypeIII.torsionCoefficientReduce_ker
#print axioms PrimeGap182.TypeIII.torsionCoefficientReduce_eq_zero_iff_ell_pow_mul
#print axioms PrimeGap182.TypeIII.artinSchreierRingCharacterSheafCoefficientMap_stalk_generator
#print axioms PrimeGap182.TypeIII.limitArtinSchreierBocksteinSequence_shortExact
#print axioms PrimeGap182.TypeIII.limitArtinSchreierBocksteinTransition_comp
#print axioms PrimeGap182.TypeIII.kloostermanBockstein_exact_torsion
#print axioms PrimeGap182.TypeIII.kloostermanBocksteinConnecting_naturality
#print axioms PrimeGap182.TypeIII.kloostermanFiniteBockstein_exact_torsion
#print axioms PrimeGap182.TypeIII.kloostermanFiniteBocksteinReduction_comp
#print axioms PrimeGap182.TypeIII.kloostermanFiniteBocksteinConnecting_naturality
#print axioms PrimeGap182.TypeIII.kloostermanBocksteinSystem_exact_source
#print axioms PrimeGap182.TypeIII.kloostermanBocksteinSystem_exact_torsion
#print axioms PrimeGap182.TypeIII.kloostermanBocksteinSystem_exact_next
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.tower_isGrothendieckAbelian
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.limitFunctor_preservesInjectiveObjects
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.derivedPlusHomologyIso
#print axioms PrimeGap182.TypeIII.EtaleTowerDirectImage.functor_preservesInjectiveObjects
#print axioms PrimeGap182.TypeIII.EtaleTowerDirectImage.limitIso_hom_projection
#print axioms PrimeGap182.TypeIII.rightDerivedFunctorPlusComp_isRightDerived
#print axioms PrimeGap182.TypeIII.rightDerivedFunctorPlusCompIso_hom_fac
#print axioms PrimeGap182.TypeIII.EtaleDerivedLimitDirectImage.iso
#print axioms PrimeGap182.TypeIII.EtaleDerivedLimitDirectImage.iso_hom_fac
#print axioms PrimeGap182.TypeIII.EtaleSheafTowerEvaluation.functor_preservesInjectiveObjects
#print axioms PrimeGap182.TypeIII.EtaleSheafTowerEvaluation.evaluationBaseChangeIso_index_naturality
#print axioms PrimeGap182.TypeIII.EtaleDerivedImageTower.cohomologyIso_hom_fac
#print axioms PrimeGap182.TypeIII.kloostermanFiniteCoefficientExtendedTowerIso
#print axioms PrimeGap182.TypeIII.kloostermanDerivedLimitImageIso
#print axioms PrimeGap182.TypeIII.kloostermanDerivedLimitResolutionIso_augmentation
#print axioms PrimeGap182.TypeIII.kloostermanFiniteCoefficientDerivedLimitToOriginalIso_interchange
#print axioms PrimeGap182.TypeIII.kloostermanFullDerivedTowerFiniteCohomologyIso
#print axioms PrimeGap182.TypeIII.kloostermanFullDerivedTowerFiniteCohomologyIso_transition
#print axioms PrimeGap182.TypeIII.homogeneous_coordinate_intersection
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.levelModule_annihilated
#print axioms PrimeGap182.TypeIII.AdicCompatibleSystem.completionMap_comp_of
#print axioms PrimeGap182.TypeIII.AdicCompatibleSystem.completionMap_bijective
#print axioms PrimeGap182.TypeIII.InfinitesimalCompletion.completionMap_comp_of
#print axioms PrimeGap182.TypeIII.InfinitesimalCompletion.exists_original_section_of_completed_idempotent_lift
#print axioms PrimeGap182.TypeIII.InfinitesimalAffineSections.restriction_ker
#print axioms PrimeGap182.TypeIII.InfinitesimalAffineCompletion.completionMap_bijective
#print axioms PrimeGap182.TypeIII.InfinitesimalAffineCompletion.exists_completed_idempotent_lift
#print axioms PrimeGap182.TypeIII.AffineLimitIdempotentDescent.exists_stage
#print axioms PrimeGap182.TypeIII.AffineLimitIdempotentDescent.exists_common_refinement_clopen
