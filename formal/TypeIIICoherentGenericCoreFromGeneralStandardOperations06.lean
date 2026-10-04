import TypeIIICoherentGenericZeroBoundaryFromGeneralLocalization06
import TypeIIICanonicalPrimitiveEligibilityFromGeneralPublishedLaws05
import TypeIIIOriginalAffineFiniteOriginFromSharedEquivariantCompactification04
import TypeIIINormalizedInfinityFromLiteralOpenAdjunction01
import TypeIIIGenericLocalObservablesFromActualParameterFibers
import TypeIIIPublishedCohomologyFunctor
import TypeIIICanonicalSourceLocalData
import TypeIIIGeneralFuPrimitiveInfinityApplication03

/-!
# Generic core from one standard ordinary/perverse theory

All actual ordinary inverse images, primitive constructors, geometric fibers,
local realizations, ordinary dual, derived category, perverse-heart family,
normalization, Fourier kernel, retained compactifications and GENERAL laws
are chosen before p. The geometric parameter fields are not finite fields.
No arithmetic common-trait/Frobenius dictionary is substituted for them.

At p>3 the actual prime pulls, standard-character primitives and individual
Kl3/AS guards, shared zero/boundary, ordinary j-star compactification,
normalized finite-origin package, its compact and infinity comparisons and
all-rank Fu primitive-infinity specialization are computed. Existing source
coordinate identities and GOS then construct the literal CoreLocalData,
including rank six; no completed rank/profile/local-family/model is input.

The listed GENERAL clauses must be projections of ONE genuine continuous
adic theory. This source does not construct those foundations. It is not yet
an assertion of UniformApplications, a TypeIII endpoint or numerical
inequalities. NEW source only; no Lean execution is claimed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.CoherentGenericCoreFromGeneralStandardOperations06
open ExactInverseImagesToDerived QSTPrimitiveBridgesFromCommonKatzConstruction
open RationalPointStalksFromUniversalFiber CanonicalPrimeFramework
open PublishedPhysicalConstruction CanonicalCurveInput PublishedPhaseApplication PublishedLocalConstruction
open GenericSourceSpecialization GenericCurvePullback FourierSourceMaps FourierSourcePullbacks
open OriginModelsFromSameComputedCoefficients CurveDataFromOperations
open QSTCompactBridgeFromCompactifiedDerivedPushforward
open CoherentNormalizedFourierCompactInfinity03
open OriginalAffineKernelFromPublishedOpenCompact03
open CanonicalSourceLocalData BoundaryFromSourceModels MiddleFromLocalization
open FourierStalkFromSources FourierStalkInertia CanonicalSourceFourierStalk

universe cover
variable (C : Scheme → Type) [∀ X, Category.{0} (C X)]
  [∀ X, Abelian (C X)] [∀ X, MonoidalCategory (C X)] [∀ X, MonoidalClosed (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (AF : ArithmeticFibers C) (primitive : Constructions C)
  (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)
  (M : PrimitiveRamificationFromGeneralKatzTheory.LocalRealization C)
  [∀ (E : Type) [Field E], (M.origin E).Monoidal]
  [∀ (E : Type) [Field E], (M.infinity E).Monoidal]
  (DO : QSTDualityBridgesFromSmoothLisseVerdier.Operations C)
  [∀ X, ObjectProperty.IsClosedUnderIsomorphisms (DO.globalLisse X)]
  (profiles : UniformSourceLocalObservablesFromParameterFibers.OriginProfiles C M)
  (coefficients : PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.CoefficientFibers C AF)
  (primitiveLaws : CanonicalPrimitiveEligibilityFromGeneralPublishedLaws05.GeneralPrimitiveLaws
    C U AF primitive coefficients G DO.globalLisse M)
  (tame : ∀ (E : Type) [Field E], M.originGroup E →* Multiplicative ℂ)
  (originLaws : CoherentGenericSourceZeroFromGeneralOrigin03.GeneralOriginApplicationLaws
    C U M G DO.globalLisse primitive tame)
  (tameNonzero : ∀ (E : Type) [Field E] (_h2 : (2 : E) ≠ 0),
    ∃ z, (tame E z).toAdd ≠ 0)
  (compact : Operations C)
  (Open : OrdinaryOpenExtensionsFromAdjunctions.OrdinaryOpenFamily C U)
  (geometricPure : ∀ X : Scheme, C X → ℝ → Prop)
  (genericCompactification : ∀ (K : Type) [Field K], Compactification (genericProjection K))
  (affineCompactification : ∀ (K : Type) [Field K],
    Compactification (GenericRelativeAffineLineCoordinates.relativeProjection K))

local instance allDerived : ∀ X : Scheme, HasDerivedCategory.{0} (C X) :=
  fun _ => HasDerivedCategory.standard _

/-- The transcendental geometric field inherits the coefficient guard. -/
theorem phaseGuard (K : Type) [Field K] (hK : (2 : K) ≠ 0) : (2 : PhaseField K) ≠ 0 := by
  simpa only [map_ofNat, map_zero] using (algebraMap K (PhaseField K)).injective.ne hK

/-- Numerical prime guard, proved independently of any family. -/
theorem primeGuard (p : ℕ) [Fact p.Prime] (hp : 3 < p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hdiv := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
  omega

abbrev primePulls (p : ℕ) [Fact p.Prime] :=
  SourceInverseImageSystem.System.geometricPullbacks (primeSource C U p)
abbrev primeLocalPulls (p : ℕ) [Fact p.Prime] :=
  SourceInverseImageSystem.System.localPullbacks (primeSource C U p)

abbrev originalObservations (p : ℕ) [Fact p.Prime] :=
  SourcePurityFromStalks.geometry (pointStalks C U AF p)
    (UniformSourceLocalObservablesFromParameterFibers.sourceObservables (ZMod p)
      C U G DO.globalLisse M profiles)
abbrev originalCurve (p : ℕ) [Fact p.Prime] :=
  (originalObservations C U AF G M DO profiles p).curveData
    (QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C (StartingSourceMaps.sourceScheme (ZMod p)))

abbrev genericObservations (K : Type) [Field K] :=
  GenericLocalObservablesFromActualParameterFibers.genericObservables K C U DO.globalLisse M
    profiles G (geometricPure (genericScheme K))
abbrev genericDual (K : Type) [Field K] :=
  QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C (genericScheme K)
abbrev genericCurve (K : Type) [Field K] :=
  (genericObservations C U G M DO profiles geometricPure K).curveData (genericDual C K)
abbrev genericH (K : Type) [Field K] :=
  (cohomologyData C compact (genericCompactification K) 1).cohomology
abbrev genericPoint (K : Type) [Field K] :=
  GenericLocalObservablesFromActualParameterFibers.parameterPoint K
    (GenericOriginFractionFieldCoordinates.ParameterFractionField K)
abbrev observer (K : Type) [Field K] := nearbyOrigin C M (PhaseField K)
abbrev boundaryObserver (K : Type) [Field K] :=
  observer C M K ⋙ forgetInertia (M.originGroup (PhaseField K))

/-- Generic curve infinity is the literal SAME-U fraction-field restriction,
followed by SAME M.infinity and the fixed coefficient equivalence. -/
abbrev genericInfinity (K : Type) [Field K] :=
  U.pull (GenericOriginFractionFieldCoordinates.genericFractionMorphism K) ⋙
    GeneralFuPrimitiveInfinityApplication03.infinityObserver
      (C := C) (M := M) (GenericOriginFractionFieldCoordinates.ParameterFractionField K)

variable
  [∀ (K : Type) [Field K], (boundaryObserver C M K).Additive]
  [∀ (K : Type) [Field K], PreservesFiniteLimits (boundaryObserver C M K)]
  [∀ (K : Type) [Field K], PreservesFiniteColimits (boundaryObserver C M K)]

/-- GENERAL full-inertia dual, positive-break vanishing and localization
on the literal zero/infinity operators. No independently chosen infinity
functor or source-boundaryTheorems/model record is input. -/
structure GeneralBoundaryTheorems where
  dual : ∀ (K : Type) [Field K] (_hK : (2 : K) ≠ 0) A,
    (genericCurve C U G M DO profiles geometricPure K).Lisse A →
      Representation.Equiv
        ((OriginModelsFromSameComputedCoefficients.genericZero C U M K).obj
          ((genericDual C K).obj (op A))).ρ
        (PublishedPhaseApplication.dualRepresentation
          ((OriginModelsFromSameComputedCoefficients.genericZero C U M K).obj A)).ρ
  positiveSlope : ∀ (K : Type) [Field K] (_hK : (2 : K) ≠ 0) A,
    (genericCurve C U G M DO profiles geometricPure K).Isoclinic A 1 →
      Representation.invariants ((genericInfinity C U M K).obj A).ρ = ⊥
  connecting : ∀ (K : Type) [Field K] (_hK : (2 : K) ≠ 0) A,
    (Representation.invariants ((OriginModelsFromSameComputedCoefficients.genericZero C U M K).obj A).ρ ×
      Representation.invariants ((genericInfinity C U M K).obj A).ρ) →ₗ[ℂ]
        (boundaryObserver C M K).obj ((genericH C compact genericCompactification K).compact A)
  connecting_injective : ∀ (K : Type) [Field K] (hK : (2 : K) ≠ 0) A,
    (genericCurve C U G M DO profiles geometricPure K).Lisse A →
    (genericCurve C U G M DO profiles geometricPure K).Isoclinic A 1 →
      Function.Injective (connecting K hK A)
  connecting_exact : ∀ (K : Type) [Field K] (hK : (2 : K) ≠ 0) A,
    (genericCurve C U G M DO profiles geometricPure K).Lisse A →
    (genericCurve C U G M DO profiles geometricPure K).TameZero A →
    (genericCurve C U G M DO profiles geometricPure K).Isoclinic A 1 →
      LinearMap.range (connecting K hK A) =
        LinearMap.ker ((boundaryObserver C M K).map
          ((genericH C compact genericCompactification K).comparison A)).hom

variable (boundaryTheorems : GeneralBoundaryTheorems C U G M DO profiles compact geometricPure genericCompactification)

/-- Assemble the old generic boundaryTheorems interface on literal full-inertia
operators. All fields are general theorem projections or computed data. -/
abbrev computedBoundaryClauses :
    CoherentGenericZeroBoundaryFromGeneralLocalization06.GeneralCurveBoundaryClauses
      C U M GenericLocalObservablesFromActualParameterFibers.ParameterPoint
      (fun K => genericObservations C U G M DO profiles geometricPure K)
      (fun K => genericDual C K) (fun K => genericH C compact genericCompactification K)
      (fun K => boundaryObserver C M K)
      (fun K => M.infinityGroup (GenericOriginFractionFieldCoordinates.ParameterFractionField K)) where
  infinity K _ _ := genericInfinity C U M K
  dual := boundaryTheorems.dual
  positiveSlope := boundaryTheorems.positiveSlope
  connecting := boundaryTheorems.connecting
  connecting_injective := boundaryTheorems.connecting_injective
  connecting_exact := boundaryTheorems.connecting_exact

abbrev computedBoundary (K : Type) [Field K] (hK : (2 : K) ≠ 0) :=
  CoherentGenericZeroBoundaryFromGeneralLocalization06.computedBoundarySequence
    C U M GenericLocalObservablesFromActualParameterFibers.ParameterPoint
    (fun K => genericObservations C U G M DO profiles geometricPure K)
    (fun K => genericDual C K) (fun K => genericH C compact genericCompactification K)
    (fun K => boundaryObserver C M K)
    (fun K => M.infinityGroup (GenericOriginFractionFieldCoordinates.ParameterFractionField K))
    (computedBoundaryClauses C U G M DO profiles compact geometricPure genericCompactification boundaryTheorems) K hK
abbrev computedRestriction (K : Type) [Field K] (hK : (2 : K) ≠ 0) :=
  CoherentGenericZeroBoundaryFromGeneralLocalization06.computedRestriction
    C U M GenericLocalObservablesFromActualParameterFibers.ParameterPoint
    (fun K => genericObservations C U G M DO profiles geometricPure K)
    (fun K => genericDual C K) (fun K => genericH C compact genericCompactification K)
    (fun K => boundaryObserver C M K)
    (fun K => M.infinityGroup (GenericOriginFractionFieldCoordinates.ParameterFractionField K))
    (computedBoundaryClauses C U G M DO profiles compact geometricPure genericCompactification boundaryTheorems) K hK
abbrev computedZeroFunctor (K : Type) [Field K] (hK : (2 : K) ≠ 0) :=
  CoherentGenericZeroBoundaryFromGeneralLocalization06.computedZeroFunctor
    C U M GenericLocalObservablesFromActualParameterFibers.ParameterPoint
    (fun K => genericObservations C U G M DO profiles geometricPure K)
    (fun K => genericDual C K) (fun K => genericH C compact genericCompactification K)
    (fun K => boundaryObserver C M K)
    (fun K => M.infinityGroup (GenericOriginFractionFieldCoordinates.ParameterFractionField K))
    (computedBoundaryClauses C U G M DO profiles compact geometricPure genericCompactification boundaryTheorems) K hK

/-- GENERAL curve, smooth-dual, coordinate-pullback and GOS applications
on literal operators. Every clause concerns ALL eligible ordinary objects;
none supplies a primitive model, rank-six, profile or finished core. -/
structure GeneralGeometricTheorems where
  scalar : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p),
    ScalarPullbackRules (originalPullbackData (ZMod p) (primePulls C U p))
      (CanonicalPrimitiveEligibilityFromGeneralPublishedLaws05.canonicalGeometry C U AF G DO.globalLisse M p)
      (originalCurve C U AF G M DO profiles p)
  original : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p),
    CurveRules (originalCurve C U AF G M DO profiles p)
  curve : ∀ (K : Type) [Field K] (_hK : (2 : K) ≠ 0),
    CurveRules (genericCurve C U G M DO profiles geometricPure K)
  pullback : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p)
    (g : genericScheme (ZMod p) ⟶ StartingSourceMaps.sourceScheme (ZMod p))
    (f : parameterScheme (ZMod p) ⟶ PhysicalTorusMorphism.torusScheme (ZMod p)),
    CoordinateBaseChange (ZMod p) g f →
      PulledCurveInput.PullbackProperties (originalCurve C U AF G M DO profiles p)
        (genericCurve C U G M DO profiles geometricPure (ZMod p)) (U.pull g)
  dualSpecialization : ∀ (K : Type) [Field K] (_hK : (2 : K) ≠ 0)
    (A : C (localScheme K)),
    (genericDual C K).obj (op ((U.pull (projectionMorphism K)).obj A)) ≅
      (U.pull (projectionMorphism K)).obj
        ((QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C (localScheme K)).obj (op A))
  gos : ∀ (K : Type) [Field K] (_hK : (2 : K) ≠ 0) (A : C (genericScheme K)),
    (genericCurve C U G M DO profiles geometricPure K).Lisse A →
    (genericCurve C U G M DO profiles geometricPure K).Isoclinic A 1 →
    (genericCurve C U G M DO profiles geometricPure K).Isoclinic
      ((genericCurve C U G M DO profiles geometricPure K).dual A) 1 →
    Module.finrank ℂ ((observer C M K).obj ((genericH C compact genericCompactification K).compact A)).V =
      (genericCurve C U G M DO profiles geometricPure K).swanZero A (genericPoint K) +
      (genericCurve C U G M DO profiles geometricPure K).swanInfinity A (genericPoint K)

variable (geometric : GeneralGeometricTheorems C U AF G M DO profiles compact geometricPure genericCompactification)

include geometric in
omit [∀ (E : Type) [Field E], (M.origin E).Monoidal]
  [∀ (E : Type) [Field E], (M.infinity E).Monoidal]
  [∀ X, ObjectProperty.IsClosedUnderIsomorphisms (DO.globalLisse X)]
  [∀ (K : Type) [Field K], (boundaryObserver C M K).Additive]
  [∀ (K : Type) [Field K], PreservesFiniteLimits (boundaryObserver C M K)]
  [∀ (K : Type) [Field K], PreservesFiniteColimits (boundaryObserver C M K)] in
/-- Actual ALL-object finite generic fibers are already finite representations. -/
theorem computedGeometricFiberRules (K : Type) [Field K] (hK : (2 : K) ≠ 0) :
    GeometricCoreRank.GeometricFiberRules
      (genericCurve C U G M DO profiles geometricPure K)
      (genericH C compact genericCompactification K) (boundaryObserver C M K) (genericPoint K) where
  compact_finite A _ := by
    change FiniteDimensional ℂ ((observer C M K).obj ((genericH C compact genericCompactification K).compact A)).V
    infer_instance
  compact_rank := geometric.gos K hK

/-- The actual local ordinary scalar/internal-dual/j-star operations. -/
abbrev localOperations (K : Type) [Field K] (hK : (2 : K) ≠ 0) :=
  NormalizedInfinityFromLiteralOpenAdjunction01.actualLocalOperations C U Open K (phaseGuard K hK)

/-- General smooth-dual compatibility computes the specialization record. -/
def computedSpecialization (K : Type) [Field K] (hK : (2 : K) ≠ 0) :
    SpecializationCompatibility (D := genericCurve C U G M DO profiles geometricPure K)
      (localOperations C U Open K hK) (U.pull (projectionMorphism K)) (genericDual C K) where
  tensor _ _ := Iso.refl _
  dual _ := Iso.refl _
  dualSpecialization := geometric.dualSpecialization K hK

/- The remaining shared proper/localization operators are chosen ONCE on
all fields, before any primitive or p. Their affine term is not a field:
it is the literal ordinary relative j-star compact recipe. -/
variable
  (projective : ∀ (K : Type) [Field K], C (genericScheme K) ⥤ FDRep ℂ (M.originGroup (PhaseField K)))
  (fromCompact : ∀ (K : Type) [Field K] (hK : (2 : K) ≠ 0) A,
    (observer C M K).obj ((genericH C compact genericCompactification K).compact A) ⟶
      (observedAffineFunctor C U compact Open K (phaseGuard K hK) (affineCompactification K)
        (observer C M K)).obj A)
  (toProjective : ∀ (K : Type) [Field K] (hK : (2 : K) ≠ 0),
    observedAffineFunctor C U compact Open K (phaseGuard K hK) (affineCompactification K)
      (observer C M K) ⟶ projective K)
  (leray : ∀ (K : Type) [Field K] (_hK : (2 : K) ≠ 0) A,
    (projective K).obj A ⟶ (observer C M K).obj ((genericH C compact genericCompactification K).ordinary A))
  (fromInfinity : ∀ (K : Type) [Field K] (hK : (2 : K) ≠ 0) A,
    invariantModule ((computedRestriction C U G M DO profiles compact geometricPure
      genericCompactification boundaryTheorems K hK).infinity A) ⟶
    (observedAffineFunctor C U compact Open K (phaseGuard K hK) (affineCompactification K)
      (observer C M K) ⋙ forgetInertia (M.originGroup (PhaseField K))).obj A)

abbrev computedDiagram (K : Type) [Field K] (hK : (2 : K) ≠ 0) :=
  OriginalAffineFiniteOriginFromSharedEquivariantCompactification04.sharedDiagram
    (C := C) (U := U) (O := compact) (F := Open) (K := K) (h2 := phaseGuard K hK)
    (c := affineCompactification K)
    (Obs := genericObservations C U G M DO profiles geometricPure K) (dualGeneric := genericDual C K)
    (H := genericH C compact genericCompactification K) (observer := observer C M K)
    (BS := computedBoundary C U G M DO profiles compact geometricPure genericCompactification boundaryTheorems K hK)
    (Z := computedRestriction C U G M DO profiles compact geometricPure genericCompactification boundaryTheorems K hK)
    (projective := projective K) (fromCompact := fromCompact K hK)
    (toProjective := toProjective K hK) (leray := leray K hK) (fromInfinity := fromInfinity K hK)
abbrev computedCompactification (K : Type) [Field K] (hK : (2 : K) ≠ 0) :=
  (computedDiagram C U G M DO profiles compact Open geometricPure genericCompactification
    affineCompactification boundaryTheorems projective fromCompact toProjective leray fromInfinity K hK).compactification
abbrev computedAffineInertia (K : Type) [Field K] (hK : (2 : K) ≠ 0) :=
  (computedDiagram C U G M DO profiles compact Open geometricPure genericCompactification
    affineCompactification boundaryTheorems projective fromCompact toProjective leray fromInfinity K hK).inertia

/-- ALL-lisse localization/point-vanishing/Leray on the literal j-star term. -/
structure GeneralLocalizationTheorems : Prop where
  comparison : ∀ (K : Type) [Field K] (hK : (2 : K) ≠ 0) A,
    (genericCurve C U G M DO profiles geometricPure K).Lisse A →
      (forgetInertia (M.originGroup (PhaseField K))).map (fromCompact K hK A) ≫
      (forgetInertia (M.originGroup (PhaseField K))).map ((toProjective K hK).app A) ≫
      (forgetInertia (M.originGroup (PhaseField K))).map (leray K hK A) =
        (boundaryObserver C M K).map ((genericH C compact genericCompactification K).comparison A)
  zero : ∀ (K : Type) [Field K] (hK : (2 : K) ≠ 0) A,
    (genericCurve C U G M DO profiles geometricPure K).Lisse A →
      LinearMap.range ((forgetInertia (M.originGroup (PhaseField K))).map (fromCompact K hK A)).hom = ⊤
  infinity : ∀ (K : Type) [Field K] (hK : (2 : K) ≠ 0) A,
    (genericCurve C U G M DO profiles geometricPure K).Lisse A →
      LinearMap.range (fromInfinity K hK A).hom =
        LinearMap.ker ((forgetInertia (M.originGroup (PhaseField K))).map ((toProjective K hK).app A)).hom
  leray : ∀ (K : Type) [Field K] (hK : (2 : K) ≠ 0) A,
    (genericCurve C U G M DO profiles geometricPure K).Lisse A →
      Function.Injective ((forgetInertia (M.originGroup (PhaseField K))).map (leray K hK A)).hom

variable (localization : GeneralLocalizationTheorems C U G M DO profiles compact Open geometricPure
  genericCompactification affineCompactification boundaryTheorems projective fromCompact toProjective leray fromInfinity)

include localization in
omit [∀ (E : Type) [Field E], (M.infinity E).Monoidal]
  [∀ X, ObjectProperty.IsClosedUnderIsomorphisms (DO.globalLisse X)]
  [∀ (K : Type) [Field K], (boundaryObserver C M K).Additive]
  [∀ (K : Type) [Field K], PreservesFiniteLimits (boundaryObserver C M K)]
  [∀ (K : Type) [Field K], PreservesFiniteColimits (boundaryObserver C M K)] in
/-- General localization yields MR; no finished MR is an input. -/
theorem computedCompactificationRules (K : Type) [Field K] (hK : (2 : K) ≠ 0) :
    CompactificationRules
      (computedRestriction C U G M DO profiles compact geometricPure genericCompactification boundaryTheorems K hK)
      (computedCompactification C U G M DO profiles compact Open geometricPure genericCompactification
        affineCompactification boundaryTheorems projective fromCompact toProjective leray fromInfinity K hK) where
  comparison := localization.comparison K hK
  zero_exact A hA := by
    change LinearMap.range ((forgetInertia (M.originGroup (PhaseField K))).map (fromCompact K hK A)).hom =
      LinearMap.ker (0 : _ →ₗ[ℂ] _)
    rw [LinearMap.ker_zero]
    exact localization.zero K hK A hA
  infinity_exact := localization.infinity K hK
  leray_injective := localization.leray K hK

/- A standard perverse-heart family in the SAME derived categories. No
perverse membership of all ordinary inputs or normalization exactness. -/
variable (perverse : ∀ X : Scheme, ObjectProperty (DerivedCategory (C X)))
  (N : ∀ (K : Type) [Field K] (_hK : (2 : K) ≠ 0),
    CurveNormalizationOperations (Ord := C (StartingSourceMaps.affineLine (PhaseField K)))
      (perverse (StartingSourceMaps.affineLine (PhaseField K))).ι)
  (LF : ∀ (K : Type) [Field K] [Fintype K] (_hK : (2 : K) ≠ 0)
      (ψ : AddChar K (PadicAlgCl 2)) (_hψ : ψ ≠ 1),
    LocalFourierData K ℂ (M.infinityGroup (PhaseField K)) (M.originGroup (PhaseField K)))
  (S : ∀ (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
      (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1),
    StandardFiniteOriginOperations (LF := LF K hK ψ hψ)
      (perverse (StartingSourceMaps.affineLine (PhaseField K))).ι)

/-- The exact literal kernel Fourier construction and point-torsion laws
for ALL finite base fields/characters and ALL ordinary inputs. Infinity is
not a field: it is SAME-U open restriction followed by SAME M.infinity. -/
structure GeneralFourierFiberTheorems where
  fiber : ∀ (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) (s : PhaseField K) (hs : s ≠ 0),
    ((N K hK).shiftOne ⋙ (S K hK ψ hψ).radialFourier s hs) ⋙ (S K hK ψ hψ).originGenericMinusOne ≅
      observedFullCompactFunctor C U compact K (affineCompactification K)
        (primitive.artinSchreier K hK ψ)
        (scaledObserver (C := C) (U := U) (K := K) (Units.mk0 s hs) (observer C M K))
  quotient : ∀ (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (_hψ : ψ ≠ 1) (s : PhaseField K) (hs : s ≠ 0) A,
    IsIso ((observedFullCompactFunctor C U compact K (affineCompactification K)
      (primitive.artinSchreier K hK ψ)
      (scaledObserver (C := C) (U := U) (K := K) (Units.mk0 s hs) (observer C M K))).map
        ((N K hK).quotientMap.app A))
  infinity : ∀ (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1),
    (N K hK).shiftOne ⋙ (S K hK ψ hψ).infinityGenericMinusOne ≅
      NormalizedInfinityFromLiteralOpenAdjunction01.actualOrdinaryInfinity C U M K
  infinityQuotient : ∀ (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0) A,
    IsIso ((NormalizedInfinityFromLiteralOpenAdjunction01.actualOrdinaryInfinity C U M K).map
      ((N K hK).quotientMap.app A))
  dualInfinity : ∀ (K : Type) [Field K] (_hK : (2 : K) ≠ 0) (A : C (localScheme K)),
    Representation.Equiv
      ((NormalizedInfinityFromLiteralOpenAdjunction01.actualInfinity C M K).obj
        ((QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C (localScheme K)).obj (op A))).ρ
      (dualRepresentation ((NormalizedInfinityFromLiteralOpenAdjunction01.actualInfinity C M K).obj A)).ρ
  perverseOrigin : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p) (K : Type) [Field K] [Fintype K]
    [CharP K p] (hK : (2 : K) ≠ 0) (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1),
    FiniteOriginRules p (S K hK ψ hψ).perverseData
  additivity : ∀ (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1), LocalFourierAdditivity (LF K hK ψ hψ)

variable (fourier : GeneralFourierFiberTheorems C U primitive M compact affineCompactification perverse N LF S)

abbrev observedFourierRules (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    ObservedFourierCurveRules C U compact K (affineCompactification K)
      (perverse (StartingSourceMaps.affineLine (PhaseField K))).ι (N K hK) (S K hK ψ hψ)
      (primitive.artinSchreier K hK ψ) where
  radialObserver := observer C M K
  ordinaryInfinity := NormalizedInfinityFromLiteralOpenAdjunction01.actualOrdinaryInfinity C U M K
  fourierFiber := fourier.fiber K hK ψ hψ
  compactQuotientIsIso := fourier.quotient K hK ψ hψ
  infinityFiber := fourier.infinity K hK ψ hψ
  infinityQuotientIsIso := fourier.infinityQuotient K hK

abbrev literalFiberClauses (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    NormalizedInfinityFromLiteralOpenAdjunction01.GeneralLiteralFiberClauses
      C U M K (perverse (StartingSourceMaps.affineLine (PhaseField K))).ι (N K hK) (S K hK ψ hψ) where
  compactDegreeOne s hs := observedFullCompactFunctor C U compact K (affineCompactification K)
    (primitive.artinSchreier K hK ψ)
    (scaledObserver (C := C) (U := U) (K := K) (Units.mk0 s hs) (observer C M K))
  fourierFiber := fourier.fiber K hK ψ hψ
  compactQuotientIsIso := fourier.quotient K hK ψ hψ
  infinityFiber := fourier.infinity K hK ψ hψ
  infinityQuotientIsIso := fourier.infinityQuotient K hK

variable
  (smoothOpen : OrdinaryFourierKernelExtensionFromGeneralSmoothBaseChange.UniversalSmoothOpenBaseChange C U Open)
  (lisseProjection : OrdinaryFourierKernelExtensionFromGeneralSmoothBaseChange.UniversalLisseOpenProjection
    C U Open DO.globalLisse)
  (compactBaseChange : CoherentGeneralOpenCompactKernelApplication01.UniversalCompactBaseChange C U compact)

/-- The compact comparison is an OUTPUT of general open/projection/compact
base change on the literal AS(T²*x/s) kernel. No FC/BC comparison is input. -/
def computedCompactFourierComparison (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) (s : PhaseField K) (hs : s ≠ 0)
    (A : C (localScheme K)) :=
  (normalizedOriginToLiteralASAffineEquiv
    (C := C) (U := U) (O := compact) (F := Open) (lisse := DO.globalLisse)
    (smoothOpen := smoothOpen) (lisseProjection := lisseProjection)
    (lissePull := primitiveLaws.lissePull) (compactBaseChange := compactBaseChange)
    (K := K) (h2 := phaseGuard K hK) (c := affineCompactification K)
    (underlying := (perverse (StartingSourceMaps.affineLine (PhaseField K))).ι)
    (N := N K hK) (S := S K hK ψ hψ) (as := primitive.artinSchreier K hK ψ)
    (hAS := primitiveLaws.standardASLisse K hK ψ hψ)
    (R := observedFourierRules C U primitive M compact affineCompactification perverse N LF S fourier K hK ψ hψ)
    (s := s) (hs := hs) (A := A)).toLinearEquiv

/-- InfinityCompatibility is constructed from the SAME actual open
adjunction and normalization, never from a finished correlation model. -/
def computedInfinityCompatibility (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :=
  NormalizedInfinityFromLiteralOpenAdjunction01.computedInfinityCompatibility
    (C := C) (U := U) (F := Open) (M := M) (K := K) (h2 := phaseGuard K hK)
    (underlying := (perverse (StartingSourceMaps.affineLine (PhaseField K))).ι)
    (N := N K hK) (S := S K hK ψ hψ)
    (laws := literalFiberClauses C U primitive M compact affineCompactification perverse N LF S fourier K hK ψ hψ)
    (dualGenericInfinity := fourier.dualInfinity K hK)

variable (Cover : ∀ (E : Type) [Field E], ℕ → Type cover)
  [∀ (E : Type) [Field E] (n : ℕ), Group (Cover E n)]
  (fu : GeneralFuPrimitiveInfinityApplication03.GeneralFuInfinityClauses C U M primitive Cover)

/-- GENERAL power-cover/linear-kernel/scalar and local-FT eligibility laws.
No rank-three primitive model or KloostermanInfinityRules family is input. -/
structure GeneralCoverOperationTheorems where
  cover : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Fintype K] [CharP K p]
    (hK : (2 : K) ≠ 0) (hp : 3 < p),
    PublishedMackey.CubicCoverRules (GeneralFuPrimitiveInfinityApplication03.cubicCover
      (C := C) (U := U) (M := M) (O := primitive) (H := Cover) (R := fu)
      p (PhaseField K) (phaseGuard K hK) hp)
  linear : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Fintype K] [CharP K p]
    (hK : (2 : K) ≠ 0) (hp : 3 < p) (ψ : AddChar K (PadicAlgCl 2)) (_hψ : ψ ≠ 1),
    PublishedMackey.LinearASRules (GeneralFuPrimitiveInfinityApplication03.cubicCover
      (C := C) (U := U) (M := M) (O := primitive) (H := Cover) (R := fu)
      p (PhaseField K) (phaseGuard K hK) hp)
      (fu.linearKernel K (PhaseField K) 3 (primitive.artinSchreier K hK ψ))
  scalar : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Fintype K] [CharP K p]
    (hK : (2 : K) ≠ 0) (hp : 3 < p) (ψ : AddChar K (PadicAlgCl 2)) (_hψ : ψ ≠ 1),
    KloostermanInfinityFromScalar.ScalarRules (localOperations C U Open K hK)
      (NormalizedInfinityFromLiteralOpenAdjunction01.actualInfinity C M K)
      (GeneralFuPrimitiveInfinityApplication03.cubicCover
        (C := C) (U := U) (M := M) (O := primitive) (H := Cover) (R := fu)
        p (PhaseField K) (phaseGuard K hK) hp)
      (fu.linearKernel K (PhaseField K) 3 (primitive.artinSchreier K hK ψ))
  admissible : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Fintype K] [CharP K p]
    (hK : (2 : K) ≠ 0) (hp : 3 < p) (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1),
    CubicInputAdmissibility (GeneralFuPrimitiveInfinityApplication03.cubicCover
      (C := C) (U := U) (M := M) (O := primitive) (H := Cover) (R := fu)
      p (PhaseField K) (phaseGuard K hK) hp)
      (fu.linearKernel K (PhaseField K) 3 (primitive.artinSchreier K hK ψ)) (LF K hK ψ hψ)

variable (covers : GeneralCoverOperationTheorems C U primitive M Open LF Cover fu)


/-- The old compact Fourier base-change record is computed from the
actual equivariant normalized kernel map and actual affine diagram. -/
def computedKernelBaseChange (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :=
  OriginalAffineFiniteOriginFromSharedEquivariantCompactification04.computedFourierBaseChange
    (C := C) (U := U) (O := compact) (F := Open) (lisse := DO.globalLisse)
    (smoothOpen := smoothOpen) (lisseProjection := lisseProjection)
    (lissePull := primitiveLaws.lissePull) (compactBaseChange := compactBaseChange)
    (K := K) (h2 := phaseGuard K hK) (c := affineCompactification K)
    (Obs := genericObservations C U G M DO profiles geometricPure K) (dualGeneric := genericDual C K)
    (underlying := (perverse (StartingSourceMaps.affineLine (PhaseField K))).ι)
    (N := N K hK) (S := S K hK ψ hψ) (as := primitive.artinSchreier K hK ψ)
    (hAS := primitiveLaws.standardASLisse K hK ψ hψ)
    (R := observedFourierRules C U primitive M compact affineCompactification perverse N LF S fourier K hK ψ hψ)
    (dualLocal := fun A => (QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C (localScheme K)).obj (op A))
    (Z' := computedRestriction C U G M DO profiles compact geometricPure genericCompactification boundaryTheorems K hK)
    (projective' := projective K) (fromCompact' := fromCompact K hK)
    (toProjective' := toProjective K hK) (leray' := leray K hK) (fromInfinity' := fromInfinity K hK)

omit [∀ (E : Type) [Field E], (M.infinity E).Monoidal]
  [∀ X, ObjectProperty.IsClosedUnderIsomorphisms (DO.globalLisse X)]
  [∀ (K : Type) [Field K], (boundaryObserver C M K).Additive]
  [∀ (K : Type) [Field K], PreservesFiniteLimits (boundaryObserver C M K)]
  [∀ (K : Type) [Field K], PreservesFiniteColimits (boundaryObserver C M K)] in
/-- Inertia compatibility of BC is also an OUTPUT of that same FDRep map;
no independently chosen BI or finished-family intertwiner is input. -/
theorem computedKernelFourierInertia (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    FourierInertia
      (computedRestriction C U G M DO profiles compact geometricPure genericCompactification boundaryTheorems K hK)
      (computedCompactification C U G M DO profiles compact Open geometricPure genericCompactification
        affineCompactification boundaryTheorems projective fromCompact toProjective leray fromInfinity K hK)
      (computedAffineInertia C U G M DO profiles compact Open geometricPure genericCompactification
        affineCompactification boundaryTheorems projective fromCompact toProjective leray fromInfinity K hK)
      (localOperations C U Open K hK) (U.pull (projectionMorphism K))
      (CoherentNormalizedFourierCompactInfinity03.normalizedData (N K hK) (S K hK ψ hψ))
      (computedKernelBaseChange C U AF primitive G M DO profiles coefficients primitiveLaws compact Open
        geometricPure genericCompactification affineCompactification boundaryTheorems projective fromCompact
        toProjective leray fromInfinity perverse N LF S fourier smoothOpen lisseProjection compactBaseChange
        K hK ψ hψ) :=
  OriginalAffineFiniteOriginFromSharedEquivariantCompactification04.computedFourierInertia
    (C := C) (U := U) (O := compact) (F := Open) (lisse := DO.globalLisse)
    (smoothOpen := smoothOpen) (lisseProjection := lisseProjection)
    (lissePull := primitiveLaws.lissePull) (compactBaseChange := compactBaseChange)
    (K := K) (h2 := phaseGuard K hK) (c := affineCompactification K)
    (Obs := genericObservations C U G M DO profiles geometricPure K) (dualGeneric := genericDual C K)
    (underlying := (perverse (StartingSourceMaps.affineLine (PhaseField K))).ι)
    (N := N K hK) (S := S K hK ψ hψ) (as := primitive.artinSchreier K hK ψ)
    (hAS := primitiveLaws.standardASLisse K hK ψ hψ)
    (R := observedFourierRules C U primitive M compact affineCompactification perverse N LF S fourier K hK ψ hψ)
    (dualLocal := fun A => (QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C (localScheme K)).obj (op A))
    (Z' := computedRestriction C U G M DO profiles compact geometricPure genericCompactification boundaryTheorems K hK)
    (projective' := projective K) (fromCompact' := fromCompact K hK)
    (toProjective' := toProjective K hK) (leray' := leray K hK) (fromInfinity' := fromInfinity K hK)

section ActualPrimeCore
variable (p : ℕ) [Fact p.Prime] (hp : 3 < p)

abbrev actualPrimitives :=
  RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U AF p)
    (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C primitive p (primeGuard p hp))
abbrev actualKl :=
  PublishedPrimitiveSources.Data.twistOne (actualPrimitives C U AF primitive p hp)
    (PublishedPrimitiveSources.Data.rawKl (actualPrimitives C U AF primitive p hp))
abbrev actualAS := PublishedPrimitiveSources.Data.as (actualPrimitives C U AF primitive p hp)
abbrev actualLineGeometry :=
  CanonicalPrimitiveEligibilityFromGeneralPublishedLaws05.canonicalGeometry C U AF G DO.globalLisse M p

include primitiveLaws coefficients in
omit [∀ X, MonoidalClosed (C X)]
  [∀ (E : Type) [Field E], (M.origin E).Monoidal]
  [∀ (E : Type) [Field E], (M.infinity E).Monoidal]
  [∀ (K : Type) [Field K], (boundaryObserver C M K).Additive]
  [∀ (K : Type) [Field K], PreservesFiniteLimits (boundaryObserver C M K)]
  [∀ (K : Type) [Field K], PreservesFiniteColimits (boundaryObserver C M K)] in
theorem actualKlProperties :
    Kl3Properties (actualLineGeometry C U AF G M DO p) (actualKl C U AF primitive p hp) :=
  CanonicalPrimitiveEligibilityFromGeneralPublishedLaws05.computedKl3Properties
    (C := C) (U := U) (F := AF) (O := primitive) (B := coefficients)
    (G := G) (L := DO.globalLisse) (M := M) (T := primitiveLaws) p (primeGuard p hp)

include primitiveLaws coefficients in
omit [∀ X, ObjectProperty.IsClosedUnderIsomorphisms (DO.globalLisse X)] in
omit [∀ X, MonoidalClosed (C X)]
  [∀ (E : Type) [Field E], (M.origin E).Monoidal]
  [∀ (E : Type) [Field E], (M.infinity E).Monoidal]
  [∀ (K : Type) [Field K], (boundaryObserver C M K).Additive]
  [∀ (K : Type) [Field K], PreservesFiniteLimits (boundaryObserver C M K)]
  [∀ (K : Type) [Field K], PreservesFiniteColimits (boundaryObserver C M K)] in
theorem actualASProperties :
    ASProperties (actualLineGeometry C U AF G M DO p) (actualAS C U AF primitive p hp) :=
  CanonicalPrimitiveEligibilityFromGeneralPublishedLaws05.computedASProperties
    (C := C) (U := U) (F := AF) (O := primitive) (B := coefficients)
    (G := G) (L := DO.globalLisse) (M := M) (T := primitiveLaws) p (primeGuard p hp)

omit [∀ (E : Type) [Field E], (M.infinity E).Monoidal]
  [∀ X, ObjectProperty.IsClosedUnderIsomorphisms (DO.globalLisse X)]
  [∀ (K : Type) [Field K], (boundaryObserver C M K).Additive]
  [∀ (K : Type) [Field K], PreservesFiniteLimits (boundaryObserver C M K)]
  [∀ (K : Type) [Field K], PreservesFiniteColimits (boundaryObserver C M K)] in
/-- The literal zero restriction computed from the same general curve
boundary has exactly the source origin functor used in the primitive theorem. -/
theorem computed_zero_literal (A : C (genericScheme (ZMod p))) :
    (computedRestriction C U G M DO profiles compact geometricPure genericCompactification
      boundaryTheorems (ZMod p) (primeGuard p hp)).zero A =
      (OriginModelsFromSameComputedCoefficients.genericZero C U M (ZMod p)).obj A := rfl

/-- ZK is computed on ANY scalar, through the actual parameter fraction field. -/
def computedKlZero (lambda : (PhaseField (ZMod p))ˣ) :=
  CoherentGenericSourceZeroFromGeneralOrigin03.computedLocalKlZero
    (C := C) (U := U) (M := M) (G := G) (L := DO.globalLisse) (O := primitive)
    (tame := tame) (laws := originLaws) (p := p) (h2 := primeGuard p hp)
    (R := pointStalks C U AF p)
    (hkl := actualKlProperties C U AF primitive G M DO coefficients primitiveLaws p hp) hp lambda

/-- ZA is computed on ANY nonzero additive scale; the parameter field is infinite. -/
def computedASZero (s : (PhaseField (ZMod p))ˣ) :=
  CoherentGenericSourceZeroFromGeneralOrigin03.computedAdditiveZero
    (C := C) (U := U) (M := M) (G := G) (L := DO.globalLisse) (O := primitive)
    (tame := tame) (laws := originLaws) (p := p) (h2 := primeGuard p hp)
    (R := pointStalks C U AF p)
    (has := actualASProperties C U AF primitive G M DO coefficients primitiveLaws p hp) hp s

omit [∀ X, MonoidalClosed (C X)] in
/-- The total arithmetic primitive takes its genuine raw branch at the
canonical nontrivial character. Both local coordinate maps are the SAME
literal aeval(variableUnit), so their ordinary inverse image is unchanged. -/
theorem actualLocalKl_eq_normalizedThree :
    localSource (ZMod p) (primePulls C U p) (primeLocalPulls C U p)
      (actualKl C U AF primitive p hp) =
      GeneralFuPrimitiveInfinityApplication03.localNormalizedThree
        (C := C) (U := U) (O := primitive) (ZMod p) (PhaseField (ZMod p))
        (primeGuard p hp) (CanonicalSourceCharacter.prime p)
        (CanonicalSourceCharacter.prime_ne_one p) := by
  change (U.pull (ArithmeticSourceMaps.localInputMorphism (ZMod p) (PhaseField (ZMod p)))).obj
    ((primitive.lineTate (ZMod p) (primeGuard p hp) 1).obj
      (ArithmeticPrimitivesFromCommonKatzConstruction.kloosterman3 C primitive (ZMod p)
        (primeGuard p hp) (CanonicalSourceCharacter.prime p))) =
    (U.pull (ArithmeticSourceMaps.localInputMorphism (ZMod p) (PhaseField (ZMod p)))).obj
      ((primitive.lineTate (ZMod p) (primeGuard p hp) 1).obj
        (rawKloosterman3 C primitive (ZMod p) (primeGuard p hp)
          (CanonicalSourceCharacter.prime p) (CanonicalSourceCharacter.prime_ne_one p)))
  rw [ArithmeticPrimitivesFromCommonKatzConstruction.kloosterman3_nontrivial
    C primitive (ZMod p) (primeGuard p hp) (CanonicalSourceCharacter.prime p)
    (CanonicalSourceCharacter.prime_ne_one p)]

/-- Typed SAME-source KR output. The nontrivial-character branch equality
transports the general all-rank Fu application to the literal localSource
and localSheafOperations used by BOTH the core and physical endpoint. -/
def computedKlInfinity :
    PublishedMackey.KloostermanInfinityRules p
      (GeneralFuPrimitiveInfinityApplication03.cubicCover
        (C := C) (U := U) (M := M) (O := primitive) (H := Cover) (R := fu)
        p (PhaseField (ZMod p)) (phaseGuard (ZMod p) (primeGuard p hp)) hp)
      (fu.linearKernel (ZMod p) (PhaseField (ZMod p)) 3
        (primitive.artinSchreier (ZMod p) (primeGuard p hp) (CanonicalSourceCharacter.prime p)))
      (CanonicalLocalCorrelation.sourceInfinity
        (localSheafOperations (ZMod p) (primePulls C U p) (primeLocalPulls C U p)
          (fun A => (QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C
            (localScheme (ZMod p))).obj (op A))
          (NormalizedInfinityFromLiteralOpenAdjunction01.actualJStar C U Open (ZMod p)
            (phaseGuard (ZMod p) (primeGuard p hp))))
        (NormalizedInfinityFromLiteralOpenAdjunction01.actualInfinity C M (ZMod p))
        (localSource (ZMod p) (primePulls C U p) (primeLocalPulls C U p)
          (actualKl C U AF primitive p hp))) := by
  rw [actualLocalKl_eq_normalizedThree C U AF primitive p hp]
  exact GeneralFuPrimitiveInfinityApplication03.computedInfinityRules
    (C := C) (U := U) (M := M) (O := primitive) (H := Cover) (R := fu)
    p (ZMod p) (primeGuard p hp) (phaseGuard (ZMod p) (primeGuard p hp)) hp
    (CanonicalSourceCharacter.prime p) (CanonicalSourceCharacter.prime_ne_one p)
    (localOperations C U Open (ZMod p) (primeGuard p hp))
    (covers.scalar p (ZMod p) (primeGuard p hp) hp
      (CanonicalSourceCharacter.prime p) (CanonicalSourceCharacter.prime_ne_one p))

/-- Finished CoreLocalData is a theorem application OUTPUT. The existing
construction proves source identities, regular-unipotent zero models,
GOS compact rank nine, the zero-boundary subtraction giving parabolic
rank six, the actual j-star/Fourier comparison and the exhaustive local
Fourier profile. It retains the SAME actual origin representation. -/
def computedLocalCore (alpha m n : (ZMod p)ˣ) := by
  let hK : (2 : ZMod p) ≠ 0 := primeGuard p hp
  let ψ := CanonicalSourceCharacter.prime p
  let hψ : ψ ≠ 1 := CanonicalSourceCharacter.prime_ne_one p
  let PP := primePulls C U p
  let RR := primeLocalPulls C U p
  letI : (localSpecialization (ZMod p) PP RR).Monoidal := by
    change (U.pull (projectionMorphism (ZMod p))).Monoidal
    infer_instance
  let DD := originalCurve C U AF G M DO profiles p
  let DG := genericCurve C U G M DO profiles geometricPure (ZMod p)
  let LG := actualLineGeometry C U AF G M DO p
  let kl := actualKl C U AF primitive p hp
  let as := actualAS C U AF primitive p hp
  let dualLocal : C (localScheme (ZMod p)) → C (localScheme (ZMod p)) :=
    fun A => (QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C (localScheme (ZMod p))).obj (op A)
  let middle := NormalizedInfinityFromLiteralOpenAdjunction01.actualJStar C U Open (ZMod p)
    (phaseGuard (ZMod p) hK)
  let ZZ := computedRestriction C U G M DO profiles compact geometricPure genericCompactification
    boundaryTheorems (ZMod p) hK
  let MM := computedCompactification C U G M DO profiles compact Open geometricPure
    genericCompactification affineCompactification boundaryTheorems projective fromCompact toProjective leray fromInfinity
    (ZMod p) hK
  let NN := N (ZMod p) hK
  let SS := S (ZMod p) hK ψ hψ
  let FFO := CoherentNormalizedFourierCompactInfinity03.normalizedData NN SS
  let CC := GeneralFuPrimitiveInfinityApplication03.cubicCover
    (C := C) (U := U) (M := M) (O := primitive) (H := Cover) (R := fu)
    p (PhaseField (ZMod p)) (phaseGuard (ZMod p) hK) hp
  let linearAS := fu.linearKernel (ZMod p) (PhaseField (ZMod p)) 3 as
  exact CanonicalSourceLocalData.canonicalSourceCoreLocalData_overClosure
    (K := ZMod p) (P := PP) (R := RR) (D := DD) (DG := DG) (LG := LG)
    (SR := geometric.scalar p hp) (kl := kl) (as := as)
    (hkl := actualKlProperties C U AF primitive G M DO coefficients primitiveLaws p hp)
    (has := actualASProperties C U AF primitive G M DO coefficients primitiveLaws p hp)
    (dualLocal := dualLocal) (middle := middle) (dualGeneric := genericDual C (ZMod p))
    (T := computedSpecialization C U AF G M DO profiles compact Open geometricPure
      genericCompactification geometric (ZMod p) hK)
    (Z := ZZ) (M := MM)
    (MR := computedCompactificationRules C U G M DO profiles compact Open geometricPure
      genericCompactification affineCompactification boundaryTheorems projective fromCompact toProjective leray fromInfinity
      localization (ZMod p) hK)
    (FO := FFO)
    (FC := computedCompactFourierComparison C U AF primitive G M DO coefficients primitiveLaws compact Open
      affineCompactification perverse N LF S fourier smoothOpen lisseProjection compactBaseChange
      (ZMod p) hK ψ hψ)
    (ZF := computedZeroFunctor C U G M DO profiles compact geometricPure genericCompactification
      boundaryTheorems (ZMod p) hK)
    (tame := tame (GenericOriginFractionFieldCoordinates.ParameterFractionField (ZMod p)))
    (htame := tameNonzero (GenericOriginFractionFieldCoordinates.ParameterFractionField (ZMod p))
      (OriginModelsFromSameComputedCoefficients.fraction_two_ne_zero (ZMod p) hK))
    (ZK := computedKlZero C U AF primitive G M DO coefficients primitiveLaws tame originLaws p hp)
    (ZA := computedASZero C U AF primitive G M DO coefficients primitiveLaws tame originLaws p hp)
    (CRG := geometric.curve (ZMod p) hK) (alpha := alpha) (m := m) (n := n)
    (RP := geometric.pullback p hp
      (GenericSourceSpecialization.specializationMorphism (ZMod p) alpha m n)
      (GenericCurvePullback.radialParameterMorphism (ZMod p) alpha m n)
      (GenericCurvePullback.genericSourceSquare_coordinateBaseChange (ZMod p) alpha m n))
    (point := genericPoint (ZMod p))
    (V := computedGeometricFiberRules
      (C := C) (U := U) (AF := AF) (G := G) (M := M) (DO := DO) (profiles := profiles)
      (compact := compact) (geometricPure := geometricPure)
      (genericCompactification := genericCompactification) (geometric := geometric) (ZMod p) hK)
    (Jinf := NormalizedInfinityFromLiteralOpenAdjunction01.actualInfinity C M (ZMod p))
    (IR := computedInfinityCompatibility C U primitive M compact Open affineCompactification
      perverse N LF S fourier (ZMod p) hK ψ hψ)
    (p := p) (CC := CC) (AS := linearAS)
    (PR := covers.cover p (ZMod p) hK hp)
    (AR := covers.linear p (ZMod p) hK hp ψ hψ)
    (KR := computedKlInfinity
      (C := C) (U := U) (AF := AF) (primitive := primitive) (M := M) (Open := Open)
      (LF := LF) (Cover := Cover) (fu := fu) (covers := covers) p hp)
    (FR := fourier.additivity (ZMod p) hK ψ hψ)
    (FA := covers.admissible p (ZMod p) hK hp ψ hψ)
    (SRF := CoherentNormalizedFourierCompactInfinity03.normalizedRules p NN SS
      (fourier.perverseOrigin p hp (ZMod p) hK ψ hψ)) (hp := hp)

end ActualPrimeCore
end PrimeGap182.TypeIII.CoherentGenericCoreFromGeneralStandardOperations06

#print axioms PrimeGap182.TypeIII.CoherentGenericCoreFromGeneralStandardOperations06.actualKlProperties
#print axioms PrimeGap182.TypeIII.CoherentGenericCoreFromGeneralStandardOperations06.actualASProperties
#print axioms PrimeGap182.TypeIII.CoherentGenericCoreFromGeneralStandardOperations06.computedCompactificationRules
#print axioms PrimeGap182.TypeIII.CoherentGenericCoreFromGeneralStandardOperations06.computedCompactFourierComparison
#print axioms PrimeGap182.TypeIII.CoherentGenericCoreFromGeneralStandardOperations06.computedInfinityCompatibility
#print axioms PrimeGap182.TypeIII.CoherentGenericCoreFromGeneralStandardOperations06.computedKlZero
#print axioms PrimeGap182.TypeIII.CoherentGenericCoreFromGeneralStandardOperations06.computedASZero
#print axioms PrimeGap182.TypeIII.CoherentGenericCoreFromGeneralStandardOperations06.computedKlInfinity
#print axioms PrimeGap182.TypeIII.CoherentGenericCoreFromGeneralStandardOperations06.computedLocalCore

#print axioms PrimeGap182.TypeIII.CoherentGenericCoreFromGeneralStandardOperations06.computedBoundaryClauses
#print axioms PrimeGap182.TypeIII.CoherentGenericCoreFromGeneralStandardOperations06.computedKernelFourierInertia

#print axioms PrimeGap182.TypeIII.CoherentGenericCoreFromGeneralStandardOperations06.actualLocalKl_eq_normalizedThree
