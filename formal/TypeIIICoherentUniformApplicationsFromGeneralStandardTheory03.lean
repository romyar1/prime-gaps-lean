-- NEW frozen consumer Source; its dependencies were checked, this Source is uncompiled.
import TypeIIICoherentGenericCoreFromGeneralStandardOperations06
import TypeIIIAllPrimeArithmeticFromGeneralStandardOperationTheorems08
import TypeIIIPlaneGeneralTheoryFromSharedOperationsBeforePrime03
import TypeIIISameICRadialFromGeneralRestrictionEvaluationHELD04
import TypeIIIOriginalGoodSourceGeometryFromThinGeneralLaurent03
import TypeIIICoherentStandardDirectEndpointApplicationDraft05
import TypeIIICanonicalCoefficients

/-!
# Closed UniformApplications from one coherent published standard theory

All categories, ordinary/derived/perverse operators, primitive constructors,
point/local observers, whole arithmetic IC lift, compactifications, GENERAL
published clauses, complexity functions and quantitative witnesses are chosen
before p. The source constructs the prime arithmetic realization, primitive
eligibility, same generic zero/boundary/affine/Fourier data, the parabolic rank
six and profile, actual physical IC family and every Application internally.
No forall-prime finished family/profile/rank/comparison/AM/Application provider
is an assumption. Genuine continuous-adic meaning of this precisely GENERAL
standard-theory interface remains external. Numerical hypotheses are unchanged.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory PrimeGap182.TypeIII.TwoAdicComplexEmbedding

namespace PrimeGap182.TypeIII.CoherentUniformApplicationsFromGeneralStandardTheory03
open ExactInverseImagesToDerived QSTPrimitiveBridgesFromCommonKatzConstruction
open RationalPointStalksFromUniversalFiber CanonicalPrimeFramework
open PublishedPhysicalConstruction CanonicalCurveInput PublishedPhaseApplication PublishedLocalConstruction
open GenericSourceSpecialization GenericCurvePullback FourierSourceMaps FourierSourcePullbacks
open OriginModelsFromSameComputedCoefficients CurveDataFromOperations
open QSTCompactBridgeFromCompactifiedDerivedPushforward
open CoherentNormalizedFourierCompactInfinity03 OriginalAffineKernelFromPublishedOpenCompact03
open CanonicalSourceLocalData BoundaryFromSourceModels MiddleFromLocalization FourierStalkInertia
open CoherentGenericCoreFromGeneralStandardOperations06
open StandardGmTraceFromFaithfulArithmeticOperations StandardP1BoundaryPrimitives
open OriginInputsFromSharedStandardOperationsHELD04 AllPrimeOriginInputsFromGeneralOperationFamilies05
open PublishedTypeIII PublishedSupportRules PublishedStalkCertificate PublishedFourierRules
open StartingSourceComplexity PublishedConstructionComplexity PublishedPolynomialComplexity
open CohomologyInputTransport OrdinaryBaseChangeFromDuality OriginalCoreFourierStalk
open ConstantSignInertia GenericPhysicalEntry PhysicalTensorComparison

universe nu g ps pt gi plane curve
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

variable
  [∀ (K : Type) [Field K], (boundaryObserver C M K).Additive]
  [∀ (K : Type) [Field K], PreservesFiniteLimits (boundaryObserver C M K)]
  [∀ (K : Type) [Field K], PreservesFiniteColimits (boundaryObserver C M K)]

variable (boundaryTheorems : GeneralBoundaryTheorems C U G M DO profiles compact geometricPure genericCompactification)

variable (geometric : GeneralGeometricTheorems C U AF G M DO profiles compact geometricPure genericCompactification)

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

variable (localization : GeneralLocalizationTheorems C U G M DO profiles compact Open geometricPure
  genericCompactification affineCompactification boundaryTheorems projective fromCompact toProjective leray fromInfinity)

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

variable (fourier : GeneralFourierFiberTheorems C U primitive M compact affineCompactification perverse N LF S)

variable
  (smoothOpen : OrdinaryFourierKernelExtensionFromGeneralSmoothBaseChange.UniversalSmoothOpenBaseChange C U Open)
  (lisseProjection : OrdinaryFourierKernelExtensionFromGeneralSmoothBaseChange.UniversalLisseOpenProjection
    C U Open DO.globalLisse)
  (compactBaseChange : CoherentGeneralOpenCompactKernelApplication01.UniversalCompactBaseChange C U compact)

variable (Cover : ∀ (E : Type) [Field E], ℕ → Type plane)
  [∀ (E : Type) [Field E] (n : ℕ), Group (Cover E n)]
  (fu : GeneralFuPrimitiveInfinityApplication03.GeneralFuInfinityClauses C U M primitive Cover)

variable (covers : GeneralCoverOperationTheorems C U primitive M Open LF Cover fu)

variable [∀ X, BraidedCategory (C X)]
  [∀ (E : Type) [Field E] [Fintype E], (AF.fiber E).Additive]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteLimits (AF.fiber E)]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteColimits (AF.fiber E)]
  (nativeCompact : ∀ (E : Type) [Field E] [Fintype E] (_hE : (2 : E) ≠ 0),
    Fin 3 → C (ArithmeticSourceMaps.fiberScheme E) ⥤ C (Spec (.of E)))
  {baseStd : StandardGmPrimitives.{nu}} (B : Primitives.{nu,0,0} baseStd)
  (AR : FaithfulArithmeticOperations C U AF nativeCompact baseStd)
  (originTrait : NativeCommonArithmeticTraitWeilCone.OriginTraitDictionary baseStd B)
  (originGeneral : GeneralSharedOriginTheory.{0,nu,g,ps,pt}
    (C := C) (U := U) (F := AF) (O := primitive)
    (geometricFiber := G) (lisse := DO.globalLisse) (nativeCompact := nativeCompact)
    (B := B) (D := AR) (originTrait := originTrait) (geometricM := M))
  [realizationMonoidal : ∀ (E : Type) [Field E] [Fintype E] (hE : (2 : E) ≠ 0),
    letI := B.curveMonoidal E hE; (AR.curveRealization E hE).Monoidal]
  (sourceCompactification : ∀ (K : Type) [Field K], Compactification (SourceProjectionForQST.projection K))
  (signed : ∀ (p : ℕ) [Fact p.Prime],
    C (PhysicalTorusMorphism.torusScheme (ZMod p)) ⥤ C (PhysicalTorusMorphism.torusScheme (ZMod p)))
  (InfinityGroup : ℕ → Type gi) [∀ p, Group (InfinityGroup p)]
  (arithmeticGeneral : AllPrimeArithmeticFromGeneralStandardOperationTheorems08.GeneralArithmeticOperationTheorems
    (C := C) (U := U) (F := AF) (O := primitive) (G := G) (Mgeo := M) (DO := DO) (Z := profiles)
    (nativeCompact := nativeCompact) (B := B) (AR := AR) (originTrait := originTrait)
    (originGeneral := originGeneral) (realizationMonoidal := realizationMonoidal)
    (compactOps := compact) (sourceCompactification := sourceCompactification)
    (signed := signed) (InfinityGroup := InfinityGroup))
  (geometry : QSTDualityBridgesFromSmoothLisseVerdier.LaurentTorusGeometry)
  (standardP1 : OriginalGoodSourceGeometryFromThinGeneralLaurent03.UniversalGoodLaurentGeometry)

abbrev actualParameterOperations : CoherentSourceGlobalCohomologyFromGuardedLaurent04.ParameterOperations C where
  dualTateMinusOne X := QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C X ⋙
    QSTDualityBridgesFromSmoothLisseVerdier.ordinaryTate C DO X (-1)
  signed := signed

abbrev originalH (p : ℕ) [Fact p.Prime] :=
  CoherentSourceGlobalCohomologyFromGuardedLaurent04.nativeCohomology
    C compact (ZMod p) (sourceCompactification (ZMod p))
abbrev originalParameter (p : ℕ) [Fact p.Prime] :=
  CoherentSourceGlobalCohomologyFromGuardedLaurent04.nativeParameter C U DO.globalLisse
    (actualParameterOperations C DO signed) p (pointStalks C U AF p)
abbrev originalDualTate (p : ℕ) [Fact p.Prime] :=
  QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C (PhysicalTorusMorphism.torusScheme (ZMod p)) ⋙
    QSTDualityBridgesFromSmoothLisseVerdier.ordinaryTate C DO (PhysicalTorusMorphism.torusScheme (ZMod p)) (-1)

/-- The local unsigned base needs only lissity and dual Tate; its signed
field is identity, never used for removing the original arithmetic sign. -/
def genericParameter (K : Type) [Field K] : ParameterData (C (parameterScheme K)) where
  Lisse := DO.globalLisse (parameterScheme K)
  Pure := geometricPure (parameterScheme K)
  dualTateMinusOne A := (QSTDualityBridgesFromSmoothLisseVerdier.ordinaryTate C DO (parameterScheme K) (-1)).obj
    ((QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C (parameterScheme K)).obj (op A))
  signed := id
abbrev genericDualTate (K : Type) [Field K] :=
  QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C (parameterScheme K) ⋙
    QSTDualityBridgesFromSmoothLisseVerdier.ordinaryTate C DO (parameterScheme K) (-1)

variable
  (guardedFamily : CoherentSourceGlobalCohomologyFromGuardedLaurent04.GeneralGuardedFamilyLaws
    C U DO.globalLisse G M profiles compact (actualParameterOperations C DO signed)
      (fun p => pointStalks C U AF p))

include geometry standardP1 guardedFamily in
omit [∀ (E : Type) [Field E], (M.origin E).Monoidal]
  [∀ (E : Type) [Field E], (M.infinity E).Monoidal]
  [∀ (K : Type) [Field K], (boundaryObserver C M K).Additive]
  [∀ (K : Type) [Field K], PreservesFiniteLimits (boundaryObserver C M K)]
  [∀ (K : Type) [Field K], PreservesFiniteColimits (boundaryObserver C M K)]
  [∀ X, BraidedCategory (C X)]
  [∀ (E : Type) [Field E] [Fintype E], (AF.fiber E).Additive]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteLimits (AF.fiber E)]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteColimits (AF.fiber E)] in
/-- The actual P1 Laurent chart and ALL-input guarded family theorem
compute the cohomology geometry, including every λ=1 geometric fiber. -/
theorem computedOriginalCohomologyRules (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    CohomologyRules (originalCurve C U AF G M DO profiles p)
      (originalH C compact sourceCompactification p) (originalParameter C U AF DO signed p) :=
  CoherentSourceGlobalCohomologyFromGuardedLaurent04.cohomologyRules
    C U DO.globalLisse G M profiles compact (actualParameterOperations C DO signed)
    (fun p => pointStalks C U AF p) p guardedFamily (primeGuard p hp)
    (OriginalGoodSourceGeometryFromThinGeneralLaurent03.computedGoodSourceGeometry
      geometry standardP1 (ZMod p) (primeGuard p hp)) (sourceCompactification (ZMod p))

variable (PlaneObj : ℕ → Type plane) (CurveObj : ℕ → Type curve)
  (planeTheory : PlaneGeneralTheoryFromSharedOperationsBeforePrime03.GeneralPlaneOperationsAndPublishedTheorems
    PlaneObj CurveObj)
  (planeOps : SameICRadialFromGeneralRestrictionEvaluationHELD04.PlaneOperations
    C PlaneObj planeTheory.surface planeTheory.realization)
  (traceData : ∀ (p : ℕ) [Fact p.Prime], PublishedCovarianceRules.TraceData p (planeTheory.realization p))
  (PD : ∀ (p : ℕ) [Fact p.Prime], PhaseData (ZMod p) ℂ (M.originGroup (PhaseField (ZMod p))))
  (radialLaws : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p),
    PublishedFourierRules.LocalRules (planeTheory.surface p) (planeTheory.coefficient p)
      (CoherentComputedRadialProjection01.computedFourierData (planeTheory.fourier p)
        (ConstantFieldLocalData.phaseData (ZMod p) (AlgebraicClosure (ZMod p)) (PD p))
        (SameICRadialFromGeneralRestrictionEvaluationHELD04.nativeRadial C M
          PlaneObj planeTheory.surface planeTheory.realization planeOps p)))

abbrev actualBaseTheory (p : ℕ) [Fact p.Prime] (hp : 3 < p) :=
  PlaneGeneralTheoryFromSharedOperationsBeforePrime03.theory PlaneObj CurveObj planeTheory p hp
abbrev actualNativeRadial (p : ℕ) [Fact p.Prime] :=
  SameICRadialFromGeneralRestrictionEvaluationHELD04.nativeRadial C M
    PlaneObj planeTheory.surface planeTheory.realization planeOps p
abbrev actualTheory (p : ℕ) [Fact p.Prime] (hp : 3 < p) :=
  CoherentComputedRadialProjection01.computedTheory (actualBaseTheory PlaneObj CurveObj planeTheory p hp)
    (ConstantFieldLocalData.phaseData (ZMod p) (AlgebraicClosure (ZMod p)) (PD p))
    (actualNativeRadial (C := C) (M := M) (PlaneObj := PlaneObj) (CurveObj := CurveObj)
      (planeTheory := planeTheory) (planeOps := planeOps) p) (radialLaws p hp)
abbrev actualIC (p : ℕ) [Fact p.Prime] :=
  SameICRadialFromGeneralRestrictionEvaluationHELD04.intermediateExtension
    C PlaneObj planeTheory.surface planeTheory.realization planeOps p

/-- Precisely ALL-lisse/pure IC theorems on the actual whole arithmetic
lift, restricted to coefficient-invertible primes. No selected IC/profile
or any individual geometric constituent Frobenius lift is a field. -/
structure GeneralEligibleICTheorems : Prop where
  pure : ∀ (p : ℕ) [Fact p.Prime] (hp : 3 < p) A a,
    (originalParameter C U AF DO signed p).Lisse A → (originalParameter C U AF DO signed p).Pure A a →
    (actualTheory (C := C) (M := M) (PlaneObj := PlaneObj) (CurveObj := CurveObj)
        (planeTheory := planeTheory) (planeOps := planeOps) (PD := PD) (radialLaws := radialLaws) p hp).traceWeights.PureOfWeight
      (planeOps.wholeWeil p A) (a + 2)
  full : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p) A a,
    (originalParameter C U AF DO signed p).Lisse A → (originalParameter C U AF DO signed p).Pure A a →
      (planeTheory.surface p).NoProperConstituents (planeOps.middle p A)
  torusIC : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p) A a,
    (originalParameter C U AF DO signed p).Lisse A → (originalParameter C U AF DO signed p).Pure A a →
      (traceData p).TorusIC (planeOps.middle p A)
  trace : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p) A,
    (originalParameter C U AF DO signed p).Lisse A →
    ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ,
      (traceData p).trace E (planeOps.wholeWeil p A) (x : E) (y : E) =
        (RationalPointStalks.Data.torusArithmetic (pointStalks C U AF p)).trace E A x y

variable (middleLaws : GeneralEligibleICTheorems C U AF M DO signed PlaneObj CurveObj
  planeTheory planeOps traceData PD radialLaws)
  (icRestriction : SameICRadialFromGeneralRestrictionEvaluationHELD04.GeneralPlaneRestriction
    C U DO PlaneObj planeTheory.surface planeTheory.realization planeOps)
  (evaluation : SameICRadialFromGeneralRestrictionEvaluationHELD04.GeneralGeometricEvaluation C U M DO)

include middleLaws in
omit [∀ X, BraidedCategory (C X)]
  [∀ (E : Type) [Field E], (M.origin E).Monoidal]
  [∀ (E : Type) [Field E], (M.infinity E).Monoidal]
  [∀ X, ObjectProperty.IsClosedUnderIsomorphisms (DO.globalLisse X)]
  [∀ (K : Type) [Field K], (boundaryObserver C M K).Additive]
  [∀ (K : Type) [Field K], PreservesFiniteLimits (boundaryObserver C M K)]
  [∀ (K : Type) [Field K], PreservesFiniteColimits (boundaryObserver C M K)]
  [∀ (E : Type) [Field E] [Fintype E], (AF.fiber E).Additive]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteLimits (AF.fiber E)]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteColimits (AF.fiber E)] in
/-- The whole IC purity/support/trace clauses produce the old ICR interface. -/
theorem computedICRules (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    IntermediateExtensionRules
      (actualTheory (C := C) (M := M) (PlaneObj := PlaneObj) (CurveObj := CurveObj)
        (planeTheory := planeTheory) (planeOps := planeOps) (PD := PD) (radialLaws := radialLaws) p hp).traceWeights
      (traceData p) (originalParameter C U AF DO signed p)
      (RationalPointStalks.Data.torusArithmetic (pointStalks C U AF p))
      (actualIC (C := C) (PlaneObj := PlaneObj) (CurveObj := CurveObj)
        (planeTheory := planeTheory) (planeOps := planeOps) p) where
  pure := middleLaws.pure p hp
  full := middleLaws.full p hp
  torusIC := middleLaws.torusIC p hp
  trace := middleLaws.trace p hp

abbrev computedICInertia (p : ℕ) [Fact p.Prime] (hp : 3 < p) :=
  SameICRadialFromGeneralRestrictionEvaluationHELD04.inertiaCompatibility
    (C := C) (U := U) (M := M) (DO := DO) (signed := signed)
    (RF := fun p => pointStalks C U AF p) (PlaneObj := PlaneObj)
    (surface := planeTheory.surface) (realization := planeTheory.realization)
    planeOps icRestriction evaluation p (primeGuard p hp)

/- All five envelopes and the actual operation/source complexity functions
are fixed before p. Uniform rules concern ALL standard eligible objects. -/
variable (boundFn : ℕ → ℕ) (sourceCap0 unitCap : ℕ) (bnd : PublishedUniformComplexity.Bounds)
  (inputComplexity : ∀ (K : Type) [Field K], C (StartingSourceMaps.sourceScheme K) → ℕ)
  (parameterComplexity : ∀ (K : Type) [Field K], C (PhysicalTorusMorphism.torusScheme K) → ℕ)
  (lineComplexity : ∀ (K : Type) [Field K], C (StartingSourceMaps.affineLine K) → ℕ)
  (sourceMorphismComplexity : ∀ (K : Type) [Field K], StartingSourceMaps.MorphismComplexity K)
  (torusMorphismComplexity : ∀ (K : Type) [Field K], TorusMorphismComplexity K)

structure GeneralComplexityTheorems where
  operation : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p),
    OperationBounds (D := originalCurve C U AF G M DO profiles p)
      (H := originalH C compact sourceCompactification p) (P := originalParameter C U AF DO signed p)
      boundFn unitCap (inputComplexity (ZMod p)) (parameterComplexity (ZMod p))
      (torusMorphismComplexity (ZMod p))
      (SourceInverseImageSystem.System.torusOperations (primeSource C U p))
      (actualIC (C := C) (PlaneObj := PlaneObj) (CurveObj := CurveObj)
        (planeTheory := planeTheory) (planeOps := planeOps) p)
  torusPolynomial : ∀ (K : Type) [Field K], TorusPolynomialRules (torusMorphismComplexity K)
  source : ∀ (p : ℕ) [Fact p.Prime] (hp : 3 < p), StartingSourceComplexity.Bounds
    (originalPullbackData (ZMod p) (primePulls C U p))
    (primitiveClasses C primitive (ZMod p) (primeGuard p hp)) boundFn sourceCap0
    (lineComplexity (ZMod p)) (inputComplexity (ZMod p)) (sourceMorphismComplexity (ZMod p))
  sourcePolynomial : ∀ (K : Type) [Field K], StartingSourceMaps.PolynomialRules K (sourceMorphismComplexity K)
  uniform : ∀ (p : ℕ) [Fact p.Prime] (hp : 3 < p), PublishedUniformComplexity.Rules bnd
    (actualTheory (C := C) (M := M) (PlaneObj := PlaneObj) (CurveObj := CurveObj)
        (planeTheory := planeTheory) (planeOps := planeOps) (PD := PD) (radialLaws := radialLaws) p hp)
  torus : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p),
    TorusRules (originalParameter C U AF DO signed p)
      (SourceInverseImageSystem.System.torusOperations (primeSource C U p))
      (RationalPointStalks.Data.torusArithmetic (pointStalks C U AF p))

variable (complexity : GeneralComplexityTheorems C U AF primitive G M DO profiles compact sourceCompactification
  signed PlaneObj CurveObj planeTheory planeOps PD radialLaws boundFn sourceCap0 unitCap bnd
  inputComplexity parameterComplexity lineComplexity sourceMorphismComplexity torusMorphismComplexity)

abbrev physicalEnvelope := physicalCap boundFn (sourceCap boundFn sourceCap0) unitCap


/-- GENERAL compact-BC/relative-duality and pairing diagrams on the SAME
standard functors, before p and every coordinate square. These concern
all eligible inputs and never supply the desired ordinary/core/family iso. -/
structure GeneralRelativeCohomologyTheorems where
  originalDuality : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p),
    RelativeDuality (originalCurve C U AF G M DO profiles p)
      (H := originalH C compact sourceCompactification p) (P := originalParameter C U AF DO signed p)
      (originalDualTate C DO p)
  genericLissity : ∀ (K : Type) [Field K] (_hK : (2 : K) ≠ 0),
    CompactLissityRules (genericCurve C U G M DO profiles geometricPure K)
      (H := genericH C compact genericCompactification K) (P := genericParameter C DO geometricPure K)
  genericDuality : ∀ (K : Type) [Field K] (_hK : (2 : K) ≠ 0),
    RelativeDuality (genericCurve C U G M DO profiles geometricPure K)
      (H := genericH C compact genericCompactification K) (P := genericParameter C DO geometricPure K)
      (genericDualTate C DO K)
  curveBaseChange : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p)
    (f : parameterScheme (ZMod p) ⟶ PhysicalTorusMorphism.torusScheme (ZMod p))
    (g : genericScheme (ZMod p) ⟶ StartingSourceMaps.sourceScheme (ZMod p)),
    CoordinateBaseChange (ZMod p) g f →
    CompactBaseChange (originalCurve C U AF G M DO profiles p) (originalDualTate C DO p)
      (genericCurve C U G M DO profiles geometricPure (ZMod p)) (genericDualTate C DO (ZMod p))
      (U.pull f) (U.pull g).obj
      (H := originalH C compact sourceCompactification p)
      (H' := genericH C compact genericCompactification (ZMod p))
      (P := originalParameter C U AF DO signed p)
  pairing : ∀ (p : ℕ) [Fact p.Prime] (hp : 3 < p)
    (f : parameterScheme (ZMod p) ⟶ PhysicalTorusMorphism.torusScheme (ZMod p))
    (g : genericScheme (ZMod p) ⟶ StartingSourceMaps.sourceScheme (ZMod p))
    (sq : CoordinateBaseChange (ZMod p) g f),
    CompactPairingBaseChange (originalCurve C U AF G M DO profiles p) (arithmeticGeneral.curve p hp)
      (computedOriginalCohomologyRules C U AF G M DO profiles compact sourceCompactification signed
        geometry standardP1 guardedFamily p hp)
      (originalDualTate C DO p) (originalDuality p hp)
      (genericCurve C U G M DO profiles geometricPure (ZMod p)) (genericDualTate C DO (ZMod p))
      (genericDuality (ZMod p) (primeGuard p hp)) (U.pull f) (U.pull g).obj
      (realizedCompactFunctor (cohomologyData C compact (genericCompactification (ZMod p)) 1).functorial)
      (curveBaseChange p hp f g sq)

variable (relative : GeneralRelativeCohomologyTheorems
  (C := C) (U := U) (AF := AF) (primitive := primitive) (G := G) (M := M) (DO := DO) (profiles := profiles)
  (compact := compact) (genericCompactification := genericCompactification) (geometricPure := geometricPure)
  (nativeCompact := nativeCompact) (B := B) (AR := AR) (originTrait := originTrait) (originGeneral := originGeneral)
  (realizationMonoidal := realizationMonoidal) (sourceCompactification := sourceCompactification)
  (signed := signed) (InfinityGroup := InfinityGroup) (arithmeticGeneral := arithmeticGeneral)
  (geometry := geometry) (standardP1 := standardP1) (guardedFamily := guardedFamily))

variable (signLine : ∀ (p : ℕ) [Fact p.Prime], C (PhysicalTorusMorphism.torusScheme (ZMod p)))

/-- The original arithmetic sign is retained by AM and trace rules. These
are GENERAL ALL-object tensor and ALL-map geometric constant-line laws;
they do not give a signed-core equivalence or discard Frobenius -1. -/
structure GeneralSignTheorems where
  tensor : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p) A,
    (signed p).obj A ≅ signLine p ⊗ A
  rank : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p)
    (f : parameterScheme (ZMod p) ⟶ PhysicalTorusMorphism.torusScheme (ZMod p)),
    Module.finrank ℂ ((U.pull f ⋙ observer C M (ZMod p)).obj (signLine p)) = 1
  action : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p)
    (f : parameterScheme (ZMod p) ⟶ PhysicalTorusMorphism.torusScheme (ZMod p)),
    ∀ g, ((U.pull f ⋙ observer C M (ZMod p)).obj (signLine p)).ρ g = 1

variable (signLaws : GeneralSignTheorems C U M signed signLine)

abbrev computedSignTensor (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    SignTensorData (originalParameter C U AF DO signed p) where
  line := signLine p
  tensorIso := signLaws.tensor p hp

/-- The auxiliary group in this interface is geometric inertia itself,
with degree zero. Arithmetic Frobenius/sign is separately retained in AM.
Rank-one and trivial geometric action compute the required line model. -/
def computedGeometricSignModel (p : ℕ) [Fact p.Prime] (hp : 3 < p)
    (f : parameterScheme (ZMod p) ⟶ PhysicalTorusMorphism.torusScheme (ZMod p)) :
    SignLineModel (1 : M.originGroup (PhaseField (ZMod p)) →* Multiplicative ℤ)
      (MonoidHom.id _) ((U.pull f ⋙ observer C M (ZMod p)).obj (signLine p)) where
  basis := Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (by simpa using signLaws.rank p hp f))
  action g v := by
    rw [signLaws.action p hp f g]
    simp

/-- GENERAL phase, monomial local-Fourier, coefficient-transport and Fourier
naturality statements. The Fu comparison ranges ALL A,q (including its
nondegeneracy guards), never the selected correlation. Coefficient action
is the already proved continuous root-squaring action, fixed before all
finite extensions and rectangle parameters. No rank/profile/phase subset,
eight-covariance or finished Application is a premise. -/
structure GeneralPhaseAndCoefficientTheorems where
  phase : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p), PhaseRules (PD p)
  monomialFourier : ∀ (p : ℕ) [Fact p.Prime] (hp : 3 < p),
    FuFromQuadraticPullback.Inputs.{0,0,0,plane} p (PD p)
      (cubicFourierData
        (GeneralFuPrimitiveInfinityApplication03.cubicCover
          (C := C) (U := U) (M := M) (O := primitive) (H := Cover) (R := fu)
          p (PhaseField (ZMod p)) (phaseGuard (ZMod p) (primeGuard p hp)) hp)
        (fu.linearKernel (ZMod p) (PhaseField (ZMod p)) 3
          (primitive.artinSchreier (ZMod p) (primeGuard p hp) (CanonicalSourceCharacter.prime p)))
        (LF (ZMod p) (primeGuard p hp) (CanonicalSourceCharacter.prime p) (CanonicalSourceCharacter.prime_ne_one p))
        (covers.admissible p (ZMod p) (primeGuard p hp) hp
          (CanonicalSourceCharacter.prime p) (CanonicalSourceCharacter.prime_ne_one p)))
  coefficient : ∀ (p : ℕ) [Fact p.Prime] (hp : 3 < p),
    CoefficientTraceTransport.Rules
      (T := (complexity.uniform p hp).theory.coefficient) (traceData p)
      (CanonicalCoefficients.tau p hp).toRingEquiv
  fourier : ∀ (p : ℕ) [Fact p.Prime] (hp : 3 < p),
    PublishedCovarianceRules.FourierCovarianceRules
      (T := (complexity.uniform p hp).theory.coefficient) (F := (complexity.uniform p hp).theory.fourier)
      (Units.mk0 2 (primeGuard p hp))

variable (phaseAndCoefficient : GeneralPhaseAndCoefficientTheorems
  (C := C) (U := U) (primitive := primitive) (M := M) (Open := Open) (LF := LF) (Cover := Cover) (fu := fu) (covers := covers)
  (AF := AF) (G := G) (DO := DO) (profiles := profiles) (compact := compact)
  (sourceCompactification := sourceCompactification) (signed := signed)
  (PlaneObj := PlaneObj) (CurveObj := CurveObj) (planeTheory := planeTheory) (planeOps := planeOps)
  (traceData := traceData) (PD := PD) (radialLaws := radialLaws)
  (boundFn := boundFn) (sourceCap0 := sourceCap0) (unitCap := unitCap) (bnd := bnd)
  (inputComplexity := inputComplexity) (parameterComplexity := parameterComplexity) (lineComplexity := lineComplexity)
  (sourceMorphismComplexity := sourceMorphismComplexity) (torusMorphismComplexity := torusMorphismComplexity)
  (complexity := complexity))

include C U AF primitive G M DO profiles coefficients primitiveLaws tame originLaws tameNonzero compact Open geometricPure genericCompactification affineCompactification boundaryTheorems geometric projective fromCompact toProjective leray fromInfinity localization perverse N LF S fourier smoothOpen lisseProjection compactBaseChange Cover fu covers nativeCompact B AR originTrait originGeneral realizationMonoidal sourceCompactification signed InfinityGroup arithmeticGeneral geometry standardP1 guardedFamily PlaneObj CurveObj planeTheory planeOps traceData PD radialLaws middleLaws icRestriction evaluation boundFn sourceCap0 unitCap bnd inputComplexity parameterComplexity lineComplexity sourceMorphismComplexity torusMorphismComplexity complexity relative signLine signLaws phaseAndCoefficient

/-- Compute every specialized cut internally, then apply the already checked
lower same-object endpoint constructor. No local data/profile/family/AM/
Application is supplied. This constructs the actual p>3 Application. -/
def computedApplication (p : ℕ) [Fact p.Prime] (hp : 3 < p)
    (alpha m m' n n' : (ZMod p)ˣ) := by
  let hK : (2 : ZMod p) ≠ 0 := primeGuard p hp
  let PP := primePulls C U p
  let RR := primeLocalPulls C U p
  letI : ∀ (a b c : (ZMod p)ˣ),
      (PP.along (specializationMorphism (ZMod p) a b c)).Monoidal :=
    fun a b c => by
      change (U.pull (specializationMorphism (ZMod p) a b c)).Monoidal
      infer_instance
  letI : (localSpecialization (ZMod p) PP RR).Monoidal := by
    change (U.pull (projectionMorphism (ZMod p))).Monoidal
    infer_instance
  let ψ := CanonicalSourceCharacter.prime p
  let hψ : ψ ≠ 1 := CanonicalSourceCharacter.prime_ne_one p
  let CC := GeneralFuPrimitiveInfinityApplication03.cubicCover
    (C := C) (U := U) (M := M) (O := primitive) (H := Cover) (R := fu)
    p (PhaseField (ZMod p)) (phaseGuard (ZMod p) hK) hp
  let AA := fu.linearKernel (ZMod p) (PhaseField (ZMod p)) 3
    (primitive.artinSchreier (ZMod p) hK ψ)
  let ZZ := computedRestriction C U G M DO profiles compact geometricPure genericCompactification
    boundaryTheorems (ZMod p) hK
  let MM := computedCompactification C U G M DO profiles compact Open geometricPure genericCompactification
    affineCompactification boundaryTheorems projective fromCompact toProjective leray fromInfinity (ZMod p) hK
  let FFO := CoherentNormalizedFourierCompactInfinity03.normalizedData (N (ZMod p) hK) (S (ZMod p) hK ψ hψ)
  exact CoherentStandardDirectEndpointApplicationDraft04.sourceApplication
    (P := PP) (R := RR)
    (D := originalCurve C U AF G M DO profiles p) (DG := genericCurve C U G M DO profiles geometricPure (ZMod p))
    (LG := actualLineGeometry C U AF G M DO p) (SR := arithmeticGeneral.scalar p hp)
    (kl := actualKl C U AF primitive p hp) (as := actualAS C U AF primitive p hp)
    (hkl := actualKlProperties C U AF primitive G M DO coefficients primitiveLaws p hp)
    (has := actualASProperties C U AF primitive G M DO coefficients primitiveLaws p hp)
    (dualLocal := fun A => (QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C (localScheme (ZMod p))).obj (op A))
    (middle := NormalizedInfinityFromLiteralOpenAdjunction01.actualJStar C U Open (ZMod p) (phaseGuard (ZMod p) hK))
    (dualGeneric := genericDual C (ZMod p))
    (T := computedSpecialization C U AF G M DO profiles compact Open geometricPure genericCompactification
      geometric (ZMod p) hK) (J := observer C M (ZMod p))
    (Z := ZZ) (M := MM)
    (MR := computedCompactificationRules C U G M DO profiles compact Open geometricPure genericCompactification
      affineCompactification boundaryTheorems projective fromCompact toProjective leray fromInfinity localization (ZMod p) hK)
    (FO := FFO)
    (FC := computedCompactFourierComparison C U AF primitive G M DO coefficients primitiveLaws compact Open
      affineCompactification perverse N LF S fourier smoothOpen lisseProjection compactBaseChange (ZMod p) hK ψ hψ)
    (RM := computedAffineInertia C U G M DO profiles compact Open geometricPure genericCompactification
      affineCompactification boundaryTheorems projective fromCompact toProjective leray fromInfinity (ZMod p) hK)
    (RI := (computedDiagram C U G M DO profiles compact Open geometricPure genericCompactification
      affineCompactification boundaryTheorems projective fromCompact toProjective leray fromInfinity (ZMod p) hK).localizationInertia)
    (BI := computedKernelFourierInertia C U AF primitive G M DO profiles coefficients primitiveLaws compact Open
      geometricPure genericCompactification affineCompactification boundaryTheorems projective fromCompact toProjective
      leray fromInfinity perverse N LF S fourier smoothOpen lisseProjection compactBaseChange (ZMod p) hK ψ hψ)
    (CRG := geometric.curve (ZMod p) hK)
    (RP := fun a b c => geometric.pullback p hp
      (GenericSourceSpecialization.specializationMorphism (ZMod p) a b c)
      (GenericCurvePullback.radialParameterMorphism (ZMod p) a b c)
      (GenericCurvePullback.genericSourceSquare_coordinateBaseChange (ZMod p) a b c))
    (CR := arithmeticGeneral.curve p hp)
    (GC := computedOriginalCohomologyRules C U AF G M DO profiles compact sourceCompactification signed
      geometry standardP1 guardedFamily p hp)
    (DT0 := originalDualTate C DO p) (S0 := relative.originalDuality p hp)
    (GC' := relative.genericLissity (ZMod p) hK) (DTG := genericDualTate C DO (ZMod p))
    (SG := relative.genericDuality (ZMod p) hK)
    (HC := (cohomologyData C compact (genericCompactification (ZMod p)) 1).functorial)
    (BP := fun f => U.pull f) (CB := relative.curveBaseChange p hp) (PN := relative.pairing p hp)
    (tensorSource := fun _ _ => Iso.refl _)
    (O := SourceInverseImageSystem.System.torusOperations (primeSource C U p))
    (PC := SourceInverseImageSystem.System.parameterComposition (primeSource C U p))
    (ST := computedSignTensor C U AF M DO signed signLine signLaws p hp)
    (degree := (1 : M.originGroup (PhaseField (ZMod p)) →* Multiplicative ℤ))
    (inertia := MonoidHom.id _) (geometric := fun _ => rfl)
    (RS := computedGeometricSignModel C U M signed signLine signLaws p hp)
    (TA := RationalPointStalks.Data.torusArithmetic (pointStalks C U AF p)) (TR := complexity.torus p hp)
    (baseTheory := actualBaseTheory PlaneObj CurveObj planeTheory p hp) (PD := PD p)
    (nativeRadial := actualNativeRadial (C := C) (M := M) (PlaneObj := PlaneObj) (CurveObj := CurveObj)
      (planeTheory := planeTheory) (planeOps := planeOps) p) (radialLaws := radialLaws p hp)
    (UR := complexity.uniform p hp) (traceData := traceData p) (IC := actualIC (C := C) (PlaneObj := PlaneObj) (CurveObj := CurveObj)
        (planeTheory := planeTheory) (planeOps := planeOps) p)
    (IR := computedICInertia (C := C) (U := U) (AF := AF) (M := M) (DO := DO) (signed := signed)
       (PlaneObj := PlaneObj) (CurveObj := CurveObj) (planeTheory := planeTheory) (planeOps := planeOps)
       (icRestriction := icRestriction) (evaluation := evaluation) p hp)
    (ZF := computedZeroFunctor C U G M DO profiles compact geometricPure genericCompactification boundaryTheorems (ZMod p) hK)
    (tame := tame (GenericOriginFractionFieldCoordinates.ParameterFractionField (ZMod p)))
    (htame := tameNonzero (GenericOriginFractionFieldCoordinates.ParameterFractionField (ZMod p))
      (fraction_two_ne_zero (ZMod p) hK))
    (ZK := computedKlZero C U AF primitive G M DO coefficients primitiveLaws tame originLaws p hp)
    (ZA := computedASZero C U AF primitive G M DO coefficients primitiveLaws tame originLaws p hp)
    (point := genericPoint (ZMod p))
    (V := computedGeometricFiberRules C U AF G M DO profiles compact geometricPure genericCompactification geometric (ZMod p) hK)
    (Jinf := NormalizedInfinityFromLiteralOpenAdjunction01.actualInfinity C M (ZMod p))
    (IRinf := computedInfinityCompatibility C U primitive M compact Open affineCompactification perverse N LF S fourier (ZMod p) hK ψ hψ)
    (CC := CC) (AS := AA) (PR := covers.cover p (ZMod p) hK hp) (AR := covers.linear p (ZMod p) hK hp ψ hψ)
    (KR := computedKlInfinity
      (C := C) (U := U) (AF := AF) (primitive := primitive) (M := M) (Open := Open)
      (LF := LF) (Cover := Cover) (fu := fu) (covers := covers) p hp)
    (FR := fourier.additivity (ZMod p) hK ψ hψ) (FA := covers.admissible p (ZMod p) hK hp ψ hψ)
    (SRF := CoherentNormalizedFourierCompactInfinity03.normalizedRules p (N (ZMod p) hK) (S (ZMod p) hK ψ hψ)
      (fourier.perverseOrigin p hp (ZMod p) hK ψ hψ)) (hp := hp)
    (AM := AllPrimeArithmeticFromGeneralStandardOperationTheorems08.computedCohomologicalRealization
      (C := C) (U := U) (F := AF) (O := primitive) (G := G) (Mgeo := M) (DO := DO) (Z := profiles)
      (nativeCompact := nativeCompact) (B := B) (AR := AR) (originTrait := originTrait)
      (originGeneral := originGeneral) (realizationMonoidal := realizationMonoidal)
      (compactOps := compact) (sourceCompactification := sourceCompactification) (signed := signed)
      (InfinityGroup := InfinityGroup) (coefficients := coefficients) (primitiveGeneral := primitiveLaws)
      (general := arithmeticGeneral) p hp)
    (ICR := computedICRules C U AF M DO signed PlaneObj CurveObj planeTheory planeOps traceData
      PD radialLaws middleLaws p hp)
    (boundFn := boundFn) (sourceCap0 := sourceCap0) (unitCap := unitCap)
    (ci := inputComplexity (ZMod p)) (cp := parameterComplexity (ZMod p)) (cm := torusMorphismComplexity (ZMod p))
    (QB := complexity.operation p hp) (QM := complexity.torusPolynomial (ZMod p))
    (SC := primitiveClasses C primitive (ZMod p) hK) (cl := lineComplexity (ZMod p))
    (cs := sourceMorphismComplexity (ZMod p)) (QS := complexity.source p hp)
    (QSM := complexity.sourcePolynomial (ZMod p))
    (hhyper := ArithmeticPrimitivesFromCommonKatzConstruction.canonical_hypergeometric C primitive p hK U (pointStalks C U AF p))
    (hAS := ArithmeticPrimitivesFromCommonKatzConstruction.canonical_nontrivialAS C primitive p hK U (pointStalks C U AF p))
    (bnd := bnd) (phaseLaws := phaseAndCoefficient.phase p hp) (fuGeometry := phaseAndCoefficient.monomialFourier p hp)
    (sigma := CanonicalCoefficients.sigma p hp) (hsigma := CanonicalCoefficients.sigma_stdAddChar p hp)
    (chebotarev := CanonicalCoefficients.chebotarev p hp (traceData p) (phaseAndCoefficient.coefficient p hp))
    (fourierCovariance := phaseAndCoefficient.fourier p hp) alpha m m' n n'

/-- All constants are fixed before p; at each admissible prime the actual
same-theory Application is computed from the named GENERAL clauses. -/
def computedUniformApplications :
    UniformApplications (bnd.stalkCap (physicalEnvelope boundFn sourceCap0 unitCap))
      (bnd.physicalSupportCap (physicalEnvelope boundFn sourceCap0 unitCap))
      (bnd.exceptionalCap (physicalEnvelope boundFn sourceCap0 unitCap))
      (bnd.properCap (physicalEnvelope boundFn sourceCap0 unitCap))
      (bnd.punctualCap (physicalEnvelope boundFn sourceCap0 unitCap)) where
  theory p _ hcut := (complexity.uniform p (three_lt_of_cutoff hcut)).theory
  application p _ hcut alpha m m' n n' ha hm hm' hn hn' :=
    computedApplication
    (C := C) (U := U) (AF := AF) (primitive := primitive) (G := G)
    (M := M) (DO := DO) (profiles := profiles) (coefficients := coefficients) (primitiveLaws := primitiveLaws)
    (tame := tame) (originLaws := originLaws) (tameNonzero := tameNonzero) (compact := compact) (Open := Open)
    (geometricPure := geometricPure) (genericCompactification := genericCompactification) (affineCompactification := affineCompactification) (boundaryTheorems := boundaryTheorems) (geometric := geometric)
    (projective := projective) (fromCompact := fromCompact) (toProjective := toProjective) (leray := leray) (fromInfinity := fromInfinity)
    (localization := localization) (perverse := perverse) (N := N) (LF := LF) (S := S)
    (fourier := fourier) (smoothOpen := smoothOpen) (lisseProjection := lisseProjection) (compactBaseChange := compactBaseChange) (Cover := Cover)
    (fu := fu) (covers := covers) (nativeCompact := nativeCompact) (B := B) (AR := AR)
    (originTrait := originTrait) (originGeneral := originGeneral) (realizationMonoidal := realizationMonoidal) (sourceCompactification := sourceCompactification) (signed := signed)
    (InfinityGroup := InfinityGroup) (arithmeticGeneral := arithmeticGeneral) (geometry := geometry) (standardP1 := standardP1) (guardedFamily := guardedFamily)
    (PlaneObj := PlaneObj) (CurveObj := CurveObj) (planeTheory := planeTheory) (planeOps := planeOps) (traceData := traceData)
    (PD := PD) (radialLaws := radialLaws) (middleLaws := middleLaws) (icRestriction := icRestriction) (evaluation := evaluation)
    (boundFn := boundFn) (sourceCap0 := sourceCap0) (unitCap := unitCap) (bnd := bnd) (inputComplexity := inputComplexity)
    (parameterComplexity := parameterComplexity) (lineComplexity := lineComplexity) (sourceMorphismComplexity := sourceMorphismComplexity) (torusMorphismComplexity := torusMorphismComplexity) (complexity := complexity)
    (relative := relative) (signLine := signLine) (signLaws := signLaws) (phaseAndCoefficient := phaseAndCoefficient)
      p (three_lt_of_cutoff hcut)
      (Units.mk0 alpha ha) (Units.mk0 m hm) (Units.mk0 m' hm')
      (Units.mk0 n hn) (Units.mk0 n' hn')

/-- The exact original finite/curve exceptional Type III proposition,
with the numerical hypotheses elsewhere in the project unchanged. -/
theorem computedTypeIIIInput : HasFiniteExceptionalTypeIIIInput :=
  (computedUniformApplications
    (C := C) (U := U) (AF := AF) (primitive := primitive) (G := G)
    (M := M) (DO := DO) (profiles := profiles) (coefficients := coefficients) (primitiveLaws := primitiveLaws)
    (tame := tame) (originLaws := originLaws) (tameNonzero := tameNonzero) (compact := compact) (Open := Open)
    (geometricPure := geometricPure) (genericCompactification := genericCompactification) (affineCompactification := affineCompactification) (boundaryTheorems := boundaryTheorems) (geometric := geometric)
    (projective := projective) (fromCompact := fromCompact) (toProjective := toProjective) (leray := leray) (fromInfinity := fromInfinity)
    (localization := localization) (perverse := perverse) (N := N) (LF := LF) (S := S)
    (fourier := fourier) (smoothOpen := smoothOpen) (lisseProjection := lisseProjection) (compactBaseChange := compactBaseChange) (Cover := Cover)
    (fu := fu) (covers := covers) (nativeCompact := nativeCompact) (B := B) (AR := AR)
    (originTrait := originTrait) (originGeneral := originGeneral) (realizationMonoidal := realizationMonoidal) (sourceCompactification := sourceCompactification) (signed := signed)
    (InfinityGroup := InfinityGroup) (arithmeticGeneral := arithmeticGeneral) (geometry := geometry) (standardP1 := standardP1) (guardedFamily := guardedFamily)
    (PlaneObj := PlaneObj) (CurveObj := CurveObj) (planeTheory := planeTheory) (planeOps := planeOps) (traceData := traceData)
    (PD := PD) (radialLaws := radialLaws) (middleLaws := middleLaws) (icRestriction := icRestriction) (evaluation := evaluation)
    (boundFn := boundFn) (sourceCap0 := sourceCap0) (unitCap := unitCap) (bnd := bnd) (inputComplexity := inputComplexity)
    (parameterComplexity := parameterComplexity) (lineComplexity := lineComplexity) (sourceMorphismComplexity := sourceMorphismComplexity) (torusMorphismComplexity := torusMorphismComplexity) (complexity := complexity)
    (relative := relative) (signLine := signLine) (signLaws := signLaws) (phaseAndCoefficient := phaseAndCoefficient)).hasFiniteExceptionalTypeIIIInput_on_torus

end PrimeGap182.TypeIII.CoherentUniformApplicationsFromGeneralStandardTheory03

#print axioms PrimeGap182.TypeIII.CoherentUniformApplicationsFromGeneralStandardTheory03.computedOriginalCohomologyRules
#print axioms PrimeGap182.TypeIII.CoherentUniformApplicationsFromGeneralStandardTheory03.computedICRules
#print axioms PrimeGap182.TypeIII.CoherentUniformApplicationsFromGeneralStandardTheory03.computedSignTensor
#print axioms PrimeGap182.TypeIII.CoherentUniformApplicationsFromGeneralStandardTheory03.computedGeometricSignModel
#print axioms PrimeGap182.TypeIII.CoherentUniformApplicationsFromGeneralStandardTheory03.computedApplication
#print axioms PrimeGap182.TypeIII.CoherentUniformApplicationsFromGeneralStandardTheory03.computedUniformApplications
#print axioms PrimeGap182.TypeIII.CoherentUniformApplicationsFromGeneralStandardTheory03.computedTypeIIIInput
