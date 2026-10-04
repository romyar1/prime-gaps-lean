import TypeIIIArithmeticRealizationFromComputedStandardBoundary13
import TypeIIICanonicalPrimitiveEligibilityFromGeneralPublishedLaws05

/-!
# Computed arithmetic realization with computed primitive eligibility

The primitive Kl3/AS eligibility guards are discharged by the all-field,
all-rank, all-character published primitive theorem package on the same
literal C/U/F/O/G/L/M. The seven-field origin, SAME nearby/Frobenius,
arithmetic localization and AM are then constructed by the existing
computed standard boundary chain. No finished primitive eligibility,
OriginInputs, corrected trace, AM or uniform Application is an input.

This is a fixed-prime component, conditional on the explicitly named
genuine GENERAL operation clauses. It does not assert the existence or
interpretation of an arbitrary adic model and has not been executed in Lean.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.ArithmeticRealizationFromPublishedPrimitiveAndBoundary05
open ExactInverseImagesToDerived RationalPointStalksFromUniversalFiber
open QSTPrimitiveBridgesFromCommonKatzConstruction CanonicalPrimeFramework
open StandardGmTraceFromFaithfulArithmeticOperations StandardP1BoundaryPrimitives
open PublishedPhysicalConstruction CanonicalCurveInput
open OriginInputsFromSharedStandardOperationsHELD04
open AllPrimeOriginInputsFromGeneralOperationFamilies05
open ArithmeticRealizationFromComputedStandardBoundary13

universe nu g pt ps h gi
variable (C : Scheme → Type) [∀ X, Category.{0} (C X)]
  [∀ X, Abelian (C X)] [∀ X, MonoidalCategory (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (F : ArithmeticFibers C)
  [∀ (E : Type) [Field E] [Fintype E], (F.fiber E).Additive]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteLimits (F.fiber E)]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteColimits (F.fiber E)]
  (O : Constructions C)
  (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)
  (L : ∀ X : Scheme, ObjectProperty (C X))
  (Mgeo : PrimitiveRamificationFromGeneralKatzTheory.LocalRealization C)
  (nativeCompact : ∀ (E : Type) [Field E] [Fintype E] (_h2 : (2 : E) ≠ 0),
    Fin 3 → C (ArithmeticSourceMaps.fiberScheme E) ⥤ C (Spec (.of E)))
  {S : StandardGmPrimitives.{nu}} (B : Primitives.{nu,0,0} S)
  (AR : FaithfulArithmeticOperations C U F nativeCompact S)
  (originTrait : NativeCommonArithmeticTraitWeilCone.OriginTraitDictionary S B)
  (originGeneral : GeneralSharedOriginTheory.{0,nu,g,ps,pt} (C := C) (U := U) (F := F) (O := O)
    (geometricFiber := G) (lisse := L) (nativeCompact := nativeCompact)
    (B := B) (D := AR) (originTrait := originTrait) (geometricM := Mgeo))
  [realizationMonoidal : ∀ (E : Type) [Field E] [Fintype E] (h2E : (2 : E) ≠ 0),
    letI := B.curveMonoidal E h2E; (AR.curveRealization E h2E).Monoidal]

variable {p : ℕ} [Fact p.Prime] (h2p : (2 : ZMod p) ≠ 0) (hp : 3 < p)


variable {Point : Type h}
  (Obs : CurveDataFromOperations.Observables (C (StartingSourceMaps.sourceScheme (ZMod p))) Point)
  (dualInput : (C (StartingSourceMaps.sourceScheme (ZMod p)))ᵒᵖ ⥤
    C (StartingSourceMaps.sourceScheme (ZMod p)))
  {H : CohomologyData (C (StartingSourceMaps.sourceScheme (ZMod p)))
    (C (PhysicalTorusMorphism.torusScheme (ZMod p)))}
  {PP : ParameterData (C (PhysicalTorusMorphism.torusScheme (ZMod p)))}
  {Ginf : Type gi} [Group Ginf]
  (boundaryGeneral : GeneralArithmeticBoundaryClauses
    (C := C) (U := U) (F := F) (nativeCompact := nativeCompact) (B := B) (AR := AR) (originTrait := originTrait)
    (realizationMonoidal := realizationMonoidal) (Ginf := Ginf) (H := H)
    (h2p := h2p) (Obs := Obs) (dualInput := dualInput))
  (cohomologyGeneral : GeneralArithmeticCohomologyClauses
    (C := C) (U := U) (F := F) (O := O) (G := G) (L := L) (Mgeo := Mgeo)
    (nativeCompact := nativeCompact) (B := B) (AR := AR) (originTrait := originTrait) (originGeneral := originGeneral)
    (realizationMonoidal := realizationMonoidal) (Ginf := Ginf) (H := H) (PP := PP)
    (h2p := h2p) (Obs := Obs) (dualInput := dualInput) (boundaryGeneral := boundaryGeneral))
  [∀ X, (L X).IsClosedUnderIsomorphisms]
  (coefficients : PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.CoefficientFibers C F)
  (primitiveGeneral : CanonicalPrimitiveEligibilityFromGeneralPublishedLaws05.GeneralPrimitiveLaws
    C U F O coefficients G L Mgeo)
  (tateTrace : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
      (A : C (StartingSourceMaps.affineLine (ZMod p))) z,
    (pointStalks C U F p).lineTrace (E := E)
      ((O.lineTate (ZMod p) h2p 1).obj A) z =
      (Fintype.card E : ℂ)⁻¹ * (pointStalks C U F p).lineTrace (E := E) A z)
  (SR : ScalarPullbackRules
    (FourierSourcePullbacks.originalPullbackData (ZMod p)
      (SourceInverseImageSystem.System.geometricPullbacks (primeSource C U p)))
    (computedPrimitiveLine C U F G L Mgeo p) (Obs.curveData dualInput))
  (CR : CurveRules (Obs.curveData dualInput))
  (htame : ∃ z, (originGeneral.tame (ZMod p) z).toAdd ≠ 0)

include C U F O G L Mgeo nativeCompact B AR originTrait originGeneral realizationMonoidal
  h2p hp Obs dualInput boundaryGeneral cohomologyGeneral coefficients primitiveGeneral tateTrace SR CR htame

/-- Both selected primitive guards and all arithmetic realization records
are computed internally from the named GENERAL primitive/operation clauses. -/
def computedCohomologicalRealization :=
  ArithmeticRealizationFromComputedStandardBoundary13.computedCohomologicalRealization
    (C := C) (U := U) (F := F) (O := O) (G := G) (L := L) (Mgeo := Mgeo)
    (nativeCompact := nativeCompact) (B := B) (AR := AR) (originTrait := originTrait)
    (originGeneral := originGeneral) (realizationMonoidal := realizationMonoidal)
    (h2p := h2p) (hp := hp) (Obs := Obs) (dualInput := dualInput)
    (H := H) (PP := PP) (Ginf := Ginf)
    (boundaryGeneral := boundaryGeneral) (cohomologyGeneral := cohomologyGeneral)
    (coefficients := coefficients) (coefficientFormulas := primitiveGeneral.coefficientFormulas)
    (tateTrace := tateTrace) (SR := SR)
    (hkl := CanonicalPrimitiveEligibilityFromGeneralPublishedLaws05.computedKl3Properties
      (C := C) (U := U) (F := F) (O := O) (B := coefficients)
      (G := G) (L := L) (M := Mgeo) (T := primitiveGeneral) (p := p) (h2 := h2p))
    (has := CanonicalPrimitiveEligibilityFromGeneralPublishedLaws05.computedASProperties
      (C := C) (U := U) (F := F) (O := O) (B := coefficients)
      (G := G) (L := L) (M := Mgeo) (T := primitiveGeneral) (p := p) (h2 := h2p))
    (CR := CR) (htame := htame)

end PrimeGap182.TypeIII.ArithmeticRealizationFromPublishedPrimitiveAndBoundary05

#print axioms PrimeGap182.TypeIII.ArithmeticRealizationFromPublishedPrimitiveAndBoundary05.computedCohomologicalRealization
