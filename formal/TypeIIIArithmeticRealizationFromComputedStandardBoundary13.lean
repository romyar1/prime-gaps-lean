import TypeIIIAllPrimeOriginInputsFromGeneralOperationFamilies05
import TypeIIICoherentArithmeticFromLiteralPrimitivesDraft11
import TypeIIILiteralArithmeticOriginBoundaryBindingHELD04

/-!
# Arithmetic realization from computed standard origin and boundary operations

ONE ordinary theory, source primitives, point Frobenius and origin action are
fixed before p. The arithmetic origin group is the common positive trait
for Fp, distinct from the geometric function-field group. J0 and LF0 are
literal common native operations, not independently selected dictionaries.

Seven-field origin Inputs, geometric boundary sequence/restriction, arithmetic
restriction, specialization, covariance and invariant-product boundary action
are outputs. The lower clauses quantify ALL ordinary eligible objects: actual
localization/dual/tensor/Frobenius operations, point cohomology, Tate and sign.
No completed OriginInputs, BS, AZ, AP, AB, SC or AM family is an input.

This is a fixed-prime arithmetic component for the coherent uniform factory.
Primitive hkl/has remain eligibility guards for the separate general primitive
application. Existing explicit standard primitive/constant interpretation
boundaries are not proved by packaging arbitrary MODEL predicates. Genuine
continuous-adic interpretation and SAME-operator calibration remain external.
NEW staged Source only, not a Lean check or completed uniform endpoint.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.ArithmeticRealizationFromComputedStandardBoundary13
open ExactInverseImagesToDerived RationalPointStalksFromUniversalFiber
open QSTPrimitiveBridgesFromCommonKatzConstruction CanonicalPrimeFramework
open StandardGmTraceFromFaithfulArithmeticOperations StandardP1BoundaryPrimitives
open PublishedPhysicalConstruction CanonicalCurveInput BoundaryFromSourceModels
open RestrictionFrobenius ArithmeticBoundaryFromSources ArithmeticSourceTransport
open OriginInputsFromSharedStandardOperationsHELD04
open AllPrimeOriginInputsFromGeneralOperationFamilies05

universe mu nu g pt ps h gi
variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)]
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
  (originGeneral : GeneralSharedOriginTheory.{mu,nu,g,ps,pt} (C := C) (U := U) (F := F) (O := O)
    (geometricFiber := G) (lisse := L) (nativeCompact := nativeCompact)
    (B := B) (D := AR) (originTrait := originTrait) (geometricM := Mgeo))
  [realizationMonoidal : ∀ (E : Type) [Field E] [Fintype E] (h2E : (2 : E) ≠ 0),
    letI := B.curveMonoidal E h2E; (AR.curveRealization E h2E).Monoidal]

variable {p : ℕ} [Fact p.Prime] (h2p : (2 : ZMod p) ≠ 0) (hp : 3 < p)

/-- The literal finite-extension arithmetic nearby operation. -/
abbrev arithmeticNearby (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] :
    C (ArithmeticSourceMaps.fiberScheme E) ⥤ FDRep ℂ (CommonGroup.{g} (ZMod p)) :=
  nativeNearby.{mu,nu,g} C U F nativeCompact B AR originTrait
    (ZMod p) E (extensionGuard p h2p E)

/-- Geometric Frobenius is the SAME full local Weil action. -/
abbrev arithmeticWeil (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] :
    LocalWeilAction.Data
      (arithmeticNearby.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E)
      (NativeCommonArithmeticTraitWeilCone.conjugation (ZMod p) E B originTrait
        (extensionGuard p h2p E)) :=
  NativeCommonArithmeticTraitWeilCone.weilData.{0,mu,nu,g} (ZMod p) E B
    originTrait (extensionGuard p h2p E) (AR.curveRealization E (extensionGuard p h2p E))

local instance arithmeticNearbyMonoidal
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] :
    (arithmeticNearby.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).Monoidal :=
  NativeCommonArithmeticTraitWeilCone.fiberMonoidal.{0,mu,nu,g} (ZMod p) E B originTrait
    (extensionGuard p h2p E) (AR.curveRealization E (extensionGuard p h2p E))
    (realizationMonoidal E (extensionGuard p h2p E))

/-- The actual specialization, using the ONE universal inverse-image system. -/
abbrev arithmeticAlong (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (x y : Eˣ) :=
  (SourceInverseImageSystem.System.arithmeticPullbacks (primeSource C U p) E).along
    (ArithmeticSourceMaps.specializationMorphism (ZMod p) E x y)

/-- Monoidality is the existing SAME universal inverse-image structure. -/
local instance arithmeticAlongMonoidal
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (x y : Eˣ) :
    (arithmeticAlong (p := p) C U E x y).Monoidal := by
  change (U.pull (ArithmeticSourceMaps.specializationMorphism (ZMod p) E x y)).Monoidal
  infer_instance

variable {Point : Type h}
  (Obs : CurveDataFromOperations.Observables (C (StartingSourceMaps.sourceScheme (ZMod p))) Point)
  (dualInput : (C (StartingSourceMaps.sourceScheme (ZMod p)))ᵒᵖ ⥤
    C (StartingSourceMaps.sourceScheme (ZMod p)))
  {H : CohomologyData (C (StartingSourceMaps.sourceScheme (ZMod p)))
    (C (PhysicalTorusMorphism.torusScheme (ZMod p)))}
  {PP : ParameterData (C (PhysicalTorusMorphism.torusScheme (ZMod p)))}
  {Ginf : Type gi} [Group Ginf]

/-- Only actual maps and guarded ALL-object localization/dual/slope clauses.
This record is neither a supplied boundary sequence nor a restriction model. -/
structure OrdinaryBoundaryClauses
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (x y : Eˣ) where
  infinity : C (StartingSourceMaps.sourceScheme (ZMod p)) ⥤ FDRep ℂ Ginf
  dualRestriction : ∀ A, Obs.Lisse A →
    Representation.Equiv
      ((arithmeticAlong (p := p) C U E x y ⋙ arithmeticNearby.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).obj
        (dualInput.obj (op A))).ρ
      (PublishedPhaseApplication.dualRepresentation
        ((arithmeticAlong (p := p) C U E x y ⋙ arithmeticNearby.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).obj A)).ρ
  positiveSlope : ∀ A, Obs.Isoclinic A 1 →
    Representation.invariants (infinity.obj A).ρ = ⊥
  connecting : ∀ A,
    (Representation.invariants
      ((arithmeticAlong (p := p) C U E x y ⋙ arithmeticNearby.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).obj A).ρ ×
      Representation.invariants (infinity.obj A).ρ) →ₗ[ℂ]
        ((RationalPointStalks.Data.torusArithmetic (pointStalks C U F p)).fiber E x y).obj (H.compact A)
  connecting_injective : ∀ A, Obs.Lisse A → Obs.Isoclinic A 1 →
    Function.Injective (connecting A)
  connecting_exact : ∀ A, Obs.Lisse A → Obs.TameZero A → Obs.Isoclinic A 1 →
    LinearMap.range (connecting A) = LinearMap.ker
      (((RationalPointStalks.Data.torusArithmetic (pointStalks C U F p)).fiber E x y).map
        (H.comparison A)).hom

variable (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (x y : Eˣ)
  (boundary : OrdinaryBoundaryClauses.{mu,nu,g,h,gi} (Ginf := Ginf) (H := H) C U F nativeCompact B AR originTrait h2p Obs dualInput E x y)

include realizationMonoidal

/-- Assemble the geometric maps on zero=actual along followed by actual J0. -/
def computedBoundaryMaps :=
  LiteralArithmeticOriginBoundaryBindingHELD04.canonicalBoundaryMaps
    (Obs := Obs) (dualInput := dualInput) (H := H)
    (coeffFiber := (RationalPointStalks.Data.torusArithmetic (pointStalks C U F p)).fiber E x y)
    (along := arithmeticAlong (p := p) C U E x y)
    (J := arithmeticNearby.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E)
    (infinity := boundary.infinity) (dualRestriction := boundary.dualRestriction)
    (positiveSlope := boundary.positiveSlope) (toCompact := boundary.connecting)
    (boundaryInjective := boundary.connecting_injective)
    (boundaryExact := boundary.connecting_exact)

abbrev computedBoundarySequence :=
  letI : (arithmeticAlong (p := p) C U E x y).Monoidal := by
    change (U.pull (ArithmeticSourceMaps.specializationMorphism (ZMod p) E x y)).Monoidal
    infer_instance
  letI : (arithmeticNearby.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).Monoidal :=
    NativeCommonArithmeticTraitWeilCone.fiberMonoidal.{0,mu,nu,g} (ZMod p) E B originTrait
      (extensionGuard p h2p E) (AR.curveRealization E (extensionGuard p h2p E))
      (realizationMonoidal E (extensionGuard p h2p E))
  (computedBoundaryMaps C U F nativeCompact B AR originTrait h2p Obs dualInput E x y boundary).data.boundarySequence

abbrev computedRestriction :=
  letI : (arithmeticAlong (p := p) C U E x y).Monoidal := by
    change (U.pull (ArithmeticSourceMaps.specializationMorphism (ZMod p) E x y)).Monoidal
    infer_instance
  letI : (arithmeticNearby.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).Monoidal :=
    NativeCommonArithmeticTraitWeilCone.fiberMonoidal.{0,mu,nu,g} (ZMod p) E B originTrait
      (extensionGuard p h2p E) (AR.curveRealization E (extensionGuard p h2p E))
      (realizationMonoidal E (extensionGuard p h2p E))
  (computedBoundaryMaps C U F nativeCompact B AR originTrait h2p Obs dualInput E x y boundary).data.restriction
    (Obs.tensorComparison dualInput) (Obs.dualComparison dualInput)

variable
  (tensorWeil : ArithmeticTensorFromWeil.TensorRules
    (arithmeticWeil.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E))
  (dualWeil : ∀ A (hA : Obs.Lisse A) z,
    (computedRestriction.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal) h2p Obs dualInput E x y boundary).dualZero A hA
      ((arithmeticWeil.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).localFrobenius.action
        ((arithmeticAlong (p := p) C U E x y).obj ((Obs.curveData dualInput).dual A)) z) =
    ((arithmeticWeil.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).localFrobenius.action
      ((arithmeticAlong (p := p) C U E x y).obj A)).symm.toLinearMap.dualMap
      ((computedRestriction.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal) h2p Obs dualInput E x y boundary).dualZero A hA z))

/-- Tensor and guarded dual rules construct AP on that SAME zero. -/
abbrev computedArithmeticRestriction : RestrictionFrobenius.ArithmeticRestriction
    (computedRestriction.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait
      (realizationMonoidal := realizationMonoidal) h2p Obs dualInput E x y boundary) :=
  letI : (arithmeticAlong (p := p) C U E x y).Monoidal := by
    change (U.pull (ArithmeticSourceMaps.specializationMorphism (ZMod p) E x y)).Monoidal
    infer_instance
  letI : (arithmeticNearby.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).Monoidal :=
    NativeCommonArithmeticTraitWeilCone.fiberMonoidal.{0,mu,nu,g} (ZMod p) E B originTrait
      (extensionGuard p h2p E) (AR.curveRealization E (extensionGuard p h2p E))
      (realizationMonoidal E (extensionGuard p h2p E))
  { zeroFr := fun A =>
      (arithmeticWeil.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).localFrobenius.action
        ((arithmeticAlong (p := p) C U E x y).obj A)
    tensor_natural := by
      intro A A' z
      change TensorListRepresentation.equivOfIso
        ((arithmeticAlong (p := p) C U E x y ⋙
          arithmeticNearby.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).mapIso
            (Iso.refl (A ⊗ A')) ≪≫
          (Functor.Monoidal.μIso
            (arithmeticAlong (p := p) C U E x y ⋙
              arithmeticNearby.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E) A A').symm)
        ((arithmeticWeil.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).localFrobenius.action
          ((arithmeticAlong (p := p) C U E x y).obj (A ⊗ A')) z) =
        TensorProduct.map
          ((arithmeticWeil.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).localFrobenius.action
            ((arithmeticAlong (p := p) C U E x y).obj A)).toLinearMap
          ((arithmeticWeil.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).localFrobenius.action
            ((arithmeticAlong (p := p) C U E x y).obj A')).toLinearMap
          (TensorListRepresentation.equivOfIso
            ((arithmeticAlong (p := p) C U E x y ⋙
              arithmeticNearby.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).mapIso
                (Iso.refl (A ⊗ A')) ≪≫
              (Functor.Monoidal.μIso
                (arithmeticAlong (p := p) C U E x y ⋙
                  arithmeticNearby.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E) A A').symm) z)
      have hi :
          (arithmeticAlong (p := p) C U E x y ⋙
            arithmeticNearby.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).mapIso
              (Iso.refl (A ⊗ A')) ≪≫
            (Functor.Monoidal.μIso
              (arithmeticAlong (p := p) C U E x y ⋙
                arithmeticNearby.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E) A A').symm =
          (Functor.Monoidal.μIso
            (arithmeticAlong (p := p) C U E x y ⋙
              arithmeticNearby.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E) A A').symm := by
        ext
        simp
      rw [hi]
      exact ArithmeticTensorFromWeil.tensor_inverse
        (arithmeticWeil.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E)
        (arithmeticAlong (p := p) C U E x y) tensorWeil A A' z
    dual_natural := dualWeil }

include realizationMonoidal originTrait h2p E in
omit [∀ (E : Type) [Field E] [Fintype E], (F.fiber E).Additive]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteLimits (F.fiber E)]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteColimits (F.fiber E)] in
/-- No second inertia action or separately chosen covariance square. -/
theorem computedCovariance A z v :
    (computedArithmeticRestriction.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal)
      h2p Obs dualInput E x y boundary tensorWeil dualWeil).zeroFr A
      (((computedRestriction.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal) h2p Obs dualInput E x y boundary).zero A).ρ z v) =
    ((computedRestriction.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal) h2p Obs dualInput E x y boundary).zero A).ρ
      (NativeCommonArithmeticTraitWeilCone.conjugation (ZMod p) E B originTrait (extensionGuard p h2p E) z)
      ((computedArithmeticRestriction.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal)
        h2p Obs dualInput E x y boundary tensorWeil dualWeil).zeroFr A v) := by
  change (arithmeticWeil.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).localFrobenius.action
    ((arithmeticAlong (p := p) C U E x y).obj A)
      (((arithmeticNearby.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).obj ((arithmeticAlong (p := p) C U E x y).obj A)).ρ z v) = _
  exact (arithmeticWeil.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).covariance
    ((arithmeticAlong (p := p) C U E x y).obj A) z v


section AllFiniteExtensions
omit E x y boundary tensorWeil dualWeil

/-- GENERAL ordinary localization and categorical Weil laws on ALL source
objects at EVERY finite extension and parameter. No record of BS/AZ/AP exists
as an input. These clauses must be the genuine standard operation projections. -/
structure GeneralArithmeticBoundaryClauses where
  ordinary : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (x y : Eˣ),
    OrdinaryBoundaryClauses.{mu,nu,g,h,gi} (Ginf := Ginf) (H := H) C U F nativeCompact B AR originTrait h2p Obs dualInput E x y
  tensorWeil : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
    ArithmeticTensorFromWeil.TensorRules (arithmeticWeil.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E)
  dualWeil : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (x y : Eˣ)
      A (hA : Obs.Lisse A) z,
    (computedRestriction.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal) h2p Obs dualInput E x y
      (ordinary E x y)).dualZero A hA
      ((arithmeticWeil.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).localFrobenius.action
        ((arithmeticAlong (p := p) C U E x y).obj ((Obs.curveData dualInput).dual A)) z) =
    ((arithmeticWeil.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).localFrobenius.action
      ((arithmeticAlong (p := p) C U E x y).obj A)).symm.toLinearMap.dualMap
      ((computedRestriction.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal) h2p Obs dualInput E x y
        (ordinary E x y)).dualZero A hA z)

variable (boundaryGeneral : GeneralArithmeticBoundaryClauses.{mu,nu,g,h,gi} (Ginf := Ginf) (H := H) C U F nativeCompact B AR originTrait
  (realizationMonoidal := realizationMonoidal) h2p Obs dualInput)

abbrev allBoundaryMaps (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (x y : Eˣ) :=
  computedBoundaryMaps C U F nativeCompact B AR originTrait h2p Obs dualInput E x y
    (boundaryGeneral.ordinary E x y)
abbrev allBoundarySequence (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (x y : Eˣ) :=
  letI : (arithmeticAlong (p := p) C U E x y).Monoidal := by
    change (U.pull (ArithmeticSourceMaps.specializationMorphism (ZMod p) E x y)).Monoidal
    infer_instance
  letI : (arithmeticNearby.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).Monoidal :=
    NativeCommonArithmeticTraitWeilCone.fiberMonoidal.{0,mu,nu,g} (ZMod p) E B originTrait
      (extensionGuard p h2p E) (AR.curveRealization E (extensionGuard p h2p E))
      (realizationMonoidal E (extensionGuard p h2p E))
  (allBoundaryMaps.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal) h2p Obs dualInput
    boundaryGeneral E x y).data.boundarySequence
abbrev allRestriction (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (x y : Eˣ) :=
  computedRestriction.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal) h2p Obs dualInput E x y
    (boundaryGeneral.ordinary E x y)
abbrev allArithmeticRestriction (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (x y : Eˣ) :=
  computedArithmeticRestriction.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal) h2p Obs dualInput E x y
    (boundaryGeneral.ordinary E x y) (boundaryGeneral.tensorWeil E) (boundaryGeneral.dualWeil E x y)

omit [∀ (E : Type) [Field E] [Fintype E], (F.fiber E).Additive]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteLimits (F.fiber E)]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteColimits (F.fiber E)] in
/-- Universal covariance is inherited from the SAME common Weil action. -/
theorem allCovariance (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (x y : Eˣ) A z v :
    (allArithmeticRestriction.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal) h2p Obs dualInput
      boundaryGeneral E x y).zeroFr A
      (((allRestriction.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal) h2p Obs dualInput
        boundaryGeneral E x y).zero A).ρ z v) =
    ((allRestriction.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal) h2p Obs dualInput
      boundaryGeneral E x y).zero A).ρ
      (NativeCommonArithmeticTraitWeilCone.conjugation (ZMod p) E B originTrait (extensionGuard p h2p E) z)
      ((allArithmeticRestriction.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal) h2p Obs dualInput
        boundaryGeneral E x y).zeroFr A v) :=
  computedCovariance C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal) h2p Obs dualInput
    E x y (boundaryGeneral.ordinary E x y) (boundaryGeneral.tensorWeil E)
    (boundaryGeneral.dualWeil E x y) A z v

/-- General arithmetic localization, point cohomology and sign laws on the
SAME operators. Each record clause quantifies all ordinary objects; none
asserts a corrected trace or boundary model of the selected TypeIII family. -/
structure GeneralArithmeticCohomologyClauses where
  point : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], Eˣ → Eˣ → Point
  fiberRules : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (x y : Eˣ),
    CurveFiberRules (Obs.curveData dualInput) H
      ((RationalPointStalks.Data.torusArithmetic (pointStalks C U F p)).fiber E x y)
      ((RationalPointStalks.Data.torusArithmetic (pointStalks C U F p)).frobenius E x y) E
      ((pointStalks C U F p).curveTraceData (E := E) (Obs.curveData dualInput) (point E x y) x y)
  localizationWeil : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (x y : Eˣ),
    letI : (arithmeticAlong (p := p) C U E x y).Monoidal := by
      change (U.pull (ArithmeticSourceMaps.specializationMorphism (ZMod p) E x y)).Monoidal
      infer_instance
    letI : (arithmeticNearby.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).Monoidal :=
      NativeCommonArithmeticTraitWeilCone.fiberMonoidal.{0,mu,nu,g} (ZMod p) E B originTrait
        (extensionGuard p h2p E) (AR.curveRealization E (extensionGuard p h2p E))
        (realizationMonoidal E (extensionGuard p h2p E))
    let Sdata :=
      (allBoundaryMaps.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal) h2p Obs dualInput
        boundaryGeneral E x y).data
    let Rdata := Sdata.restriction (Obs.tensorComparison dualInput) (Obs.dualComparison dualInput)
    let Pdata : RestrictionFrobenius.ArithmeticRestriction Rdata :=
      allArithmeticRestriction.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal) h2p Obs dualInput
        boundaryGeneral E x y
    let covariance : ∀ A z v,
        Pdata.zeroFr A ((Sdata.zero.obj A).ρ z v) =
          (Sdata.zero.obj A).ρ
            (NativeCommonArithmeticTraitWeilCone.conjugation (ZMod p) E B originTrait (extensionGuard p h2p E) z)
            (Pdata.zeroFr A v) := by
      intro A z v
      exact allCovariance.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal) h2p Obs dualInput
        boundaryGeneral E x y A z v
    ArithmeticBoundaryFromInvariantFunctors.Inputs.{0,h,g,gi,mu,mu}
      Sdata (Obs.tensorComparison dualInput) (Obs.dualComparison dualInput) Pdata
      ((RationalPointStalks.Data.torusArithmetic (pointStalks C U F p)).frobenius E x y)
      (NativeCommonArithmeticTraitWeilCone.conjugation (ZMod p) E B originTrait (extensionGuard p h2p E))
      covariance
  tameFrobenius : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] z,
    (originGeneral.tame (ZMod p)
      (NativeCommonArithmeticTraitWeilCone.conjugation (ZMod p) E B originTrait (extensionGuard p h2p E) z)).toAdd =
      (Fintype.card E : ℂ)⁻¹ * (originGeneral.tame (ZMod p) z).toAdd
  sign : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (x y : Eˣ),
    SignStalkComparison PP
      ((RationalPointStalks.Data.torusArithmetic (pointStalks C U F p)).fiber E x y)
      ((RationalPointStalks.Data.torusArithmetic (pointStalks C U F p)).frobenius E x y)
      (Module.finrank (ZMod p) E)

variable (cohomologyGeneral : GeneralArithmeticCohomologyClauses (Ginf := Ginf) (H := H) (PP := PP) C U F O G L Mgeo nativeCompact B AR originTrait
  originGeneral (realizationMonoidal := realizationMonoidal) h2p Obs dualInput boundaryGeneral)

/-- The complete boundary Frobenius is the product of the invariant actions. -/
abbrev allArithmeticBoundary (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (x y : Eˣ) :=
  (cohomologyGeneral.localizationWeil E x y).arithmeticBoundary

variable
  (coefficients : PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.CoefficientFibers C F)
  (coefficientFormulas : PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.PublishedCoefficientFormulas
    C U F O coefficients)
  (tateTrace : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
      (A : C (StartingSourceMaps.affineLine (ZMod p))) z,
    (pointStalks C U F p).lineTrace (E := E)
      ((O.lineTate (ZMod p) h2p 1).obj A) z =
      (Fintype.card E : ℂ)⁻¹ * (pointStalks C U F p).lineTrace (E := E) A z)
  (SR : ScalarPullbackRules
    (FourierSourcePullbacks.originalPullbackData (ZMod p)
      (SourceInverseImageSystem.System.geometricPullbacks (primeSource C U p)))
    (computedPrimitiveLine C U F G L Mgeo p) (Obs.curveData dualInput))
  (hkl : Kl3Properties (computedPrimitiveLine C U F G L Mgeo p)
    ((PublishedPrimitiveSources.Data.twistOne (RationalPointStalks.PrimitiveOperations.primitive
      (pointStalks C U F p) (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p)))
      (PublishedPrimitiveSources.Data.rawKl (RationalPointStalks.PrimitiveOperations.primitive
        (pointStalks C U F p) (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p)))))
  (has : ASProperties (computedPrimitiveLine C U F G L Mgeo p)
    (PublishedPrimitiveSources.Data.as (RationalPointStalks.PrimitiveOperations.primitive
      (pointStalks C U F p) (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p))))
  (CR : CurveRules (Obs.curveData dualInput))
  (htame : ∃ z, (originGeneral.tame (ZMod p) z).toAdd ≠ 0)

include C U F O G L Mgeo nativeCompact B AR originTrait originGeneral realizationMonoidal
  h2p hp Obs dualInput boundaryGeneral cohomologyGeneral coefficients coefficientFormulas tateTrace SR hkl has CR htame

/-- AM11 is now called with internally computed origin, boundary, arithmetic
restriction, specialization and covariance families on the literal J/LF.
The remaining inputs are precisely the named GENERAL all-object operation
clauses and primitive eligibility guards, not completed residual records. -/
def computedCohomologicalRealization :=
  CoherentArithmeticFromLiteralPrimitivesDraft11.literalCohomologicalRealization
    C U F O coefficients originGeneral.zeroRestriction coefficientFormulas h2p tateTrace
    (computedPrimitiveLine C U F G L Mgeo p) SR hkl has CR (originGeneral.tame (ZMod p)) htame
    cohomologyGeneral.point cohomologyGeneral.fiberRules
    (fun E _ _ _ x y => allBoundarySequence C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal)
      h2p Obs dualInput boundaryGeneral E x y)
    (fun E _ _ _ x y => allRestriction.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal)
      h2p Obs dualInput boundaryGeneral E x y)
    (fun E _ _ _ x y => allArithmeticRestriction.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal)
      h2p Obs dualInput boundaryGeneral E x y)
    (fun E _ _ _ x y => allArithmeticBoundary C U F O G L Mgeo nativeCompact B AR originTrait originGeneral
      (realizationMonoidal := realizationMonoidal) h2p Obs dualInput boundaryGeneral cohomologyGeneral E x y)
    (fun E _ _ _ _x _y => NativeCommonArithmeticTraitWeilCone.conjugation (ZMod p) E B originTrait
      (extensionGuard p h2p E))
    (fun E _ _ _ _x _y => cohomologyGeneral.tameFrobenius E)
    (fun E _ _ _ x y => allCovariance.{mu,nu,g,h,gi} C U F nativeCompact B AR originTrait (realizationMonoidal := realizationMonoidal)
      h2p Obs dualInput boundaryGeneral E x y)
    (fun E _ _ _ => arithmeticNearby.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E)
    (fun E _ _ _ => (arithmeticWeil.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E).localFrobenius)
    (fun E _ _ _ => computedAllPrimeOriginInputs
      (C := C) (U := U) (F := F) (O := O) (geometricFiber := G) (lisse := L)
      (nativeCompact := nativeCompact) (B := B) (D := AR) (originTrait := originTrait)
      (geometricM := Mgeo) (general := originGeneral) p h2p hp E hkl has)
    (fun E _ _ _ x y => LiteralArithmeticOriginBoundaryBindingHELD04.canonicalSpecialization
      (along := arithmeticAlong (p := p) C U E x y)
      (J := arithmeticNearby.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E)
      (W := arithmeticWeil.{mu,nu,g} C U F nativeCompact B AR originTrait h2p E))
    cohomologyGeneral.sign

end AllFiniteExtensions
end PrimeGap182.TypeIII.ArithmeticRealizationFromComputedStandardBoundary13

#print axioms PrimeGap182.TypeIII.ArithmeticRealizationFromComputedStandardBoundary13.computedCovariance
#print axioms PrimeGap182.TypeIII.ArithmeticRealizationFromComputedStandardBoundary13.allCovariance
#print axioms PrimeGap182.TypeIII.ArithmeticRealizationFromComputedStandardBoundary13.computedCohomologicalRealization
