import TypeIIIExactInverseImagesToDerived
import TypeIIILinearRadialPhaseFromPoleTransport

/-!
# The common origin realization from one exact ordinary system

The three indices are the ACTUAL A1_k, full A2_k and Spec L[t]. Their
ordinary ambient abelian sheaf realization remains general framework data.
All ambient derived categories, inverse images, shifts and ordinary
cohomology are constructed by the standard Mathlib localization. Actual
coordinate automorphisms and ordinary inverse-image identity/composition
construct the origin scaling and constant-field equivalences. Exactness
constructs ordinary-cohomology inverse-image compatibility.

The remaining application parameters are one common ordinary generic-zero
wild-stalk functor and its group transport, plus ambient realization of the
ORIGINAL curve/plane objects, smooth linear [1] normalization and the
ORIGINAL radial stalk comparison. They are geometric realization premises,
not a rescaled-phase equality or a rectangle/support conclusion. No adic
category, wild fundamental group or complete input family is constructed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

namespace PrimeGap182.TypeIII.OriginRealizationFromExactInverseImages

open PublishedFourierRules

inductive Index where
  | curve | plane | origin
  deriving DecidableEq

variable (k : Type) [Field k]

def scheme : Index → Scheme
  | .curve => LocalFourierKernelCoordinates.affineLine k
  | .plane => FullFourierKernelCoordinates.planeScheme k
  | .origin => LinearRadialPhaseFromPoleTransport.originScheme k

universe v w dh c dc e g

/-- Exact ORDINARY inverse image commutes with ordinary derived
cohomology. The comparison is constructed on short/cochain complexes
and uniquely lifted to the derived localization. -/
def exactDerivedCohomology {C1 C2 : Type v} [Category.{w} C1] [Category.{w} C2]
    [Abelian C1] [Abelian C2] [HasDerivedCategory.{dh} C1] [HasDerivedCategory.{dh} C2]
    (F : C1 ⥤ C2) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n : ℤ) : F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C2 n ≅
      DerivedCategory.homologyFunctor C1 n ⋙ F := by
  let Q1 := DerivedCategory.Q (C := C1)
  let H1 := HomologicalComplex.homologyFunctor C1 (ComplexShape.up ℤ) n
  let H2 := HomologicalComplex.homologyFunctor C2 (ComplexShape.up ℤ) n
  let DH1 := DerivedCategory.homologyFunctor C1 n
  let DH2 := DerivedCategory.homologyFunctor C2 n
  have ec : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ H2 ≅ H1 ⋙ F :=
    Functor.isoWhiskerLeft
      (HomologicalComplex.shortComplexFunctor C1 (ComplexShape.up ℤ) n)
      (ShortComplex.homologyFunctorIso F)
  have el : Q1 ⋙ (F.mapDerivedCategory ⋙ DH2) ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ H2 :=
    (Functor.associator ..).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫ Functor.associator .. ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors C2 n)
  have er : Q1 ⋙ (DH1 ⋙ F) ≅ H1 ⋙ F :=
    (Functor.associator ..).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C1 n) F
  letI : Localization.Lifting Q1 (HomologicalComplex.quasiIso C1 (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ H2) (F.mapDerivedCategory ⋙ DH2) := ⟨el⟩
  letI : Localization.Lifting Q1 (HomologicalComplex.quasiIso C1 (ComplexShape.up ℤ))
      (H1 ⋙ F) (DH1 ⋙ F) := ⟨er⟩
  exact Localization.liftNatIso Q1 (HomologicalComplex.quasiIso C1 (ComplexShape.up ℤ))
    _ _ _ _ ec

variable {k}

theorem scalarHom_inverse (u : (LinearRadialPhaseFromPoleTransport.L k)ˣ) :
    (LinearRadialPhaseFromPoleTransport.originScalarHom u).comp (LinearRadialPhaseFromPoleTransport.originScalarHom u⁻¹) =
      AlgHom.id k (Polynomial (LinearRadialPhaseFromPoleTransport.L k)) := by
  apply AlgHom.coe_ringHom_injective
  apply Polynomial.ringHom_ext
  · intro a
    simp [LinearRadialPhaseFromPoleTransport.originScalarHom]
  · simp [LinearRadialPhaseFromPoleTransport.originScalarHom]
    rw [← mul_assoc, ← Polynomial.C_mul]
    simp

theorem constantHom_inverse (σ : LinearRadialPhaseFromPoleTransport.L k ≃ₐ[k] LinearRadialPhaseFromPoleTransport.L k) :
    (LinearRadialPhaseFromPoleTransport.originConstantHom σ).comp (LinearRadialPhaseFromPoleTransport.originConstantHom σ.symm) =
      AlgHom.id k (Polynomial (LinearRadialPhaseFromPoleTransport.L k)) := by
  apply AlgHom.coe_ringHom_injective
  apply Polynomial.ringHom_ext
  · intro a
    simp [LinearRadialPhaseFromPoleTransport.originConstantHom]
  · simp [LinearRadialPhaseFromPoleTransport.originConstantHom]

theorem scalarMorphism_inverse (u : (LinearRadialPhaseFromPoleTransport.L k)ˣ) :
    LinearRadialPhaseFromPoleTransport.originScalarMorphism u ≫ LinearRadialPhaseFromPoleTransport.originScalarMorphism u⁻¹ =
      𝟙 (LinearRadialPhaseFromPoleTransport.originScheme k) := by
  dsimp only [LinearRadialPhaseFromPoleTransport.originScalarMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  change Spec.map (CommRingCat.ofHom
    (((LinearRadialPhaseFromPoleTransport.originScalarHom u).comp (LinearRadialPhaseFromPoleTransport.originScalarHom u⁻¹)).toRingHom)) = _
  rw [scalarHom_inverse]
  exact Spec.map_id _

theorem constantMorphism_inverse (σ : LinearRadialPhaseFromPoleTransport.L k ≃ₐ[k] LinearRadialPhaseFromPoleTransport.L k) :
    LinearRadialPhaseFromPoleTransport.originConstantMorphism σ ≫ LinearRadialPhaseFromPoleTransport.originConstantMorphism σ.symm =
      𝟙 (LinearRadialPhaseFromPoleTransport.originScheme k) := by
  dsimp only [LinearRadialPhaseFromPoleTransport.originConstantMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  change Spec.map (CommRingCat.ofHom
    (((LinearRadialPhaseFromPoleTransport.originConstantHom σ).comp (LinearRadialPhaseFromPoleTransport.originConstantHom σ.symm)).toRingHom)) = _
  rw [constantHom_inverse]
  exact Spec.map_id _

variable (C : Index → Type v) [∀ i, Category.{w} (C i)] [∀ i, Abelian (C i)]

local instance nativeLocalizations : ∀ i, HasDerivedCategory.{max v w} (C i) :=
  fun i => HasDerivedCategory.standard (C i)

variable {C} (A : ExactInverseImagesToDerived.OrdinarySystem (scheme k) C)

/-- Actual inverse scheme maps induce a genuine derived equivalence.
Mathlib adjointifies the two inverse-image identity comparisons while
retaining the actual derived inverse-image functors. -/
def automorphismEquivalence (f g : scheme k .origin ⟶ scheme k .origin)
    (hfg : f ≫ g = 𝟙 _) (hgf : g ≫ f = 𝟙 _) : A.Derived .origin ≌ A.Derived .origin :=
  CategoryTheory.Equivalence.mk (A.derivedPull (i := .origin) (j := .origin) f)
    (A.derivedPull (i := .origin) (j := .origin) g)
    ((A.derivedComposition (i := .origin) (j := .origin) (k := .origin) g f ≪≫
      eqToIso (congrArg (fun h => A.derivedPull (i := .origin) (j := .origin) h) hgf) ≪≫
      A.derivedIdentity .origin).symm)
    (A.derivedComposition (i := .origin) (j := .origin) (k := .origin) f g ≪≫
      eqToIso (congrArg (fun h => A.derivedPull (i := .origin) (j := .origin) h) hfg) ≪≫
      A.derivedIdentity .origin)

def scaleEquivalence (u : (LinearRadialPhaseFromPoleTransport.L k)ˣ) : A.Derived .origin ≌ A.Derived .origin :=
  automorphismEquivalence A (LinearRadialPhaseFromPoleTransport.originScalarMorphism u) (LinearRadialPhaseFromPoleTransport.originScalarMorphism u⁻¹)
    (scalarMorphism_inverse u) (by simpa only [scheme, inv_inv] using scalarMorphism_inverse u⁻¹)

def constantEquivalence (σ : LinearRadialPhaseFromPoleTransport.L k ≃ₐ[k] LinearRadialPhaseFromPoleTransport.L k) : A.Derived .origin ≌ A.Derived .origin :=
  automorphismEquivalence A (LinearRadialPhaseFromPoleTransport.originConstantMorphism σ) (LinearRadialPhaseFromPoleTransport.originConstantMorphism σ.symm)
    (constantMorphism_inverse σ) (by simpa only [scheme, AlgEquiv.symm_symm] using constantMorphism_inverse σ.symm)

variable {Obj : Type c} {CurveObj : Type dc}
  {E : Type e} [Field E] {G : Type g} [Group G]
  (F : FourierData k Obj CurveObj) (radial : Obj → FDRep E G)

/-- Only the remaining geometric SAME-object and ordinary wild/group
realization. Intrinsic derived operations and laws are not fields. -/
structure Application where
  wild : C .origin ⥤ FDRep E G
  traitScale : (LinearRadialPhaseFromPoleTransport.L k)ˣ → (FDRep E G ≌ FDRep E G)
  traitTwist : (LinearRadialPhaseFromPoleTransport.L k ≃ₐ[k] LinearRadialPhaseFromPoleTransport.L k) → (FDRep E G ≌ FDRep E G)
  [scaleZero : ∀ u, (traitScale u).functor.PreservesZeroMorphisms]
  [scaleInverseZero : ∀ u, (traitScale u).inverse.PreservesZeroMorphisms]
  [twistZero : ∀ σ, (traitTwist σ).functor.PreservesZeroMorphisms]
  scaleWild : ∀ u, A.pull (i := .origin) (j := .origin) (LinearRadialPhaseFromPoleTransport.originScalarMorphism u) ⋙ wild ≅
    wild ⋙ (traitScale u).functor
  twistWild : ∀ σ, A.pull (i := .origin) (j := .origin) (LinearRadialPhaseFromPoleTransport.originConstantMorphism σ) ⋙ wild ≅
    wild ⋙ (traitTwist σ).functor
  curveRealization : CurveObj → A.Derived .curve
  planeRealization : Obj → A.Derived .plane
  linearRealization : ∀ Q a b, (a, b) ≠ (0, 0) →
    (planeRealization (F.linearPullback (a, b) Q) ≅ (A.shiftOne .plane).obj
      ((A.derivedPull (i := .plane) (j := .curve) (LinearRadialPhaseFromPoleTransport.linearMorphism a b)).obj (curveRealization Q)))
  radialStalk : ∀ P, radial P ≅
    (A.ordinary .origin (-2) ⋙ wild).obj
      ((A.derivedPull (i := .origin) (j := .plane) (LinearRadialPhaseFromPoleTransport.radialMorphism (k := k))).obj (planeRealization P))

attribute [instance] Application.scaleZero Application.scaleInverseZero Application.twistZero

variable {A F radial} (R : Application A F radial)

def Application.origin : LinearRadialPhaseFromPoleTransport.DerivedOrigin F radial where
  CurveDerived := A.Derived .curve
  PlaneDerived := A.Derived .plane
  OriginDerived := A.Derived .origin
  curveRealization := R.curveRealization
  planeRealization := R.planeRealization
  linearInverseImage f := A.derivedPull (i := .plane) (j := .curve) f
  curveInverseImage f := A.derivedPull (i := .origin) (j := .curve) f
  originInverseImage f := A.derivedPull (i := .origin) (j := .origin) f
  radialInverseImage := A.derivedPull (i := .origin) (j := .plane) (LinearRadialPhaseFromPoleTransport.radialMorphism (k := k))
  planeShiftOne := A.shiftOne .plane
  originShiftOne := A.shiftOne .origin
  minusOne := A.ordinary .origin (-1) ⋙ R.wild
  minusTwo := A.ordinary .origin (-2) ⋙ R.wild
  originScale := scaleEquivalence A
  traitScale := R.traitScale
  originTwist := constantEquivalence A
  traitTwist := R.traitTwist
  composition f := A.derivedComposition (i := .origin) (j := .plane) (k := .curve)
    (LinearRadialPhaseFromPoleTransport.radialMorphism (k := k)) f
  radialShift := A.pullShift (i := .origin) (j := .plane) (LinearRadialPhaseFromPoleTransport.radialMorphism (k := k))
  ordinaryShift := (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight (A.ordinaryShift .origin) R.wild
  originComposition f g := A.derivedComposition (i := .origin) (j := .origin) (k := .curve) f g
  scaleRealization _u := Iso.refl _
  twistRealization _σ := Iso.refl _
  scaleCohomology u := (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight
      (exactDerivedCohomology (A.pull (i := .origin) (j := .origin) (LinearRadialPhaseFromPoleTransport.originScalarMorphism u)) (-1)) _ ≪≫
    Functor.associator .. ≪≫ Functor.isoWhiskerLeft _ (R.scaleWild u) ≪≫ (Functor.associator ..).symm
  twistCohomology σ := (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight
      (exactDerivedCohomology (A.pull (i := .origin) (j := .origin) (LinearRadialPhaseFromPoleTransport.originConstantMorphism σ)) (-1)) _ ≪≫
    Functor.associator .. ≪≫ Functor.isoWhiskerLeft _ (R.twistWild σ) ≪≫ (Functor.associator ..).symm
  linearRealization := R.linearRealization
  radialStalk := R.radialStalk

end PrimeGap182.TypeIII.OriginRealizationFromExactInverseImages

#print axioms PrimeGap182.TypeIII.OriginRealizationFromExactInverseImages.exactDerivedCohomology
#print axioms PrimeGap182.TypeIII.OriginRealizationFromExactInverseImages.scaleEquivalence
#print axioms PrimeGap182.TypeIII.OriginRealizationFromExactInverseImages.constantEquivalence
#print axioms PrimeGap182.TypeIII.OriginRealizationFromExactInverseImages.Application.origin
