import TypeIIICanonicalSourceLocalData

/-!
# Geometric boundary and source transport from shared inertia functors

The boundary is the product of invariant spaces of the actual zero and
infinity restriction functors. Its connecting map and the general scoped
localization laws remain inputs. Tensor restriction follows from the
zero functor's monoidality, using the existing curve tensor comparison;
dual restriction uses the existing curve dual comparison and a general
dual-functor law. Source-isomorphism transport uses that same zero functor.

This constructs the old boundary, restriction and zero-functor interfaces
together. It does not assert existence of the geometric functors, assume
a completed family model, or change the tame-zero exactness guard.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.GeometricBoundaryFromFunctors

open PublishedPhysicalConstruction BoundaryFromSourceModels PublishedPhaseApplication
open PublishedMackey CanonicalSourceLocalData TensorListRepresentation

universe u v a b c d

variable {Input : Type u} [Category.{c} Input] [MonoidalCategory Input]
  {Point : Type v} {C : Type} [Category.{d} C] [Abelian C]
  (D : CurveData Input Point) (H : CohomologyData Input C)
  (F : C ⥤ ModuleCat ℂ) (dualInput : Inputᵒᵖ ⥤ Input)
  {G0 : Type a} [Group G0] {Ginf : Type b} [Group Ginf]

/-- Standard restriction functors and the original geometric localization
map. The boundary space is defined by these functors, not chosen separately. -/
structure Data where
  zero : Input ⥤ FDRep ℂ G0
  [zeroMonoidal : zero.Monoidal]
  infinity : Input ⥤ FDRep ℂ Ginf
  dual : ∀ A, D.Lisse A → Representation.Equiv (zero.obj (dualInput.obj (op A))).ρ
    (dualRepresentation (zero.obj A)).ρ
  positiveSlope : ∀ A, D.Isoclinic A 1 →
    Representation.invariants (infinity.obj A).ρ = ⊥
  toCompact : ∀ A,
    (Representation.invariants (zero.obj A).ρ ×
      Representation.invariants (infinity.obj A).ρ) →ₗ[ℂ] F.obj (H.compact A)
  injective : ∀ A, D.Lisse A → D.Isoclinic A 1 →
    Function.Injective (toCompact A)
  exact : ∀ A, D.Lisse A → D.TameZero A → D.Isoclinic A 1 →
    LinearMap.range (toCompact A) = LinearMap.ker (F.map (H.comparison A)).hom

variable {D H F dualInput} (S : Data (G0 := G0) (Ginf := Ginf) D H F dualInput)

/-- Keep the original connecting map on the literal invariant product. -/
def Data.boundarySequence : BoundarySequence D H F where
  space A := ModuleCat.of ℂ (Representation.invariants (S.zero.obj A).ρ ×
    Representation.invariants (S.infinity.obj A).ρ)
  toCompact := S.toCompact
  injective := S.injective
  exact := S.exact

variable (tensorComparison : ∀ A B, D.tensor A B ≅ A ⊗ B)
  (dualComparison : ∀ A, D.dual A ≅ dualInput.obj (op A))

/-- Construct restriction using the same functors and canonical boundary.
The tensor and source-operation comparisons are derived by composition. -/
def Data.restriction :
    RestrictionData (G0 := G0) (Ginf := Ginf) D H F S.boundarySequence := by
  letI := S.zeroMonoidal
  exact {
    zero := S.zero.obj
    infinity := S.infinity.obj
    tensorZero := fun A B => equivOfIso
      (S.zero.mapIso (tensorComparison A B) ≪≫ (Functor.Monoidal.μIso S.zero A B).symm)
    dualZero := fun A hA => (equivOfIso (S.zero.mapIso (dualComparison A))).trans (S.dual A hA)
    boundary := fun _ _ => LinearEquiv.refl ℂ _
    positiveSlope := S.positiveSlope }

/-- Source isomorphisms act through the same zero restriction, so the
comparison to the old zero-object interface is the identity. -/
def Data.zeroFunctor : ZeroFunctor D (S.restriction tensorComparison dualComparison) where
  functor := S.zero
  comparison _ := Representation.Equiv.refl _

end PrimeGap182.TypeIII.GeometricBoundaryFromFunctors

#print axioms PrimeGap182.TypeIII.GeometricBoundaryFromFunctors.Data.boundarySequence
#print axioms PrimeGap182.TypeIII.GeometricBoundaryFromFunctors.Data.restriction
#print axioms PrimeGap182.TypeIII.GeometricBoundaryFromFunctors.Data.zeroFunctor
