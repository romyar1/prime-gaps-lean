import TypeIIIGeometricBoundaryFromFunctors
import TypeIIIArithmeticRestrictionFromStalks

/-!
# Arithmetic boundary at the same specialized zero-stalk

The zero restriction is the actual specialization functor followed by
local inertia. Its comparison with the arithmetic source stalk is the
identity. Its monoidal structure is inherited from these two functors.
The original localization maps and their guarded exactness remain general
published inputs on this fixed zero functor. No connecting map is changed.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.ArithmeticZeroFromSpecialization
open PublishedPhysicalConstruction BoundaryFromSourceModels PublishedMackey PublishedPhaseApplication
open GeometricBoundaryFromFunctors ArithmeticSourceTransport ArithmeticRestrictionFromStalks

universe u v a b c d e f
variable {Input : Type u} [Category.{c} Input] [MonoidalCategory Input]
  {Point : Type v} {C : Type} [Category.{d} C] [Abelian C]
  (D : CurveData Input Point) (H : CohomologyData Input C)
  (F : C ⥤ ModuleCat ℂ) (dualInput : Inputᵒᵖ ⥤ Input)
  {G0 : Type a} [Group G0] {Ginf : Type b} [Group Ginf]
  (zero : Input ⥤ FDRep ℂ G0)

/-- The original localization data with zero restriction fixed by the
same specialization and local stalk as the arithmetic source proof. -/
structure BoundaryMaps where
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

variable {D H F dualInput zero} [zero.Monoidal]
  (M : BoundaryMaps (Ginf := Ginf) D H F dualInput zero)

/-- Retain the same boundary maps and use the fixed zero functor. -/
abbrev BoundaryMaps.data : Data (G0 := G0) (Ginf := Ginf) D H F dualInput where
  zero := zero
  zeroMonoidal := inferInstance
  infinity := M.infinity
  dual := M.dual
  positiveSlope := M.positiveSlope
  toCompact := M.toCompact
  injective := M.injective
  exact := M.exact

section Stalk
variable {Local : Type e} [Category.{f} Local]
  (along : Input ⥤ Local) (J : Local ⥤ FDRep ℂ G0)

/-- The source and boundary use the identical specialized local stalk. -/
def stalks : Stalks J along (along ⋙ J).obj where
  comparison _ := Representation.Equiv.refl _

omit [MonoidalCategory Input] in
/-- The transported original action is literally local Frobenius on the
specialized object; no independent geometric or arithmetic comparison is used. -/
theorem action (LF : LocalFrobenius J) (A : Input) (x : ((along ⋙ J).obj A).V) :
    (stalks along J).action LF A x = LF.action (along.obj A) x := rfl

end Stalk
end PrimeGap182.TypeIII.ArithmeticZeroFromSpecialization

#print axioms PrimeGap182.TypeIII.ArithmeticZeroFromSpecialization.BoundaryMaps.data
#print axioms PrimeGap182.TypeIII.ArithmeticZeroFromSpecialization.stalks
#print axioms PrimeGap182.TypeIII.ArithmeticZeroFromSpecialization.action
