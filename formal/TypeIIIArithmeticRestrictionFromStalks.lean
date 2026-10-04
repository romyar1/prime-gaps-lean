import TypeIIIArithmeticCovarianceFromSpecialization
import TypeIIIRestrictionFrobenius

/-!
# Original arithmetic action from the same specialized stalk

The original zero-stalk Frobenius is the conjugate of local Frobenius
through the selected geometric stalk comparison. Its specialization
compatibility and inertia covariance are derived, rather than independent
choices. Uniqueness shows that this is exactly any original action already
compatible with that comparison, so the construction does not change it.
The general tensor/dual laws remain explicit on the resulting action.
-/

noncomputable section
open CategoryTheory

namespace PrimeGap182.TypeIII.ArithmeticRestrictionFromStalks
open ArithmeticSourceTransport RestrictionFrobenius
open PublishedPhysicalConstruction BoundaryFromSourceModels

universe u v a b c w z d
variable {Input : Type u} [Category.{a} Input]
  {Local : Type v} [Category.{b} Local] {G : Type c} [Group G]
  (J : Local ⥤ FDRep ℂ G) (along : Input ⥤ Local)
  (zero : Input → FDRep ℂ G)

/-- General geometric stalk comparison along the fixed specialization.
It supplies no independent arithmetic operator or compatibility equation. -/
structure Stalks where
  comparison : ∀ A, Representation.Equiv (zero A).ρ (J.obj (along.obj A)).ρ

variable {J along zero} (S : Stalks J along zero) (LF : LocalFrobenius J)

/-- Transport the actual local action to the original zero-stalk. -/
def Stalks.action (A : Input) : (zero A).V ≃ₗ[ℂ] (zero A).V :=
  ((S.comparison A).toLinearEquiv.trans (LF.action (along.obj A))).trans
    (S.comparison A).toLinearEquiv.symm

/-- The comparison intertwines the transported action by construction. -/
theorem Stalks.action_comparison (A : Input) (x : (zero A).V) :
    S.comparison A (S.action LF A x) =
      LF.action (along.obj A) (S.comparison A x) := by
  exact (S.comparison A).toLinearEquiv.apply_symm_apply _

/-- Any pre-existing compatible action is this action, not a second
choice of Frobenius. This also fixes the inverse/contragredient convention. -/
theorem Stalks.action_unique (original : ∀ A, (zero A).V ≃ₗ[ℂ] (zero A).V)
    (h : ∀ A x, S.comparison A (original A x) =
      LF.action (along.obj A) (S.comparison A x)) : original = S.action LF := by
  funext A
  apply LinearEquiv.ext
  intro x
  apply (S.comparison A).toLinearEquiv.injective
  exact (h A x).trans (S.action_comparison LF A x).symm

/-- Supply the old specialization interface from the shared local action. -/
def Stalks.specialization :
    SpecializationComparison J along zero (S.action LF) LF where
  comparison := S.comparison
  frobenius := S.action_comparison LF

/-- Conjugation, rather than commutation, transports to the original stalk. -/
theorem Stalks.covariance (phi : G →* G)
    (h : ∀ A g v, LF.action A ((J.obj A).ρ g v) =
      (J.obj A).ρ (phi g) (LF.action A v)) (A : Input) (g : G) (v : (zero A).V) :
    S.action LF A ((zero A).ρ g v) = (zero A).ρ (phi g) (S.action LF A v) :=
  ArithmeticCovarianceFromSpecialization.covariance J along zero (S.action LF) LF
    (S.specialization LF) phi h A g v

section Restriction
variable {Point : Type w} {C : Type} [Category.{z} C] [Abelian C]
  {D : CurveData Input Point} {H : CohomologyData Input C}
  {F : C ⥤ ModuleCat ℂ} {BS : BoundarySequence D H F}
  {Ginf : Type d} [Group Ginf]
  (Z : RestrictionData (G0 := G) (Ginf := Ginf) D H F BS)
  (S : Stalks J along Z.zero)

/-- General tensor/dual Frobenius compatibility on the same restricted
stalks. Neither an action nor a specialization equation is supplied. -/
structure TensorDualRules : Prop where
  tensor_natural : ∀ A B x,
    Z.tensorZero A B (S.action LF (D.tensor A B) x) =
      TensorProduct.map (S.action LF A).toLinearMap (S.action LF B).toLinearMap
        (Z.tensorZero A B x)
  dual_natural : ∀ A (hA : D.Lisse A) x,
    Z.dualZero A hA (S.action LF (D.dual A) x) =
      (S.action LF A).symm.toLinearMap.dualMap (Z.dualZero A hA x)

/-- The old restriction data use the derived action everywhere. -/
abbrev Stalks.restriction (R : TensorDualRules LF Z S) : ArithmeticRestriction Z where
  zeroFr := S.action LF
  tensor_natural := R.tensor_natural
  dual_natural := R.dual_natural

end Restriction
end PrimeGap182.TypeIII.ArithmeticRestrictionFromStalks

#print axioms PrimeGap182.TypeIII.ArithmeticRestrictionFromStalks.Stalks.action
#print axioms PrimeGap182.TypeIII.ArithmeticRestrictionFromStalks.Stalks.action_comparison
#print axioms PrimeGap182.TypeIII.ArithmeticRestrictionFromStalks.Stalks.action_unique
#print axioms PrimeGap182.TypeIII.ArithmeticRestrictionFromStalks.Stalks.specialization
#print axioms PrimeGap182.TypeIII.ArithmeticRestrictionFromStalks.Stalks.covariance
#print axioms PrimeGap182.TypeIII.ArithmeticRestrictionFromStalks.Stalks.restriction
