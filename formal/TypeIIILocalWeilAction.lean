import TypeIIIArithmeticSourceTransport

/-!
# Local Frobenius from a common Weil action on inertia stalks

A general Weil representation on each actual stalk supplies Frobenius
by evaluating the representation at one geometric Frobenius lift. Its
invertibility is the group law. Naturality holds for all morphisms, and
its inertia covariance follows from one relation in the Weil group.
No sheaf-dependent covariance or Frobenius operator is separately chosen.
The common arithmetic realization, inertia restriction and general
Weil-group data remain explicit published-framework inputs.
-/

noncomputable section
open CategoryTheory

namespace PrimeGap182.TypeIII.LocalWeilAction
open ArithmeticSourceTransport TensorListRepresentation

universe u v w a
variable {Local : Type u} [Category.{v} Local] {G : Type w} [Group G]
  (J : Local ⥤ FDRep ℂ G) (phi : G →* G)

/-- A Weil action extending the same geometric inertia stalk functor.
The relation uses a geometric Frobenius lift and therefore the selected
inverse-Frobenius convention. The group relation has no sheaf parameter. -/
structure Data where
  Weil : Type w
  [group : Group Weil]
  inertia : G →* Weil
  frobenius : Weil
  relation : ∀ g, frobenius * inertia g = inertia (phi g) * frobenius
  representation : ∀ A, Representation ℂ Weil (J.obj A).V
  restriction : ∀ A g, representation A (inertia g) = (J.obj A).ρ g
  natural : ∀ {A B} (f : A ⟶ B) w x,
    (J.map f).hom.hom (representation A w x) =
      representation B w ((J.map f).hom.hom x)

attribute [instance] Data.group

section GroupAction
variable {W : Type w} [Group W] {V : Type a} [AddCommGroup V] [Module ℂ V]
  (rho : Representation ℂ W V) (w : W)

/-- Invertibility uses the same representation evaluated at the inverse. -/
def actionEquiv : V ≃ₗ[ℂ] V where
  toLinearMap := rho w
  invFun := rho w⁻¹
  left_inv x := by
    change (rho w⁻¹ * rho w) x = x
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv x := by
    change (rho w * rho w⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl

end GroupAction

variable {J phi} (D : Data J phi)

/-- Every local Frobenius action comes from the same Weil element. -/
def Data.localFrobenius : LocalFrobenius J where
  action A := actionEquiv (D.representation A) D.frobenius
  natural f x := by
    change (J.map f.hom).hom.hom (D.representation _ D.frobenius x) =
      D.representation _ D.frobenius ((J.map f.hom).hom.hom x)
    exact D.natural f.hom D.frobenius x

/-- Conjugation on every sheaf follows from the representation's product
law and the single Weil-group relation. No commutation is assumed. -/
theorem Data.covariance (A : Local) (g : G) (x : (J.obj A).V) :
    D.localFrobenius.action A ((J.obj A).ρ g x) =
      (J.obj A).ρ (phi g) (D.localFrobenius.action A x) := by
  change D.representation A D.frobenius ((J.obj A).ρ g x) =
    (J.obj A).ρ (phi g) (D.representation A D.frobenius x)
  rw [← D.restriction A g, ← D.restriction A (phi g)]
  change (D.representation A D.frobenius * D.representation A (D.inertia g)) x =
    (D.representation A (D.inertia (phi g)) * D.representation A D.frobenius) x
  rw [← map_mul, ← map_mul, D.relation g]

/-- The inverse operator used in contragredients is the inverse Weil lift. -/
theorem Data.inverse_action (A : Local) (x : (J.obj A).V) :
    (D.localFrobenius.action A).symm x = D.representation A D.frobenius⁻¹ x := rfl

end PrimeGap182.TypeIII.LocalWeilAction

#print axioms PrimeGap182.TypeIII.LocalWeilAction.actionEquiv
#print axioms PrimeGap182.TypeIII.LocalWeilAction.Data.localFrobenius
#print axioms PrimeGap182.TypeIII.LocalWeilAction.Data.covariance
#print axioms PrimeGap182.TypeIII.LocalWeilAction.Data.inverse_action
