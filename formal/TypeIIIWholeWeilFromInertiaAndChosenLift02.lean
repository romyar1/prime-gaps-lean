import TypeIIILocalWeilAction
import Mathlib.Algebra.Group.Subgroup.Basic

/-! Pure transport of every Weil action from inertia and one chosen lift.
The normal form is explicit group DATA, not a native-geometric realization
claim. Standard-to-native transport additionally requires an injective
same-group dictionary. No completed boundary or model is constructed. -/
noncomputable section
open CategoryTheory
namespace PrimeGap182.TypeIII.WholeWeilFromInertiaAndChosenLift
universe g w gs ws a b u v us vs

section PureRepresentation
variable {G : Type g} [Group G] {W : Type w} [Group W]
  {StandardW : Type ws} [Group StandardW]
  {V : Type a} [AddCommGroup V] [Module ℂ V]
  {StandardV : Type b} [AddCommGroup StandardV] [Module ℂ StandardV]
  (rho : Representation ℂ W V) (standardRho : Representation ℂ StandardW StandardV)
  (weilMap : W →* StandardW) (coefficient : V →ₗ[ℂ] StandardV)

/-- Those elements for which one linear coefficient map intertwines the actions. -/
def intertwiningSubgroup : Subgroup W where
  carrier := {w | ∀ x, coefficient (rho w x) = standardRho (weilMap w) (coefficient x)}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro w z hw hz x
    simp only [map_mul, Module.End.mul_apply]
    exact (hw (rho z x)).trans (congrArg (standardRho (weilMap w)) (hz x))
  inv_mem' := by
    intro w hw x
    have h := congrArg (standardRho (weilMap w⁻¹)) (hw (rho w⁻¹ x))
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, inv_mul_cancel,
      map_one, Module.End.one_apply] using h.symm

/-- Inertia and one chosen lift determine intertwining on a group with normal form. -/
theorem intertwining_of_normalForm (inertia : G →* W) (frobenius : W)
    (normalForm : ∀ w : W, ∃ q : G, ∃ n : ℤ, w = inertia q * frobenius ^ n)
    (inertiaIntertwining : ∀ q x,
      coefficient (rho (inertia q) x) = standardRho (weilMap (inertia q)) (coefficient x))
    (liftIntertwining : ∀ x,
      coefficient (rho frobenius x) = standardRho (weilMap frobenius) (coefficient x))
    (w : W) (x : V) :
    coefficient (rho w x) = standardRho (weilMap w) (coefficient x) := by
  rcases normalForm w with ⟨q,n,rfl⟩
  let H := intertwiningSubgroup rho standardRho weilMap coefficient
  have hq : inertia q ∈ H := inertiaIntertwining q
  have hF : frobenius ∈ H := liftIntertwining
  exact H.mul_mem hq (H.zpow_mem hF n) x
end PureRepresentation

/-- Pull genuine standard normal form back through the SAME injective dictionary.
This theorem does not assert that an arbitrary retained native Weil map is injective. -/
theorem normalForm_of_injective_dictionary
    {G : Type g} [Group G] {W : Type w} [Group W]
    {StandardG : Type gs} [Group StandardG] {StandardW : Type ws} [Group StandardW]
    (inertia : G →* W) (frobenius : W)
    (standardInertia : StandardG →* StandardW) (standardFrobenius : StandardW)
    (originGroup : G ≃* StandardG) (weilMap : W →* StandardW)
    (injective : Function.Injective weilMap)
    (inertia_eq : ∀ q, weilMap (inertia q) = standardInertia (originGroup q))
    (frobenius_eq : weilMap frobenius = standardFrobenius)
    (standardNormalForm : ∀ w : StandardW,
      ∃ q : StandardG, ∃ n : ℤ, w = standardInertia q * standardFrobenius ^ n)
    (w : W) : ∃ q : G, ∃ n : ℤ, w = inertia q * frobenius ^ n := by
  rcases standardNormalForm (weilMap w) with ⟨q,n,h⟩
  refine ⟨originGroup.symm q,n,injective ?_⟩
  rw [map_mul,map_zpow,inertia_eq,frobenius_eq,originGroup.apply_symm_apply]
  exact h

section CoefficientFunctor
variable {Local : Type u} [Category.{v} Local]
  {StandardLocal : Type us} [Category.{vs} StandardLocal]
  {G : Type g} [Group G] {StandardG : Type gs} [Group StandardG]
  (J : Local ⥤ FDRep ℂ G) (phi : G →* G) (D : LocalWeilAction.Data J phi)
  (realization : Local ⥤ StandardLocal)
  (standardJ : StandardLocal ⥤ FDRep ℂ StandardG)
  (standardPhi : StandardG →* StandardG)
  (standardD : LocalWeilAction.Data standardJ standardPhi)
  (originGroup : G ≃* StandardG) (weilMap : D.Weil →* standardD.Weil)
  (coefficient : J ≅ (realization ⋙ standardJ) ⋙
    Action.res (FGModuleCat ℂ) originGroup.toMonoidHom)

/-- The existing coefficient representation isomorphism automatically intertwines inertia. -/
theorem inertiaIntertwining_of_coefficientIso
    (inertia_eq : ∀ q, weilMap (D.inertia q) = standardD.inertia (originGroup q))
    (A : Local) (q : G) (x : (J.obj A).V) :
    (coefficient.app A).hom.hom.hom (D.representation A (D.inertia q) x) =
      standardD.representation (realization.obj A) (weilMap (D.inertia q))
        ((coefficient.app A).hom.hom.hom x) := by
  rw [D.restriction,inertia_eq,standardD.restriction]
  exact Rep.hom_comm_apply
    ((forget₂ (FDRep ℂ G) (Rep ℂ G)).map (coefficient.app A).hom) q x

/-- The exact whole-Weil DATA equation follows from the coefficient iso and one lift square. -/
theorem wholeWeil_of_coefficientIso
    (inertia_eq : ∀ q, weilMap (D.inertia q) = standardD.inertia (originGroup q))
    (frobenius_eq : weilMap D.frobenius = standardD.frobenius)
    (normalForm : ∀ w : D.Weil,
      ∃ q : G, ∃ n : ℤ, w = D.inertia q * D.frobenius ^ n)
    (liftIntertwining : ∀ (A : Local) (x : (J.obj A).V),
      (coefficient.app A).hom.hom.hom (D.representation A D.frobenius x) =
        standardD.representation (realization.obj A) standardD.frobenius
          ((coefficient.app A).hom.hom.hom x))
    (A : Local) (w : D.Weil) (x : (J.obj A).V) :
    (coefficient.app A).hom.hom.hom (D.representation A w x) =
      standardD.representation (realization.obj A) (weilMap w)
        ((coefficient.app A).hom.hom.hom x) := by
  apply intertwining_of_normalForm (D.representation A)
    (standardD.representation (realization.obj A)) weilMap
    (coefficient.app A).hom.hom.hom.hom D.inertia D.frobenius normalForm
  · exact inertiaIntertwining_of_coefficientIso J phi D realization standardJ standardPhi
      standardD originGroup weilMap coefficient inertia_eq A
  · intro y
    rw [frobenius_eq]
    exact liftIntertwining A y

/-- Standard normal form and a genuine injective group dictionary give the same exact equation. -/
theorem wholeWeil_of_standardNormalForm
    (injective : Function.Injective weilMap)
    (inertia_eq : ∀ q, weilMap (D.inertia q) = standardD.inertia (originGroup q))
    (frobenius_eq : weilMap D.frobenius = standardD.frobenius)
    (standardNormalForm : ∀ w : standardD.Weil,
      ∃ q : StandardG, ∃ n : ℤ,
      w = standardD.inertia q * standardD.frobenius ^ n)
    (liftIntertwining : ∀ (A : Local) (x : (J.obj A).V),
      (coefficient.app A).hom.hom.hom (D.representation A D.frobenius x) =
        standardD.representation (realization.obj A) standardD.frobenius
          ((coefficient.app A).hom.hom.hom x))
    (A : Local) (w : D.Weil) (x : (J.obj A).V) :
    (coefficient.app A).hom.hom.hom (D.representation A w x) =
      standardD.representation (realization.obj A) (weilMap w)
        ((coefficient.app A).hom.hom.hom x) := by
  apply wholeWeil_of_coefficientIso J phi D realization standardJ standardPhi standardD
    originGroup weilMap coefficient inertia_eq frobenius_eq
    (normalForm_of_injective_dictionary D.inertia D.frobenius standardD.inertia
      standardD.frobenius originGroup weilMap injective inertia_eq frobenius_eq standardNormalForm)
    liftIntertwining A w x
end CoefficientFunctor
end PrimeGap182.TypeIII.WholeWeilFromInertiaAndChosenLift
