import TypeIIIArithmeticBoundaryPrimitiveDataFromChosenLift03
import Mathlib.CategoryTheory.Action.Monoidal
import Mathlib.Algebra.Group.ULift

/-! Pure application transport. Compatible local functors and Weil actions
are computed from the SAME standard action and individual group equivalences.
The standard groups/actions and the geometric meaning of the dictionaries
remain external. No native sheaf model or uniform prime family is asserted. -/
noncomputable section
open CategoryTheory MonoidalCategory
open scoped TensorProduct MonoidalCategory
namespace PrimeGap182.TypeIII.CanonicalLocalWeilFiberFromGroupDictionary
open LocalWeilAction

universe u v us vs g gs t ts

section Restriction
variable {G : Type g} [Group G] {H : Type gs} [Group H] (h : G →* H)

/-- Literal group restriction preserves tensor and unit on underlying modules. -/
def restrictionCoreMonoidal : (Action.res (FGModuleCat ℂ) h).CoreMonoidal where
  εIso := Action.mkIso (Iso.refl _)
  μIso _ _ := Action.mkIso (Iso.refl _)
  μIso_hom_natural_left := by
    intro X Y f Z
    apply Action.hom_ext
    change f.hom ▷ Z.V ≫ 𝟙 _ = 𝟙 _ ≫ (f.hom ▷ Z.V)
    simp
  μIso_hom_natural_right := by
    intro X Y Z f
    apply Action.hom_ext
    change Z.V ◁ f.hom ≫ 𝟙 _ = 𝟙 _ ≫ (Z.V ◁ f.hom)
    simp
  associativity := by
    intro X Y Z
    apply Action.hom_ext
    simp only [Action.comp_hom, Action.whiskerRight_hom, Action.whiskerLeft_hom,
      Action.associator_hom_hom, Action.res_map_hom]
    change (𝟙 (X.V ⊗ Y.V) ▷ Z.V) ≫ 𝟙 _ ≫ (α_ X.V Y.V Z.V).hom =
      (α_ X.V Y.V Z.V).hom ≫ (X.V ◁ 𝟙 (Y.V ⊗ Z.V)) ≫ 𝟙 _
    simp
  left_unitality := by
    intro X
    apply Action.hom_ext
    simp only [Action.comp_hom, Action.whiskerRight_hom,
      Action.leftUnitor_hom_hom, Action.res_map_hom]
    change (λ_ X.V).hom = (𝟙 (𝟙_ (FGModuleCat ℂ)) ▷ X.V) ≫ 𝟙 _ ≫ (λ_ X.V).hom
    simp
  right_unitality := by
    intro X
    apply Action.hom_ext
    simp only [Action.comp_hom, Action.whiskerLeft_hom,
      Action.rightUnitor_hom_hom, Action.res_map_hom]
    change (ρ_ X.V).hom = (X.V ◁ 𝟙 (𝟙_ (FGModuleCat ℂ))) ≫ 𝟙 _ ≫ (ρ_ X.V).hom
    simp

instance restrictionMonoidal : (Action.res (FGModuleCat ℂ) h).Monoidal :=
  (restrictionCoreMonoidal h).toMonoidal

end Restriction

variable {Local : Type u} [Category.{v} Local] [MonoidalCategory Local]
  {StandardLocal : Type us} [Category.{vs} StandardLocal] [MonoidalCategory StandardLocal]
  {G : Type g} [Group G] {StandardG : Type gs} [Group StandardG]
  {Gi : Type t} [Group Gi] {StandardGi : Type ts} [Group StandardGi]
  (realization : Local ⥤ StandardLocal) [realization.Monoidal]
  (standardJ : StandardLocal ⥤ FDRep ℂ StandardG) [standardJ.Monoidal]
  (standardPhi : StandardG →* StandardG) (standardD : Data standardJ standardPhi)
  (origin : G ≃* StandardG) (infinity : Gi ≃* StandardGi)

def fiber : Local ⥤ FDRep ℂ G :=
  (realization ⋙ standardJ) ⋙ Action.res (FGModuleCat ℂ) origin.toMonoidHom

instance fiberMonoidal : (fiber realization standardJ origin).Monoidal :=
  inferInstanceAs ((realization ⋙ standardJ) ⋙
    Action.res (FGModuleCat ℂ) origin.toMonoidHom).Monoidal

def conjugation : G →* G :=
  origin.symm.toMonoidHom.comp (standardPhi.comp origin.toMonoidHom)

variable {W : Type g} [Group W] (weil : W ≃* standardD.Weil)

/-- All Weil representations are the same standard representations restricted
along the individual dictionary. No faithfulness of weak Data is inferred. -/
def weilData : Data (fiber realization standardJ origin) (conjugation standardPhi origin) where
  Weil := W
  inertia := weil.symm.toMonoidHom.comp (standardD.inertia.comp origin.toMonoidHom)
  frobenius := weil.symm standardD.frobenius
  relation q := by
    apply weil.injective
    simp only [map_mul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, conjugation]
    exact standardD.relation (origin q)
  representation A := (standardD.representation (realization.obj A)).comp weil.toMonoidHom
  restriction A q := by
    change standardD.representation (realization.obj A)
      (weil (weil.symm (standardD.inertia (origin q)))) = _
    rw [MulEquiv.apply_symm_apply]
    exact standardD.restriction (realization.obj A) (origin q)
  natural f w x := standardD.natural (realization.map f) (weil w) x

def coefficientIso : fiber realization standardJ origin ≅
    (realization ⋙ standardJ) ⋙ Action.res (FGModuleCat ℂ) origin.toMonoidHom :=
  Iso.refl _

def chosenLiftData :
    ArithmeticBoundaryPrimitiveDataFromChosenLift.ChosenLiftPrimitiveData
      (Gi := Gi) (StandardGi := StandardGi)
      (fiber realization standardJ origin) (conjugation standardPhi origin)
      (weilData realization standardJ standardPhi standardD origin weil)
      realization standardJ standardPhi standardD where
  originGroup := origin
  infinityGroup := infinity
  coefficient := coefficientIso realization standardJ origin
  coefficientUnit z := by rfl
  coefficientTensor A B x y := by rfl
  weilMap := weil.toMonoidHom
  inertia_eq q := weil.apply_symm_apply _
  frobenius_eq := weil.apply_symm_apply _
  chosenLift A x := by
    change standardD.representation (realization.obj A)
      (weil (weil.symm standardD.frobenius)) x = _
    rw [MulEquiv.apply_symm_apply]
    rfl

omit [MonoidalCategory Local] [MonoidalCategory StandardLocal]
  [realization.Monoidal] [standardJ.Monoidal] in
theorem wholeWeil (A : Local) (w : W)
    (x : ((fiber realization standardJ origin).obj A).V) :
    ((coefficientIso realization standardJ origin).app A).hom.hom.hom
      ((weilData realization standardJ standardPhi standardD origin weil).representation A w x) =
      standardD.representation (realization.obj A) (weil w)
        (((coefficientIso realization standardJ origin).app A).hom.hom.hom x) := rfl

theorem sameWeilMap :
    weil.toMonoidHom =
      (chosenLiftData realization standardJ standardPhi standardD origin infinity weil).weilMap := rfl

end PrimeGap182.TypeIII.CanonicalLocalWeilFiberFromGroupDictionary
