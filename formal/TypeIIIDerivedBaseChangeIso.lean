import TypeIIIDerivedBaseChange
import TypeIIIExactFunctorInjectiveResolution

/-!
# An isomorphism criterion for the actual derived base-change maps

If the actual ordinary transformation is invertible and the exact
functor `G` preserves injective objects, the previously constructed
resolution and derived transformations are invertible.  The proof uses
the same transformations: functoriality supplies the inverse of the
mapped ordinary transformation, and the proved comparison theorem makes
the existing resolution comparison an isomorphism.

Preservation of injectives by `G` is an explicit algebraic hypothesis.
This module makes no assertion that arbitrary inverse image satisfies
it and no proper-base-change assertion.
-/

noncomputable section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {C' : Type u₃} [Category.{v₃} C'] [Abelian C'] [HasInjectiveResolutions C']
  {D' : Type u₄} [Category.{v₄} D'] [Abelian D']
  (F : C ⥤ D) [F.Additive] (F' : C' ⥤ D') [F'.Additive]
  (G : C ⥤ C') [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [G.PreservesInjectiveObjects]
  (H : D ⥤ D') [H.Additive] (β : F ⋙ H ⟶ G ⋙ F') [IsIso β]

set_option backward.isDefEq.respectTransparency false in
/-- Invertibility of the original square and preservation of injectives
make the existing resolution transformation invertible. -/
instance derivedBaseChangeResolutionMap_isIso :
    IsIso (derivedBaseChangeResolutionMap F F' G H β) := by
  let : IsIso (β.mapHomotopyCategory (ComplexShape.up ℕ)) := by
    refine ⟨⟨(inv β).mapHomotopyCategory (ComplexShape.up ℕ), ?_, ?_⟩⟩
    · rw [← NatTrans.mapHomotopyCategory_comp, IsIso.hom_inv_id,
        NatTrans.mapHomotopyCategory_id]
    · rw [← NatTrans.mapHomotopyCategory_comp, IsIso.inv_hom_id,
        NatTrans.mapHomotopyCategory_id]
  let e :=
    Functor.isoWhiskerLeft (injectiveResolutions C)
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ H)) (ComplexShape.up ℕ)) ≪≫
      Functor.isoWhiskerLeft (injectiveResolutions C)
        (asIso (β.mapHomotopyCategory (ComplexShape.up ℕ))) ≪≫
      Functor.isoWhiskerLeft (injectiveResolutions C)
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ F')) (ComplexShape.up ℕ)).symm ≪≫
      Functor.isoWhiskerRight (asIso (exactFunctorResolutionNatTrans G))
        (F'.mapHomotopyCategory (ComplexShape.up ℕ))
  exact e.isIso_hom

/-- The actual resolution isomorphism has the pre-existing transformation as its forward map. -/
def derivedBaseChangeResolutionIso :
    F.rightDerivedToHomotopyCategory ⋙ H.mapHomotopyCategory (ComplexShape.up ℕ) ≅
      G ⋙ F'.rightDerivedToHomotopyCategory :=
  asIso (derivedBaseChangeResolutionMap F F' G H β)

/-- No replacement of the original resolution transformation is involved. -/
theorem derivedBaseChangeResolutionIso_hom :
    (derivedBaseChangeResolutionIso F F' G H β).hom =
      derivedBaseChangeResolutionMap F F' G H β := rfl

variable [H.PreservesHomology]

set_option backward.isDefEq.respectTransparency false in
/-- The same derived base-change morphism is invertible in every degree. -/
instance derivedBaseChangeMap_isIso (n : ℕ) :
    IsIso (derivedBaseChangeMap F F' G H β n) := by
  let e :=
    Functor.isoWhiskerLeft F.rightDerivedToHomotopyCategory
        (exactFunctorHomotopyHomologyIso H (ComplexShape.up ℕ) n).symm ≪≫
      Functor.isoWhiskerRight (asIso (derivedBaseChangeResolutionMap F F' G H β))
        (HomotopyCategory.homologyFunctor D' (ComplexShape.up ℕ) n)
  exact e.isIso_hom

/-- The actual derived isomorphism, constructed from the invertibility of the existing map. -/
def derivedBaseChangeIso (n : ℕ) :
    F.rightDerived n ⋙ H ≅ G ⋙ F'.rightDerived n :=
  asIso (derivedBaseChangeMap F F' G H β n)

/-- Its forward natural transformation is exactly the previously constructed derived map. -/
theorem derivedBaseChangeIso_hom (n : ℕ) :
    (derivedBaseChangeIso F F' G H β n).hom =
      derivedBaseChangeMap F F' G H β n := rfl

#print axioms derivedBaseChangeResolutionMap_isIso
#print axioms derivedBaseChangeResolutionIso
#print axioms derivedBaseChangeResolutionIso_hom
#print axioms derivedBaseChangeMap_isIso
#print axioms derivedBaseChangeIso
#print axioms derivedBaseChangeIso_hom

end PrimeGap182.TypeIII
