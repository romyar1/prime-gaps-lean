import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Additivity of the actual injective-resolution derived functors

The chosen descents need not add as cochain maps. Their augmentations
agree, so the actual comparison homotopy identifies them in the homotopy
category. This proves additivity of the existing resolution functor and
of the right derived functors constructed from it.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Addition of original morphisms agrees with addition of their actual descents up to homotopy. -/
def injectiveResolution_desc_add_homotopy {X Y : C} (f g : X ⟶ Y)
    (I : InjectiveResolution X) (J : InjectiveResolution Y) :
    Homotopy (InjectiveResolution.desc (f + g) J I)
      (InjectiveResolution.desc f J I + InjectiveResolution.desc g J I) := by
  apply InjectiveResolution.descHomotopy (f + g)
  · exact InjectiveResolution.desc_commutes (f + g) J I
  · rw [Preadditive.comp_add, InjectiveResolution.desc_commutes,
      InjectiveResolution.desc_commutes, Functor.map_add, Preadditive.add_comp]

/-- The existing injective-resolution functor is additive in the homotopy category. -/
instance injectiveResolutions_additive [HasInjectiveResolutions C] :
    (injectiveResolutions C).Additive where
  map_add {X Y} f g := by
    change (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
        (InjectiveResolution.desc (f + g) (injectiveResolution Y) (injectiveResolution X)) =
      (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X)) +
        (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc g (injectiveResolution Y) (injectiveResolution X))
    rw [← Functor.map_add]
    apply HomotopyCategory.eq_of_homotopy
    exact injectiveResolution_desc_add_homotopy f g (injectiveResolution X) (injectiveResolution Y)

variable [HasInjectiveResolutions C] {D : Type*} [Category* D] [Abelian D]
  (F : C ⥤ D) [F.Additive]

/-- Applying an additive functor to the actual resolution functor remains additive. -/
instance rightDerivedToHomotopyCategory_additive : F.rightDerivedToHomotopyCategory.Additive :=
  inferInstanceAs ((injectiveResolutions C ⋙ F.mapHomotopyCategory (ComplexShape.up ℕ)).Additive)

/-- The actual right derived functors are additive. -/
instance rightDerived_additive (n : ℕ) : (F.rightDerived n).Additive :=
  inferInstanceAs ((F.rightDerivedToHomotopyCategory ⋙
    HomotopyCategory.homologyFunctor D (ComplexShape.up ℕ) n).Additive)

#print axioms injectiveResolution_desc_add_homotopy
#print axioms injectiveResolutions_additive
#print axioms rightDerivedToHomotopyCategory_additive
#print axioms rightDerived_additive

end PrimeGap182.TypeIII
