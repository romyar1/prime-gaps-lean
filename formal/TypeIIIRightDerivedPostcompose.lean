import TypeIIIDerivedBaseChangeIso
import TypeIIIDerivedBaseChangeZero

/-!
# Exact postcomposition of the actual right derived functors

An additive functor preserving homology commutes with taking cohomology
of the existing injective resolutions.  We specialize the already
constructed derived comparison to the identity functor on the source.
Thus a comparison F ⋙ H → F' induces RⁿF ⋙ H → RⁿF'; if the original
comparison is an isomorphism, so is the same derived map.

The degree-zero square records compatibility with the original
resolution augmentations.  No preservation of injectives by F or H is
required: the source-side comparison functor is the actual identity.
-/

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {D' : Type u₃} [Category.{v₃} D'] [Abelian D']
  (F : C ⥤ D) [F.Additive] (F' : C ⥤ D') [F'.Additive]
  (H : D ⥤ D') [H.Additive] [H.PreservesHomology]

/-- The existing derived comparison, with the source-side identity unitor removed. -/
def rightDerivedPostcomposeMap (β : F ⋙ H ⟶ F') (n : ℕ) :
    F.rightDerived n ⋙ H ⟶ F'.rightDerived n :=
  derivedBaseChangeMap F F' (𝟭 C) H (β ≫ (Functor.leftUnitor F').inv) n ≫
    (Functor.leftUnitor (F'.rightDerived n)).hom

/-- This is literally the original derived map followed by the identity unitor. -/
theorem rightDerivedPostcomposeMap_eq (β : F ⋙ H ⟶ F') (n : ℕ) :
    rightDerivedPostcomposeMap F F' H β n =
      derivedBaseChangeMap F F' (𝟭 C) H (β ≫ (Functor.leftUnitor F').inv) n ≫
        (Functor.leftUnitor (F'.rightDerived n)).hom := rfl

set_option backward.isDefEq.respectTransparency false in
/-- At degree zero the actual comparison extends the original ordinary transformation. -/
theorem rightDerivedPostcomposeMap_zero (β : F ⋙ H ⟶ F') :
    Functor.whiskerRight F.toRightDerivedZero H ≫ rightDerivedPostcomposeMap F F' H β 0 =
      β ≫ F'.toRightDerivedZero := by
  ext A
  have h := NatTrans.congr_app
    (derivedBaseChangeMap_zero F F' (𝟭 C) H (β ≫ (Functor.leftUnitor F').inv)) A
  simp only [rightDerivedPostcomposeMap, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
    comp_id] at h ⊢
  erw [comp_id]
  exact h

/-- An invertible ordinary comparison makes the same postcomposition map invertible. -/
instance rightDerivedPostcomposeMap_isIso (β : F ⋙ H ⟶ F') [IsIso β] (n : ℕ) :
    IsIso (rightDerivedPostcomposeMap F F' H β n) := by
  dsimp only [rightDerivedPostcomposeMap]
  infer_instance

/-- The actual natural isomorphism induced by an invertible ordinary comparison. -/
def rightDerivedPostcomposeIso (β : F ⋙ H ≅ F') (n : ℕ) :
    F.rightDerived n ⋙ H ≅ F'.rightDerived n :=
  asIso (rightDerivedPostcomposeMap F F' H β.hom n)

/-- Its forward map is the existing postcomposition comparison. -/
theorem rightDerivedPostcomposeIso_hom (β : F ⋙ H ≅ F') (n : ℕ) :
    (rightDerivedPostcomposeIso F F' H β n).hom =
      rightDerivedPostcomposeMap F F' H β.hom n := rfl

/-- The actual isomorphism has the original degree-zero augmentation compatibility. -/
theorem rightDerivedPostcomposeIso_zero (β : F ⋙ H ≅ F') :
    Functor.whiskerRight F.toRightDerivedZero H ≫ (rightDerivedPostcomposeIso F F' H β 0).hom =
      β.hom ≫ F'.toRightDerivedZero :=
  rightDerivedPostcomposeMap_zero F F' H β.hom

#print axioms rightDerivedPostcomposeMap
#print axioms rightDerivedPostcomposeMap_eq
#print axioms rightDerivedPostcomposeMap_zero
#print axioms rightDerivedPostcomposeMap_isIso
#print axioms rightDerivedPostcomposeIso
#print axioms rightDerivedPostcomposeIso_hom
#print axioms rightDerivedPostcomposeIso_zero

end PrimeGap182.TypeIII
