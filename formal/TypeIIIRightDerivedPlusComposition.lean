import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Composition of the original bounded below right derived functors

If an additive functor `F` preserves injectives, its original bounded below
right derived functor may be composed with the original right derived functor
of `G`.  The comparison with the right derived functor of `F ⋙ G` is obtained
from the two original units.  On a bounded below complex of injectives both
unit maps are isomorphisms, so the injective derivability structure proves the
required universal property.

This is a comparison of full derived complexes.  It neither interchanges
cohomology with a limit nor assumes exactness of either functor.
-/

noncomputable section

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category

section NaturalIso

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {F F' : C ⥤ D} [F.Additive] [F'.Additive]

/-- The original natural isomorphism, applied degreewise and passed to the
bounded below homotopy categories. -/
def mapHomotopyCategoryPlusIso (e : F ≅ F') :
    F.mapHomotopyCategoryPlus ≅ F'.mapHomotopyCategoryPlus :=
  ((HomotopyCategory.plus D).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (HomotopyCategory.Plus.ι C)
      { hom := e.hom.mapHomotopyCategory (.up ℤ)
        inv := e.inv.mapHomotopyCategory (.up ℤ)
        hom_inv_id := by
          rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id]
          exact NatTrans.mapHomotopyCategory_id _ _
        inv_hom_id := by
          rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id]
          exact NatTrans.mapHomotopyCategory_id _ _ })

variable [EnoughInjectives C] [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]

/-- The isomorphism on the original right derived functors induced by an
isomorphism of the original additive functors. -/
def rightDerivedFunctorPlusIso (e : F ≅ F') :
    F.rightDerivedFunctorPlus ≅ F'.rightDerivedFunctorPlus :=
  Functor.rightDerivedNatIso F.rightDerivedFunctorPlus F'.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnit F'.rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso C)
    (Functor.isoWhiskerRight (mapHomotopyCategoryPlusIso e) DerivedCategory.Plus.Qh)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The derived comparison retains the original natural isomorphism and the
two original unit transformations. -/
theorem rightDerivedFunctorPlusIso_hom_fac (e : F ≅ F') :
    F.rightDerivedFunctorPlusUnit ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh (rightDerivedFunctorPlusIso e).hom =
      Functor.whiskerRight (mapHomotopyCategoryPlusIso e).hom DerivedCategory.Plus.Qh ≫
        F'.rightDerivedFunctorPlusUnit := by
  exact Functor.rightDerivedNatTrans_fac F.rightDerivedFunctorPlus F'.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnit F'.rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso C) _

end NaturalIso

section Composition

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C]
  [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [EnoughInjectives D]
  [HasDerivedCategory.{w₂} D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasDerivedCategory.{w₃} E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]

/-- The comparison unit is the pasting of the original two derived units and
the original comparison for applying two functors to complexes. -/
def rightDerivedFunctorPlusCompUnit :
    (F ⋙ G).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv
      DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft F.mapHomotopyCategoryPlus G.rightDerivedFunctorPlusUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight F.rightDerivedFunctorPlusUnit G.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom

/-- At a complex, the pasted unit has the expected three original factors. -/
theorem rightDerivedFunctorPlusCompUnit_app (K : HomotopyCategory.Plus C) :
    (rightDerivedFunctorPlusCompUnit F G).app K =
      DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv.app K) ≫
        G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) := by
  simp [rightDerivedFunctorPlusCompUnit]

variable [F.PreservesInjectiveObjects]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Both original unit factors are invertible on a bounded below complex of
injectives because the first functor preserves its injective terms. -/
theorem rightDerivedFunctorPlusCompUnit_isIso (K : HomotopyCategory.Plus C)
    [∀ n : ℤ, Injective (K.obj.as.X n)] :
    IsIso ((rightDerivedFunctorPlusCompUnit F G).app K) := by
  have (n : ℤ) : Injective ((F.mapHomotopyCategoryPlus.obj K).obj.as.X n) := by
    change Injective (F.obj (K.obj.as.X n))
    infer_instance
  rw [rightDerivedFunctorPlusCompUnit_app]
  infer_instance

/-- The composite, with the actual pasted unit, satisfies the right derived
universal property for the original composite additive functor. -/
instance rightDerivedFunctorPlusComp_isRightDerived :
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (rightDerivedFunctorPlusCompUnit F G) (HomotopyCategory.Plus.quasiIso C) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
    ((F ⋙ G).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)).isRightDerivedFunctor_of_isIso
      (rightDerivedFunctorPlusCompUnit F G)
      (fun _ => rightDerivedFunctorPlusCompUnit_isIso F G _)

/-- The original right derived functor of the composite is canonically
isomorphic to the composite of the original right derived functors. -/
def rightDerivedFunctorPlusCompIso :
    (F ⋙ G).rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  Functor.rightDerivedUnique (F ⋙ G).rightDerivedFunctorPlus
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
    (F ⋙ G).rightDerivedFunctorPlusUnit (rightDerivedFunctorPlusCompUnit F G)
    (HomotopyCategory.Plus.quasiIso C)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical composition isomorphism is normalized by the original unit
of the composite, rather than by a choice of resolution comparison maps. -/
theorem rightDerivedFunctorPlusCompIso_hom_fac :
    (F ⋙ G).rightDerivedFunctorPlusUnit ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh (rightDerivedFunctorPlusCompIso F G).hom =
      rightDerivedFunctorPlusCompUnit F G := by
  simpa only [rightDerivedFunctorPlusCompIso, Functor.rightDerivedUnique,
    Functor.rightDerivedNatIso_hom, Iso.refl_hom, id_comp] using
    (Functor.rightDerivedNatTrans_fac (F ⋙ G).rightDerivedFunctorPlus
      (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
      (F ⋙ G).rightDerivedFunctorPlusUnit (rightDerivedFunctorPlusCompUnit F G)
      (HomotopyCategory.Plus.quasiIso C) (𝟙 _))

end Composition

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.mapHomotopyCategoryPlusIso
#print axioms PrimeGap182.TypeIII.rightDerivedFunctorPlusIso
#print axioms PrimeGap182.TypeIII.rightDerivedFunctorPlusIso_hom_fac
#print axioms PrimeGap182.TypeIII.rightDerivedFunctorPlusCompUnit
#print axioms PrimeGap182.TypeIII.rightDerivedFunctorPlusCompUnit_app
#print axioms PrimeGap182.TypeIII.rightDerivedFunctorPlusCompUnit_isIso
#print axioms PrimeGap182.TypeIII.rightDerivedFunctorPlusComp_isRightDerived
#print axioms PrimeGap182.TypeIII.rightDerivedFunctorPlusCompIso
#print axioms PrimeGap182.TypeIII.rightDerivedFunctorPlusCompIso_hom_fac
