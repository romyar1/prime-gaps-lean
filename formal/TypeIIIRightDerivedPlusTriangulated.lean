import TypeIIIRightDerivedPlusComparison
import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
import Mathlib.CategoryTheory.Functor.Derived.RightDerivedTriangulated

/-!
# The existing bounded below right derived functor is triangulated

The shift structure comes from the universal property of the existing right
derived functor and its existing unit.  Every arrow in the bounded below derived
category is represented by an arrow between bounded below complexes of
injectives.  A distinguished cone triangle can be formed in that homotopy
category and included in the ordinary bounded below homotopy category.  The
derived unit is an isomorphism at all three vertices of this actual triangle.

No exactness of the additive functor, preservation of injectives, or acyclicity
of an additional class of objects is assumed.
-/

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Pretriangulated

section InjectiveRepresentatives

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Morphisms between actual bounded below complexes of injectives lift through
the original homotopy-category localization. -/
instance injectiveHomotopyPlusDerived_full :
    ((InjectiveObject.ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).Full where
  map_surjective {X Y} f := by
    obtain ⟨Y, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective Y
    have hY : CochainComplex.IsKInjective
        (((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj
          ((HomotopyCategory.Plus.quotient (InjectiveObject C)).obj Y)).obj.as) := by
      change CochainComplex.IsKInjective
        (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj Y.obj)
      infer_instance
    obtain ⟨g, hg⟩ :=
      (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective _ _ hY).surjective f
    obtain ⟨u, hu⟩ := (InjectiveObject.ι C).mapHomotopyCategoryPlus.map_surjective g
    refine ⟨u, ?_⟩
    change DerivedCategory.Plus.Qh.map
      ((InjectiveObject.ι C).mapHomotopyCategoryPlus.map u) = f
    rw [hu]
    exact hg

end InjectiveRepresentatives

section RightDerived

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C]
  [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  (F : C ⥤ D) [F.Additive]

/-- The canonical shift structure obtained from the universal property of the
same bounded below right derived functor and its same unit. -/
instance rightDerivedFunctorPlus_commShift : F.rightDerivedFunctorPlus.CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift F.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso C) ℤ

/-- The original derived unit is compatible with this canonical shift structure. -/
instance rightDerivedFunctorPlusUnit_commShift :
    NatTrans.CommShift F.rightDerivedFunctorPlusUnit ℤ := by
  exact Functor.IsRightDerivedFunctor.natTrans_commShift F.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso C) ℤ

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Every actual derived arrow has a distinguished homotopy-category triangle
whose three vertices make the original derived unit invertible. -/
theorem rightDerivedFunctorPlus_injectiveTriangle {X Y : DerivedCategory.Plus C}
    (f : X ⟶ Y) :
    ∃ (T : Triangle (HomotopyCategory.Plus C)) (_ : T ∈ distTriang _)
      (_ : IsIso (F.rightDerivedFunctorPlusUnit.app T.obj₁))
      (_ : IsIso (F.rightDerivedFunctorPlusUnit.app T.obj₂))
      (_ : IsIso (F.rightDerivedFunctorPlusUnit.app T.obj₃)),
      Nonempty (Arrow.mk (DerivedCategory.Plus.Qh.map T.mor₁) ≅ Arrow.mk f) := by
  let I := (InjectiveObject.ι C).mapHomotopyCategoryPlus
  let L := I ⋙ DerivedCategory.Plus.Qh
  let a := L.mapArrow.objPreimage (Arrow.mk f)
  let e := L.mapArrow.objObjPreimageIso (Arrow.mk f)
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle a.hom
  refine ⟨I.mapTriangle.obj (Triangle.mk a.hom g h), I.map_distinguished _ hT,
    ?_, ?_, ?_, ?_⟩
  · change IsIso (F.rightDerivedFunctorPlusUnit.app (I.obj a.left))
    dsimp only [I]
    infer_instance
  · change IsIso (F.rightDerivedFunctorPlusUnit.app (I.obj a.right))
    dsimp only [I]
    infer_instance
  · change IsIso (F.rightDerivedFunctorPlusUnit.app (I.obj Z))
    dsimp only [I]
    infer_instance
  · exact ⟨e⟩

/-- The original bounded below right derived functor preserves distinguished
triangles, with its canonical shift structure. -/
instance rightDerivedFunctorPlus_isTriangulated : F.rightDerivedFunctorPlus.IsTriangulated :=
  Functor.isTriangulated_of_leftExtension F.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnit (fun {_ _} f => rightDerivedFunctorPlus_injectiveTriangle F f)

end RightDerived

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.injectiveHomotopyPlusDerived_full
#print axioms PrimeGap182.TypeIII.rightDerivedFunctorPlus_commShift
#print axioms PrimeGap182.TypeIII.rightDerivedFunctorPlusUnit_commShift
#print axioms PrimeGap182.TypeIII.rightDerivedFunctorPlus_injectiveTriangle
#print axioms PrimeGap182.TypeIII.rightDerivedFunctorPlus_isTriangulated
