import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-!
# The canonical short-exact-sequence triangle in the bounded below category

The connecting morphism is the full-subcategory lift of the existing
`ShortComplex.ShortExact.singleδ`, with the actual inclusion's shift
comparison.  Its image is the original distinguished single triangle.
No distinguishedness or compatibility hypothesis is supplied separately.
-/

noncomputable section

universe w v u

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {S : ShortComplex C} (hS : S.ShortExact)

/-- The original connecting map, lifted along the actual bounded below inclusion. -/
def shortExactPlusConnectingHom :
    (DerivedCategory.Plus.singleFunctor C 0).obj S.X₃ ⟶
      ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧ :=
  (DerivedCategory.Plus.ι (C := C)).preimage
    (hS.singleδ ≫
      ((DerivedCategory.Plus.ι (C := C)).commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁))

set_option backward.isDefEq.respectTransparency false in
/-- Inclusion and its shift comparison recover precisely the original connecting map. -/
theorem shortExactPlusConnectingHom_inclusion :
    (DerivedCategory.Plus.ι (C := C)).map (shortExactPlusConnectingHom hS) ≫
        ((DerivedCategory.Plus.ι (C := C)).commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁) = hS.singleδ := by
  rw [shortExactPlusConnectingHom, Functor.map_preimage]
  erw [CategoryTheory.Category.assoc, Iso.inv_hom_id_app, comp_id]

/-- The literal degree-zero single objects and maps form the canonical Plus triangle. -/
def shortExactPlusTriangle : Triangle (DerivedCategory.Plus C) :=
  Triangle.mk ((DerivedCategory.Plus.singleFunctor C 0).map S.f)
    ((DerivedCategory.Plus.singleFunctor C 0).map S.g)
    (shortExactPlusConnectingHom hS)

set_option backward.isDefEq.respectTransparency false in
/-- Inclusion identifies the lifted triangle with the existing single triangle. -/
def shortExactPlusTriangleInclusionIso :
    (DerivedCategory.Plus.ι (C := C)).mapTriangle.obj (shortExactPlusTriangle hS) ≅
      hS.singleTriangle := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · change (DerivedCategory.singleFunctor C 0).map S.f ≫ 𝟙 _ =
      𝟙 _ ≫ (DerivedCategory.singleFunctor C 0).map S.f
    simp only [comp_id, id_comp]
  · change (DerivedCategory.singleFunctor C 0).map S.g ≫ 𝟙 _ =
      𝟙 _ ≫ (DerivedCategory.singleFunctor C 0).map S.g
    simp only [comp_id, id_comp]
  · change ((DerivedCategory.Plus.ι (C := C)).map (shortExactPlusConnectingHom hS) ≫
        ((DerivedCategory.Plus.ι (C := C)).commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁)) ≫
          (shiftFunctor (DerivedCategory C) (1 : ℤ)).map (𝟙 _) = 𝟙 _ ≫ hS.singleδ
    erw [(shiftFunctor (DerivedCategory C) (1 : ℤ)).map_id, comp_id, id_comp]
    exact shortExactPlusConnectingHom_inclusion hS

/-- The triangle is distinguished because its actual full-subcategory image is. -/
theorem shortExactPlusTriangle_distinguished :
    shortExactPlusTriangle hS ∈ distTriang (DerivedCategory.Plus C) := by
  apply ((DerivedCategory.Plus.ι (C := C)).map_distinguished_iff _).1
  exact (distinguished_iff_of_iso (shortExactPlusTriangleInclusionIso hS)).2
    hS.singleTriangle_distinguished

variable {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
  (φ : S₁ ⟶ S₂)

/-- The original morphism of single triangles, lifted through the actual inclusion. -/
def shortExactPlusTriangleMap : shortExactPlusTriangle h₁ ⟶ shortExactPlusTriangle h₂ :=
  (DerivedCategory.Plus.ι (C := C)).mapTriangle.preimage
    ((shortExactPlusTriangleInclusionIso h₁).hom ≫
      ShortComplex.ShortExact.singleTriangle.map h₁ h₂ φ ≫
      (shortExactPlusTriangleInclusionIso h₂).inv)

/-- The lifted map recovers the original canonical map under the inclusion isomorphisms. -/
theorem shortExactPlusTriangleMap_inclusion :
    (DerivedCategory.Plus.ι (C := C)).mapTriangle.map (shortExactPlusTriangleMap h₁ h₂ φ) =
      (shortExactPlusTriangleInclusionIso h₁).hom ≫
        ShortComplex.ShortExact.singleTriangle.map h₁ h₂ φ ≫
        (shortExactPlusTriangleInclusionIso h₂).inv := by
  exact (DerivedCategory.Plus.ι (C := C)).mapTriangle.map_preimage _

set_option backward.isDefEq.respectTransparency false in
/-- The first component is the original single-functor map. -/
theorem shortExactPlusTriangleMap_hom₁ :
    (shortExactPlusTriangleMap h₁ h₂ φ).hom₁ =
      (DerivedCategory.Plus.singleFunctor C 0).map φ.τ₁ := by
  apply (DerivedCategory.Plus.ι (C := C)).map_injective
  change (DerivedCategory.Plus.ι (C := C)).map
      ((shortExactPlusTriangleMap h₁ h₂ φ).hom₁) =
    (DerivedCategory.singleFunctor C 0).map φ.τ₁
  have h := congrArg TriangleMorphism.hom₁ (shortExactPlusTriangleMap_inclusion h₁ h₂ φ)
  change (DerivedCategory.Plus.ι (C := C)).map
      ((shortExactPlusTriangleMap h₁ h₂ φ).hom₁) =
    𝟙 _ ≫ (DerivedCategory.singleFunctor C 0).map φ.τ₁ ≫ 𝟙 _ at h
  simpa only [id_comp, comp_id] using h

set_option backward.isDefEq.respectTransparency false in
/-- The second component is the original single-functor map. -/
theorem shortExactPlusTriangleMap_hom₂ :
    (shortExactPlusTriangleMap h₁ h₂ φ).hom₂ =
      (DerivedCategory.Plus.singleFunctor C 0).map φ.τ₂ := by
  apply (DerivedCategory.Plus.ι (C := C)).map_injective
  change (DerivedCategory.Plus.ι (C := C)).map
      ((shortExactPlusTriangleMap h₁ h₂ φ).hom₂) =
    (DerivedCategory.singleFunctor C 0).map φ.τ₂
  have h := congrArg TriangleMorphism.hom₂ (shortExactPlusTriangleMap_inclusion h₁ h₂ φ)
  change (DerivedCategory.Plus.ι (C := C)).map
      ((shortExactPlusTriangleMap h₁ h₂ φ).hom₂) =
    𝟙 _ ≫ (DerivedCategory.singleFunctor C 0).map φ.τ₂ ≫ 𝟙 _ at h
  simpa only [id_comp, comp_id] using h

set_option backward.isDefEq.respectTransparency false in
/-- The third component is the original single-functor map. -/
theorem shortExactPlusTriangleMap_hom₃ :
    (shortExactPlusTriangleMap h₁ h₂ φ).hom₃ =
      (DerivedCategory.Plus.singleFunctor C 0).map φ.τ₃ := by
  apply (DerivedCategory.Plus.ι (C := C)).map_injective
  change (DerivedCategory.Plus.ι (C := C)).map
      ((shortExactPlusTriangleMap h₁ h₂ φ).hom₃) =
    (DerivedCategory.singleFunctor C 0).map φ.τ₃
  have h := congrArg TriangleMorphism.hom₃ (shortExactPlusTriangleMap_inclusion h₁ h₂ φ)
  change (DerivedCategory.Plus.ι (C := C)).map
      ((shortExactPlusTriangleMap h₁ h₂ φ).hom₃) =
    𝟙 _ ≫ (DerivedCategory.singleFunctor C 0).map φ.τ₃ ≫ 𝟙 _ at h
  simpa only [id_comp, comp_id] using h

set_option backward.isDefEq.respectTransparency false in
/-- The lifted connecting map is natural for actual morphisms of short exact sequences. -/
theorem shortExactPlusConnectingHom_naturality :
    (DerivedCategory.Plus.singleFunctor C 0).map φ.τ₃ ≫ shortExactPlusConnectingHom h₂ =
      shortExactPlusConnectingHom h₁ ≫
        ((DerivedCategory.Plus.singleFunctor C 0).map φ.τ₁)⟦(1 : ℤ)⟧' := by
  have h := (shortExactPlusTriangleMap h₁ h₂ φ).comm₃
  change shortExactPlusConnectingHom h₁ ≫
      ((shortExactPlusTriangleMap h₁ h₂ φ).hom₁)⟦(1 : ℤ)⟧' =
    (shortExactPlusTriangleMap h₁ h₂ φ).hom₃ ≫ shortExactPlusConnectingHom h₂ at h
  rw [shortExactPlusTriangleMap_hom₁, shortExactPlusTriangleMap_hom₃] at h
  exact h.symm

#print axioms shortExactPlusConnectingHom
#print axioms shortExactPlusConnectingHom_inclusion
#print axioms shortExactPlusTriangle
#print axioms shortExactPlusTriangleInclusionIso
#print axioms shortExactPlusTriangle_distinguished
#print axioms shortExactPlusTriangleMap
#print axioms shortExactPlusTriangleMap_inclusion
#print axioms shortExactPlusTriangleMap_hom₁
#print axioms shortExactPlusTriangleMap_hom₂
#print axioms shortExactPlusTriangleMap_hom₃
#print axioms shortExactPlusConnectingHom_naturality

end PrimeGap182.TypeIII
