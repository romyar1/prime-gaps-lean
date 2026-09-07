import TypeIIIExactFunctorResolution
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Exact functors that preserve injective resolutions

For an additive exact functor that preserves injective objects, the
existing literal mapped resolution is an actual injective resolution.
Its full augmentation is obtained by mapping the original augmentation
and using the canonical comparison for complexes supported in degree zero.

The existing comparison to a chosen injective resolution is a homotopy
equivalence. Consequently the existing natural transformation of
resolution functors is an isomorphism in the homotopy category.

Preservation of injective objects is explicit here. No assertion is
made that arbitrary inverse image has that property.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (G : C ⥤ D) [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [G.PreservesInjectiveObjects] {A : C}

/-- The literal mapped complex is an actual injective resolution when
the exact functor preserves injective objects. -/
def exactFunctorInjectiveResolution (I : InjectiveResolution A) :
    InjectiveResolution (G.obj A) where
  cocomplex := exactFunctorResolutionComplex G I
  injective n := G.injective_obj (I.cocomplex.X n)
  ι := (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℕ) 0).inv.app A ≫
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
  quasiIso := by infer_instance

/-- The resolution uses exactly the existing mapped cochain complex. -/
theorem exactFunctorInjectiveResolution_cocomplex (I : InjectiveResolution A) :
    (exactFunctorInjectiveResolution G I).cocomplex =
      exactFunctorResolutionComplex G I := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Its degree-zero augmentation is exactly the existing mapped augmentation. -/
@[simp] theorem exactFunctorInjectiveResolution_ι_f_zero (I : InjectiveResolution A) :
    (exactFunctorInjectiveResolution G I).ι.f 0 =
      exactFunctorResolutionAugmentation G I := by
  simp [exactFunctorInjectiveResolution, HomologicalComplex.singleMapHomologicalComplex]

variable [HasInjectiveResolutions D]

set_option backward.isDefEq.respectTransparency.types false in
/-- The existing chain comparison intertwines the full actual augmentations. -/
@[reassoc (attr := simp)]
theorem exactFunctorResolutionComparison_augmentation (I : InjectiveResolution A) :
    (exactFunctorInjectiveResolution G I).ι ≫ exactFunctorResolutionComparison G I =
      (injectiveResolution (G.obj A)).ι := by
  ext
  change (exactFunctorInjectiveResolution G I).ι.f 0 ≫
    (exactFunctorResolutionComparison G I).f 0 = _
  rw [exactFunctorInjectiveResolution_ι_f_zero]
  exact exactFunctorResolutionComparison_commutes G I

set_option backward.isDefEq.respectTransparency false in
/-- The existing comparison is an actual homotopy equivalence. Its inverse
is the ordinary comparison into the actual mapped injective resolution. -/
def exactFunctorResolutionComparisonHomotopyEquiv (I : InjectiveResolution A) :
    HomotopyEquiv (exactFunctorResolutionComplex G I)
      (injectiveResolution (G.obj A)).cocomplex where
  hom := exactFunctorResolutionComparison G I
  inv := InjectiveResolution.desc (𝟙 (G.obj A)) (exactFunctorInjectiveResolution G I)
    (injectiveResolution (G.obj A))
  homotopyHomInvId :=
    exactResolutionComparisonHomotopy (exactFunctorResolutionComplex G I)
      (exactFunctorResolutionAugmentation G I) (exactFunctorResolutionAugmentation_d G I)
      (exactFunctorResolution_exact_zero G I) (exactFunctorResolution_exact_succ G I)
      (𝟙 (G.obj A)) (exactFunctorInjectiveResolution G I) _ _
      (by
        change exactFunctorResolutionAugmentation G I ≫
          ((exactFunctorResolutionComparison G I).f 0 ≫
            (InjectiveResolution.desc (𝟙 (G.obj A)) (exactFunctorInjectiveResolution G I)
              (injectiveResolution (G.obj A))).f 0) = _
        rw [← assoc, exactFunctorResolutionComparison_commutes]
        exact InjectiveResolution.desc_commutes_zero _ _ _)
      (by
        change exactFunctorResolutionAugmentation G I ≫ (𝟙 _) =
          (𝟙 _) ≫ (exactFunctorInjectiveResolution G I).ι.f 0
        rw [Category.comp_id, Category.id_comp, exactFunctorInjectiveResolution_ι_f_zero])
  homotopyInvHomId :=
    exactResolutionComparisonHomotopy (injectiveResolution (G.obj A)).cocomplex
      ((injectiveResolution (G.obj A)).ι.f 0)
      (injectiveResolution (G.obj A)).ι_f_zero_comp_complex_d
      (injectiveResolution (G.obj A)).exact₀ (injectiveResolution (G.obj A)).exact_succ
      (𝟙 (G.obj A)) (injectiveResolution (G.obj A)) _ _
      (by
        change (injectiveResolution (G.obj A)).ι.f 0 ≫
          ((InjectiveResolution.desc (𝟙 (G.obj A)) (exactFunctorInjectiveResolution G I)
              (injectiveResolution (G.obj A))).f 0 ≫
            (exactFunctorResolutionComparison G I).f 0) = _
        rw [← assoc, InjectiveResolution.desc_commutes_zero, assoc,
          exactFunctorInjectiveResolution_ι_f_zero, exactFunctorResolutionComparison_commutes])
      (by
        change (injectiveResolution (G.obj A)).ι.f 0 ≫ (𝟙 _) =
          (𝟙 _) ≫ (injectiveResolution (G.obj A)).ι.f 0
        rw [Category.comp_id, Category.id_comp])

/-- The equivalence's forward chain map is exactly the pre-existing comparison. -/
theorem exactFunctorResolutionComparisonHomotopyEquiv_hom (I : InjectiveResolution A) :
    (exactFunctorResolutionComparisonHomotopyEquiv G I).hom =
      exactFunctorResolutionComparison G I := rfl

/-- The actual comparison induces an isomorphism in the actual homotopy category. -/
def exactFunctorResolutionComparisonIso (I : InjectiveResolution A) :
    (HomotopyCategory.quotient D (ComplexShape.up ℕ)).obj
        (exactFunctorResolutionComplex G I) ≅
      (HomotopyCategory.quotient D (ComplexShape.up ℕ)).obj
        (injectiveResolution (G.obj A)).cocomplex :=
  HomotopyCategory.isoOfHomotopyEquiv (exactFunctorResolutionComparisonHomotopyEquiv G I)

/-- The isomorphism's forward map is the quotient of the existing comparison. -/
theorem exactFunctorResolutionComparisonIso_hom (I : InjectiveResolution A) :
    (exactFunctorResolutionComparisonIso G I).hom =
      (HomotopyCategory.quotient D (ComplexShape.up ℕ)).map
        (exactFunctorResolutionComparison G I) := rfl

/-- Invertibility belongs to the existing comparison, rather than to an unrelated choice. -/
instance exactFunctorResolutionComparison_isIso (I : InjectiveResolution A) :
    IsIso ((HomotopyCategory.quotient D (ComplexShape.up ℕ)).map
      (exactFunctorResolutionComparison G I)) := by
  change IsIso (exactFunctorResolutionComparisonIso G I).hom
  infer_instance

variable [HasInjectiveResolutions C]

/-- The existing natural transformation of actual resolution functors is an isomorphism
when the exact functor preserves injective objects. -/
instance exactFunctorResolutionNatTrans_isIso : IsIso (exactFunctorResolutionNatTrans G) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro A
  change IsIso ((HomotopyCategory.quotient D (ComplexShape.up ℕ)).map
    (exactFunctorResolutionComparison G (injectiveResolution A)))
  infer_instance

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.exactFunctorInjectiveResolution
#print axioms PrimeGap182.TypeIII.exactFunctorInjectiveResolution_cocomplex
#print axioms PrimeGap182.TypeIII.exactFunctorInjectiveResolution_ι_f_zero
#print axioms PrimeGap182.TypeIII.exactFunctorResolutionComparison_augmentation
#print axioms PrimeGap182.TypeIII.exactFunctorResolutionComparisonHomotopyEquiv
#print axioms PrimeGap182.TypeIII.exactFunctorResolutionComparisonHomotopyEquiv_hom
#print axioms PrimeGap182.TypeIII.exactFunctorResolutionComparisonIso
#print axioms PrimeGap182.TypeIII.exactFunctorResolutionComparisonIso_hom
#print axioms PrimeGap182.TypeIII.exactFunctorResolutionComparison_isIso
#print axioms PrimeGap182.TypeIII.exactFunctorResolutionNatTrans_isIso
