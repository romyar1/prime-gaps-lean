import TypeIIIExactFunctorResolution

/-!
# Natural transformations and the original resolution comparisons

For a natural transformation between additive exact functors, the
original resolution comparisons commute up to homotopy.  The first map
applies the transformation to the given resolution and then compares to
the chosen target resolution.  The second first compares the exact image
resolution and then applies the original resolution map of the component
at the augmented object.

Both maps extend that same component.  The source is the actual exact
image of the supplied resolution, and only the chosen target resolution
needs injective terms.  No preservation of injectives, acyclicity, or
prior comparison hypothesis is imposed.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasInjectiveResolutions D]
  (G G' : C ⥤ D) [G.Additive] [G'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  (τ : G ⟶ G') {A : C}

omit [PreservesFiniteLimits G] [PreservesFiniteColimits G] in
/-- Applying the original transformation on the resolution and then
the original comparison extends its component on the augmented object. -/
theorem exactFunctorResolutionComparison_transformation_commutes
    (I : InjectiveResolution A) :
    exactFunctorResolutionAugmentation G I ≫
        (((τ.mapHomologicalComplex (ComplexShape.up ℕ)).app I.cocomplex ≫
          exactFunctorResolutionComparison G' I).f 0) =
      τ.app A ≫ (injectiveResolution (G'.obj A)).ι.f 0 := by
  change G.map (I.ι.f 0) ≫
      (τ.app (I.cocomplex.X 0) ≫ (exactFunctorResolutionComparison G' I).f 0) = _
  rw [← assoc, τ.naturality, assoc, exactFunctorResolutionComparison_commutes]
  simp only [CochainComplex.single₀_obj_zero]

omit [G'.Additive] [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] in
/-- The original comparison followed by the original resolution map
of the component extends the same map of augmented objects. -/
theorem exactFunctorResolutionComparison_transformation_desc_commutes
    (I : InjectiveResolution A) :
    exactFunctorResolutionAugmentation G I ≫
        ((exactFunctorResolutionComparison G I ≫
          InjectiveResolution.desc (τ.app A) (injectiveResolution (G'.obj A))
            (injectiveResolution (G.obj A))).f 0) =
      τ.app A ≫ (injectiveResolution (G'.obj A)).ι.f 0 := by
  change exactFunctorResolutionAugmentation G I ≫
      ((exactFunctorResolutionComparison G I).f 0 ≫
        (InjectiveResolution.desc (τ.app A) (injectiveResolution (G'.obj A))
          (injectiveResolution (G.obj A))).f 0) = _
  rw [← assoc, exactFunctorResolutionComparison_commutes]
  exact InjectiveResolution.desc_commutes_zero _ _ _

/-- The original comparison is natural in the exact functor up to
homotopy, without assuming injectivity of the mapped source terms. -/
def exactFunctorResolutionComparisonTransformationHomotopy
    (I : InjectiveResolution A) :
    Homotopy
      ((τ.mapHomologicalComplex (ComplexShape.up ℕ)).app I.cocomplex ≫
        exactFunctorResolutionComparison G' I)
      (exactFunctorResolutionComparison G I ≫
        InjectiveResolution.desc (τ.app A) (injectiveResolution (G'.obj A))
          (injectiveResolution (G.obj A))) :=
  exactResolutionComparisonHomotopy (exactFunctorResolutionComplex G I)
    (exactFunctorResolutionAugmentation G I) (exactFunctorResolutionAugmentation_d G I)
    (exactFunctorResolution_exact_zero G I) (exactFunctorResolution_exact_succ G I)
    (τ.app A) (injectiveResolution (G'.obj A)) _ _
    (exactFunctorResolutionComparison_transformation_commutes G G' τ I)
    (exactFunctorResolutionComparison_transformation_desc_commutes G G' τ I)

/-- In the actual homotopy category, the two original chain maps
give the same morphism. -/
theorem exactFunctorResolutionComparison_transformation_quotient
    (I : InjectiveResolution A) :
    (HomotopyCategory.quotient D (ComplexShape.up ℕ)).map
        ((τ.mapHomologicalComplex (ComplexShape.up ℕ)).app I.cocomplex ≫
          exactFunctorResolutionComparison G' I) =
      (HomotopyCategory.quotient D (ComplexShape.up ℕ)).map
        (exactFunctorResolutionComparison G I ≫
          InjectiveResolution.desc (τ.app A) (injectiveResolution (G'.obj A))
            (injectiveResolution (G.obj A))) :=
  HomotopyCategory.eq_of_homotopy _ _
    (exactFunctorResolutionComparisonTransformationHomotopy G G' τ I)

#print axioms exactFunctorResolutionComparison_transformation_commutes
#print axioms exactFunctorResolutionComparison_transformation_desc_commutes
#print axioms exactFunctorResolutionComparisonTransformationHomotopy
#print axioms exactFunctorResolutionComparison_transformation_quotient

end PrimeGap182.TypeIII
