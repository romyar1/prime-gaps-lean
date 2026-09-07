import TypeIIIExactFunctorResolution

/-!
# Composition of the original exact-functor resolution comparisons

For two additive exact functors, the existing comparison for their
composite is homotopic to the existing two-stage comparison.  Both maps
start from the literal image of the given injective resolution and end
in the same chosen injective resolution of the composite image.

The source is exact because both functors are exact.  Comparison
uniqueness only requires injectivity of the chosen target resolution;
neither functor is assumed to preserve injectives or acyclic objects.
The resulting equality is stated for the original homotopy-category
quotient maps, with no replacement of the chosen resolutions.
-/

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {C' : Type u₂} [Category.{v₂} C'] [Abelian C'] [HasInjectiveResolutions C']
  {C'' : Type u₃} [Category.{v₃} C''] [Abelian C''] [HasInjectiveResolutions C'']
  (G : C ⥤ C') [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (G' : C' ⥤ C'') [G'.Additive] [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  {A : C}

/-- The original two-stage comparison extends the same augmentation
as the original comparison for the composite functor. -/
theorem exactFunctorResolutionComparison_comp_commutes (I : InjectiveResolution A) :
    exactFunctorResolutionAugmentation (G ⋙ G') I ≫
        (((G'.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (exactFunctorResolutionComparison G I) ≫
          exactFunctorResolutionComparison G' (injectiveResolution (G.obj A))).f 0) =
      (injectiveResolution ((G ⋙ G').obj A)).ι.f 0 := by
  change G'.map (G.map (I.ι.f 0)) ≫
      (G'.map ((exactFunctorResolutionComparison G I).f 0) ≫
        (exactFunctorResolutionComparison G' (injectiveResolution (G.obj A))).f 0) = _
  rw [← assoc, ← G'.map_comp, exactFunctorResolutionComparison_commutes]
  exact exactFunctorResolutionComparison_commutes G' (injectiveResolution (G.obj A))

/-- The comparison for the composite functor is homotopic to the
literal composite of the two existing resolution comparisons. -/
def exactFunctorResolutionComparisonCompHomotopy (I : InjectiveResolution A) :
    Homotopy (exactFunctorResolutionComparison (G ⋙ G') I)
      ((G'.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (exactFunctorResolutionComparison G I) ≫
        exactFunctorResolutionComparison G' (injectiveResolution (G.obj A))) :=
  exactResolutionComparisonHomotopy (exactFunctorResolutionComplex (G ⋙ G') I)
    (exactFunctorResolutionAugmentation (G ⋙ G') I)
    (exactFunctorResolutionAugmentation_d (G ⋙ G') I)
    (exactFunctorResolution_exact_zero (G ⋙ G') I)
    (exactFunctorResolution_exact_succ (G ⋙ G') I)
    (𝟙 ((G ⋙ G').obj A)) (injectiveResolution ((G ⋙ G').obj A)) _ _
    (by simpa only [id_comp] using exactFunctorResolutionComparison_commutes (G ⋙ G') I)
    (by simpa only [id_comp] using exactFunctorResolutionComparison_comp_commutes G G' I)

/-- In the actual homotopy category, the original comparison for the
composite equals the quotient of the original two-stage chain map. -/
theorem exactFunctorResolutionComparison_comp_quotient (I : InjectiveResolution A) :
    (HomotopyCategory.quotient C'' (ComplexShape.up ℕ)).map
        (exactFunctorResolutionComparison (G ⋙ G') I) =
      (HomotopyCategory.quotient C'' (ComplexShape.up ℕ)).map
        ((G'.mapHomologicalComplex (ComplexShape.up ℕ)).map
            (exactFunctorResolutionComparison G I) ≫
          exactFunctorResolutionComparison G' (injectiveResolution (G.obj A))) :=
  HomotopyCategory.eq_of_homotopy _ _ (exactFunctorResolutionComparisonCompHomotopy G G' I)

/-- The same quotient equality, with the two original quotient maps
displayed separately for use in composition of derived comparisons. -/
theorem exactFunctorResolutionComparison_comp_quotient_factors (I : InjectiveResolution A) :
    (HomotopyCategory.quotient C'' (ComplexShape.up ℕ)).map
        (exactFunctorResolutionComparison (G ⋙ G') I) =
      (HomotopyCategory.quotient C'' (ComplexShape.up ℕ)).map
          ((G'.mapHomologicalComplex (ComplexShape.up ℕ)).map
            (exactFunctorResolutionComparison G I)) ≫
        (HomotopyCategory.quotient C'' (ComplexShape.up ℕ)).map
          (exactFunctorResolutionComparison G' (injectiveResolution (G.obj A))) := by
  rw [exactFunctorResolutionComparison_comp_quotient, Functor.map_comp]

#print axioms exactFunctorResolutionComparison_comp_commutes
#print axioms exactFunctorResolutionComparisonCompHomotopy
#print axioms exactFunctorResolutionComparison_comp_quotient
#print axioms exactFunctorResolutionComparison_comp_quotient_factors

end PrimeGap182.TypeIII
