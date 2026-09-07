import TypeIIIExactFunctorHomologyComposition
import TypeIIIExactFunctorResolutionComposition

/-!
# Pasting the original derived comparison squares

The ordinary pasted square has component H'(β_A) followed by β'_(GA).
For the original resolution comparisons, the resulting chain map is
homotopic to the two successive original chain maps.  This uses the
proved composition homotopy of exact mapped resolutions and ordinary
naturality of the second square.

All comparisons concern the original chosen injective resolutions and
the original maps.  Neither preservation of injectives nor acyclicity
of the mapped terms is assumed.
-/

noncomputable section

universe v₁ v₂ v₃ w₁ w₂ w₃ u₁ u₂ u₃ z₁ z₂ z₃

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C₁ : Type u₁} [Category.{v₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃]
  {D₁ : Type z₁} [Category.{w₁} D₁]
  {D₂ : Type z₂} [Category.{w₂} D₂]
  {D₃ : Type z₃} [Category.{w₃} D₃]
  (F : C₁ ⥤ D₁) (F' : C₂ ⥤ D₂) (F'' : C₃ ⥤ D₃)
  (G : C₁ ⥤ C₂) (G' : C₂ ⥤ C₃)
  (H : D₁ ⥤ D₂) (H' : D₂ ⥤ D₃)
  (β : F ⋙ H ⟶ G ⋙ F') (β' : F' ⋙ H' ⟶ G' ⋙ F'')

/-- The actual pasted ordinary square, with its literal component formula. -/
def derivedBaseChangeSquarePaste : F ⋙ (H ⋙ H') ⟶ (G ⋙ G') ⋙ F'' where
  app A := H'.map (β.app A) ≫ β'.app (G.obj A)
  naturality {A B} f := by
    change H'.map (H.map (F.map f)) ≫
        (H'.map (β.app B) ≫ β'.app (G.obj B)) =
      (H'.map (β.app A) ≫ β'.app (G.obj A)) ≫ F''.map (G'.map (G.map f))
    rw [← assoc, ← H'.map_comp]
    erw [β.naturality]
    rw [H'.map_comp, assoc]
    erw [β'.naturality (G.map f)]
    rw [assoc]
    rfl

/-- The pasted square uses exactly the two original ordinary components. -/
theorem derivedBaseChangeSquarePaste_app (A : C₁) :
    (derivedBaseChangeSquarePaste F F' F'' G G' H H' β β').app A =
      H'.map (β.app A) ≫ β'.app (G.obj A) := rfl

variable [Abelian C₁] [Abelian C₂] [Abelian C₃]
  [Abelian D₁] [Abelian D₂] [Abelian D₃]
  [HasInjectiveResolutions C₂] [HasInjectiveResolutions C₃]
  [F.Additive] [F'.Additive] [F''.Additive]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [G'.Additive] [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [H.Additive] [H'.Additive]

/-- Ordinary naturality identifies the literal two-stage chain map with
the pasted ordinary square followed by the two-stage resolution map. -/
theorem derivedBaseChangeChainMap_comp_stages {A : C₁} (I : InjectiveResolution A) :
    ((derivedBaseChangeSquarePaste F F' F'' G G' H H' β β').mapHomologicalComplex
        (ComplexShape.up ℕ)).app I.cocomplex ≫
        (F''.mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((G'.mapHomologicalComplex (ComplexShape.up ℕ)).map
              (exactFunctorResolutionComparison G I) ≫
            exactFunctorResolutionComparison G' (injectiveResolution (G.obj A))) =
      (H'.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (derivedBaseChangeChainMap F F' G H β I) ≫
        derivedBaseChangeChainMap F' F'' G' H' β' (injectiveResolution (G.obj A)) := by
  ext n
  change (H'.map (β.app (I.cocomplex.X n)) ≫ β'.app (G.obj (I.cocomplex.X n))) ≫
      F''.map (G'.map ((exactFunctorResolutionComparison G I).f n) ≫
        (exactFunctorResolutionComparison G' (injectiveResolution (G.obj A))).f n) =
    H'.map (β.app (I.cocomplex.X n) ≫ F'.map ((exactFunctorResolutionComparison G I).f n)) ≫
      (β'.app ((injectiveResolution (G.obj A)).cocomplex.X n) ≫
        F''.map ((exactFunctorResolutionComparison G' (injectiveResolution (G.obj A))).f n))
  rw [F''.map_comp, H'.map_comp]
  simp only [assoc]
  erw [← β'.naturality_assoc ((exactFunctorResolutionComparison G I).f n)]
  rfl

/-- The original chain map for the pasted square is homotopic to the
literal composite of the original chain maps for its two squares. -/
def derivedBaseChangeChainMapCompHomotopy {A : C₁} (I : InjectiveResolution A) :
    Homotopy
      (derivedBaseChangeChainMap F F'' (G ⋙ G') (H ⋙ H')
        (derivedBaseChangeSquarePaste F F' F'' G G' H H' β β') I)
      ((H'.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (derivedBaseChangeChainMap F F' G H β I) ≫
        derivedBaseChangeChainMap F' F'' G' H' β' (injectiveResolution (G.obj A))) := by
  have h := (F''.mapHomotopy (exactFunctorResolutionComparisonCompHomotopy G G' I)).compLeft
    (((derivedBaseChangeSquarePaste F F' F'' G G' H H' β β').mapHomologicalComplex
      (ComplexShape.up ℕ)).app I.cocomplex)
  rw [derivedBaseChangeChainMap_comp_stages] at h
  exact h

/-- The same original chain maps therefore induce the expected pasted
map on actual homology, in every degree. -/
theorem derivedBaseChangeChainMap_comp_homology {A : C₁} (I : InjectiveResolution A) (n : ℕ) :
    HomologicalComplex.homologyMap
        (derivedBaseChangeChainMap F F'' (G ⋙ G') (H ⋙ H')
          (derivedBaseChangeSquarePaste F F' F'' G G' H H' β β') I) n =
      HomologicalComplex.homologyMap
          ((H'.mapHomologicalComplex (ComplexShape.up ℕ)).map
            (derivedBaseChangeChainMap F F' G H β I)) n ≫
        HomologicalComplex.homologyMap
          (derivedBaseChangeChainMap F' F'' G' H' β' (injectiveResolution (G.obj A))) n := by
  rw [(derivedBaseChangeChainMapCompHomotopy F F' F'' G G' H H' β β' I).homologyMap_eq n,
    HomologicalComplex.homologyMap_comp]

variable [HasInjectiveResolutions C₁]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits H'] [PreservesFiniteColimits H']

/-- The original derived comparison for a pasted ordinary square is
the composite of the two original derived comparisons, in every degree. -/
theorem derivedBaseChangeMap_comp_app (n : ℕ) (A : C₁) :
    (derivedBaseChangeMap F F'' (G ⋙ G') (H ⋙ H')
      (derivedBaseChangeSquarePaste F F' F'' G G' H H' β β') n).app A =
      H'.map ((derivedBaseChangeMap F F' G H β n).app A) ≫
        (derivedBaseChangeMap F' F'' G' H' β' n).app (G.obj A) := by
  let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (injectiveResolution A).cocomplex
  let L := (F'.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (injectiveResolution (G.obj A)).cocomplex
  let B : (H.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶ L :=
    derivedBaseChangeChainMap F F' G H β (injectiveResolution A)
  have hnat :
      H'.map (HomologicalComplex.homologyMap B n) ≫
          (exactFunctorHomologyIso H' (ComplexShape.up ℕ) n).inv.app L =
        (exactFunctorHomologyIso H' (ComplexShape.up ℕ) n).inv.app
            ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ≫
          HomologicalComplex.homologyMap
            ((H'.mapHomologicalComplex (ComplexShape.up ℕ)).map B) n :=
    (exactFunctorHomologyIso H' (ComplexShape.up ℕ) n).inv.naturality B
  apply (cancel_mono ((HomotopyCategory.homologyFunctorFactors D₃ (ComplexShape.up ℕ) n).hom.app
    ((F''.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution (G'.obj (G.obj A))).cocomplex))).mp
  conv_rhs =>
    rw [assoc, derivedBaseChangeMap_factors F' F'' G' H' β',
      ← H'.map_comp_assoc, derivedBaseChangeMap_factors F F' G H β,
      H'.map_comp, H'.map_comp]
  rw [derivedBaseChangeMap_factors,
    exactFunctorHomologyIso_comp_inv_app]
  change H'.map (H.map ((HomotopyCategory.homologyFunctorFactors D₁
        (ComplexShape.up ℕ) n).hom.app K)) ≫
      (H'.map ((exactFunctorHomologyIso H (ComplexShape.up ℕ) n).inv.app K) ≫
        (exactFunctorHomologyIso H' (ComplexShape.up ℕ) n).inv.app
          ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)) ≫
      HomologicalComplex.homologyMap
        (derivedBaseChangeChainMap F F'' (G ⋙ G') (H ⋙ H')
          (derivedBaseChangeSquarePaste F F' F'' G G' H H' β β')
          (injectiveResolution A)) n = _
  rw [derivedBaseChangeChainMap_comp_homology]
  simp only [assoc]
  have hnat' := congrArg (fun f => f ≫ HomologicalComplex.homologyMap
    (derivedBaseChangeChainMap F' F'' G' H' β' (injectiveResolution (G.obj A))) n) hnat
  simp only [assoc] at hnat'
  erw [← hnat']
  rfl

/-- Equality of the original natural transformations, retaining the
literal ordinary and derived component formulas. -/
theorem derivedBaseChangeMap_comp (n : ℕ) :
    derivedBaseChangeMap F F'' (G ⋙ G') (H ⋙ H')
        (derivedBaseChangeSquarePaste F F' F'' G G' H H' β β') n =
      derivedBaseChangeSquarePaste (F.rightDerived n) (F'.rightDerived n)
        (F''.rightDerived n) G G' H H'
        (derivedBaseChangeMap F F' G H β n)
        (derivedBaseChangeMap F' F'' G' H' β' n) := by
  ext A
  exact derivedBaseChangeMap_comp_app F F' F'' G G' H H' β β' n A

#print axioms derivedBaseChangeSquarePaste
#print axioms derivedBaseChangeSquarePaste_app
#print axioms derivedBaseChangeChainMap_comp_stages
#print axioms derivedBaseChangeChainMapCompHomotopy
#print axioms derivedBaseChangeChainMap_comp_homology
#print axioms derivedBaseChangeMap_comp_app
#print axioms derivedBaseChangeMap_comp

end PrimeGap182.TypeIII
