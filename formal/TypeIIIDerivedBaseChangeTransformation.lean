import TypeIIIDerivedBaseChangeZero
import TypeIIIExactFunctorResolutionTransformation

/-!
# Transformations of the original derived comparison squares

A commuting square between two ordinary functor comparisons induces
a commuting square between their original derived comparison maps.
The chain proof uses the actual ordinary square and the existing
homotopy for a transformation of exact-functor resolution comparisons.

The derived proof uses the original quotient-to-homology factorization
and the canonical homology comparison for an exact functor.  Neither
transformation is assumed invertible, and no preservation of injectives
or acyclicity condition is required.
-/

noncomputable section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

section RightDerivedMorphism

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) [F.Additive]

/-- The map of the original right derived functor is the homology of
the original chosen resolution descent, through the canonical factors. -/
theorem rightDerivedMap_homologyFactors (n : ℕ) {A B : C} (f : A ⟶ B) :
    (F.rightDerived n).map f ≫
        (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) n).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution B).cocomplex) =
      (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) n).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution A).cocomplex) ≫
        (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
            (InjectiveResolution.desc f (injectiveResolution B) (injectiveResolution A))) := by
  exact (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) n).hom.naturality
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
      (InjectiveResolution.desc f (injectiveResolution B) (injectiveResolution A)))

end RightDerivedMorphism

section Transformation

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {C' : Type u₃} [Category.{v₃} C'] [Abelian C'] [HasInjectiveResolutions C']
  {D' : Type u₄} [Category.{v₄} D'] [Abelian D']
  (F : C ⥤ D) [F.Additive] (F' : C' ⥤ D') [F'.Additive]
  (G G' : C ⥤ C') [G.Additive] [G'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  (H H' : D ⥤ D') [H.Additive] [H'.Additive]
  (τ : G ⟶ G') (σ : H ⟶ H')
  (β : F ⋙ H ⟶ G ⋙ F') (β' : F ⋙ H' ⟶ G' ⋙ F')
  (h : β ≫ Functor.whiskerRight τ F' = Functor.whiskerLeft F σ ≫ β')

include h

/-- The ordinary square and the original resolution-transformation
homotopy give a homotopy of the literal derived comparison chain maps. -/
def derivedBaseChangeChainMapTransformationHomotopy {A : C}
    (I : InjectiveResolution A) :
    Homotopy
      ((σ.mapHomologicalComplex (ComplexShape.up ℕ)).app
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) ≫
        derivedBaseChangeChainMap F F' G' H' β' I)
      (derivedBaseChangeChainMap F F' G H β I ≫
        (F'.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc (τ.app A) (injectiveResolution (G'.obj A))
            (injectiveResolution (G.obj A)))) := by
  have hleft :
      (σ.mapHomologicalComplex (ComplexShape.up ℕ)).app
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) ≫
          derivedBaseChangeChainMap F F' G' H' β' I =
        (β.mapHomologicalComplex (ComplexShape.up ℕ)).app I.cocomplex ≫
          (F'.mapHomologicalComplex (ComplexShape.up ℕ)).map
            ((τ.mapHomologicalComplex (ComplexShape.up ℕ)).app I.cocomplex ≫
              exactFunctorResolutionComparison G' I) := by
    ext j
    have hj := NatTrans.congr_app h (I.cocomplex.X j)
    change β.app (I.cocomplex.X j) ≫ F'.map (τ.app (I.cocomplex.X j)) =
      σ.app (F.obj (I.cocomplex.X j)) ≫ β'.app (I.cocomplex.X j) at hj
    change σ.app (F.obj (I.cocomplex.X j)) ≫
        (β'.app (I.cocomplex.X j) ≫ F'.map ((exactFunctorResolutionComparison G' I).f j)) =
      β.app (I.cocomplex.X j) ≫
        F'.map (τ.app (I.cocomplex.X j) ≫ (exactFunctorResolutionComparison G' I).f j)
    simpa only [Functor.map_comp, assoc] using
      congrArg (fun f => f ≫ F'.map ((exactFunctorResolutionComparison G' I).f j)) hj.symm
  have hright :
      derivedBaseChangeChainMap F F' G H β I ≫
          (F'.mapHomologicalComplex (ComplexShape.up ℕ)).map
            (InjectiveResolution.desc (τ.app A) (injectiveResolution (G'.obj A))
              (injectiveResolution (G.obj A))) =
        (β.mapHomologicalComplex (ComplexShape.up ℕ)).app I.cocomplex ≫
          (F'.mapHomologicalComplex (ComplexShape.up ℕ)).map
            (exactFunctorResolutionComparison G I ≫
              InjectiveResolution.desc (τ.app A) (injectiveResolution (G'.obj A))
                (injectiveResolution (G.obj A))) := by
    simp only [derivedBaseChangeChainMap, Functor.map_comp, assoc]
  rw [hleft, hright]
  exact (F'.mapHomotopy
    (exactFunctorResolutionComparisonTransformationHomotopy G G' τ I)).compLeft
      ((β.mapHomologicalComplex (ComplexShape.up ℕ)).app I.cocomplex)

/-- The same two chain maps induce the same maps on actual homology. -/
theorem derivedBaseChangeChainMap_transformation_homology {A : C}
    (I : InjectiveResolution A) (n : ℕ) :
    (HomologicalComplex.homologyFunctor D' (ComplexShape.up ℕ) n).map
        ((σ.mapHomologicalComplex (ComplexShape.up ℕ)).app
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)) ≫
        (HomologicalComplex.homologyFunctor D' (ComplexShape.up ℕ) n).map
          (derivedBaseChangeChainMap F F' G' H' β' I) =
      (HomologicalComplex.homologyFunctor D' (ComplexShape.up ℕ) n).map
          (derivedBaseChangeChainMap F F' G H β I) ≫
        (HomologicalComplex.homologyFunctor D' (ComplexShape.up ℕ) n).map
          ((F'.mapHomologicalComplex (ComplexShape.up ℕ)).map
            (InjectiveResolution.desc (τ.app A) (injectiveResolution (G'.obj A))
              (injectiveResolution (G.obj A)))) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact (derivedBaseChangeChainMapTransformationHomotopy F F' G G' H H' τ σ β β' h I).homologyMap_eq n

variable [HasInjectiveResolutions C]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits H'] [PreservesFiniteColimits H']

/-- Each component of the original derived comparison respects the
given ordinary square, using the original right derived map of τ. -/
theorem derivedBaseChangeMap_transformation_app (n : ℕ) (A : C) :
    (derivedBaseChangeMap F F' G H β n).app A ≫ (F'.rightDerived n).map (τ.app A) =
      σ.app ((F.rightDerived n).obj A) ≫ (derivedBaseChangeMap F F' G' H' β' n).app A := by
  let I := injectiveResolution A
  let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let L := (F'.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (injectiveResolution (G.obj A)).cocomplex
  let L' := (F'.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (injectiveResolution (G'.obj A)).cocomplex
  let a := (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) n).hom.app K
  let b := (HomotopyCategory.homologyFunctorFactors D' (ComplexShape.up ℕ) n).hom.app L
  let b' := (HomotopyCategory.homologyFunctorFactors D' (ComplexShape.up ℕ) n).hom.app L'
  let c := (exactFunctorHomologyIso H (ComplexShape.up ℕ) n).inv.app K
  let c' := (exactFunctorHomologyIso H' (ComplexShape.up ℕ) n).inv.app K
  let T := (F'.mapHomologicalComplex (ComplexShape.up ℕ)).map
    (InjectiveResolution.desc (τ.app A) (injectiveResolution (G'.obj A))
      (injectiveResolution (G.obj A)))
  let s := (σ.mapHomologicalComplex (ComplexShape.up ℕ)).app K
  let B := derivedBaseChangeChainMap F F' G H β I
  let B' := derivedBaseChangeChainMap F F' G' H' β' I
  let hom := HomologicalComplex.homologyFunctor D' (ComplexShape.up ℕ) n
  have hmap : (F'.rightDerived n).map (τ.app A) ≫ b' = b ≫ hom.map T :=
    rightDerivedMap_homologyFactors F' n (τ.app A)
  have hβ : (derivedBaseChangeMap F F' G H β n).app A ≫ b =
      H.map a ≫ c ≫ hom.map B := derivedBaseChangeMap_factors F F' G H β n A
  have hβ' : (derivedBaseChangeMap F F' G' H' β' n).app A ≫ b' =
      H'.map a ≫ c' ≫ hom.map B' := derivedBaseChangeMap_factors F F' G' H' β' n A
  have hchain : hom.map s ≫ hom.map B' = hom.map B ≫ hom.map T :=
    derivedBaseChangeChainMap_transformation_homology F F' G G' H H' τ σ β β' h I n
  have hhom : c ≫ hom.map s = σ.app (K.homology n) ≫ c' := by
    change ((K.sc n).mapHomologyIso H).inv ≫
        ShortComplex.homologyMap ((K.sc n).mapNatTrans σ) =
      σ.app (K.sc n).homology ≫ ((K.sc n).mapHomologyIso H').inv
    rw [ShortComplex.homologyMap_mapNatTrans]
    simp only [Iso.inv_hom_id_assoc]
  have hσ : H.map a ≫ σ.app (K.homology n) =
      σ.app ((F.rightDerived n).obj A) ≫ H'.map a := σ.naturality a
  apply (cancel_mono b').mp
  calc
    ((derivedBaseChangeMap F F' G H β n).app A ≫
        (F'.rightDerived n).map (τ.app A)) ≫ b' =
      (derivedBaseChangeMap F F' G H β n).app A ≫
        ((F'.rightDerived n).map (τ.app A) ≫ b') := assoc _ _ _
    _ = (derivedBaseChangeMap F F' G H β n).app A ≫ (b ≫ hom.map T) := by rw [hmap]
    _ = ((derivedBaseChangeMap F F' G H β n).app A ≫ b) ≫ hom.map T :=
      (assoc _ _ _).symm
    _ = (H.map a ≫ c ≫ hom.map B) ≫ hom.map T := by rw [hβ]
    _ = H.map a ≫ c ≫ (hom.map B ≫ hom.map T) := by simp only [assoc]
    _ = H.map a ≫ c ≫ (hom.map s ≫ hom.map B') := by rw [← hchain]
    _ = H.map a ≫ (c ≫ hom.map s) ≫ hom.map B' := by simp only [assoc]
    _ = H.map a ≫ (σ.app (K.homology n) ≫ c') ≫ hom.map B' := by rw [hhom]
    _ = (H.map a ≫ σ.app (K.homology n)) ≫ c' ≫ hom.map B' := by simp only [assoc]
    _ = (σ.app ((F.rightDerived n).obj A) ≫ H'.map a) ≫ c' ≫ hom.map B' := by rw [hσ]
    _ = σ.app ((F.rightDerived n).obj A) ≫ (H'.map a ≫ c' ≫ hom.map B') := by
      simp only [assoc]
    _ = σ.app ((F.rightDerived n).obj A) ≫
        ((derivedBaseChangeMap F F' G' H' β' n).app A ≫ b') := by rw [← hβ']
    _ = (σ.app ((F.rightDerived n).obj A) ≫
        (derivedBaseChangeMap F F' G' H' β' n).app A) ≫ b' := (assoc _ _ _).symm

/-- The original derived maps form a commuting square for the two
ordinary transformations, in every degree. -/
theorem derivedBaseChangeMap_transformation (n : ℕ) :
    derivedBaseChangeMap F F' G H β n ≫ Functor.whiskerRight τ (F'.rightDerived n) =
      Functor.whiskerLeft (F.rightDerived n) σ ≫ derivedBaseChangeMap F F' G' H' β' n := by
  apply NatTrans.ext
  funext A
  exact derivedBaseChangeMap_transformation_app F F' G G' H H' τ σ β β' h n A

end Transformation

#print axioms rightDerivedMap_homologyFactors
#print axioms derivedBaseChangeChainMapTransformationHomotopy
#print axioms derivedBaseChangeChainMap_transformation_homology
#print axioms derivedBaseChangeMap_transformation_app
#print axioms derivedBaseChangeMap_transformation

end PrimeGap182.TypeIII
