import TypeIIIExactFunctorResolution
import TypeIIIInjectiveResolutionAdditivity

/-!
# Derived comparison from an ordinary square of functors

For additive functors `F`, `F'`, an exact functor `G`, a homology-preserving
additive functor `H`, and an actual transformation `F ⋙ H ⟶ G ⋙ F'`, this
module constructs the transformation `F.rightDerived n ⋙ H ⟶
G ⋙ F'.rightDerived n`.

The construction uses the actual injective resolutions, the proved
comparison from the exact mapped resolution, and the canonical homology
comparison.  It does not assume that `G` preserves injectives, that the
mapped terms are `F'`-acyclic, or that the resulting morphism is invertible.
-/

noncomputable section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ w

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

section Homology

variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {D' : Type u₄} [Category.{v₄} D'] [Abelian D']
  (H : D ⥤ D') [H.Additive] [H.PreservesHomology]
  {ι : Type w} (c : ComplexShape ι) (n : ι)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical homology comparison on the literal mapped complexes. -/
def exactFunctorHomologyIso :
    H.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor D' c n ≅
      HomologicalComplex.homologyFunctor D c n ⋙ H :=
  NatIso.ofComponents (fun K => (K.sc n).mapHomologyIso H)
    (fun φ => ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor D c n).map φ) H)

/-- Its component is the existing homology isomorphism for the actual short complex. -/
theorem exactFunctorHomologyIso_app (K : HomologicalComplex D c) :
    (exactFunctorHomologyIso H c n).app K = (K.sc n).mapHomologyIso H := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The same canonical comparison descends to the actual homotopy categories. -/
def exactFunctorHomotopyHomologyIso :
    H.mapHomotopyCategory c ⋙ HomotopyCategory.homologyFunctor D' c n ≅
      HomotopyCategory.homologyFunctor D c n ⋙ H :=
  Quotient.natIsoLift _
    (Functor.isoWhiskerRight (H.mapHomotopyCategoryFactors c)
        (HomotopyCategory.homologyFunctor D' c n) ≪≫
      Functor.isoWhiskerLeft (H.mapHomologicalComplex c)
        (HomotopyCategory.homologyFunctorFactors D' c n) ≪≫
      exactFunctorHomologyIso H c n ≪≫
      Functor.isoWhiskerRight (HomotopyCategory.homologyFunctorFactors D c n).symm H)

end Homology

section Derived

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {C' : Type u₃} [Category.{v₃} C'] [Abelian C'] [HasInjectiveResolutions C']
  {D' : Type u₄} [Category.{v₄} D'] [Abelian D']
  (F : C ⥤ D) [F.Additive] (F' : C' ⥤ D') [F'.Additive]
  (G : C ⥤ C') [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (H : D ⥤ D') [H.Additive] (β : F ⋙ H ⟶ G ⋙ F')

set_option backward.isDefEq.respectTransparency false in
/-- The literal chain map: apply the ordinary square in every degree and
then apply `F'` to the proved comparison of resolutions. -/
def derivedBaseChangeChainMap {A : C} (I : InjectiveResolution A) :
    (H.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) ⟶
      (F'.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (G.obj A)).cocomplex :=
  (β.mapHomologicalComplex (ComplexShape.up ℕ)).app I.cocomplex ≫
    (F'.mapHomologicalComplex (ComplexShape.up ℕ)).map (exactFunctorResolutionComparison G I)

omit [HasInjectiveResolutions C] in
/-- In each degree the chain map is the ordinary component followed by the
actual mapped resolution comparison. -/
theorem derivedBaseChangeChainMap_f {A : C} (I : InjectiveResolution A) (n : ℕ) :
    (derivedBaseChangeChainMap F F' G H β I).f n =
      β.app (I.cocomplex.X n) ≫ F'.map ((exactFunctorResolutionComparison G I).f n) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual ordinary square followed by the proved resolution comparison,
as a natural transformation with values in the homotopy category. -/
def derivedBaseChangeResolutionMap :
    F.rightDerivedToHomotopyCategory ⋙ H.mapHomotopyCategory (ComplexShape.up ℕ) ⟶
      G ⋙ F'.rightDerivedToHomotopyCategory :=
  Functor.whiskerLeft (injectiveResolutions C)
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ H)) (ComplexShape.up ℕ)).hom ≫
    Functor.whiskerLeft (injectiveResolutions C) (β.mapHomotopyCategory (ComplexShape.up ℕ)) ≫
    Functor.whiskerLeft (injectiveResolutions C)
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ F')) (ComplexShape.up ℕ)).inv ≫
    Functor.whiskerRight (exactFunctorResolutionNatTrans G)
      (F'.mapHomotopyCategory (ComplexShape.up ℕ))

set_option backward.isDefEq.respectTransparency false in
/-- The homotopy-category component is represented by the literal chain map. -/
theorem derivedBaseChangeResolutionMap_app (A : C) :
    (derivedBaseChangeResolutionMap F F' G H β).app A =
      (HomotopyCategory.quotient D' (ComplexShape.up ℕ)).map
        (derivedBaseChangeChainMap F F' G H β (injectiveResolution A)) := by
  change
    (HomotopyCategory.quotient D' (ComplexShape.up ℕ)).map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ H))
            (ComplexShape.up ℕ)).hom.app (injectiveResolution A).cocomplex) ≫
        (HomotopyCategory.quotient D' (ComplexShape.up ℕ)).map
          ((β.mapHomologicalComplex (ComplexShape.up ℕ)).app
            (injectiveResolution A).cocomplex) ≫
        (HomotopyCategory.quotient D' (ComplexShape.up ℕ)).map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ F'))
            (ComplexShape.up ℕ)).inv.app (injectiveResolution A).cocomplex) ≫
      (HomotopyCategory.quotient D' (ComplexShape.up ℕ)).map
        ((F'.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (exactFunctorResolutionComparison G (injectiveResolution A))) = _
  simp only [← Functor.map_comp]
  apply (HomotopyCategory.quotient D' (ComplexShape.up ℕ)).congr_map
  ext n
  simp [derivedBaseChangeChainMap, Functor.mapHomologicalComplexCompIso,
    NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex]

variable [H.PreservesHomology]

set_option backward.isDefEq.respectTransparency false in
/-- The genuine derived comparison induced by the actual ordinary transformation.
It is a morphism, with no invertibility assertion. -/
def derivedBaseChangeMap (n : ℕ) :
    F.rightDerived n ⋙ H ⟶ G ⋙ F'.rightDerived n :=
  Functor.whiskerLeft F.rightDerivedToHomotopyCategory
      (exactFunctorHomotopyHomologyIso H (ComplexShape.up ℕ) n).inv ≫
    Functor.whiskerRight (derivedBaseChangeResolutionMap F F' G H β)
      (HomotopyCategory.homologyFunctor D' (ComplexShape.up ℕ) n)

/-- The component uses canonical homology transport and the actual resolution morphism. -/
theorem derivedBaseChangeMap_app (n : ℕ) (A : C) :
    (derivedBaseChangeMap F F' G H β n).app A =
      (exactFunctorHomotopyHomologyIso H (ComplexShape.up ℕ) n).inv.app
          (F.rightDerivedToHomotopyCategory.obj A) ≫
        (HomotopyCategory.homologyFunctor D' (ComplexShape.up ℕ) n).map
          ((derivedBaseChangeResolutionMap F F' G H β).app A) := rfl

end Derived

#print axioms exactFunctorHomologyIso
#print axioms exactFunctorHomologyIso_app
#print axioms exactFunctorHomotopyHomologyIso
#print axioms derivedBaseChangeChainMap
#print axioms derivedBaseChangeChainMap_f
#print axioms derivedBaseChangeResolutionMap
#print axioms derivedBaseChangeResolutionMap_app
#print axioms derivedBaseChangeMap
#print axioms derivedBaseChangeMap_app

end PrimeGap182.TypeIII
