import TypeIIIExactResolutionComparison
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Exact functors and actual injective resolutions

An additive functor preserving finite limits and colimits sends an actual
injective resolution to an exact augmented complex.  Its terms are not
asserted to be injective.  The comparison for exact sources constructs an
actual chain map from this complex to the chosen injective resolution of
the image object.  Uniqueness up to homotopy proves naturality and gives
a natural transformation between the actual homotopy-category functors.

This is the resolution comparison used in a derived base-change map;
no base-change isomorphism is asserted here.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (G : C ⥤ D) [G.Additive]
  {A B : C}

/-- The literal image under the functor of the given injective-resolution complex. -/
abbrev exactFunctorResolutionComplex (I : InjectiveResolution A) : CochainComplex D ℕ :=
  (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual mapped augmentation in degree zero. -/
abbrev exactFunctorResolutionAugmentation (I : InjectiveResolution A) :
    G.obj A ⟶ (exactFunctorResolutionComplex G I).X 0 :=
  G.map (I.ι.f 0)

set_option backward.isDefEq.respectTransparency false in
/-- The mapped augmentation is monomorphic because the functor preserves finite limits. -/
instance exactFunctorResolutionAugmentation_mono [PreservesFiniteLimits G]
    (I : InjectiveResolution A) :
    Mono (exactFunctorResolutionAugmentation G I) := by
  exact G.map_mono (I.ι.f 0)

set_option backward.isDefEq.respectTransparency false in
/-- The mapped augmentation is killed by the first mapped differential. -/
theorem exactFunctorResolutionAugmentation_d (I : InjectiveResolution A) :
    exactFunctorResolutionAugmentation G I ≫
      (exactFunctorResolutionComplex G I).d 0 1 = 0 := by
  change G.map (I.ι.f 0) ≫ G.map (I.cocomplex.d 0 1) = 0
  rw [← G.map_comp, I.ι_f_zero_comp_complex_d, G.map_zero]

variable [PreservesFiniteLimits G] [PreservesFiniteColimits G]

set_option backward.isDefEq.respectTransparency false in
/-- Exactness at degree zero follows by applying the exact functor to the actual resolution. -/
theorem exactFunctorResolution_exact_zero (I : InjectiveResolution A) :
    (ShortComplex.mk (exactFunctorResolutionAugmentation G I)
      ((exactFunctorResolutionComplex G I).d 0 1)
      (exactFunctorResolutionAugmentation_d G I)).Exact :=
  I.exact₀.map G

/-- Exactness at every positive degree is inherited from the actual resolution. -/
theorem exactFunctorResolution_exact_succ (I : InjectiveResolution A) (n : ℕ) :
    (ShortComplex.mk ((exactFunctorResolutionComplex G I).d n (n + 1))
      ((exactFunctorResolutionComplex G I).d (n + 1) (n + 2))
      ((exactFunctorResolutionComplex G I).d_comp_d n (n + 1) (n + 2))).Exact :=
  (I.exact_succ n).map G

variable [HasInjectiveResolutions D]

/-- The actual comparison to the chosen injective resolution of the image object. -/
def exactFunctorResolutionComparison (I : InjectiveResolution A) :
    exactFunctorResolutionComplex G I ⟶ (injectiveResolution (G.obj A)).cocomplex :=
  exactResolutionComparison (exactFunctorResolutionComplex G I)
    (exactFunctorResolutionAugmentation G I) (exactFunctorResolutionAugmentation_d G I)
    (exactFunctorResolution_exact_zero G I) (exactFunctorResolution_exact_succ G I)
    (𝟙 (G.obj A)) (injectiveResolution (G.obj A))

set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison extends the identity of the actual image object. -/
@[reassoc (attr := simp)]
theorem exactFunctorResolutionComparison_commutes (I : InjectiveResolution A) :
    exactFunctorResolutionAugmentation G I ≫ (exactFunctorResolutionComparison G I).f 0 =
      (injectiveResolution (G.obj A)).ι.f 0 := by
  simpa only [id_comp, exactFunctorResolutionComparison] using exactResolutionComparison_commutes
    (exactFunctorResolutionComplex G I) (exactFunctorResolutionAugmentation G I)
    (exactFunctorResolutionAugmentation_d G I) (exactFunctorResolution_exact_zero G I)
    (exactFunctorResolution_exact_succ G I) (𝟙 (G.obj A))
    (injectiveResolution (G.obj A))

omit [PreservesFiniteLimits G] [PreservesFiniteColimits G] [HasInjectiveResolutions D] in
set_option backward.isDefEq.respectTransparency false in
/-- Mapping a genuine resolution morphism maps its augmentation square. -/
@[reassoc]
theorem exactFunctorResolutionAugmentation_naturality
    (I : InjectiveResolution A) (I' : InjectiveResolution B) (f : A ⟶ B)
    (φ : I.cocomplex ⟶ I'.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ I'.ι.f 0) :
    exactFunctorResolutionAugmentation G I ≫
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map φ).f 0 =
      G.map f ≫ exactFunctorResolutionAugmentation G I' := by
  change G.map (I.ι.f 0 : A ⟶ I.cocomplex.X 0) ≫ G.map (φ.f 0) =
    G.map f ≫ G.map (I'.ι.f 0 : B ⟶ I'.cocomplex.X 0)
  simpa only [Functor.map_comp] using
    congrArg (fun (u : A ⟶ I'.cocomplex.X 0) => G.map u) hφ

set_option backward.isDefEq.respectTransparency false in
/-- The actual comparisons are natural up to homotopy.  No mapped source term
is assumed injective. -/
def exactFunctorResolutionComparisonHomotopy
    (I : InjectiveResolution A) (I' : InjectiveResolution B) (f : A ⟶ B)
    (φ : I.cocomplex ⟶ I'.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ I'.ι.f 0) :
    Homotopy
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map φ ≫
        exactFunctorResolutionComparison G I')
      (exactFunctorResolutionComparison G I ≫
        InjectiveResolution.desc (G.map f) (injectiveResolution (G.obj B))
          (injectiveResolution (G.obj A))) :=
  exactResolutionComparisonHomotopy (exactFunctorResolutionComplex G I)
    (exactFunctorResolutionAugmentation G I) (exactFunctorResolutionAugmentation_d G I)
    (exactFunctorResolution_exact_zero G I) (exactFunctorResolution_exact_succ G I)
    (G.map f) (injectiveResolution (G.obj B)) _ _
    (by
      change exactFunctorResolutionAugmentation G I ≫
          (((G.mapHomologicalComplex (ComplexShape.up ℕ)).map φ).f 0 ≫
            (exactFunctorResolutionComparison G I').f 0) = _
      rw [← assoc, exactFunctorResolutionAugmentation_naturality G I I' f φ hφ,
        assoc, exactFunctorResolutionComparison_commutes])
    (by
      change exactFunctorResolutionAugmentation G I ≫
          ((exactFunctorResolutionComparison G I).f 0 ≫
            (InjectiveResolution.desc (G.map f) (injectiveResolution (G.obj B))
              (injectiveResolution (G.obj A))).f 0) = _
      rw [← assoc, exactFunctorResolutionComparison_commutes,
        InjectiveResolution.desc_commutes_zero])

variable [HasInjectiveResolutions C]

set_option backward.isDefEq.respectTransparency false in
/-- The chosen chain comparisons form a natural transformation in the actual
homotopy categories. -/
def exactFunctorResolutionNatTrans :
    injectiveResolutions C ⋙ G.mapHomotopyCategory (ComplexShape.up ℕ) ⟶
      G ⋙ injectiveResolutions D where
  app A := (HomotopyCategory.quotient D (ComplexShape.up ℕ)).map
    (exactFunctorResolutionComparison G (injectiveResolution A))
  naturality {A B} f := by
    change (HomotopyCategory.quotient D (ComplexShape.up ℕ)).map
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc f (injectiveResolution B) (injectiveResolution A))) ≫
        (HomotopyCategory.quotient D (ComplexShape.up ℕ)).map
          (exactFunctorResolutionComparison G (injectiveResolution B)) =
      (HomotopyCategory.quotient D (ComplexShape.up ℕ)).map
          (exactFunctorResolutionComparison G (injectiveResolution A)) ≫
        (HomotopyCategory.quotient D (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc (G.map f) (injectiveResolution (G.obj B))
            (injectiveResolution (G.obj A)))
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact HomotopyCategory.eq_of_homotopy _ _
      (exactFunctorResolutionComparisonHomotopy G (injectiveResolution A)
        (injectiveResolution B) f
        (InjectiveResolution.desc f (injectiveResolution B) (injectiveResolution A))
        (InjectiveResolution.desc_commutes_zero _ _ _))

/-- The natural transformation uses the actual comparison chain map at each object. -/
theorem exactFunctorResolutionNatTrans_app (A : C) :
    (exactFunctorResolutionNatTrans G).app A =
      (HomotopyCategory.quotient D (ComplexShape.up ℕ)).map
        (exactFunctorResolutionComparison G (injectiveResolution A)) := rfl

#print axioms exactFunctorResolutionComplex
#print axioms exactFunctorResolutionAugmentation
#print axioms exactFunctorResolutionAugmentation_mono
#print axioms exactFunctorResolutionAugmentation_d
#print axioms exactFunctorResolution_exact_zero
#print axioms exactFunctorResolution_exact_succ
#print axioms exactFunctorResolutionComparison
#print axioms exactFunctorResolutionComparison_commutes
#print axioms exactFunctorResolutionAugmentation_naturality
#print axioms exactFunctorResolutionComparisonHomotopy
#print axioms exactFunctorResolutionNatTrans
#print axioms exactFunctorResolutionNatTrans_app

end PrimeGap182.TypeIII
