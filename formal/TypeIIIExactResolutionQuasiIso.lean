import TypeIIIExactResolutionCycles
import Mathlib.Algebra.Homology.QuasiIso

/-!
# The original exact-resolution comparison is a quasi-isomorphism

A map of exact nonnegative augmented complexes that extends an isomorphism
of the original augmented objects is a quasi-isomorphism. Applied to the
existing exact-functor resolution comparison, this proves a property of
that same chain map without assuming that its source terms are injective.

An arbitrary left exact functor need not preserve this quasi-isomorphism.
The separate acyclic-resolution argument must justify that later step.
-/

noncomputable section

universe v u v' u' v'' u''

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

section Augmented

variable {K L : CochainComplex C ℕ} {A B : C}
  (a : A ⟶ K.X 0) (b : B ⟶ L.X 0) [Mono a] [Mono b]
  (ha : a ≫ K.d 0 1 = 0) (hb : b ≫ L.d 0 1 = 0)
  (hea : (ShortComplex.mk a (K.d 0 1) ha).Exact)
  (heb : (ShortComplex.mk b (L.d 0 1) hb).Exact)
  (φ : K ⟶ L) (f : A ⟶ B) (h : a ≫ φ.f 0 = f ≫ b)

include ha hb hea heb h

/-- The original map of zero-cycles is transported from the original
map of augmented objects through the proved augmentation isomorphisms. -/
theorem cochainCyclesMap_zero_eq :
    HomologicalComplex.cyclesMap φ 0 =
      (cochainAugmentationCyclesIso K a ha hea).inv ≫ f ≫
        (cochainAugmentationCyclesIso L b hb heb).hom := by
  apply (cancel_epi (cochainAugmentationCyclesIso K a ha hea).hom).1
  rw [Iso.hom_inv_id_assoc]
  exact cochainAugmentationCyclesIso_naturality a b ha hb hea heb φ f h

/-- An invertible map of augmented objects makes the actual map of
degree-zero cycles invertible. -/
theorem cochainCyclesMap_zero_isIso [IsIso f] :
    IsIso (HomologicalComplex.cyclesMap φ 0) := by
  rw [cochainCyclesMap_zero_eq a b ha hb hea heb φ f h]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Exact augmented complexes have the expected comparison theorem for
the original cochain map; it is a quasi-isomorphism, with no claim of a
homotopy equivalence. -/
theorem cochainMap_quasiIso_of_augmentedExact [IsIso f]
    (hK : ∀ n : ℕ, K.ExactAt (n + 1)) (hL : ∀ n : ℕ, L.ExactAt (n + 1)) :
    QuasiIso φ := by
  let : IsIso (HomologicalComplex.cyclesMap φ 0) :=
    cochainCyclesMap_zero_isIso a b ha hb hea heb φ f h
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
      rw [quasiIsoAt_iff_isIso_homologyMap]
      have hh : HomologicalComplex.homologyMap φ 0 =
          inv (K.homologyπ 0) ≫ HomologicalComplex.cyclesMap φ 0 ≫ L.homologyπ 0 := by
        apply (cancel_epi (K.homologyπ 0)).1
        rw [IsIso.hom_inv_id_assoc]
        exact HomologicalComplex.homologyπ_naturality φ 0
      rw [hh]
      infer_instance
  | succ n =>
      exact (quasiIsoAt_iff_exactAt φ (n + 1) (hK n)).2 (hL n)

end Augmented

section ExactFunctor

variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasInjectiveResolutions D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {A : C}

set_option backward.isDefEq.respectTransparency false in
/-- The existing comparison from the actual mapped resolution to the
chosen injective resolution is a quasi-isomorphism. No preservation of
injectives by the exact functor is assumed. -/
theorem exactFunctorResolutionComparison_quasiIso (I : InjectiveResolution A) :
    QuasiIso (exactFunctorResolutionComparison G I) := by
  apply cochainMap_quasiIso_of_augmentedExact
    (exactFunctorResolutionAugmentation G I) ((injectiveResolution (G.obj A)).ι.f 0)
    (exactFunctorResolutionAugmentation_d G I)
    (injectiveResolution (G.obj A)).ι_f_zero_comp_complex_d
    (exactFunctorResolution_exact_zero G I) (injectiveResolution (G.obj A)).exact₀
    (exactFunctorResolutionComparison G I) (𝟙 (G.obj A))
    (by simpa only [id_comp] using exactFunctorResolutionComparison_commutes G I)
    (exactFunctorResolution_exactAt_succ G I)
    (injectiveResolution (G.obj A)).cocomplex_exactAt_succ

/-- An exact target functor preserves the quasi-isomorphism of this
same comparison map. This exact case does not assert preservation by
an arbitrary left exact target functor. -/
theorem exactFunctorResolutionComparison_map_quasiIso
    {D' : Type u''} [Category.{v''} D'] [Abelian D']
    (F : D ⥤ D') [F.Additive] [F.PreservesHomology] (I : InjectiveResolution A) :
    QuasiIso
      ((F.mapHomologicalComplex (.up ℕ)).map (exactFunctorResolutionComparison G I)) := by
  let : QuasiIso (exactFunctorResolutionComparison G I) :=
    exactFunctorResolutionComparison_quasiIso G I
  infer_instance

end ExactFunctor

section ExactDerived

variable [HasInjectiveResolutions C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]

/-- An exact additive functor has zero higher right derived functors,
computed through the original chosen injective resolution. -/
theorem rightDerived_isZero_of_preservesHomology (n : ℕ) (A : C) :
    IsZero ((F.rightDerived (n + 1)).obj A) := by
  refine IsZero.of_iso ?_ ((injectiveResolution A).isoRightDerivedObj F (n + 1))
  erw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  exact ((injectiveResolution A).exact_succ n).map F

end ExactDerived

#print axioms cochainCyclesMap_zero_eq
#print axioms cochainCyclesMap_zero_isIso
#print axioms cochainMap_quasiIso_of_augmentedExact
#print axioms exactFunctorResolutionComparison_quasiIso
#print axioms exactFunctorResolutionComparison_map_quasiIso
#print axioms rightDerived_isZero_of_preservesHomology

end PrimeGap182.TypeIII
