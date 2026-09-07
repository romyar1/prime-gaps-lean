import TypeIIIExactFunctorResolution
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Cycles in an actual exact augmented cochain complex

The cycles of an exact nonnegative cochain complex give actual short exact
sequences. A specified monomorphic, exact augmentation identifies its source
with the degree-zero cycles, compatibly with the original cochain maps.
These constructions retain the given differentials and augmentation; no
injectivity of the terms is needed for the cycle sequences.
-/

noncomputable section

universe v u v' u'

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The actual cycle inclusion and the original differential with codomain
restricted to the cycles in the following degree. -/
def cochainCyclesSequence (K : CochainComplex C ℕ) (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1)) (by
    rw [← cancel_mono (K.iCycles (n + 1)), assoc, HomologicalComplex.toCycles_i,
      HomologicalComplex.iCycles_d, zero_comp])

set_option backward.isDefEq.respectTransparency false in
/-- This sequence is always exact at the original term of the complex. -/
theorem cochainCyclesSequence_exact (K : CochainComplex C ℕ) (n : ℕ) :
    (cochainCyclesSequence K n).Exact := by
  let T := ShortComplex.mk (K.iCycles n) (K.d n (n + 1)) (K.iCycles_d n (n + 1))
  let φ : cochainCyclesSequence K n ⟶ T :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := K.iCycles (n + 1)
      comm₁₂ := by
        change 𝟙 _ ≫ K.iCycles n = K.iCycles n ≫ 𝟙 _
        simp only [id_comp, comp_id]
      comm₂₃ := by
        change 𝟙 _ ≫ K.d n (n + 1) = K.toCycles n (n + 1) ≫ K.iCycles (n + 1)
        rw [id_comp, HomologicalComplex.toCycles_i] }
  let : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 (K.cycles n)))
  let : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (K.X n)))
  let : Mono φ.τ₃ := inferInstanceAs (Mono (K.iCycles (n + 1)))
  apply (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
  exact ShortComplex.exact_of_f_is_kernel T (K.cyclesIsKernel n (n + 1) (by simp))

set_option backward.isDefEq.respectTransparency false in
/-- Exactness in the following degree makes the original differential onto
those cycles. -/
theorem cochainCyclesSequence_epi (K : CochainComplex C ℕ) (n : ℕ)
    (h : K.ExactAt (n + 1)) : Epi (cochainCyclesSequence K n).g := by
  change Epi (K.toCycles n (n + 1))
  exact Preadditive.epi_of_isZero_cokernel' _ (K.homologyIsCokernel n (n + 1) (by simp))
    ((HomologicalComplex.exactAt_iff_isZero_homology K (n + 1)).1 h)

set_option backward.isDefEq.respectTransparency false in
/-- The cycle sequence is short exact when the following homology vanishes. -/
theorem cochainCyclesSequence_shortExact (K : CochainComplex C ℕ) (n : ℕ)
    (h : K.ExactAt (n + 1)) : (cochainCyclesSequence K n).ShortExact where
  exact := cochainCyclesSequence_exact K n
  mono_f := inferInstanceAs (Mono (K.iCycles n))
  epi_g := cochainCyclesSequence_epi K n h

set_option backward.isDefEq.respectTransparency false in
/-- A cochain map gives a morphism of these same cycle sequences. -/
def cochainCyclesSequenceMap {K L : CochainComplex C ℕ} (φ : K ⟶ L) (n : ℕ) :
    cochainCyclesSequence K n ⟶ cochainCyclesSequence L n where
  τ₁ := HomologicalComplex.cyclesMap φ n
  τ₂ := φ.f n
  τ₃ := HomologicalComplex.cyclesMap φ (n + 1)
  comm₁₂ := HomologicalComplex.cyclesMap_i φ n
  comm₂₃ := by
    change φ.f n ≫ L.toCycles n (n + 1) =
      K.toCycles n (n + 1) ≫ HomologicalComplex.cyclesMap φ (n + 1)
    rw [← cancel_mono (L.iCycles (n + 1))]
    simp only [assoc, HomologicalComplex.toCycles_i, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.Hom.comm]
    rw [← assoc, HomologicalComplex.toCycles_i]

/-- A specified exact monomorphic augmentation identifies its actual source
with the actual cycles in degree zero. -/
def cochainAugmentationCyclesIso (K : CochainComplex C ℕ) {A : C}
    (a : A ⟶ K.X 0) [Mono a] (ha : a ≫ K.d 0 1 = 0)
    (he : (ShortComplex.mk a (K.d 0 1) ha).Exact) : A ≅ K.cycles 0 := by
  let hnext : (ComplexShape.up ℕ).next 0 = 1 := by simp
  let : IsIso (K.liftCycles a 1 hnext ha) :=
    (CochainComplex.isIso_liftCycles_iff K a ha).2 ⟨he, inferInstance⟩
  exact asIso (K.liftCycles a 1 hnext ha)

set_option backward.isDefEq.respectTransparency false in
/-- Composing the isomorphism with the cycle inclusion recovers the supplied
original augmentation. -/
theorem cochainAugmentationCyclesIso_hom_i (K : CochainComplex C ℕ) {A : C}
    (a : A ⟶ K.X 0) [Mono a] (ha : a ≫ K.d 0 1 = 0)
    (he : (ShortComplex.mk a (K.d 0 1) ha).Exact) :
    (cochainAugmentationCyclesIso K a ha he).hom ≫ K.iCycles 0 = a := by
  let hnext : (ComplexShape.up ℕ).next 0 = 1 := by simp
  change K.liftCycles a 1 hnext ha ≫ K.iCycles 0 = a
  exact K.liftCycles_i a 1 hnext ha

set_option backward.isDefEq.respectTransparency false in
/-- The comparison of degree-zero cycles commutes with any original map
of the specified augmentations. -/
theorem cochainAugmentationCyclesIso_naturality {K L : CochainComplex C ℕ}
    {A B : C} (a : A ⟶ K.X 0) (b : B ⟶ L.X 0) [Mono a] [Mono b]
    (ha : a ≫ K.d 0 1 = 0) (hb : b ≫ L.d 0 1 = 0)
    (hea : (ShortComplex.mk a (K.d 0 1) ha).Exact)
    (heb : (ShortComplex.mk b (L.d 0 1) hb).Exact)
    (φ : K ⟶ L) (f : A ⟶ B) (h : a ≫ φ.f 0 = f ≫ b) :
    (cochainAugmentationCyclesIso K a ha hea).hom ≫ HomologicalComplex.cyclesMap φ 0 =
      f ≫ (cochainAugmentationCyclesIso L b hb heb).hom := by
  apply (cancel_mono (L.iCycles 0)).1
  calc
    _ = (cochainAugmentationCyclesIso K a ha hea).hom ≫ K.iCycles 0 ≫ φ.f 0 := by
      rw [assoc, HomologicalComplex.cyclesMap_i]
    _ = a ≫ φ.f 0 := by rw [← assoc, cochainAugmentationCyclesIso_hom_i]
    _ = f ≫ b := h
    _ = _ := by rw [assoc, cochainAugmentationCyclesIso_hom_i]

section ExactFunctor

variable {D : Type u'} [Category.{v'} D] [Abelian D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {A : C}

/-- The actual complex obtained by applying an exact functor to the specified
injective resolution is exact at every positive degree. -/
theorem exactFunctorResolution_exactAt_succ (I : InjectiveResolution A) (n : ℕ) :
    (exactFunctorResolutionComplex G I).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  exact exactFunctorResolution_exact_succ G I n

/-- Actual cycles of the mapped resolution give short exact sequences,
without assuming that the mapped terms are injective. -/
theorem exactFunctorResolution_cycles_shortExact (I : InjectiveResolution A) (n : ℕ) :
    (cochainCyclesSequence (exactFunctorResolutionComplex G I) n).ShortExact :=
  cochainCyclesSequence_shortExact _ n (exactFunctorResolution_exactAt_succ G I n)

/-- The original mapped augmentation gives the degree-zero cycles isomorphism. -/
def exactFunctorResolution_cyclesZeroIso (I : InjectiveResolution A) :
    G.obj A ≅ (exactFunctorResolutionComplex G I).cycles 0 :=
  cochainAugmentationCyclesIso _ (exactFunctorResolutionAugmentation G I)
    (exactFunctorResolutionAugmentation_d G I) (exactFunctorResolution_exact_zero G I)

end ExactFunctor

#print axioms cochainCyclesSequence
#print axioms cochainCyclesSequence_exact
#print axioms cochainCyclesSequence_epi
#print axioms cochainCyclesSequence_shortExact
#print axioms cochainCyclesSequenceMap
#print axioms cochainAugmentationCyclesIso
#print axioms cochainAugmentationCyclesIso_hom_i
#print axioms cochainAugmentationCyclesIso_naturality
#print axioms exactFunctorResolution_exactAt_succ
#print axioms exactFunctorResolution_cycles_shortExact
#print axioms exactFunctorResolution_cyclesZeroIso

end PrimeGap182.TypeIII
