import TypeIIILeftExactCochainHomology
import TypeIIIRightDerivedLongExact
import TypeIIIExactResolutionQuasiIso

/-!
# The actual comparison for a resolution by acyclic objects

For a left exact additive functor, an exact augmented nonnegative complex of
acyclic objects computes the ordinary right derived functors.  The proof here
retains the original comparison map.  The positive derived maps on cycles are
isomorphisms by induction using the actual connecting maps.  The degree-zero
part of the long exact sequence supplies the cokernels computing the homology
of the mapped complex.

The final result concerns the existing `exactFunctorResolutionComparison`.
It proves a quasi-isomorphism after applying the left exact functor.  It does
not assert a homotopy equivalence or acyclicity for any geometric restriction.
-/

noncomputable section

universe w₁ w₂ v₁ v₂ v₃ u₁ u₂ u₃

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

section AcyclicComplexes

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C]
  [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  (F : C ⥤ D) [F.Additive]
  {S : ShortComplex C} (hS : S.ShortExact)

/-- The actual degree-zero connecting map, preceded by the original map from
the functor to its zeroth right derived functor. -/
def leftExactConnectingHom : F.obj S.X₃ ⟶ (F.rightDerived 1).obj S.X₁ :=
  F.toRightDerivedZero.app S.X₃ ≫ rightDerivedConnectingHom F hS 0

set_option backward.isDefEq.respectTransparency false in
/-- The mapped original arrow is killed by the degree-zero connecting map. -/
theorem comp_leftExactConnectingHom : F.map S.g ≫ leftExactConnectingHom F hS = 0 := by
  rw [leftExactConnectingHom, ← assoc, F.toRightDerivedZero.naturality S.g, assoc,
    comp_rightDerivedConnectingHom, comp_zero]

variable [PreservesFiniteLimits F]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Left exactness identifies the initial part of the actual ordinary long exact
sequence with the original functor's maps. -/
theorem leftExactConnectingHom_exact :
    (ShortComplex.mk (F.map S.g) (leftExactConnectingHom F hS)
      (comp_leftExactConnectingHom F hS)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (rightDerivedLongExact_exact₃ F hS 0)
  refine ShortComplex.isoMk
    ((asIso F.toRightDerivedZero).app S.X₂).symm
    ((asIso F.toRightDerivedZero).app S.X₃).symm (Iso.refl _) ?_ ?_
  · exact ((asIso F.toRightDerivedZero).inv.naturality S.g).symm
  · change ((asIso F.toRightDerivedZero).app S.X₃).inv ≫ leftExactConnectingHom F hS =
      rightDerivedConnectingHom F hS 0 ≫ 𝟙 _
    rw [leftExactConnectingHom]
    change ((asIso F.toRightDerivedZero).app S.X₃).inv ≫
        ((asIso F.toRightDerivedZero).app S.X₃).hom ≫ rightDerivedConnectingHom F hS 0 = _
    rw [Iso.inv_hom_id_assoc, comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing of the first derived middle term makes this actual connecting map surjective. -/
theorem leftExactConnectingHom_epi (h : IsZero ((F.rightDerived 1).obj S.X₂)) :
    Epi (leftExactConnectingHom F hS) := by
  have : Epi (rightDerivedConnectingHom F hS 0) :=
    (rightDerivedLongExact_exact₁ F hS 0).epi_f_iff.mpr (h.eq_of_tgt _ _)
  dsimp only [leftExactConnectingHom]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The actual connecting map is a cokernel of the original mapped arrow when
the first derived middle term vanishes. -/
def leftExactConnectingHom_isCokernel (h : IsZero ((F.rightDerived 1).obj S.X₂)) :
    IsColimit (CokernelCofork.ofπ (leftExactConnectingHom F hS)
      (comp_leftExactConnectingHom F hS)) := by
  have : Epi (leftExactConnectingHom F hS) := leftExactConnectingHom_epi F hS h
  exact (leftExactConnectingHom_exact F hS).gIsCokernel

omit [PreservesFiniteLimits F] in
set_option backward.isDefEq.respectTransparency false in
/-- This degree-zero connecting map is natural for the original morphism of
short exact sequences. -/
theorem leftExactConnectingHom_naturality {S₁ S₂ : ShortComplex C}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) :
    F.map φ.τ₃ ≫ leftExactConnectingHom F h₂ =
      leftExactConnectingHom F h₁ ≫ (F.rightDerived 1).map φ.τ₁ := by
  rw [leftExactConnectingHom, ← assoc, F.toRightDerivedZero.naturality φ.τ₃, assoc,
    rightDerivedConnectingHom_naturality F h₁ h₂ φ 0]
  simp only [leftExactConnectingHom, assoc]

omit [PreservesFiniteLimits F] in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Positive derived maps on the actual cycles are isomorphisms.  The induction
uses only exactness, termwise acyclicity, and the original zero-cycle isomorphism. -/
theorem rightDerived_cyclesMap_isIso {K L : CochainComplex C ℕ} (φ : K ⟶ L)
    [IsIso (cyclesMap φ 0)]
    (hK : ∀ j : ℕ, K.ExactAt (j + 1)) (hL : ∀ j : ℕ, L.ExactAt (j + 1))
    (aK : ∀ j m : ℕ, IsZero ((F.rightDerived (m + 1)).obj (K.X j)))
    (aL : ∀ j m : ℕ, IsZero ((F.rightDerived (m + 1)).obj (L.X j)))
    (j m : ℕ) : IsIso ((F.rightDerived (m + 1)).map (cyclesMap φ j)) := by
  induction j generalizing m with
  | zero => infer_instance
  | succ j ih =>
      let h₁ := cochainCyclesSequence_shortExact K j (hK j)
      let h₂ := cochainCyclesSequence_shortExact L j (hL j)
      have : IsIso (rightDerivedConnectingHom F h₁ (m + 1)) :=
        rightDerivedConnectingHom_isIso_of_isZero_middle F h₁ (m + 1)
          (aK j m) (aK j (m + 1))
      have : IsIso (rightDerivedConnectingHom F h₂ (m + 1)) :=
        rightDerivedConnectingHom_isIso_of_isZero_middle F h₂ (m + 1)
          (aL j m) (aL j (m + 1))
      have : IsIso ((F.rightDerived ((m + 1) + 1)).map (cyclesMap φ j)) := ih (m + 1)
      have hn := rightDerivedConnectingHom_naturality F h₁ h₂
        (cochainCyclesSequenceMap φ j) (m + 1)
      change (F.rightDerived (m + 1)).map (cyclesMap φ (j + 1)) ≫
          rightDerivedConnectingHom F h₂ (m + 1) =
        rightDerivedConnectingHom F h₁ (m + 1) ≫
          (F.rightDerived ((m + 1) + 1)).map (cyclesMap φ j) at hn
      have : IsIso ((F.rightDerived (m + 1)).map (cyclesMap φ (j + 1)) ≫
          rightDerivedConnectingHom F h₂ (m + 1)) := by
        rw [hn]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (rightDerivedConnectingHom F h₂ (m + 1))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The literal mapped comparison of two exact complexes of acyclic objects is
a quasi-isomorphism when its original zero-cycle map is invertible. -/
theorem cochainMap_map_quasiIso_of_acyclic {K L : CochainComplex C ℕ} (φ : K ⟶ L)
    [IsIso (cyclesMap φ 0)]
    (hK : ∀ j : ℕ, K.ExactAt (j + 1)) (hL : ∀ j : ℕ, L.ExactAt (j + 1))
    (aK : ∀ j m : ℕ, IsZero ((F.rightDerived (m + 1)).obj (K.X j)))
    (aL : ∀ j m : ℕ, IsZero ((F.rightDerived (m + 1)).obj (L.X j))) :
    QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map φ) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero => exact leftExactCochain_quasiIsoAt_zero F φ
  | succ n =>
      let h₁ := cochainCyclesSequence_shortExact K n (hK n)
      let h₂ := cochainCyclesSequence_shortExact L n (hL n)
      have : IsIso ((F.rightDerived 1).map (cyclesMap φ n)) :=
        rightDerived_cyclesMap_isIso F φ hK hL aK aL n 0
      exact leftExactCochain_quasiIsoAt_succ_of_cokernel F φ n
        (leftExactConnectingHom F h₁) (comp_leftExactConnectingHom F h₁)
        (leftExactConnectingHom_isCokernel F h₁ (aK n 0))
        (leftExactConnectingHom F h₂) (comp_leftExactConnectingHom F h₂)
        (leftExactConnectingHom_isCokernel F h₂ (aL n 0))
        ((F.rightDerived 1).map (cyclesMap φ n))
        (leftExactConnectingHom_naturality F h₁ h₂ (cochainCyclesSequenceMap φ n)).symm

end AcyclicComplexes

section ExactFunctor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [EnoughInjectives D]
  [HasDerivedCategory.{w₁} D]
  {D' : Type u₃} [Category.{v₃} D'] [Abelian D'] [HasDerivedCategory.{w₂} D']
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (F : D ⥤ D') [F.Additive] [PreservesFiniteLimits F]
  {A : C}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Applying the left exact functor to the existing exact-resolution comparison
is a quasi-isomorphism if the actual mapped source terms are acyclic.  The target
terms are acyclic because they are the original injectives. -/
theorem exactFunctorResolutionComparison_map_quasiIso_of_acyclic (I : InjectiveResolution A)
    (h : ∀ j m : ℕ, IsZero ((F.rightDerived (m + 1)).obj (G.obj (I.cocomplex.X j)))) :
    QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map (exactFunctorResolutionComparison G I)) := by
  have : IsIso (cyclesMap (exactFunctorResolutionComparison G I) 0) :=
    cochainCyclesMap_zero_isIso
      (exactFunctorResolutionAugmentation G I) ((injectiveResolution (G.obj A)).ι.f 0)
      (exactFunctorResolutionAugmentation_d G I)
      (injectiveResolution (G.obj A)).ι_f_zero_comp_complex_d
      (exactFunctorResolution_exact_zero G I) (injectiveResolution (G.obj A)).exact₀
      (exactFunctorResolutionComparison G I) (𝟙 (G.obj A))
      (by simpa only [id_comp] using exactFunctorResolutionComparison_commutes G I)
  exact cochainMap_map_quasiIso_of_acyclic F (exactFunctorResolutionComparison G I)
    (exactFunctorResolution_exactAt_succ G I)
    (injectiveResolution (G.obj A)).cocomplex_exactAt_succ h
    (fun j m => F.isZero_rightDerived_obj_injective_succ m
      ((injectiveResolution (G.obj A)).cocomplex.X j))

end ExactFunctor

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.leftExactConnectingHom
#print axioms PrimeGap182.TypeIII.comp_leftExactConnectingHom
#print axioms PrimeGap182.TypeIII.leftExactConnectingHom_exact
#print axioms PrimeGap182.TypeIII.leftExactConnectingHom_epi
#print axioms PrimeGap182.TypeIII.leftExactConnectingHom_isCokernel
#print axioms PrimeGap182.TypeIII.leftExactConnectingHom_naturality
#print axioms PrimeGap182.TypeIII.rightDerived_cyclesMap_isIso
#print axioms PrimeGap182.TypeIII.cochainMap_map_quasiIso_of_acyclic
#print axioms PrimeGap182.TypeIII.exactFunctorResolutionComparison_map_quasiIso_of_acyclic
