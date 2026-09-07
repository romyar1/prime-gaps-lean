import TypeIIIDerivedPlusSingleTriangle
import TypeIIIRightDerivedPlusComparison
import TypeIIIRightDerivedPlusTriangulated
import TypeIIIInjectiveResolutionAdditivity

/-!
# The long exact sequence of the existing ordinary right derived functors

The original short-exact-sequence triangle is sent through the actual
bounded below derived functor.  Its homology sequence is transported
through the proved natural comparison with `F.rightDerived n`.
The connecting maps and every other map therefore belong to those
existing ordinary derived functors.  Triangulatedness is supplied by
its proved construction, rather than an additional hypothesis.
-/

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Pretriangulated

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C]
  [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  (F : C ⥤ D) [F.Additive]
  {S : ShortComplex C} (hS : S.ShortExact)

/-- The original single triangle mapped by the actual bounded below derived functor. -/
def rightDerivedPlusSingleTriangle : Triangle (DerivedCategory D) :=
  (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
    (shortExactPlusTriangle hS)

/-- Distinguishedness follows from the proved triangulated structure of the actual functor. -/
theorem rightDerivedPlusSingleTriangle_distinguished :
    rightDerivedPlusSingleTriangle F hS ∈ distTriang (DerivedCategory D) :=
  (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map_distinguished _
    (shortExactPlusTriangle_distinguished hS)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical connecting map between the existing ordinary right derived functors. -/
def rightDerivedConnectingHom (n : ℕ) :
    (F.rightDerived n).obj S.X₃ ⟶ (F.rightDerived (n + 1)).obj S.X₁ :=
  ((rightDerivedPlusComparisonIso F n).app S.X₃).hom ≫
    DerivedCategory.HomologySequence.δ (rightDerivedPlusSingleTriangle F hS)
      (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp) ≫
    ((rightDerivedPlusComparisonIso F (n + 1)).app S.X₁).inv

set_option backward.isDefEq.respectTransparency false in
/-- The original map to the third term composes to zero with the connecting map. -/
theorem comp_rightDerivedConnectingHom (n : ℕ) :
    (F.rightDerived n).map S.g ≫ rightDerivedConnectingHom F hS n = 0 := by
  have hg := (rightDerivedPlusComparisonIso F n).hom.naturality S.g
  change (F.rightDerived n).map S.g ≫
      ((rightDerivedPlusComparisonIso F n).app S.X₃).hom =
    ((rightDerivedPlusComparisonIso F n).app S.X₂).hom ≫
      (DerivedCategory.homologyFunctor D (n : ℤ)).map
        (rightDerivedPlusSingleTriangle F hS).mor₂ at hg
  rw [rightDerivedConnectingHom, ← assoc, hg, assoc]
  simpa only [assoc, comp_zero, zero_comp] using
    congrArg (fun z => ((rightDerivedPlusComparisonIso F n).app S.X₂).hom ≫ z ≫
      ((rightDerivedPlusComparisonIso F (n + 1)).app S.X₁).inv)
      (DerivedCategory.HomologySequence.comp_δ (rightDerivedPlusSingleTriangle F hS)
        (rightDerivedPlusSingleTriangle_distinguished F hS)
        (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp))

set_option backward.isDefEq.respectTransparency false in
/-- The connecting map composes to zero with the original next-degree map. -/
theorem rightDerivedConnectingHom_comp (n : ℕ) :
    rightDerivedConnectingHom F hS n ≫ (F.rightDerived (n + 1)).map S.f = 0 := by
  have hf := (rightDerivedPlusComparisonIso F (n + 1)).inv.naturality S.f
  change (DerivedCategory.homologyFunctor D ((n + 1 : ℕ) : ℤ)).map
      (rightDerivedPlusSingleTriangle F hS).mor₁ ≫
      ((rightDerivedPlusComparisonIso F (n + 1)).app S.X₂).inv =
    ((rightDerivedPlusComparisonIso F (n + 1)).app S.X₁).inv ≫
      (F.rightDerived (n + 1)).map S.f at hf
  simp only [rightDerivedConnectingHom, assoc]
  rw [← hf]
  simpa only [assoc, comp_zero, zero_comp] using
    congrArg (fun z => ((rightDerivedPlusComparisonIso F n).app S.X₃).hom ≫ z ≫
      ((rightDerivedPlusComparisonIso F (n + 1)).app S.X₂).inv)
      (DerivedCategory.HomologySequence.δ_comp (rightDerivedPlusSingleTriangle F hS)
        (rightDerivedPlusSingleTriangle_distinguished F hS)
        (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp))

include hS in
set_option backward.isDefEq.respectTransparency false in
/-- Exactness at the middle term uses the original maps of `F.rightDerived n`. -/
theorem rightDerivedLongExact_exact₂ (n : ℕ) :
    (S.map (F.rightDerived n)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    (DerivedCategory.HomologySequence.exact₂ (rightDerivedPlusSingleTriangle F hS)
      (rightDerivedPlusSingleTriangle_distinguished F hS) (n : ℤ))
  refine ShortComplex.isoMk
    ((rightDerivedPlusComparisonIso F n).app S.X₁).symm
    ((rightDerivedPlusComparisonIso F n).app S.X₂).symm
    ((rightDerivedPlusComparisonIso F n).app S.X₃).symm ?_ ?_
  · exact ((rightDerivedPlusComparisonIso F n).inv.naturality S.f).symm
  · exact ((rightDerivedPlusComparisonIso F n).inv.naturality S.g).symm

set_option backward.isDefEq.respectTransparency false in
/-- Exactness at the third term uses the canonical transported connecting map. -/
theorem rightDerivedLongExact_exact₃ (n : ℕ) :
    (ShortComplex.mk ((F.rightDerived n).map S.g) (rightDerivedConnectingHom F hS n)
      (comp_rightDerivedConnectingHom F hS n)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    (DerivedCategory.HomologySequence.exact₃ (rightDerivedPlusSingleTriangle F hS)
      (rightDerivedPlusSingleTriangle_distinguished F hS)
      (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp))
  refine ShortComplex.isoMk
    ((rightDerivedPlusComparisonIso F n).app S.X₂).symm
    ((rightDerivedPlusComparisonIso F n).app S.X₃).symm
    ((rightDerivedPlusComparisonIso F (n + 1)).app S.X₁).symm ?_ ?_
  · exact ((rightDerivedPlusComparisonIso F n).inv.naturality S.g).symm
  · change ((rightDerivedPlusComparisonIso F n).app S.X₃).inv ≫
        rightDerivedConnectingHom F hS n =
      DerivedCategory.HomologySequence.δ (rightDerivedPlusSingleTriangle F hS)
        (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp) ≫
        ((rightDerivedPlusComparisonIso F (n + 1)).app S.X₁).inv
    rw [rightDerivedConnectingHom, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Exactness at the first term in the next degree completes the long exact sequence. -/
theorem rightDerivedLongExact_exact₁ (n : ℕ) :
    (ShortComplex.mk (rightDerivedConnectingHom F hS n) ((F.rightDerived (n + 1)).map S.f)
      (rightDerivedConnectingHom_comp F hS n)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    (DerivedCategory.HomologySequence.exact₁ (rightDerivedPlusSingleTriangle F hS)
      (rightDerivedPlusSingleTriangle_distinguished F hS)
      (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp))
  refine ShortComplex.isoMk
    ((rightDerivedPlusComparisonIso F n).app S.X₃).symm
    ((rightDerivedPlusComparisonIso F (n + 1)).app S.X₁).symm
    ((rightDerivedPlusComparisonIso F (n + 1)).app S.X₂).symm ?_ ?_
  · change ((rightDerivedPlusComparisonIso F n).app S.X₃).inv ≫
        rightDerivedConnectingHom F hS n =
      DerivedCategory.HomologySequence.δ (rightDerivedPlusSingleTriangle F hS)
        (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp) ≫
        ((rightDerivedPlusComparisonIso F (n + 1)).app S.X₁).inv
    rw [rightDerivedConnectingHom, Iso.inv_hom_id_assoc]
  · exact ((rightDerivedPlusComparisonIso F (n + 1)).inv.naturality S.f).symm

set_option backward.isDefEq.respectTransparency false in
/-- The canonical ordinary connecting maps are natural for actual morphisms of short exact sequences. -/
theorem rightDerivedConnectingHom_naturality
    {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
    (φ : S₁ ⟶ S₂) (n : ℕ) :
    (F.rightDerived n).map φ.τ₃ ≫ rightDerivedConnectingHom F h₂ n =
      rightDerivedConnectingHom F h₁ n ≫ (F.rightDerived (n + 1)).map φ.τ₁ := by
  have hd := (DerivedCategory.homologyFunctor D 0).homologySequenceδ_naturality
    ((F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.map
      (shortExactPlusTriangleMap h₁ h₂ φ))
    (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp)
  change (DerivedCategory.homologyFunctor D (n : ℤ)).map
      ((F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map
        (shortExactPlusTriangleMap h₁ h₂ φ).hom₃) ≫
      DerivedCategory.HomologySequence.δ (rightDerivedPlusSingleTriangle F h₂)
        (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp) =
    DerivedCategory.HomologySequence.δ (rightDerivedPlusSingleTriangle F h₁)
        (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp) ≫
      (DerivedCategory.homologyFunctor D ((n + 1 : ℕ) : ℤ)).map
        ((F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map
          (shortExactPlusTriangleMap h₁ h₂ φ).hom₁) at hd
  rw [shortExactPlusTriangleMap_hom₃, shortExactPlusTriangleMap_hom₁] at hd
  have h₃ := (rightDerivedPlusComparisonIso F n).hom.naturality φ.τ₃
  change (F.rightDerived n).map φ.τ₃ ≫
      ((rightDerivedPlusComparisonIso F n).app S₂.X₃).hom =
    ((rightDerivedPlusComparisonIso F n).app S₁.X₃).hom ≫
      (DerivedCategory.homologyFunctor D (n : ℤ)).map
        ((F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map
          ((DerivedCategory.Plus.singleFunctor C 0).map φ.τ₃)) at h₃
  have h₁' := (rightDerivedPlusComparisonIso F (n + 1)).inv.naturality φ.τ₁
  change (DerivedCategory.homologyFunctor D ((n + 1 : ℕ) : ℤ)).map
      ((F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map
        ((DerivedCategory.Plus.singleFunctor C 0).map φ.τ₁)) ≫
      ((rightDerivedPlusComparisonIso F (n + 1)).app S₂.X₁).inv =
    ((rightDerivedPlusComparisonIso F (n + 1)).app S₁.X₁).inv ≫
      (F.rightDerived (n + 1)).map φ.τ₁ at h₁'
  simp only [rightDerivedConnectingHom, assoc]
  rw [← assoc, h₃, assoc]
  erw [reassoc_of% hd, h₁']

/-- Vanishing of the two adjacent derived middle terms makes this same connecting map an isomorphism. -/
theorem rightDerivedConnectingHom_isIso_of_isZero_middle (n : ℕ)
    (h₀ : IsZero ((F.rightDerived n).obj S.X₂))
    (h₁ : IsZero ((F.rightDerived (n + 1)).obj S.X₂)) :
    IsIso (rightDerivedConnectingHom F hS n) := by
  have : Mono (rightDerivedConnectingHom F hS n) :=
    (rightDerivedLongExact_exact₃ F hS n).mono_g_iff.2 (h₀.eq_of_src _ _)
  have : Epi (rightDerivedConnectingHom F hS n) :=
    (rightDerivedLongExact_exact₁ F hS n).epi_f_iff.2 (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi (rightDerivedConnectingHom F hS n)

#print axioms rightDerivedPlusSingleTriangle
#print axioms rightDerivedPlusSingleTriangle_distinguished
#print axioms rightDerivedConnectingHom
#print axioms comp_rightDerivedConnectingHom
#print axioms rightDerivedConnectingHom_comp
#print axioms rightDerivedLongExact_exact₂
#print axioms rightDerivedLongExact_exact₃
#print axioms rightDerivedLongExact_exact₁
#print axioms rightDerivedConnectingHom_naturality
#print axioms rightDerivedConnectingHom_isIso_of_isZero_middle

end PrimeGap182.TypeIII
