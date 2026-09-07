import TypeIIIArtinSchreierBockstein

/-!
# Transitions between the original coefficient Bockstein sequences

Reducing from level n to level m gives a morphism between the existing
short exact sequences. Its components are multiplication by ell^(n-m),
the identity, and the original finite reduction. The two squares and
the identity and composition laws are proved for these literal maps.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell)
  {R : Type} [CommRing R] [CharP R p] (f : R)

/-- The actual transition between the original short exact sequences.
Its right component is the unchanged finite reduction over the limit ring. -/
def limitArtinSchreierBocksteinTransition {m n : ℕ} (hmn : m ≤ n) :
    limitArtinSchreierBocksteinSequence p ell hne f n ⟶
      limitArtinSchreierBocksteinSequence p ell hne f m where
  τ₁ := (ell ^ (n - m)) • 𝟙 (limitArtinSchreierSheaf p ell hne f)
  τ₂ := 𝟙 (limitArtinSchreierSheaf p ell hne f)
  τ₃ := torsionArtinSchreierLimitModuleReduction p ell hne f hmn
  comm₁₂ := by
    change ((ell ^ (n - m)) • 𝟙 (limitArtinSchreierSheaf p ell hne f)) ≫
        ((ell ^ (m + 1)) • 𝟙 (limitArtinSchreierSheaf p ell hne f)) =
      ((ell ^ (n + 1)) • 𝟙 (limitArtinSchreierSheaf p ell hne f)) ≫ 𝟙 _
    simp only [Preadditive.comp_nsmul, Category.comp_id]
    rw [← mul_smul, ← pow_add]
    congr 2
    omega
  comm₂₃ := by
    change 𝟙 (limitArtinSchreierSheaf p ell hne f) ≫
        limitArtinSchreierReduction p ell hne f m =
      limitArtinSchreierReduction p ell hne f n ≫
        torsionArtinSchreierLimitModuleReduction p ell hne f hmn
    rw [Category.id_comp, limitArtinSchreierReduction_comp]

/-- The left transition is the literal complementary integer power. -/
@[simp] theorem limitArtinSchreierBocksteinTransition_τ₁ {m n : ℕ} (hmn : m ≤ n) :
    (limitArtinSchreierBocksteinTransition p ell hne f hmn).τ₁ =
      (ell ^ (n - m)) • 𝟙 (limitArtinSchreierSheaf p ell hne f) := rfl

/-- The middle transition is literally the identity. -/
@[simp] theorem limitArtinSchreierBocksteinTransition_τ₂ {m n : ℕ} (hmn : m ≤ n) :
    (limitArtinSchreierBocksteinTransition p ell hne f hmn).τ₂ =
      𝟙 (limitArtinSchreierSheaf p ell hne f) := rfl

/-- The right transition is the original finite coefficient reduction. -/
@[simp] theorem limitArtinSchreierBocksteinTransition_τ₃ {m n : ℕ} (hmn : m ≤ n) :
    (limitArtinSchreierBocksteinTransition p ell hne f hmn).τ₃ =
      torsionArtinSchreierLimitModuleReduction p ell hne f hmn := rfl

/-- A level's original transition to itself is the identity short-complex map. -/
theorem limitArtinSchreierBocksteinTransition_refl (n : ℕ) :
    limitArtinSchreierBocksteinTransition p ell hne f (le_refl n) =
      𝟙 (limitArtinSchreierBocksteinSequence p ell hne f n) := by
  apply ShortComplex.hom_ext
  · change (ell ^ (n - n)) • 𝟙 (limitArtinSchreierSheaf p ell hne f) = 𝟙 _
    rw [Nat.sub_self, pow_zero, one_nsmul]
  · rfl
  · exact torsionArtinSchreierLimitModuleReduction_refl p ell hne f n

/-- Successive original short-complex transitions compose to the direct
transition, including their complementary-power left components. -/
theorem limitArtinSchreierBocksteinTransition_comp {k m n : ℕ}
    (hkm : k ≤ m) (hmn : m ≤ n) :
    limitArtinSchreierBocksteinTransition p ell hne f hmn ≫
        limitArtinSchreierBocksteinTransition p ell hne f hkm =
      limitArtinSchreierBocksteinTransition p ell hne f (hkm.trans hmn) := by
  apply ShortComplex.hom_ext
  · change ((ell ^ (n - m)) • 𝟙 (limitArtinSchreierSheaf p ell hne f)) ≫
        ((ell ^ (m - k)) • 𝟙 (limitArtinSchreierSheaf p ell hne f)) =
      (ell ^ (n - k)) • 𝟙 (limitArtinSchreierSheaf p ell hne f)
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp]
    rw [← mul_smul, ← pow_add]
    congr 2
    omega
  · change 𝟙 (limitArtinSchreierSheaf p ell hne f) ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _
  · exact torsionArtinSchreierLimitModuleReduction_comp p ell hne f hkm hmn

#print axioms limitArtinSchreierBocksteinTransition
#print axioms limitArtinSchreierBocksteinTransition_τ₁
#print axioms limitArtinSchreierBocksteinTransition_τ₂
#print axioms limitArtinSchreierBocksteinTransition_τ₃
#print axioms limitArtinSchreierBocksteinTransition_refl
#print axioms limitArtinSchreierBocksteinTransition_comp

end PrimeGap182.TypeIII
