import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Arithmetic of the Type III parameter criterion

This file verifies the real-parameter optimization in lines 833--885 of the
frozen `finite_exceptional_type_iii.tex`. It proves no exponential-sum,
sheaf-theoretic, distribution, or prime-gap estimate. The five expressions
are the manuscript's normalized exponents, including the extraction-width
losses and the stated Fourier-cutoff slack.
-/

noncomputable section

namespace PrimeGap182Audit

def typeIIITheta (ω : ℝ) : ℝ := 1 / 2 + 2 * ω

def typeIIIMu (σ : ℝ) : ℝ := 1 / 4 - 3 * σ / 2

def typeIIIMarginA (μ θ δ : ℝ) : ℝ := 8 - 5 * μ - 14 * θ - 2 * δ

def typeIIIMarginB (θ δ : ℝ) : ℝ := 27 * θ + δ - 14

def typeIIIExtraction (μ θ δ : ℝ) : ℝ := (4 - μ - 4 * θ + 2 * δ) / 6

def typeIIIDiagonalExponent (μ θ s ε : ℝ) : ℝ :=
  μ / 2 + 3 * θ / 2 + s / 2 - 1 + 3 * ε / 2

def typeIIICentralExponent (μ θ ε : ℝ) : ℝ :=
  μ + 3 * θ / 2 - 1 + 3 * ε / 2

def typeIIIFirstExponent (μ θ δ s ε : ℝ) : ℝ :=
  3 * μ / 8 + θ - s / 4 - 1 / 2 + δ / 4 + 3 * ε / 4

def typeIIISecondExponent (μ θ s ε : ℝ) : ℝ :=
  μ / 2 + 3 * θ / 4 + s / 8 - 1 / 2 + 3 * ε / 4

def typeIIIFourthExponent (μ θ δ s ε : ℝ) : ℝ :=
  μ / 2 + θ - 5 * s / 16 - 1 / 2 + 5 * δ / 16 + 3 * ε / 4

def TypeIIINegativeErrors (μ θ δ s ε : ℝ) : Prop :=
  typeIIIDiagonalExponent μ θ s ε < 0 ∧
  typeIIICentralExponent μ θ ε < 0 ∧
  typeIIIFirstExponent μ θ δ s ε < 0 ∧
  typeIIISecondExponent μ θ s ε < 0 ∧
  typeIIIFourthExponent μ θ δ s ε < 0

theorem typeIII_criteria_equivalence (σ ω δ : ℝ) :
    (0 < typeIIIMarginA (typeIIIMu σ) (typeIIITheta ω) δ ↔
      σ > 1 / 30 + 56 * ω / 15 + 4 * δ / 15) ∧
    (0 < typeIIIMarginB (typeIIITheta ω) δ ↔ 108 * ω + 2 * δ > 1) := by
  dsimp [typeIIIMarginA, typeIIIMarginB, typeIIIMu, typeIIITheta]
  constructor <;> constructor <;> intro h <;> linarith

/-- Exact identities; the right-hand sides retain all strict margins and slack. -/
theorem typeIII_exponent_identities (μ θ δ ε : ℝ) :
    typeIIIDiagonalExponent μ θ (typeIIIExtraction μ θ δ) ε =
      -typeIIIMarginA μ θ δ / 12 + 3 * ε / 2 ∧
    typeIIICentralExponent μ θ ε = -typeIIIMarginA μ θ δ / 5 -
      (20 + 13 * typeIIIMarginB θ δ + 95 * δ) / 270 + 3 * ε / 2 ∧
    typeIIIFirstExponent μ θ δ (typeIIIExtraction μ θ δ) ε =
      -typeIIIMarginA μ θ δ / 12 + 3 * ε / 4 ∧
    typeIIISecondExponent μ θ (typeIIIExtraction μ θ δ) ε =
      -23 * typeIIIMarginA μ θ δ / 240 - typeIIIMarginB θ δ / 40 -
        δ / 8 + 3 * ε / 4 ∧
    typeIIIFourthExponent μ θ δ (typeIIIExtraction μ θ δ) ε =
      -53 * typeIIIMarginA μ θ δ / 480 - typeIIIMarginB θ δ / 80 + 3 * ε / 4 := by
  dsimp [typeIIIDiagonalExponent, typeIIICentralExponent, typeIIIFirstExponent,
    typeIIISecondExponent, typeIIIFourthExponent, typeIIIExtraction,
    typeIIIMarginA, typeIIIMarginB]
  exact ⟨by ring, by ring, by ring, by ring, by ring⟩

theorem typeIII_extraction_bounds {μ θ δ : ℝ} (hμ : 0 ≤ μ) (hδ : 0 < δ)
    (hA : 0 < typeIIIMarginA μ θ δ) (hB : 0 < typeIIIMarginB θ δ) :
    1 / 2 < θ ∧ θ < 4 / 7 ∧
      0 < typeIIIExtraction μ θ δ ∧ typeIIIExtraction μ θ δ < 1 / 2 := by
  dsimp [typeIIIMarginA, typeIIIMarginB] at hA hB
  dsimp [typeIIIExtraction]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- A single positive margin works for all five errors. -/
theorem typeIII_errors_le_negative_margin {μ θ δ ε : ℝ} (hδ : 0 < δ)
    (hA : 0 < typeIIIMarginA μ θ δ) (hB : 0 < typeIIIMarginB θ δ)
    (hε : ε ≤ typeIIIMarginA μ θ δ / 100) :
    typeIIIDiagonalExponent μ θ (typeIIIExtraction μ θ δ) ε ≤
      -typeIIIMarginA μ θ δ / 24 ∧
    typeIIICentralExponent μ θ ε ≤ -typeIIIMarginA μ θ δ / 24 ∧
    typeIIIFirstExponent μ θ δ (typeIIIExtraction μ θ δ) ε ≤
      -typeIIIMarginA μ θ δ / 24 ∧
    typeIIISecondExponent μ θ (typeIIIExtraction μ θ δ) ε ≤
      -typeIIIMarginA μ θ δ / 24 ∧
    typeIIIFourthExponent μ θ δ (typeIIIExtraction μ θ δ) ε ≤
      -typeIIIMarginA μ θ δ / 24 := by
  rcases typeIII_exponent_identities μ θ δ ε with ⟨hd, hj, h₁, h₂, h₄⟩
  rw [hd, hj, h₁, h₂, h₄]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem typeIII_errors_negative {μ θ δ ε : ℝ} (hδ : 0 < δ)
    (hA : 0 < typeIIIMarginA μ θ δ) (hB : 0 < typeIIIMarginB θ δ)
    (hε : ε ≤ typeIIIMarginA μ θ δ / 100) :
    TypeIIINegativeErrors μ θ δ (typeIIIExtraction μ θ δ) ε := by
  rcases typeIII_errors_le_negative_margin hδ hA hB hε with ⟨hd, hj, h₁, h₂, h₄⟩
  have hn : -typeIIIMarginA μ θ δ / 24 < 0 := by linarith
  exact ⟨hd.trans_lt hn, hj.trans_lt hn, h₁.trans_lt hn, h₂.trans_lt hn, h₄.trans_lt hn⟩

/-- With the extraction scale fixed, lowering the actual modulus or coefficient
scale exponent preserves each negative discrepancy exponent. -/
theorem typeIII_errors_negative_mono {μ μ' θ θ' δ s ε : ℝ}
    (hμ : μ' ≤ μ) (hθ : θ' ≤ θ) (h : TypeIIINegativeErrors μ θ δ s ε) :
    TypeIIINegativeErrors μ' θ' δ s ε := by
  rcases h with ⟨hd, hj, h₁, h₂, h₄⟩
  dsimp [TypeIIINegativeErrors, typeIIIDiagonalExponent, typeIIICentralExponent,
    typeIIIFirstExponent, typeIIISecondExponent, typeIIIFourthExponent] at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The manuscript's complete strict parameter hypotheses imply an admissible
extraction scale and negativity of all five normalized error exponents, uniformly
for smaller actual scale exponents and for `0 ≤ ε ≤ A/100`. -/
theorem typeIII_parameter_criterion (σ ω δ : ℝ)
    (hω : 0 < ω) (hδ : 0 < δ) (hσ : 0 < σ) (hσupper : σ < 1 / 6)
    (hmain : σ > 1 / 30 + 56 * ω / 15 + 4 * δ / 15)
    (hswitch : 108 * ω + 2 * δ > 1) :
    0 < typeIIIMu σ ∧ typeIIIMu σ < 1 / 4 ∧
    1 / 2 < typeIIITheta ω ∧ typeIIITheta ω < 4 / 7 ∧
    0 < typeIIIExtraction (typeIIIMu σ) (typeIIITheta ω) δ ∧
    typeIIIExtraction (typeIIIMu σ) (typeIIITheta ω) δ < 1 / 2 ∧
    0 < typeIIIMarginA (typeIIIMu σ) (typeIIITheta ω) δ / 100 ∧
    ∀ μ' θ' ε : ℝ, μ' ≤ typeIIIMu σ → θ' ≤ typeIIITheta ω →
      0 ≤ ε → ε ≤ typeIIIMarginA (typeIIIMu σ) (typeIIITheta ω) δ / 100 →
      TypeIIINegativeErrors μ' θ' δ
        (typeIIIExtraction (typeIIIMu σ) (typeIIITheta ω) δ) ε := by
  have hμ : 0 < typeIIIMu σ := by dsimp [typeIIIMu]; linarith
  have hμupper : typeIIIMu σ < 1 / 4 := by dsimp [typeIIIMu]; linarith only [hσ]
  have hθ : 1 / 2 < typeIIITheta ω := by dsimp [typeIIITheta]; linarith only [hω]
  have hA := (typeIII_criteria_equivalence σ ω δ).1.mpr hmain
  have hB := (typeIII_criteria_equivalence σ ω δ).2.mpr hswitch
  have hb := typeIII_extraction_bounds hμ.le hδ hA hB
  refine ⟨hμ, hμupper, hθ, hb.2.1, hb.2.2.1, hb.2.2.2, ?_, ?_⟩
  · linarith
  · intro μ' θ' ε hμ' hθ' _ hε
    exact typeIII_errors_negative_mono hμ' hθ' (typeIII_errors_negative hδ hA hB hε)

#print axioms typeIII_criteria_equivalence
#print axioms typeIII_exponent_identities
#print axioms typeIII_errors_le_negative_margin
#print axioms typeIII_parameter_criterion

end PrimeGap182Audit
