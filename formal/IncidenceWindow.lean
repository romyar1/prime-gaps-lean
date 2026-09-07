import IncidenceShearedBox

/-!
# The actual compact-window estimate from Type II Lemma 2.2

The proof is stronger than the stated smooth case: every bounded nonnegative
weight supported in a fixed compact square is allowed. Smoothness is used
only for the explicitly constructed dominating plateau, whose properties
are proved in the preceding modules.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

def incidenceContinuousWindow (w : ℝ × ℝ → ℝ) (E₁ E₂ e₀ γ₀ τ : ℝ) (z : ℤ × ℤ) : ℝ :=
  w (((z.1 : ℝ) - e₀) / E₁, ((z.2 : ℝ) - τ * (z.1 : ℝ) - γ₀) / E₂)

theorem incidenceWindowScale_rescale (η : ℝ) (q : ℕ) (T E₁ E₂ : ℝ)
    (hT : 1 ≤ T) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) :
    incidenceWindowScale η q (T * E₁) (T * E₂) ≤ T ^ 2 * incidenceWindowScale η q E₁ E₂ := by
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hTT : T ≤ T ^ 2 := by nlinarith
  have hT2 : 1 ≤ T ^ 2 := hT.trans hTT
  have hbig : 0 ≤ (q : ℝ) ^ ((3 : ℝ) / 2 + η) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsmall : 0 ≤ (q : ℝ) ^ ((1 : ℝ) / 2 + η) * (E₁ + E₂) := by positivity
  have h₁ := mul_le_mul_of_nonneg_right hT2 hbig
  have h₂ := mul_le_mul_of_nonneg_right hTT hsmall
  unfold incidenceWindowScale
  nlinarith

set_option maxHeartbeats 600000 in
/-- The manuscript's compact-window estimate, uniformly in centers, shear,
and both positive scales, for every actual bounded nonnegative compact weight. -/
theorem incidenceCompactWindow_bound (hK4 : AllIncidenceRankFourBounds)
    (η T L : ℝ) (hη : 0 < η) (hT : 1 ≤ T) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ × ℝ → ℝ,
      (∀ z, 0 ≤ w z) → (∀ z, w z ≤ L) →
      (∀ z, w z ≠ 0 → |z.1| ≤ T ∧ |z.2| ≤ T) →
      ∀ q : ℕ, ∀ [NeZero q], Squarefree q → ∀ A : ZMod q, IsUnit A →
      ∀ E₁ E₂ e₀ γ₀ τ : ℝ, 0 < E₁ → 0 < E₂ → ∀ c : ZMod q → ℂ,
        (∑' z : ℤ × ℤ, incidenceContinuousWindow w E₁ E₂ e₀ γ₀ τ z *
          ‖(incidenceMatrixMod A *ᵥ c) (incidenceIntegerResidue q z)‖ ^ 2) ≤
          C * incidenceWindowScale η q E₁ E₂ * incidenceVectorEnergy c := by
  obtain ⟨C₀, hC₀, hbox⟩ := incidenceShearedBox_bound hK4 η hη
  have hCL : 0 ≤ C₀ * L := mul_nonneg hC₀.le hL
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  refine ⟨1 + C₀ * L * T ^ 2, by positivity, ?_⟩
  intro w hw0 hwL hws q _ hq A hA E₁ E₂ e₀ γ₀ τ hE₁ hE₂ c
  let W := incidenceContinuousWindow w E₁ E₂ e₀ γ₀ τ
  have hshape (z : ℤ × ℤ) (hz : W z ≠ 0) :
      |(z.1 : ℝ) - e₀| ≤ T * E₁ ∧
      |(z.2 : ℝ) - τ * (z.1 : ℝ) - γ₀| ≤ T * E₂ := by
    have hb := hws ((((z.1 : ℝ) - e₀) / E₁),
      (((z.2 : ℝ) - τ * (z.1 : ℝ) - γ₀) / E₂)) hz
    rw [abs_div, abs_of_pos hE₁, abs_div, abs_of_pos hE₂] at hb
    exact ⟨(div_le_iff₀ hE₁).mp hb.1, (div_le_iff₀ hE₂).mp hb.2⟩
  have hb := hbox q hq A hA (T * E₁) (T * E₂) e₀ γ₀ τ L
    (mul_pos hT0 hE₁) (mul_pos hT0 hE₂) hL W (fun z => hw0 _) (fun z => hwL _) hshape c
  calc
    _ ≤ C₀ * L * incidenceWindowScale η q (T * E₁) (T * E₂) * incidenceVectorEnergy c := hb
    _ ≤ C₀ * L * (T ^ 2 * incidenceWindowScale η q E₁ E₂) * incidenceVectorEnergy c :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (incidenceWindowScale_rescale η q T E₁ E₂ hT hE₁.le hE₂.le)
          hCL) (incidenceVectorEnergy_nonneg c)
    _ ≤ _ := by
      have hs := incidenceWindowScale_nonneg η q E₁ E₂ hE₁.le hE₂.le
      have he := incidenceVectorEnergy_nonneg c
      nlinarith [mul_nonneg hs he]

#print axioms incidenceWindowScale_rescale
#print axioms incidenceCompactWindow_bound

end PrimeGap182Audit
