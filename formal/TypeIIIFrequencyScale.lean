import TypeIIIFrequencyGCD
import TypeIIISharedScale

/-! Uniform summation of all three actual residual gcd powers at every positive scale. -/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

theorem exists_sharedThreeScale_frequency_sum {A ε : ℝ} (hA : 1 < A) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : ℕ), 0 < w → ∀ (K M R : ℝ),
      0 < K → 0 ≤ M → 0 ≤ R → ∀ F : Finset ℤ,
      (∑ c ∈ F, (integerFrequencyDecay K⁻¹ A c / K) *
        sharedThreeScale M R w (Int.gcd c (w : ℤ))) ≤
      C * (w : ℝ) ^ ε * matrixThreeScale M R w := by
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_frequencyGCDWeight_subpower hA
    (show (1 / 2 : ℝ) ≤ 1 by norm_num) hε
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_frequencyGCDWeight_subpower hA
    (show (1 / 4 : ℝ) ≤ 1 by norm_num) hε
  obtain ⟨C₃, hC₃, hb₃⟩ := exists_frequencyGCDWeight_subpower hA
    (show (5 / 8 : ℝ) ≤ 1 by norm_num) hε
  refine ⟨C₁ + C₂ + C₃, by positivity, ?_⟩
  intro w hw K M R hK hM hR F
  have hc₁ : C₁ ≤ C₁ + C₂ + C₃ := by linarith
  have hc₂ : C₂ ≤ C₁ + C₂ + C₃ := by linarith
  have hc₃ : C₃ ≤ C₁ + C₂ + C₃ := by linarith
  have hsum (b : ℝ) :
      (∑ c ∈ F, frequencyGCDWeight w K A b c) ≤ ∑' c : ℤ, frequencyGCDWeight w K A b c :=
    (frequencyGCDWeight_tsum w hw hK hA b).1.sum_le_tsum F
      (fun c _ => frequencyGCDWeight_nonneg w hK A b c)
  have h₁ : (∑ c ∈ F, frequencyGCDWeight w K A (1 / 2) c) ≤
      (C₁ + C₂ + C₃) * (w : ℝ) ^ ε :=
    (hsum (1 / 2)).trans ((hb₁ w hw K hK).trans
      (mul_le_mul_of_nonneg_right hc₁ (Real.rpow_nonneg (Nat.cast_nonneg w) _)))
  have h₂ : (∑ c ∈ F, frequencyGCDWeight w K A (1 / 4) c) ≤
      (C₁ + C₂ + C₃) * (w : ℝ) ^ ε :=
    (hsum (1 / 4)).trans ((hb₂ w hw K hK).trans
      (mul_le_mul_of_nonneg_right hc₂ (Real.rpow_nonneg (Nat.cast_nonneg w) _)))
  have h₃ : (∑ c ∈ F, frequencyGCDWeight w K A (5 / 8) c) ≤
      (C₁ + C₂ + C₃) * (w : ℝ) ^ ε :=
    (hsum (5 / 8)).trans ((hb₃ w hw K hK).trans
      (mul_le_mul_of_nonneg_right hc₃ (Real.rpow_nonneg (Nat.cast_nonneg w) _)))
  let U : ℝ := M ^ (3 / 4 : ℝ) * (w : ℝ) ^ (1 / 2 : ℝ)
  let V : ℝ := M * (w : ℝ) ^ (3 / 4 : ℝ) / R ^ (1 / 2 : ℝ)
  let W : ℝ := M * (w : ℝ) ^ (3 / 8 : ℝ)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  calc
    _ = ∑ c ∈ F, (U * frequencyGCDWeight w K A (1 / 2) c +
        V * frequencyGCDWeight w K A (1 / 4) c + W * frequencyGCDWeight w K A (5 / 8) c) := by
      apply Finset.sum_congr rfl
      intro c _
      dsimp only [sharedThreeScale, frequencyGCDWeight, U, V, W]
      ring
    _ = U * (∑ c ∈ F, frequencyGCDWeight w K A (1 / 2) c) +
        V * (∑ c ∈ F, frequencyGCDWeight w K A (1 / 4) c) +
        W * (∑ c ∈ F, frequencyGCDWeight w K A (5 / 8) c) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ U * ((C₁ + C₂ + C₃) * (w : ℝ) ^ ε) +
        V * ((C₁ + C₂ + C₃) * (w : ℝ) ^ ε) +
        W * ((C₁ + C₂ + C₃) * (w : ℝ) ^ ε) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left h₁ hU)
        (mul_le_mul_of_nonneg_left h₂ hV)) (mul_le_mul_of_nonneg_left h₃ hW)
    _ = _ := by dsimp only [matrixThreeScale, U, V, W]; ring

#print axioms exists_sharedThreeScale_frequency_sum

end

end PrimeGap182.TypeIII
