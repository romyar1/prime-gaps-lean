import IncidenceAliases
import IncidenceGcdLattice

/-!
# The nonzero completed smooth-window bound

The Fourier envelopes are explicit pointwise hypotheses in this intermediate
lemma. No completed sum is assumed. Absolute convergence, the complete alias
reindexing, the omission of the integer zero pair, and the gcd sum are proved.
-/

noncomputable section

namespace PrimeGap182Audit

open scoped BigOperators FourierTransform SchwartzMap

variable {q : ℕ} [NeZero q]

theorem incidenceDecay_div (a x d : ℝ) (hd : 0 < d) :
    incidenceDecay a (x / d) = incidenceDecay (a / d) x := by
  simp only [incidenceDecay, abs_div, abs_of_pos hd]
  congr 3
  ring

theorem incidenceAlias_sheared_argument (τ : ℝ) (z : ℤ × ℤ)
    (ξ : ZMod q × ZMod q) :
    (((incidenceAliasIndex q z ξ).1 : ℝ) +
      τ * ((incidenceAliasIndex q z ξ).2 : ℝ)) / q =
      (z.1 : ℝ) + (ξ.1.val : ℝ) / q + τ * ((z.2 : ℝ) + (ξ.2.val : ℝ) / q) := by
  rw [add_div, mul_div_assoc, incidenceAliasIndex_first_div, incidenceAliasIndex_second_div]

theorem incidenceFourierGrid_gcd_bound (u v : 𝓢(ℝ, ℂ)) (τ C₁ C₂ E₁ E₂ : ℝ)
    (hC₁ : 0 ≤ C₁) (hu : ∀ t, ‖𝓕 u t‖ ≤ C₁ * incidenceDecay E₁ t)
    (hv : ∀ t, ‖𝓕 v t‖ ≤ C₂ * incidenceDecay E₂ t)
    (z : ℤ × ℤ) (hz : z ≠ 0) :
    ‖𝓕 u (((z.1 : ℝ) + τ * (z.2 : ℝ)) / q) * 𝓕 v ((z.2 : ℝ) / q)‖ *
        Real.sqrt (Nat.gcd q (Int.gcd z.1 z.2) : ℝ) ≤
      (C₁ * C₂) * incidenceGcdDecay q (E₁ / q) (E₂ / q) τ z := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  rw [norm_mul]
  calc
    _ ≤ ((C₁ * incidenceDecay E₁ (((z.1 : ℝ) + τ * (z.2 : ℝ)) / q)) *
        (C₂ * incidenceDecay E₂ ((z.2 : ℝ) / q))) *
          Real.sqrt (Nat.gcd q (Int.gcd z.1 z.2) : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact mul_le_mul (hu _) (hv _) (norm_nonneg _)
        (mul_nonneg hC₁ (incidenceDecay_nonneg _ _))
    _ = _ := by
      rw [incidenceDecay_div _ _ _ hq, incidenceDecay_div _ _ _ hq]
      simp only [incidenceGcdDecay, incidenceShearedNonzeroDecay, ite_eq_right hz]
      ring

set_option maxHeartbeats 800000 in
/-- The complete alias sum over every nonzero finite frequency. -/
theorem incidenceShearedAliases_gcd_bound (u v : 𝓢(ℝ, ℂ)) (τ C₁ C₂ E₁ E₂ : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hE₁ : 0 < E₁) (hE₂ : 0 < E₂)
    (hu : ∀ t, ‖𝓕 u t‖ ≤ C₁ * incidenceDecay E₁ t)
    (hv : ∀ t, ‖𝓕 v t‖ ≤ C₂ * incidenceDecay E₂ t) :
    (∑ ξ ∈ (Finset.univ : Finset (ZMod q × ZMod q)).erase 0,
      ‖∑' z : ℤ × ℤ, incidenceShearedFourier u v τ
        ((ξ.1.val : ℝ) / q) ((ξ.2.val : ℝ) / q) z‖ *
        Real.sqrt (incidenceFrequencyGCD ξ : ℝ)) ≤
      (C₁ * C₂) * (q.divisors.card : ℝ) *
        (8 / ((E₁ / q) * (E₂ / q)) + 4 / (E₂ / q) + 2 / (E₁ / q)) := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  let G := incidenceGcdDecay q (E₁ / q) (E₂ / q) τ
  have hG := incidenceGcdDecay_bounds q (NeZero.pos q) (E₁ / q) (E₂ / q) τ
    (div_pos hE₁ hq) (div_pos hE₂ hq)
  have hG0 (z : ℤ × ℤ) : 0 ≤ G z :=
    mul_nonneg (incidenceShearedNonzeroDecay_nonneg _ _ _ _) (Real.sqrt_nonneg _)
  have hGa : Summable (fun p : (ℤ × ℤ) × (ZMod q × ZMod q) =>
      G (incidenceAliasIndex q p.1 p.2)) := by
    simpa only [Function.comp_def, incidenceAliasEquiv_symm_apply] using
      (incidenceAliasEquiv q).symm.summable_iff.mpr hG.1
  have hpoint (ξ : ZMod q × ZMod q) (hξ : ξ ≠ 0) (z : ℤ × ℤ) :
      ‖incidenceShearedFourier u v τ ((ξ.1.val : ℝ) / q) ((ξ.2.val : ℝ) / q) z‖ *
        Real.sqrt (incidenceFrequencyGCD ξ : ℝ) ≤ (C₁ * C₂) * G (incidenceAliasIndex q z ξ) := by
    have hb := incidenceFourierGrid_gcd_bound (q := q) u v τ C₁ C₂ E₁ E₂ hC₁ hu hv
      (incidenceAliasIndex q z ξ) (incidenceAliasIndex_ne_zero z ξ hξ)
    simpa only [incidenceAlias_sheared_argument, incidenceAliasIndex_second_div,
      incidenceAliasIndex_gcd, incidenceShearedFourier, G] using hb
  have hrow (ξ : ZMod q × ZMod q) (hξ : ξ ≠ 0) :
      ‖∑' z : ℤ × ℤ, incidenceShearedFourier u v τ
        ((ξ.1.val : ℝ) / q) ((ξ.2.val : ℝ) / q) z‖ *
        Real.sqrt (incidenceFrequencyGCD ξ : ℝ) ≤
      (C₁ * C₂) * ∑' z : ℤ × ℤ, G (incidenceAliasIndex q z ξ) := by
    have hf := (incidenceShearedFourier_summable u v τ
      ((ξ.1.val : ℝ) / q) ((ξ.2.val : ℝ) / q)).norm
    calc
      _ ≤ (∑' z : ℤ × ℤ, ‖incidenceShearedFourier u v τ
          ((ξ.1.val : ℝ) / q) ((ξ.2.val : ℝ) / q) z‖) *
            Real.sqrt (incidenceFrequencyGCD ξ : ℝ) :=
        mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hf) (Real.sqrt_nonneg _)
      _ = ∑' z : ℤ × ℤ, ‖incidenceShearedFourier u v τ
          ((ξ.1.val : ℝ) / q) ((ξ.2.val : ℝ) / q) z‖ *
            Real.sqrt (incidenceFrequencyGCD ξ : ℝ) := (tsum_mul_right).symm
      _ ≤ ∑' z : ℤ × ℤ, (C₁ * C₂) * G (incidenceAliasIndex q z ξ) :=
        (hf.mul_right _).tsum_le_tsum (hpoint ξ hξ)
          ((hGa.prod_symm.prod_factor ξ).mul_left _)
      _ = _ := tsum_mul_left
  calc
    _ ≤ ∑ ξ ∈ (Finset.univ : Finset (ZMod q × ZMod q)).erase 0,
        (C₁ * C₂) * ∑' z : ℤ × ℤ, G (incidenceAliasIndex q z ξ) := by
      apply Finset.sum_le_sum
      intro ξ hξ
      exact hrow ξ (Finset.mem_erase.mp hξ).1
    _ ≤ ∑ ξ : ZMod q × ZMod q, (C₁ * C₂) *
        ∑' z : ℤ × ℤ, G (incidenceAliasIndex q z ξ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      intro ξ _ _
      exact mul_nonneg (mul_nonneg hC₁ hC₂) (tsum_nonneg (fun z => hG0 _))
    _ = (C₁ * C₂) * ∑' z : ℤ × ℤ, G z := by
      rw [← Finset.mul_sum, incidenceAlias_tsum G hG.1]
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_left hG.2 (mul_nonneg hC₁ hC₂)
      simpa only [G, mul_assoc] using hb

#print axioms incidenceDecay_div
#print axioms incidenceAlias_sheared_argument
#print axioms incidenceFourierGrid_gcd_bound
#print axioms incidenceShearedAliases_gcd_bound

end PrimeGap182Audit
