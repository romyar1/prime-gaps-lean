import TypeIIIPoisson

/-!
# A common Fourier envelope when the completion modulus varies

The hypotheses compare the actual modulus with one common width. No lower bound by one
is imposed on that width. The profile contributes an explicit second-derivative constant.
-/

open scoped BigOperators Classical FourierTransform ContDiff

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual normalized continuous Fourier sample appearing after completion. -/
def normalizedProfileFourier (q : ℕ) (ψ : ℝ → ℂ) (N t₀ : ℝ) (c : ℤ) : ℂ :=
  (q : ℂ)⁻¹ * 𝓕 (fun t : ℝ => ψ ((t - t₀) / N)) ((c : ℝ) / (q : ℝ))

theorem reciprocal_square_common_width {q N κ ρ z : ℝ}
    (hq : 0 < q) (hκ : 0 < κ) (hρ : 0 ≤ ρ) (hz : 0 ≤ z)
    (hupper : q ≤ κ * N) (hlower : κ * N ≤ ρ * q) :
    (N / q) / (1 + N * (z / q)) ^ 2 ≤
      (ρ / κ) / (1 + z / κ) ^ 2 := by
  have hn : N / q ≤ ρ / κ := (div_le_div_iff₀ hq hκ).2 (by nlinarith)
  have hb : 1 + z / κ ≤ 1 + N * (z / q) := by
    have hNq : 1 / κ ≤ N / q := (div_le_div_iff₀ hκ hq).2 (by simpa [mul_comm] using hupper)
    have hh := mul_le_mul_of_nonneg_right hNq hz
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_assoc, mul_left_comm, mul_comm,
      add_comm] using
      add_le_add_left hh 1
  exact div_le_div₀ (div_nonneg hρ hκ.le) hn (by positivity)
    (pow_le_pow_left₀ (by positivity) hb 2)

/-- A smooth compact profile has a single nonzero-frequency envelope across all comparable
actual moduli. The common width κ can be smaller than one. -/
theorem normalizedProfileFourier_nonzero_bound
    (q : ℕ) [NeZero q] (T L N t₀ κ ρ : ℝ)
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hN : 0 < N) (hκ : 0 < κ) (hρ : 0 ≤ ρ)
    (hupper : (q : ℝ) ≤ κ * N) (hlower : κ * N ≤ ρ * (q : ℝ))
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ 2 ψ)
    (hsupport : Function.support ψ ⊆ Set.Icc (-T) T)
    (hbound : ∀ t : ℝ,
      ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L)
    (c : ℤ) (hc : c ≠ 0) :
    ‖normalizedProfileFourier q ψ N t₀ c‖ ≤
      ((8 * T) * L * ρ) * (integerFrequencyDecay κ⁻¹ 2 c / κ) := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hd := PrimeGap186.compactProfile_fourier_decay_bound T L N t₀
    hT hL hN ψ hψ hsupport hbound ((c : ℝ) / (q : ℝ))
  have hscale := reciprocal_square_common_width hq hκ hρ (abs_nonneg (c : ℝ))
    hupper hlower
  have hden : 0 ≤ 1 + κ⁻¹ * |(c : ℝ)| := by positivity
  have he : integerFrequencyDecay κ⁻¹ 2 c = (1 + |(c : ℝ)| / κ)⁻¹ ^ 2 := by
    simp only [integerFrequencyDecay, ite_eq_right hc, positiveFrequencyDecay,
      Real.rpow_neg hden, Real.rpow_two, inv_pow]
    congr 2
    ring
  rw [he]
  unfold normalizedProfileFourier
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q : ℝ)⁻¹ * ((8 * T) * L * N /
        (1 + N * |(c : ℝ) / (q : ℝ)|) ^ 2) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = ((8 * T) * L) * ((N / (q : ℝ)) /
        (1 + N * (|(c : ℝ)| / (q : ℝ))) ^ 2) := by
      rw [abs_div, abs_of_pos hq]
      ring
    _ ≤ ((8 * T) * L) * ((ρ / κ) / (1 + |(c : ℝ)| / κ) ^ 2) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by
      simp only [div_eq_mul_inv, inv_pow]
      ring

#print axioms reciprocal_square_common_width
#print axioms normalizedProfileFourier_nonzero_bound

end

end PrimeGap182.TypeIII
