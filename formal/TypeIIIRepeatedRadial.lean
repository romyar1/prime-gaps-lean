import TypeIIIRepeatedAlgebra
import TypeIIISharedFrequency

/-!
# Exact radial Fourier model of the actual Type III kernel

On each nonzero ray, the kernel is the additive Fourier transform of a
unit-masked product of two rank-three Kloosterman sums.  Fourier inversion
therefore gives an exact radial transform, with the zero-correlation term
retained.  The single-kernel radial estimate below follows only from the
established rank-three bound already isolated in `BaselineLocalInputs`.

This is not a Fourier estimate for the product of four kernels.  Multiplying
the four radial transforms corresponds to convolution, and the cancellation
and exceptional curve required by the repeated branch remain to be proved.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The actual function whose positive Fourier transform is the correlation. -/
def repeatedRadialSeed (A B x : ZMod p) : ℂ :=
  if x = 0 then 0 else kl3 p (A * x) * star (kl3 p (B * x))

theorem correlation_eq_repeatedRadialSeed_dft (A B t : ZMod p) :
    correlation p A B t = ZMod.dft (repeatedRadialSeed p A B) (-t) := by
  rw [correlation, PrimeGap186.sum_units_eq_sum_ite p
    (fun x : ZMod p => kl3 p (A * x) * star (kl3 p (B * x)) *
      ZMod.stdAddChar (t * x))]
  simp only [ZMod.dft_apply, smul_eq_mul, repeatedRadialSeed]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x = 0 <;> simp [hx, mul_comm]

/-- Fourier inversion in the actual additive correlation frequency. -/
theorem correlation_positive_fourier_frequency (A B ξ : ZMod p) :
    (∑ t : ZMod p, correlation p A B t * ZMod.stdAddChar (ξ * t)) =
      (p : ℂ) * repeatedRadialSeed p A B (-ξ) := by
  have hc : (fun t => correlation p A B t) =
      fun t => ZMod.dft (repeatedRadialSeed p A B) (-t) :=
    funext (correlation_eq_repeatedRadialSeed_dft p A B)
  calc
    _ = ZMod.dft (fun t => correlation p A B t) (-ξ) := by
      simp only [ZMod.dft_apply, smul_eq_mul, mul_neg, neg_neg]
      apply Finset.sum_congr rfl
      intro t _
      rw [mul_comm, mul_comm t ξ]
    _ = _ := by
      rw [hc, ZMod.dft_comp_neg, ZMod.dft_dft]
      simp only [neg_neg, smul_eq_mul]

/-- A nonzero ray turns the nonlinear torus pullback into a linear
additive-frequency variable. -/
theorem kernel_on_nonzero_ray (α m n z t : ZMod p)
    (hm : m ≠ 0) (hn : n ≠ 0) (hz : z ≠ 0) (ht : t ≠ 0) :
    kernel p α m n t (z * t) =
      correlation p (α * z / m) (α / (n * z ^ 2)) t := by
  rw [kernel, ite_eq_right (not_or.mpr ⟨ht, mul_ne_zero hz ht⟩),
    correlation_normalize_frequency p _ _ t ht]
  congr 1 <;> field_simp

/-- The exact positive radial Fourier transform of a single actual kernel.
The origin was deleted physically, so its full correction is subtracted. -/
theorem kernel_radial_positive_fourier (α m n z ξ : ZMod p)
    (hm : m ≠ 0) (hn : n ≠ 0) (hz : z ≠ 0) :
    (∑ t : (ZMod p)ˣ,
      kernel p α m n (t : ZMod p) (z * (t : ZMod p)) *
        ZMod.stdAddChar (ξ * (t : ZMod p))) =
      (p : ℂ) * repeatedRadialSeed p (α * z / m) (α / (n * z ^ 2)) (-ξ) -
        correlation p (α * z / m) (α / (n * z ^ 2)) 0 := by
  simp_rw [kernel_on_nonzero_ray p α m n z _ hm hn hz (Units.ne_zero _)]
  rw [PrimeGap186.sum_units_eq_sum_sub_zero p
    (fun t : ZMod p => correlation p (α * z / m) (α / (n * z ^ 2)) t *
      ZMod.stdAddChar (ξ * t))]
  simp only [mul_zero, AddChar.map_zero_eq_one, mul_one]
  rw [correlation_positive_fourier_frequency]

/-- For a prime modulus the exact lower-order correction is at most `p`. -/
theorem zeroCorrelationCorrection_le_prime : zeroCorrelationCorrection p ≤ p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hi : (p : ℝ)⁻¹ ≤ (1 : ℝ) / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
  have hi0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hi2 := pow_le_pow_left₀ hi0 hi 2
  unfold zeroCorrelationCorrection
  nlinarith

/-- The zero correlation has norm at most `p`, without any Deligne input. -/
theorem correlation_zero_norm_le_prime (A B : ZMod p) (hA : A ≠ 0) (hB : B ≠ 0) :
    ‖correlation p A B 0‖ ≤ p := by
  have he : correlation p A B 0 =
      (((if A = B then (p : ℝ) else 0) - zeroCorrelationCorrection p : ℝ) : ℂ) := by
    rw [correlation_zero p A B hA hB]
    simp only [zeroCorrelationCorrection, Complex.ofReal_sub, Complex.ofReal_add,
      Complex.ofReal_one, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_pow]
    split_ifs <;> push_cast <;> ring
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  by_cases hab : A = B
  · rw [ite_eq_left hab, abs_of_nonneg (sub_nonneg.mpr (zeroCorrelationCorrection_le_prime p))]
    exact sub_le_self _ (zeroCorrelationCorrection_nonneg p)
  · rw [ite_eq_right hab, zero_sub, abs_neg,
      abs_of_nonneg (zeroCorrelationCorrection_nonneg p)]
    exact zeroCorrelationCorrection_le_prime p

/-- Only the old rank-three pointwise bound is used in bounding the actual
radial seed.  The second baseline correlation estimate is not needed. -/
theorem repeatedRadialSeed_norm_le
    (hkl3 : ∀ t : ZMod p, t ≠ 0 → ‖kl3 p t‖ ≤ 3)
    (A B x : ZMod p) (hA : A ≠ 0) (hB : B ≠ 0) :
    ‖repeatedRadialSeed p A B x‖ ≤ 9 := by
  by_cases hx : x = 0
  · simp [repeatedRadialSeed, hx]
  · rw [repeatedRadialSeed, ite_eq_right hx, norm_mul, norm_star]
    calc
      _ ≤ (3 : ℝ) * 3 := mul_le_mul
        (hkl3 (A * x) (mul_ne_zero hA hx)) (hkl3 (B * x) (mul_ne_zero hB hx))
        (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num

/-- A uniform `10p` bound for a single kernel's radial Fourier transform.
This is stronger than entrywise summation, but is not a four-cycle bound. -/
theorem kernel_radial_positive_fourier_norm_le
    (hkl3 : ∀ t : ZMod p, t ≠ 0 → ‖kl3 p t‖ ≤ 3)
    (α m n z ξ : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0) (hz : z ≠ 0) :
    ‖∑ t : (ZMod p)ˣ,
      kernel p α m n (t : ZMod p) (z * (t : ZMod p)) *
        ZMod.stdAddChar (ξ * (t : ZMod p))‖ ≤ 10 * (p : ℝ) := by
  have hA : α * z / m ≠ 0 := div_ne_zero (mul_ne_zero hα hz) hm
  have hB : α / (n * z ^ 2) ≠ 0 :=
    div_ne_zero hα (mul_ne_zero hn (pow_ne_zero _ hz))
  rw [kernel_radial_positive_fourier p α m n z ξ hm hn hz]
  calc
    _ ≤ ‖(p : ℂ) * repeatedRadialSeed p (α * z / m) (α / (n * z ^ 2)) (-ξ)‖ +
        ‖correlation p (α * z / m) (α / (n * z ^ 2)) 0‖ := norm_sub_le _ _
    _ ≤ (p : ℝ) * 9 + p := by
      apply add_le_add _ (correlation_zero_norm_le_prime p _ _ hA hB)
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left
        (repeatedRadialSeed_norm_le p hkl3 _ _ _ hA hB) (Nat.cast_nonneg p)
    _ = _ := by ring

/-- Explicit connection to the existing baseline input boundary.  This uses
the rank-three bound in its first component and does not invoke public axioms. -/
theorem kernel_radial_positive_fourier_norm_le_baseline_inputs
    (hbase : BaselineLocalInputs)
    (α m n z ξ : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0) (hz : z ≠ 0) :
    ‖∑ t : (ZMod p)ˣ,
      kernel p α m n (t : ZMod p) (z * (t : ZMod p)) *
        ZMod.stdAddChar (ξ * (t : ZMod p))‖ ≤ 10 * (p : ℝ) := by
  apply kernel_radial_positive_fourier_norm_le p _ α m n z ξ hα hm hn hz
  intro t ht
  simpa only [kl3_eq_baseline] using hbase.1 p t ht

#print axioms correlation_eq_repeatedRadialSeed_dft
#print axioms correlation_positive_fourier_frequency
#print axioms kernel_on_nonzero_ray
#print axioms kernel_radial_positive_fourier
#print axioms zeroCorrelationCorrection_le_prime
#print axioms correlation_zero_norm_le_prime
#print axioms repeatedRadialSeed_norm_le
#print axioms kernel_radial_positive_fourier_norm_le
#print axioms kernel_radial_positive_fourier_norm_le_baseline_inputs

end

end PrimeGap182.TypeIII
