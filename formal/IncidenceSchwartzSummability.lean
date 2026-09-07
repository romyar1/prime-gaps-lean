import IncidencePoisson

/-!
# Absolute summability for sheared products of actual Schwartz functions

This module supplies both exchanges of sums needed by iterated Poisson
summation. The estimates are derived from actual Schwartz seminorm bounds.
-/

noncomputable section

namespace PrimeGap182Audit

open scoped BigOperators SchwartzMap FourierTransform

def incidenceShearedDecay (a b τ α β : ℝ) (z : ℤ × ℤ) : ℝ :=
  incidenceDecay a ((z.1 : ℝ) + α + τ * ((z.2 : ℝ) + β)) *
    incidenceDecay b ((z.2 : ℝ) + β)

theorem incidenceShearedDecay_summable (a b τ α β : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Summable (incidenceShearedDecay a b τ α β) := by
  let F (z : ℤ × ℤ) := incidenceShearedDecay a b τ α β (z.2, z.1)
  have hrows (ν : ℤ) : Summable (fun h : ℤ => F (ν, h)) := by
    have hs := (incidenceDecay_shift_bounds a (α + τ * ((ν : ℝ) + β)) ha).1
    simpa only [F, incidenceShearedDecay, add_assoc] using
      hs.mul_right (incidenceDecay b ((ν : ℝ) + β))
  have hpoint (ν : ℤ) : (∑' h : ℤ, F (ν, h)) ≤
      (2 + 4 / a) * incidenceDecay b ((ν : ℝ) + β) := by
    have hs := (incidenceDecay_shift_bounds a (α + τ * ((ν : ℝ) + β)) ha).2
    simpa only [F, incidenceShearedDecay, add_assoc, tsum_mul_right] using
      mul_le_mul_of_nonneg_right hs (incidenceDecay_nonneg _ _)
  have hsumrows : Summable (fun ν : ℤ => ∑' h : ℤ, F (ν, h)) :=
    Summable.of_nonneg_of_le
      (fun ν => tsum_nonneg (fun h => mul_nonneg (incidenceDecay_nonneg _ _)
        (incidenceDecay_nonneg _ _)))
      hpoint ((incidenceDecay_shift_bounds b β hb).1.mul_left (2 + 4 / a))
  have hF : Summable F := (summable_prod_of_nonneg
    (fun z => mul_nonneg (incidenceDecay_nonneg _ _) (incidenceDecay_nonneg _ _))).mpr
      ⟨hrows, hsumrows⟩
  exact (Equiv.prodComm ℤ ℤ).summable_iff.mp hF

/-- A genuine Schwartz function admits a reciprocal-square envelope. -/
theorem incidenceSchwartz_decay_bound (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖f x‖ ≤ C * incidenceDecay 1 x := by
  obtain ⟨C₀, hC₀, h₀⟩ := f.decay 0 0
  obtain ⟨C₂, hC₂, h₂⟩ := f.decay 2 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at h₀
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h₂
  refine ⟨2 * (C₀ + C₂), by positivity, ?_⟩
  intro x
  have hquad : (1 + |x|) ^ 2 ≤ 2 * (1 + |x| ^ 2) := by nlinarith [sq_nonneg (|x| - 1)]
  have hw : (1 + |x|) ^ 2 * ‖f x‖ ≤ 2 * (C₀ + C₂) := by
    calc
      _ ≤ (2 * (1 + |x| ^ 2)) * ‖f x‖ :=
        mul_le_mul_of_nonneg_right hquad (norm_nonneg _)
      _ ≤ 2 * (C₀ + C₂) := by nlinarith [h₀ x, h₂ x]
  calc
    _ ≤ 2 * (C₀ + C₂) / (1 + |x|) ^ 2 :=
      (le_div_iff₀ (by positivity : 0 < (1 + |x|) ^ 2)).mpr (by simpa only [mul_comm] using hw)
    _ = _ := by simp only [incidenceDecay, one_mul, div_eq_mul_inv, inv_pow]

/-- Both the physical and Fourier sides of the sheared Poisson identity
are absolutely summable; translations and shear may be arbitrary reals. -/
theorem incidenceSchwartz_shearedProduct_norm_summable (f g : 𝓢(ℝ, ℂ)) (τ α β : ℝ) :
    Summable (fun z : ℤ × ℤ =>
      ‖f ((z.1 : ℝ) + α + τ * ((z.2 : ℝ) + β)) * g ((z.2 : ℝ) + β)‖) := by
  obtain ⟨C, hC, hf⟩ := incidenceSchwartz_decay_bound f
  obtain ⟨D, hD, hg⟩ := incidenceSchwartz_decay_bound g
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((incidenceShearedDecay_summable 1 1 τ α β zero_lt_one zero_lt_one).mul_left (C * D))
  intro z
  rw [norm_mul]
  calc
    _ ≤ (C * incidenceDecay 1 ((z.1 : ℝ) + α + τ * ((z.2 : ℝ) + β))) *
        (D * incidenceDecay 1 ((z.2 : ℝ) + β)) :=
      mul_le_mul (hf _) (hg _) (norm_nonneg _)
        (mul_nonneg hC.le (incidenceDecay_nonneg _ _))
    _ = _ := by
      unfold incidenceShearedDecay
      ring

/-- Modulating a sheared product by arbitrary real characters preserves
the absolute summability just proved. -/
theorem incidenceSchwartz_shearedProduct_phase_summable (f g : 𝓢(ℝ, ℂ))
    (τ α β : ℝ) (phase : ℤ × ℤ → ℝ) :
    Summable (fun z : ℤ × ℤ =>
      f ((z.1 : ℝ) + α + τ * ((z.2 : ℝ) + β)) * g ((z.2 : ℝ) + β) *
        incidenceRealChar (phase z)) := by
  apply Summable.of_norm
  simpa only [norm_mul, incidenceRealChar_norm, mul_one] using
    incidenceSchwartz_shearedProduct_norm_summable f g τ α β

#print axioms incidenceShearedDecay_summable
#print axioms incidenceSchwartz_decay_bound
#print axioms incidenceSchwartz_shearedProduct_norm_summable
#print axioms incidenceSchwartz_shearedProduct_phase_summable

end PrimeGap182Audit
