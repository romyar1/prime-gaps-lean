import IncidenceWindowUniform

/-!
# A genuine nonnegative compact Schwartz majorant

The plateau and derivative bounds here are proved for an actual smooth bump.
They will majorize every bounded nonnegative lattice weight in a sheared box.
-/

noncomputable section

namespace PrimeGap182Audit

open scoped BigOperators SchwartzMap FourierTransform ComplexOrder ContDiff

theorem incidence_exists_plateau : ∃ f : 𝓢(ℝ, ℂ), ∃ L : ℝ,
    1 ≤ L ∧ (∀ x, 0 ≤ f x) ∧ (∀ x : ℝ, |x| ≤ 1 → f x = 1) ∧
    Function.support f ⊆ Set.Icc (-2 : ℝ) 2 ∧
    (∀ x : ℝ, ‖f x‖ ≤ L ∧ ‖deriv f x‖ ≤ L ∧ ‖deriv (deriv f) x‖ ≤ L) := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let bc : ℝ → ℂ := fun x => (b x : ℂ)
  have hc : HasCompactSupport bc := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hs : ContDiff ℝ ∞ bc := Complex.ofRealCLM.contDiff.comp b.contDiff
  let f : 𝓢(ℝ, ℂ) := hc.toSchwartzMap hs
  have hf (x : ℝ) : f x = (b x : ℂ) := rfl
  have hd : ContDiff ℝ ∞ (deriv bc) := (contDiff_infty_iff_deriv.mp hs).2
  obtain ⟨B₁, hB₁⟩ := hc.deriv.exists_bound_of_continuous hd.continuous
  obtain ⟨B₂, hB₂⟩ := hc.deriv.deriv.exists_bound_of_continuous
    (hd.continuous_deriv (by simp))
  refine ⟨f, max 1 (max B₁ B₂), le_max_left _ _, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hf]
    exact Complex.nonneg_iff.mpr ⟨b.nonneg, rfl⟩
  · intro x hx
    have ho : b x = 1 := b.one_of_mem_closedBall (by
      simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hx)
    rw [hf, ho, Complex.ofReal_one]
  · intro x hx
    have hxb : b x ≠ 0 := by
      intro hz
      apply hx
      rw [hf, hz, Complex.ofReal_zero]
    have hxball : x ∈ Metric.ball (0 : ℝ) 2 := by
      exact (b.support_eq ▸ hxb)
    exact Set.Ioo_subset_Icc_self (by simpa only [Real.ball_zero_eq_Ioo] using hxball)
  · intro x
    refine ⟨?_, (hB₁ x).trans ((le_max_left _ _).trans (le_max_right _ _)),
      (hB₂ x).trans ((le_max_right _ _).trans (le_max_right _ _))⟩
    rw [hf, Complex.norm_real, Real.norm_of_nonneg b.nonneg]
    exact b.le_one.trans (le_max_left _ _)

#print axioms incidence_exists_plateau

end PrimeGap182Audit
