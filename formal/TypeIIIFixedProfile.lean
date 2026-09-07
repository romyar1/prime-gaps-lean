import TypeIIIResidualProfile

/-! A genuine smooth nonnegative cutoff and its exact real-to-complex derivative bounds. -/

open scoped ContDiff

namespace PrimeGap182.TypeIII

noncomputable section

theorem realProfile_complex_control (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (T L : ℝ) (hsupport : Function.support ψ ⊆ Set.Icc (-T) T)
    (hbound : ∀ t : ℝ, ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L) :
    ContDiff ℝ ∞ (fun t => (ψ t : ℂ)) ∧
      Function.support (fun t => (ψ t : ℂ)) ⊆ Set.Icc (-T) T ∧
      ∀ t : ℝ, ‖(ψ t : ℂ)‖ ≤ L ∧ ‖deriv (fun t => (ψ t : ℂ)) t‖ ≤ L ∧
        ‖deriv (deriv (fun t => (ψ t : ℂ))) t‖ ≤ L := by
  have hψ₂ : ContDiff ℝ 2 ψ := hψ.of_le (by simp)
  have hd₁ : deriv (fun t => (ψ t : ℂ)) = fun t => Complex.ofReal (deriv ψ t) := by
    funext t
    exact ((hψ₂.differentiable (by norm_num) t).hasDerivAt.ofReal_comp).deriv
  have hd₂ : deriv (deriv (fun t => (ψ t : ℂ))) = fun t => Complex.ofReal (deriv (deriv ψ) t) := by
    rw [hd₁]
    funext t
    exact ((hψ₂.differentiable_deriv_two t).hasDerivAt.ofReal_comp).deriv
  refine ⟨Complex.ofRealCLM.contDiff.comp hψ, ?_, ?_⟩
  · intro t ht
    apply hsupport
    change ψ t ≠ 0
    intro he
    exact ht (by simp only [he, Complex.ofReal_zero])
  · intro t
    rw [hd₂, hd₁]
    simpa only [Complex.norm_real] using hbound t

/-- A fixed smooth bump supplies all the majorant conditions used in the Cauchy square. -/
theorem exists_typeIII_smooth_majorant : ∃ (L : ℝ) (ψ : ℝ → ℝ),
    1 ≤ L ∧ ContDiff ℝ ∞ ψ ∧
    (∀ t : ℝ, 0 ≤ ψ t) ∧
    (∀ t ∈ Set.Icc (-1 : ℝ) 1, ψ t = 1) ∧
    Function.support ψ ⊆ Set.Icc (-2 : ℝ) 2 ∧
    (∀ t : ℝ, ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L) := by
  let f : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  have hf : ContDiff ℝ ∞ (fun t : ℝ => f t) := f.contDiff
  have hf₁ : ContDiff ℝ ∞ (deriv (fun t : ℝ => f t)) := (contDiff_infty_iff_deriv.mp hf).2
  obtain ⟨B₁, hB₁⟩ := f.hasCompactSupport.deriv.exists_bound_of_continuous hf₁.continuous
  obtain ⟨B₂, hB₂⟩ := f.hasCompactSupport.deriv.deriv.exists_bound_of_continuous
    (hf₁.continuous_deriv (by simp))
  refine ⟨max 1 (max B₁ B₂), (fun t : ℝ => f t), le_max_left _ _, hf,
    (fun t => f.nonneg), ?_, ?_, ?_⟩
  · intro t ht
    apply f.one_of_mem_closedBall
    simpa only [Real.closedBall_zero_eq_Icc] using ht
  · change Function.support f ⊆ Set.Icc (-2 : ℝ) 2
    rw [f.support_eq, Real.ball_zero_eq_Ioo]
    exact Set.Ioo_subset_Icc_self
  · intro t
    refine ⟨?_, (hB₁ t).trans ((le_max_left _ _).trans (le_max_right _ _)),
      (hB₂ t).trans ((le_max_right _ _).trans (le_max_right _ _))⟩
    rw [Real.norm_of_nonneg f.nonneg]
    exact f.le_one.trans (le_max_left _ _)

#print axioms realProfile_complex_control
#print axioms exists_typeIII_smooth_majorant

end

end PrimeGap182.TypeIII
