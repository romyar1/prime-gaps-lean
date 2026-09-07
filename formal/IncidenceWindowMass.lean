import IncidenceCompactProfile
import IncidenceShearMass

/-!
# The unrestricted mass of actual nonnegative scaled product profiles
-/

noncomputable section

namespace PrimeGap182Audit

open scoped BigOperators SchwartzMap FourierTransform ComplexOrder

def incidenceScaledProductWeight (f g : 𝓢(ℝ, ℂ))
    (E₁ E₂ e₀ γ₀ τ : ℝ) (z : ℤ × ℤ) : ℝ :=
  (f (((z.1 : ℝ) - e₀) / E₁)).re *
    (g (((z.2 : ℝ) - τ * (z.1 : ℝ) - γ₀) / E₂)).re

theorem incidenceScaledProductWeight_nonneg (f g : 𝓢(ℝ, ℂ))
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (E₁ E₂ e₀ γ₀ τ : ℝ) (z : ℤ × ℤ) :
    0 ≤ incidenceScaledProductWeight f g E₁ E₂ e₀ γ₀ τ z :=
  mul_nonneg (Complex.nonneg_iff.mp (hf _)).1 (Complex.nonneg_iff.mp (hg _)).1

theorem incidenceScaledProductWeight_cast (f g : 𝓢(ℝ, ℂ))
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (E₁ E₂ e₀ γ₀ τ : ℝ) (hE₁ : E₁ ≠ 0) (hE₂ : E₂ ≠ 0) (z : ℤ × ℤ) :
    (incidenceScaledProductWeight f g E₁ E₂ e₀ γ₀ τ z : ℂ) =
      incidenceScaledSchwartz f E₁ e₀ hE₁ (z.1 : ℝ) *
        incidenceScaledSchwartz g E₂ γ₀ hE₂ ((z.2 : ℝ) - τ * (z.1 : ℝ)) := by
  simp only [incidenceScaledSchwartz_apply, incidenceScaledProductWeight]
  have hfi (x : ℝ) : (f x).im = 0 := (Complex.nonneg_iff.mp (hf x)).2.symm
  have hgi (x : ℝ) : (g x).im = 0 := (Complex.nonneg_iff.mp (hg x)).2.symm
  apply Complex.ext <;> simp only [Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, hfi, hgi, mul_zero, zero_mul, sub_zero, add_zero]

theorem incidenceScaledProductWeight_summable (f g : 𝓢(ℝ, ℂ))
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (E₁ E₂ e₀ γ₀ τ : ℝ) (hE₁ : 0 < E₁) (hE₂ : 0 < E₂) :
    Summable (incidenceScaledProductWeight f g E₁ E₂ e₀ γ₀ τ) :=
  incidenceSchwartzWeight_summable (incidenceScaledSchwartz f E₁ e₀ hE₁.ne')
    (incidenceScaledSchwartz g E₂ γ₀ hE₂.ne') τ _
      (incidenceScaledProductWeight_cast f g hf hg E₁ E₂ e₀ γ₀ τ hE₁.ne' hE₂.ne')

set_option maxHeartbeats 800000 in
/-- Uniformity in both positive scales, both real centers, and the real shear. -/
theorem incidenceScaledProductWeight_mass_bound (f g : 𝓢(ℝ, ℂ))
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    ∃ C : ℝ, 0 < C ∧ ∀ E₁ E₂ e₀ γ₀ τ : ℝ, 0 < E₁ → 0 < E₂ →
      (∑' z : ℤ × ℤ, incidenceScaledProductWeight f g E₁ E₂ e₀ γ₀ τ z) ≤
        C * (2 + 4 * E₁) * (2 + 4 * E₂) := by
  obtain ⟨C, hC, hcf⟩ := incidenceScaledSchwartz_spatial_bound f
  obtain ⟨D, hD, hdg⟩ := incidenceScaledSchwartz_spatial_bound g
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro E₁ E₂ e₀ γ₀ τ hE₁ hE₂
  let F (z : ℤ × ℤ) : ℝ :=
    incidenceShearedDecay (1 / E₂) (1 / E₁) (-τ) (-γ₀ - τ * e₀) (-e₀) (z.2, z.1)
  have hFz (z : ℤ × ℤ) : F z =
      incidenceDecay (1 / E₂) ((z.2 : ℝ) - τ * (z.1 : ℝ) - γ₀) *
        incidenceDecay (1 / E₁) ((z.1 : ℝ) - e₀) := by
    dsimp [F, incidenceShearedDecay]
    congr 1
    congr 1
    ring
  have hsG := incidenceShearedDecay_summable (1 / E₂) (1 / E₁)
    (-τ) (-γ₀ - τ * e₀) (-e₀) (one_div_pos.mpr hE₂) (one_div_pos.mpr hE₁)
  have hsF : Summable F := hsG.comp_injective (Equiv.prodComm ℤ ℤ).injective
  have hpoint (z : ℤ × ℤ) :
      incidenceScaledProductWeight f g E₁ E₂ e₀ γ₀ τ z ≤ (C * D) * F z := by
    have hw0 := incidenceScaledProductWeight_nonneg f g hf hg E₁ E₂ e₀ γ₀ τ z
    calc
      _ = ‖incidenceScaledSchwartz f E₁ e₀ hE₁.ne' (z.1 : ℝ) *
          incidenceScaledSchwartz g E₂ γ₀ hE₂.ne' ((z.2 : ℝ) - τ * (z.1 : ℝ))‖ := by
        rw [← incidenceScaledProductWeight_cast f g hf hg E₁ E₂ e₀ γ₀ τ hE₁.ne' hE₂.ne',
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
      _ ≤ (C * incidenceDecay (1 / E₁) ((z.1 : ℝ) - e₀)) *
          (D * incidenceDecay (1 / E₂) ((z.2 : ℝ) - τ * (z.1 : ℝ) - γ₀)) := by
        rw [norm_mul]
        exact mul_le_mul (hcf E₁ e₀ hE₁ _) (hdg E₂ γ₀ hE₂ _) (norm_nonneg _)
          (mul_nonneg hC.le (incidenceDecay_nonneg _ _))
      _ = _ := by rw [hFz]; ring
  calc
    _ ≤ ∑' z : ℤ × ℤ, (C * D) * F z :=
      (incidenceScaledProductWeight_summable f g hf hg E₁ E₂ e₀ γ₀ τ hE₁ hE₂).tsum_le_tsum
        hpoint (hsF.mul_left (C * D))
    _ = (C * D) * ∑' z : ℤ × ℤ,
        incidenceShearedDecay (1 / E₂) (1 / E₁) (-τ) (-γ₀ - τ * e₀) (-e₀) z := by
      rw [tsum_mul_left]
      congr 1
      exact (Equiv.prodComm ℤ ℤ).tsum_eq
        (incidenceShearedDecay (1 / E₂) (1 / E₁) (-τ) (-γ₀ - τ * e₀) (-e₀))
    _ ≤ (C * D) * ((2 + 4 / (1 / E₂)) * (2 + 4 / (1 / E₁))) :=
      mul_le_mul_of_nonneg_left
        (incidenceShearedDecay_mass_le _ _ _ _ _ (one_div_pos.mpr hE₂) (one_div_pos.mpr hE₁))
        (mul_nonneg hC.le hD.le)
    _ = _ := by field_simp [hE₁.ne', hE₂.ne']

#print axioms incidenceScaledProductWeight_cast
#print axioms incidenceScaledProductWeight_summable
#print axioms incidenceScaledProductWeight_mass_bound

end PrimeGap182Audit
