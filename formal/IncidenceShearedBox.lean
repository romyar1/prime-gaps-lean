import IncidenceWindowMajorant

/-!
# The actual incidence estimate for arbitrary bounded sheared-box weights

The weight need not factor or be smooth. Positivity permits majorization by
the actual compact product plateau, so this includes the smooth compact
weights in the manuscript without a supplied Fourier-envelope hypothesis.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators SchwartzMap FourierTransform ComplexOrder Matrix.Norms.L2Operator

variable {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι]

theorem incidenceIntegerEnergy_summable (R : Matrix (ZMod q × ZMod q) ι ℂ)
    (w : ℤ × ℤ → ℝ) (hw : Summable w) (c : ι → ℂ) :
    Summable (fun z : ℤ × ℤ => w z * ‖(R *ᵥ c) (incidenceIntegerResidue q z)‖ ^ 2) := by
  let B : ℝ := ∑ r : ZMod q × ZMod q, ‖(R *ᵥ c) r‖ ^ 2
  apply (hw.norm.mul_right B).of_norm_bounded
  intro z
  rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact Finset.single_le_sum (fun r _ => sq_nonneg ‖(R *ᵥ c) r‖) (Finset.mem_univ _)

set_option maxHeartbeats 800000 in
/-- A sharp-scale incidence bound for every actual nonnegative bounded
weight supported in the displayed sheared box. -/
theorem incidenceShearedBox_bound (hK4 : AllIncidenceRankFourBounds)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ [NeZero q], Squarefree q →
      ∀ A : ZMod q, IsUnit A → ∀ E₁ E₂ e₀ γ₀ τ L : ℝ,
      0 < E₁ → 0 < E₂ → 0 ≤ L → ∀ w : ℤ × ℤ → ℝ,
      (∀ z, 0 ≤ w z) → (∀ z, w z ≤ L) →
      (∀ z, w z ≠ 0 → |(z.1 : ℝ) - e₀| ≤ E₁ ∧
        |(z.2 : ℝ) - τ * (z.1 : ℝ) - γ₀| ≤ E₂) →
      ∀ c : ZMod q → ℂ,
        (∑' z : ℤ × ℤ, w z *
          ‖(incidenceMatrixMod A *ᵥ c) (incidenceIntegerResidue q z)‖ ^ 2) ≤
          C * L * incidenceWindowScale η q E₁ E₂ * incidenceVectorEnergy c := by
  obtain ⟨f, Lf, hLf, hf, hfone, hfs, hfb⟩ := incidence_exists_plateau
  obtain ⟨C, hC, hwindow⟩ := incidenceCompactProductWindow_bound hK4 f f hf hf
    2 2 Lf Lf (by norm_num) (by norm_num) (le_trans zero_le_one hLf)
    (le_trans zero_le_one hLf) hfs hfs hfb hfb η hη
  refine ⟨C, hC, ?_⟩
  intro q _ hq A hA E₁ E₂ e₀ γ₀ τ L hE₁ hE₂ hL w hw0 hwL hws c
  let W := incidenceScaledProductWeight f f E₁ E₂ e₀ γ₀ τ
  have hW0 (z : ℤ × ℤ) : 0 ≤ W z :=
    incidenceScaledProductWeight_nonneg f f hf hf E₁ E₂ e₀ γ₀ τ z
  have hW := incidenceScaledProductWeight_summable f f hf hf E₁ E₂ e₀ γ₀ τ hE₁ hE₂
  have hdom (z : ℤ × ℤ) : w z ≤ L * W z := by
    by_cases hz : w z = 0
    · rw [hz]
      exact mul_nonneg hL (hW0 z)
    · have hr := hws z hz
      have hf₁ : f (((z.1 : ℝ) - e₀) / E₁) = 1 := hfone _ (by
        rw [abs_div, abs_of_pos hE₁]
        exact (div_le_one hE₁).mpr hr.1)
      have hf₂ : f (((z.2 : ℝ) - τ * (z.1 : ℝ) - γ₀) / E₂) = 1 := hfone _ (by
        rw [abs_div, abs_of_pos hE₂]
        exact (div_le_one hE₂).mpr hr.2)
      simpa only [W, incidenceScaledProductWeight, hf₁, hf₂, Complex.one_re, mul_one] using hwL z
  have hw : Summable w := Summable.of_nonneg_of_le hw0 hdom (hW.mul_left L)
  calc
    _ ≤ ∑' z : ℤ × ℤ, (L * W z) *
        ‖(incidenceMatrixMod A *ᵥ c) (incidenceIntegerResidue q z)‖ ^ 2 :=
      (incidenceIntegerEnergy_summable (incidenceMatrixMod A) w hw c).tsum_le_tsum
        (fun z => mul_le_mul_of_nonneg_right (hdom z) (sq_nonneg _))
        (incidenceIntegerEnergy_summable (incidenceMatrixMod A) (fun z => L * W z)
          (hW.mul_left L) c)
    _ = L * ∑' z : ℤ × ℤ, W z *
        ‖(incidenceMatrixMod A *ᵥ c) (incidenceIntegerResidue q z)‖ ^ 2 := by
      simp only [mul_assoc, tsum_mul_left]
    _ ≤ L * (C * incidenceWindowScale η q E₁ E₂ * incidenceVectorEnergy c) :=
      mul_le_mul_of_nonneg_left (hwindow q hq A hA E₁ E₂ e₀ γ₀ τ hE₁ hE₂ c) hL
    _ = _ := by ring

#print axioms incidenceIntegerEnergy_summable
#print axioms incidenceShearedBox_bound

end PrimeGap182Audit
