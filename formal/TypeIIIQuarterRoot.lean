import TypeIIIMatrixPowerArithmetic
import Mathlib.Analysis.MeanInequalitiesPow

/-! Taking the actual normalized fourth root in the Type III matrix estimate. -/

namespace PrimeGap182.TypeIII

noncomputable section

/-- The three powers in the manuscript's matrix proposition. -/
def matrixThreeScale (M R S : ℝ) : ℝ :=
  M ^ (3 / 4 : ℝ) * S ^ (1 / 2 : ℝ) +
    M * S ^ (3 / 4 : ℝ) / R ^ (1 / 2 : ℝ) + M * S ^ (3 / 8 : ℝ)

theorem matrixThreeScale_nonneg {M R S : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    0 ≤ matrixThreeScale M R S := by unfold matrixThreeScale; positivity

/-- The sum of the three normalized monomials has the required quarter-root bound. -/
theorem matrix_three_monomials_quarter_root
    {M R S : ℝ} (hM : 0 ≤ M) (hR : 0 < R) (hS : 0 ≤ S) :
    (M ^ 3 * S ^ 2 + M ^ 4 * S ^ 3 / R ^ 2 + M ^ 4 * S * Real.sqrt S) ^ (1 / 4 : ℝ) ≤
      matrixThreeScale M R S := by
  have h₁ : (M ^ 3 * S ^ 2) ^ (1 / 4 : ℝ) =
      M ^ (3 / 4 : ℝ) * S ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast_mul hM, ← Real.rpow_natCast_mul hS]
    norm_num
  have h₂ : (M ^ 4 * S ^ 3 / R ^ 2) ^ (1 / 4 : ℝ) =
      M * S ^ (3 / 4 : ℝ) / R ^ (1 / 2 : ℝ) := by
    rw [Real.div_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast_mul hM, ← Real.rpow_natCast_mul hS,
      ← Real.rpow_natCast_mul hR.le]
    norm_num
  have h₃ : (M ^ 4 * S * Real.sqrt S) ^ (1 / 4 : ℝ) =
      M * S ^ (3 / 8 : ℝ) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) hS, ← Real.rpow_natCast_mul hM,
      Real.sqrt_eq_rpow, ← Real.rpow_mul hS]
    norm_num
    rw [mul_assoc, ← Real.rpow_add' hS]
    · norm_num
    · norm_num
  calc
    _ ≤ (M ^ 3 * S ^ 2 + M ^ 4 * S ^ 3 / R ^ 2) ^ (1 / 4 : ℝ) +
        (M ^ 4 * S * Real.sqrt S) ^ (1 / 4 : ℝ) :=
      Real.rpow_add_le_add_rpow (by positivity) (by positivity) (by norm_num) (by norm_num)
    _ ≤ ((M ^ 3 * S ^ 2) ^ (1 / 4 : ℝ) + (M ^ 4 * S ^ 3 / R ^ 2) ^ (1 / 4 : ℝ)) +
        (M ^ 4 * S * Real.sqrt S) ^ (1 / 4 : ℝ) := by
      exact add_le_add_left
        (Real.rpow_add_le_add_rpow (by positivity) (by positivity) (by norm_num) (by norm_num)) _
    _ = _ := by rw [h₁, h₂, h₃]; rfl

/-- The normalized fourth-moment estimate, with every fractional exponent explicit. -/
theorem normalized_quarter_root_bound
    {F C M R S : ℝ} (hF : 0 ≤ F) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hR : 0 < R) (hS : 0 ≤ S)
    (hbound : F ≤ C * (R ^ 2 * M ^ 3 * S ^ 2 + M ^ 4 * S ^ 3 +
      R ^ 2 * M ^ 4 * S * Real.sqrt S)) :
    (F / R ^ 2) ^ (1 / 4 : ℝ) ≤ C ^ (1 / 4 : ℝ) * matrixThreeScale M R S := by
  have hdiv := div_le_div_of_nonneg_right hbound (sq_nonneg R)
  have heq : C * (R ^ 2 * M ^ 3 * S ^ 2 + M ^ 4 * S ^ 3 +
      R ^ 2 * M ^ 4 * S * Real.sqrt S) / R ^ 2 =
      C * (M ^ 3 * S ^ 2 + M ^ 4 * S ^ 3 / R ^ 2 + M ^ 4 * S * Real.sqrt S) := by
    field_simp
  rw [heq] at hdiv
  calc
    _ ≤ (C * (M ^ 3 * S ^ 2 + M ^ 4 * S ^ 3 / R ^ 2 + M ^ 4 * S * Real.sqrt S)) ^
        (1 / 4 : ℝ) := Real.rpow_le_rpow (div_nonneg hF (sq_nonneg R)) hdiv (by norm_num)
    _ = C ^ (1 / 4 : ℝ) *
        (M ^ 3 * S ^ 2 + M ^ 4 * S ^ 3 / R ^ 2 + M ^ 4 * S * Real.sqrt S) ^ (1 / 4 : ℝ) :=
      Real.mul_rpow hC (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (matrix_three_monomials_quarter_root hM hR hS)
      (Real.rpow_nonneg hC _)

#print axioms matrix_three_monomials_quarter_root
#print axioms normalized_quarter_root_bound

end

end PrimeGap182.TypeIII
