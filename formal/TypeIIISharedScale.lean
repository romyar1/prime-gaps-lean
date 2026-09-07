import TypeIIIQuarterRoot

/-! Exact residual gcd powers after the shared matching multiplier. -/

namespace PrimeGap182.TypeIII

noncomputable section

/-- The three surviving gcd powers are exactly `1/2`, `1/4`, and `5/8`. -/
def sharedThreeScale (M R S E : ℝ) : ℝ :=
  M ^ (3 / 4 : ℝ) * S ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) +
    M * S ^ (3 / 4 : ℝ) / R ^ (1 / 2 : ℝ) * E ^ (1 / 4 : ℝ) +
      M * S ^ (3 / 8 : ℝ) * E ^ (5 / 8 : ℝ)

theorem sharedThreeScale_nonneg {M R S E : ℝ}
    (hM : 0 ≤ M) (hR : 0 ≤ R) (hS : 0 ≤ S) (hE : 0 ≤ E) :
    0 ≤ sharedThreeScale M R S E := by unfold sharedThreeScale; positivity

/-- The three residual gcd exponents are obtained by exact algebra, without weakening
the matching cost or the remaining-modulus fourth-moment estimate. -/
theorem mul_matrixThreeScale_eq_sharedThreeScale (M R E P : ℝ)
    (hE : 0 < E) (hP : 0 ≤ P) :
    E * matrixThreeScale M R P = sharedThreeScale M R (E * P) E := by
  have hhalf : E ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) = E := by
    rw [← Real.rpow_add hE]
    norm_num
  have hquarter : E ^ (3 / 4 : ℝ) * E ^ (1 / 4 : ℝ) = E := by
    rw [← Real.rpow_add hE]
    norm_num
  have heighth : E ^ (3 / 8 : ℝ) * E ^ (5 / 8 : ℝ) = E := by
    rw [← Real.rpow_add hE]
    norm_num
  unfold matrixThreeScale sharedThreeScale
  rw [Real.mul_rpow hE.le hP, Real.mul_rpow hE.le hP, Real.mul_rpow hE.le hP]
  calc
    _ = M ^ (3 / 4 : ℝ) * P ^ (1 / 2 : ℝ) *
          (E ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ)) +
        (M * P ^ (3 / 4 : ℝ) / R ^ (1 / 2 : ℝ)) *
          (E ^ (3 / 4 : ℝ) * E ^ (1 / 4 : ℝ)) +
        M * P ^ (3 / 8 : ℝ) * (E ^ (3 / 8 : ℝ) * E ^ (5 / 8 : ℝ)) := by
      rw [hhalf, hquarter, heighth]
      ring
    _ = _ := by ring

#print axioms mul_matrixThreeScale_eq_sharedThreeScale

end

end PrimeGap182.TypeIII
