import TypeIIIMatrixNorm
import Mathlib.Analysis.MeanInequalities

/-!
# Coefficients depending on both outer variables

Hölder is applied to the genuine matrix norm and the actual Euclidean coefficient norms.
No independence or factorization of the coefficients in the outer variables is required.
-/

open scoped BigOperators Classical Matrix.Norms.L2Operator
open Matrix WithLp

namespace PrimeGap182.TypeIII

noncomputable section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The actual sesquilinear sum with the conjugation convention of the manuscript. -/
def matrixCoefficientSum (A : Matrix m n ℂ) (a : EuclideanSpace ℂ m)
    (b : EuclideanSpace ℂ n) : ℂ :=
  ∑ i, ∑ j, a i * A i j * star (b j)

omit [DecidableEq m] in
/-- Its norm is controlled by the Euclidean operator norm and both Euclidean vector norms. -/
theorem matrixCoefficientSum_norm_le (A : Matrix m n ℂ) (a : EuclideanSpace ℂ m)
    (b : EuclideanSpace ℂ n) :
    ‖matrixCoefficientSum A a b‖ ≤ ‖A‖ * (‖a‖ * ‖b‖) := by
  let v : EuclideanSpace ℂ n := toLp 2 (fun j => star (b j))
  let w : EuclideanSpace ℂ m := toLp 2 (A *ᵥ v)
  have hv : ‖v‖ = ‖b‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [EuclideanSpace.norm_sq_eq, v, norm_star]
  have hw : ‖w‖ ≤ ‖A‖ * ‖b‖ := by
    have hh := Matrix.l2_opNorm_mulVec A v
    simpa only [w, hv, EuclideanSpace.equiv, PiLp.coe_symm_continuousLinearEquiv] using hh
  have heq : matrixCoefficientSum A a b = ∑ i, a i * w i := by
    simp only [matrixCoefficientSum, w, v, Matrix.mulVec, dotProduct,
      Finset.mul_sum, mul_assoc]
  have hc : ‖∑ i, a i * w i‖ ≤ ‖a‖ * ‖w‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    exact row_cauchy (fun i => a i) (fun i => w i)
  calc
    _ = ‖∑ i, a i * w i‖ := congrArg norm heq
    _ ≤ ‖a‖ * ‖w‖ := hc
    _ ≤ ‖a‖ * (‖A‖ * ‖b‖) := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _ = _ := by ring

omit [DecidableEq m] in
/-- The coefficient estimate remains valid for arbitrary dependence on the outer variable. -/
theorem sum_matrixCoefficientSum_le_fourth_moment
    {ρ : Type*} (R : Finset ρ) (A : ρ → Matrix m n ℂ)
    (a : ρ → EuclideanSpace ℂ m) (b : ρ → EuclideanSpace ℂ n) :
    (∑ r ∈ R, ‖matrixCoefficientSum (A r) (a r) (b r)‖) ≤
      (∑ r ∈ R, ‖A r‖ ^ 4) ^ (1 / 4 : ℝ) *
        (∑ r ∈ R, (‖a r‖ * ‖b r‖) ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) := by
  have hpq : Real.HolderConjugate 4 (4 / 3) := by
    apply Real.holderConjugate_iff.mpr
    norm_num
  calc
    _ ≤ ∑ r ∈ R, ‖A r‖ * (‖a r‖ * ‖b r‖) :=
      Finset.sum_le_sum (fun r _ => matrixCoefficientSum_norm_le (A r) (a r) (b r))
    _ ≤ _ := by
      have hh := Real.inner_le_Lp_mul_Lq_of_nonneg R hpq
        (fun r _ => norm_nonneg (A r)) (fun r _ => mul_nonneg (norm_nonneg (a r)) (norm_nonneg (b r)))
      norm_num only [one_div_div, div_one] at hh
      simpa only [Real.rpow_ofNat] using hh

#print axioms matrixCoefficientSum_norm_le
#print axioms sum_matrixCoefficientSum_le_fourth_moment

end

end PrimeGap182.TypeIII
