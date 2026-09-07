import TypeIIICoefficientNorms
import TypeIIIMatrixEstimate

/-! Finite coefficient averaging with the actual normalized fourth moment. -/

open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace PrimeGap182.TypeIII

noncomputable section

/-- The first moment is bounded by the normalized fourth moment at every nonempty finite set. -/
theorem sum_le_normalized_fourth_mean {ρ : Type*} (S : Finset ρ) (hS : 0 < S.card)
    (f : ρ → ℝ) (hf : ∀ r ∈ S, 0 ≤ f r) :
    (∑ r ∈ S, f r) ≤ (S.card : ℝ) *
      ((∑ r ∈ S, (f r) ^ 4) / (S.card : ℝ)) ^ (1 / 4 : ℝ) := by
  have hpq : Real.HolderConjugate 4 (4 / 3) := by
    apply Real.holderConjugate_iff.mpr
    norm_num
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg S hpq hf
    (fun (_ : ρ) (_ : _ ∈ S) => show (0 : ℝ) ≤ 1 by norm_num)
  norm_num only [mul_one, Real.rpow_ofNat, Real.one_rpow, Finset.sum_const, nsmul_eq_mul,
    one_div_div, div_one] at hh
  have hN : (0 : ℝ) < S.card := by exact_mod_cast hS
  have hF : 0 ≤ ∑ r ∈ S, (f r) ^ 4 :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have heq : (S.card : ℝ) * ((∑ r ∈ S, (f r) ^ 4) / (S.card : ℝ)) ^ (1 / 4 : ℝ) =
      (∑ r ∈ S, (f r) ^ 4) ^ (1 / 4 : ℝ) * (S.card : ℝ) ^ (3 / 4 : ℝ) := by
    rw [Real.div_rpow hF hN.le]
    rw [show (3 / 4 : ℝ) = 1 - 1 / 4 by norm_num, Real.rpow_sub hN, Real.rpow_one]
    ring
  rw [heq]
  exact hh

/-- Operator comparison and the actual coefficient norms can be applied before averaging.
The coefficients may depend arbitrarily on the outer index. -/
theorem sum_matrixCoefficients_le_comparison_mean
    {ρ m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (S : Finset ρ) (hS : 0 < S.card) (K A : ρ → Matrix m n ℂ)
    (a : ρ → EuclideanSpace ℂ m) (b : ρ → EuclideanSpace ℂ n)
    {L W : ℝ} (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hA : ∀ r ∈ S, ‖A r‖ ≤ L * ‖K r‖)
    (hab : ∀ r ∈ S, ‖a r‖ * ‖b r‖ ≤ W) :
    (∑ r ∈ S, ‖matrixCoefficientSum (A r) (a r) (b r)‖) ≤
      L * W * (S.card : ℝ) *
        ((∑ r ∈ S, ‖K r‖ ^ 4) / (S.card : ℝ)) ^ (1 / 4 : ℝ) := by
  have hpoint (r : ρ) (hr : r ∈ S) :
      ‖matrixCoefficientSum (A r) (a r) (b r)‖ ≤ (L * W) * ‖K r‖ := by
    calc
      _ ≤ ‖A r‖ * (‖a r‖ * ‖b r‖) := matrixCoefficientSum_norm_le _ _ _
      _ ≤ (L * ‖K r‖) * W :=
        mul_le_mul (hA r hr) (hab r hr)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg hL (norm_nonneg _))
      _ = _ := by ring
  calc
    _ ≤ ∑ r ∈ S, (L * W) * ‖K r‖ := Finset.sum_le_sum hpoint
    _ = (L * W) * ∑ r ∈ S, ‖K r‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ (L * W) * ((S.card : ℝ) *
        ((∑ r ∈ S, ‖K r‖ ^ 4) / (S.card : ℝ)) ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_le_normalized_fourth_mean S hS
        (fun r => ‖K r‖) (fun _ _ => norm_nonneg _)) (mul_nonneg hL hW)
    _ = _ := by ring

#print axioms sum_le_normalized_fourth_mean
#print axioms sum_matrixCoefficients_le_comparison_mean

end

end PrimeGap182.TypeIII
