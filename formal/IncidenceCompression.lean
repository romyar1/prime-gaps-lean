import IncidenceSquareModes
import TypeIIIMatrixNorm
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Explicit finite compressions and pole correction bounds

These are actual diagonal masks and permutation matrices. Their contraction
bounds are derived from Mathlib's Euclidean matrix norm. The coarse pole bound
uses the independently proved finite Frobenius/Cauchy estimate.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem incidence_norm_mul3_le (A B C : Matrix ι ι ℂ) :
    ‖A * B * C‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

theorem incidence_matrix_norm_le_card (M : Matrix ι ι ℂ)
    (hM : ∀ i j, ‖M i j‖ ≤ 1) : ‖M‖ ≤ (Fintype.card ι : ℝ) := by
  have hF : PrimeGap182.TypeIII.frobeniusSquare M ≤ (Fintype.card ι : ℝ) ^ 2 := by
    unfold PrimeGap182.TypeIII.frobeniusSquare
    calc
      _ ≤ ∑ _i : ι, ∑ _j : ι, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        simpa using pow_le_pow_left₀ (norm_nonneg _) (hM i j) 2
      _ = _ := by simp [pow_two]
  exact (PrimeGap182.TypeIII.operator_norm_le_frobenius M).trans
    ((Real.sqrt_le_sqrt hF).trans_eq (Real.sqrt_sq (Nat.cast_nonneg _)))

theorem incidence_permuted_norm_le (M : Matrix ι ι ℂ) (σ : Equiv.Perm ι) :
    ‖M.submatrix σ σ‖ ≤ ‖M‖ := by
  have heq : σ.permMatrix ℂ * M * (σ⁻¹).permMatrix ℂ = M.submatrix σ σ := by
    change σ.toPEquiv.toMatrix * M * σ.symm.toPEquiv.toMatrix = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    rfl
  rw [← heq]
  calc
    _ ≤ ‖σ.permMatrix ℂ‖ * ‖M‖ * ‖(σ⁻¹).permMatrix ℂ‖ := incidence_norm_mul3_le _ _ _
    _ ≤ 1 * ‖M‖ * 1 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (Matrix.permMatrix_l2_opNorm_le (𝕜 := ℂ) σ) (norm_nonneg _))
        (Matrix.permMatrix_l2_opNorm_le (𝕜 := ℂ) (σ⁻¹)) (norm_nonneg _) (by positivity)
    _ = _ := by ring

def incidenceDeleteIndex (a : ι) : Matrix ι ι ℂ :=
  diagonal (fun i => if i = a then 0 else 1)

def incidencePointProjection (a : ι) : Matrix ι ι ℂ :=
  diagonal (fun i => if i = a then 1 else 0)

def incidencePoleMatrix (a : ι) : Matrix ι ι ℂ :=
  fun i j => if (i = a ∧ j ≠ a) ∨ (j = a ∧ i ≠ a) then 1 else 0

theorem incidenceDeleteIndex_norm_le (a : ι) : ‖incidenceDeleteIndex a‖ ≤ 1 := by
  rw [incidenceDeleteIndex, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  by_cases h : i = a <;> simp [h]

theorem incidencePointProjection_norm_le (a : ι) : ‖incidencePointProjection a‖ ≤ 1 := by
  rw [incidencePointProjection, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  by_cases h : i = a <;> simp [h]

theorem incidencePoleMatrix_norm_le (a : ι) :
    ‖incidencePoleMatrix a‖ ≤ (Fintype.card ι : ℝ) := by
  apply incidence_matrix_norm_le_card
  intro i j
  dsimp [incidencePoleMatrix]
  split_ifs <;> norm_num

theorem incidenceDeleteIndex_mul_apply (a : ι) (M : Matrix ι ι ℂ) (i j : ι) :
    (incidenceDeleteIndex a * M * incidenceDeleteIndex a) i j =
      if i = a ∨ j = a then 0 else M i j := by
  by_cases hi : i = a <;> by_cases hj : j = a <;>
    simp [incidenceDeleteIndex, Matrix.diagonal_mul, Matrix.mul_diagonal, hi, hj]

theorem incidence_compressed_norm_le (a : ι) (M : Matrix ι ι ℂ) :
    ‖incidenceDeleteIndex a * M * incidenceDeleteIndex a‖ ≤ ‖M‖ := by
  calc
    _ ≤ ‖incidenceDeleteIndex a‖ * ‖M‖ * ‖incidenceDeleteIndex a‖ := incidence_norm_mul3_le _ _ _
    _ ≤ 1 * ‖M‖ * 1 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (incidenceDeleteIndex_norm_le a) (norm_nonneg _))
        (incidenceDeleteIndex_norm_le a) (norm_nonneg _) (by positivity)
    _ = _ := by ring

#print axioms incidence_matrix_norm_le_card
#print axioms incidence_permuted_norm_le
#print axioms incidence_compressed_norm_le
#print axioms incidencePoleMatrix_norm_le

end PrimeGap182Audit
