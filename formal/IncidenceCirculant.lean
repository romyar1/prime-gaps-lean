import IncidenceCompletion
import PrimeGaps186
import Mathlib.LinearAlgebra.Matrix.Circulant

/-!
# Euclidean norm of an actual finite circulant

The unnormalized character matrix is proved to have Gram matrix `p I`.
Consequently the norm bound below follows from the actual finite Fourier
eigenvalues; no diagonalization or contraction assertion is supplied as a
hypothesis. The only imported 186 ingredients used here are exact finite
character identities.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {p : ℕ} [Fact p.Prime]

def incidenceFourierMatrix : Matrix (ZMod p) (ZMod p) ℂ :=
  fun x s => ZMod.stdAddChar (s * x)

private theorem incidence_char_star (t : ZMod p) :
    star (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
  have hp : 0 < ringChar (ZMod p) := by
    simpa only [ringChar.eq (ZMod p) p] using (Fact.out : p.Prime).pos
  exact AddChar.starComp_apply hp t

theorem incidenceFourierMatrix_star_mul :
    (incidenceFourierMatrix (p := p))ᴴ * incidenceFourierMatrix =
      (p : ℂ) • (1 : Matrix (ZMod p) (ZMod p) ℂ) := by
  ext s t
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, incidenceFourierMatrix,
    incidence_char_star, ← AddChar.map_add_eq_mul]
  have heq (x : ZMod p) : -(s * x) + t * x = (t - s) * x := by ring
  simp_rw [heq]
  rw [PrimeGap186.stdAddChar_sum]
  by_cases h : s = t <;> simp [h, sub_eq_zero, eq_comm]

theorem incidenceFourierMatrix_mul_star :
    incidenceFourierMatrix * (incidenceFourierMatrix (p := p))ᴴ =
      (p : ℂ) • (1 : Matrix (ZMod p) (ZMod p) ℂ) := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, incidenceFourierMatrix,
    incidence_char_star, ← AddChar.map_add_eq_mul]
  have heq (s : ZMod p) : s * x + -(s * y) = (x - y) * s := by ring
  simp_rw [heq]
  rw [PrimeGap186.stdAddChar_sum]
  by_cases h : x = y <;> simp [h, sub_eq_zero]

theorem incidenceFourierMatrix_norm_sq :
    ‖incidenceFourierMatrix (p := p)‖ ^ 2 = (p : ℝ) := by
  rw [pow_two, ← Matrix.l2_opNorm_conjTranspose_mul_self,
    incidenceFourierMatrix_star_mul, norm_smul, norm_one, mul_one, Complex.norm_natCast]

/-- Actual Fourier diagonalization, with the negative-sign DFT convention. -/
theorem incidenceCirculant_mul_fourier (v : ZMod p → ℂ) :
    Matrix.circulant v * incidenceFourierMatrix =
      incidenceFourierMatrix * diagonal (ZMod.dft v) := by
  ext x s
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simp only [Matrix.circulant_apply, incidenceFourierMatrix, ZMod.dft_apply,
    smul_eq_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.subLeft x) _ _ ?_
  intro y
  simp only [Equiv.subLeft_apply]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul,
    show s * x + -((x - y) * s) = s * y by ring]
  exact mul_comm _ _

theorem incidenceCirculant_factorization (v : ZMod p → ℂ) :
    Matrix.circulant v = (p : ℂ)⁻¹ •
      (incidenceFourierMatrix * diagonal (ZMod.dft v) *
        (incidenceFourierMatrix (p := p))ᴴ) := by
  rw [← incidenceCirculant_mul_fourier, Matrix.mul_assoc,
    incidenceFourierMatrix_mul_star, Matrix.mul_smul, Matrix.mul_one,
    smul_smul, inv_mul_cancel₀ (NeZero.ne _), one_smul]

/-- The Euclidean operator norm is controlled by the actual Fourier eigenvalues. -/
theorem incidenceCirculant_norm_le (v : ZMod p → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hv : ∀ s, ‖ZMod.dft v s‖ ≤ L) :
    ‖Matrix.circulant v‖ ≤ L := by
  have hdiag : ‖(diagonal (ZMod.dft v) : Matrix (ZMod p) (ZMod p) ℂ)‖ ≤ L := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hL).mpr hv
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  calc
    _ = (p : ℝ)⁻¹ *
        ‖incidenceFourierMatrix * diagonal (ZMod.dft v) *
          (incidenceFourierMatrix (p := p))ᴴ‖ := by
      rw [incidenceCirculant_factorization, norm_smul, norm_inv, Complex.norm_natCast]
    _ ≤ (p : ℝ)⁻¹ *
        ((‖incidenceFourierMatrix (p := p)‖ * L) * ‖incidenceFourierMatrix (p := p)‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hp.le)
      calc
        _ ≤ ‖incidenceFourierMatrix * diagonal (ZMod.dft v)‖ *
            ‖(incidenceFourierMatrix (p := p))ᴴ‖ := norm_mul_le _ _
        _ ≤ (‖incidenceFourierMatrix (p := p)‖ * L) *
            ‖incidenceFourierMatrix (p := p)‖ := by
          rw [Matrix.l2_opNorm_conjTranspose]
          exact mul_le_mul_of_nonneg_right
            ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hdiag (norm_nonneg _)))
            (norm_nonneg _)
    _ = L := by
      calc
        _ = (p : ℝ)⁻¹ * (‖incidenceFourierMatrix (p := p)‖ ^ 2 * L) := by ring
        _ = L := by rw [incidenceFourierMatrix_norm_sq, ← mul_assoc,
          inv_mul_cancel₀ hp.ne', one_mul]

#print axioms incidenceFourierMatrix_star_mul
#print axioms incidenceFourierMatrix_mul_star
#print axioms incidenceFourierMatrix_norm_sq
#print axioms incidenceCirculant_mul_fourier
#print axioms incidenceCirculant_factorization
#print axioms incidenceCirculant_norm_le

end PrimeGap182Audit
