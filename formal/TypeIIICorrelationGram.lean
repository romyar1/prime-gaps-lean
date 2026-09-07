import TypeIIIBaselineBridge
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# Exact Gram matrix of the actual unpulled Type III correlation

The unit-indexed correlation contracts by additive orthogonality.  At a
fixed nonzero additive frequency its Gram matrix is `p² I` minus two
explicit positive rank-one forms.  No Weil, Deligne, or local Fourier
estimate is used.  The indices here are the correlation parameters;
the nonlinear torus substitution in the four-cycle is not discarded.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open scoped BigOperators Classical Matrix.Norms.L2Operator
open Matrix ComplexConjugate WithLp

variable (p : ℕ) [Fact p.Prime]

/-- The exact correction in the unit correlation, as a positive real number. -/
def correlationGramKappa : ℝ := 1 + (p : ℝ)⁻¹ + ((p : ℝ)⁻¹) ^ 2

omit [Fact p.Prime] in
theorem correlationGramKappa_nonneg : 0 ≤ correlationGramKappa p := by
  unfold correlationGramKappa
  positivity

/-- The one-factor unit Fourier sum entering the rank-one correction. -/
def correlationUnitFourier (A c : ZMod p) : ℂ :=
  ∑ h : (ZMod p)ˣ, kl3 p (A * (h : ZMod p)) * ZMod.stdAddChar (c * (h : ZMod p))

/-- A normalized rank-three unit Fourier sum is an ordinary rank-two sum
minus its exact missing-zero contribution. -/
theorem correlationUnitFourier_eval (A c : ZMod p) (hA : A ≠ 0) :
    correlationUnitFourier p A c =
      (if c = 0 then 0 else PrimeGap186.unnormalizedKloosterman2 p (-A / c)) -
        (p : ℂ)⁻¹ := by
  classical
  have hfull :
      (∑ x : ZMod p, kl3 p (A * x) * ZMod.stdAddChar (c * x)) =
        if c = 0 then 0 else PrimeGap186.unnormalizedKloosterman2 p (-A / c) := by
    calc
      _ = ZMod.dft (fun x => PrimeGap186.normalizedKloosterman3 p (A * x)) (-c) := by
        simp only [ZMod.dft_apply, smul_eq_mul, kl3_eq_baseline]
        apply Finset.sum_congr rfl
        intro x _
        rw [mul_comm]
        congr 2
        ring
      _ = _ := by
        rw [PrimeGap186.normalizedKloosterman3_scaled_dft p A (-c) hA]
        simp only [neg_eq_zero, div_neg, neg_div]
  rw [correlationUnitFourier, PrimeGap186.sum_units_eq_sum_sub_zero p
    (fun x : ZMod p => kl3 p (A * x) * ZMod.stdAddChar (c * x)), hfull]
  simp only [mul_zero, kl3_eq_baseline, PrimeGap186.normalizedKloosterman3_zero,
    AddChar.map_zero_eq_one, mul_one]

/-- The existing exact zero-frequency evaluation in Gram-matrix normalization. -/
theorem correlation_zero_eq_gram (A B : ZMod p) (hA : A ≠ 0) (hB : B ≠ 0) :
    correlation p A B 0 =
      (if A = B then (p : ℂ) else 0) - (correlationGramKappa p : ℂ) := by
  rw [correlation_zero p A B hA hB]
  simp only [correlationGramKappa, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_natCast]
  ring

theorem kl3_unit_gram (h h' : (ZMod p)ˣ) :
    (∑ B : (ZMod p)ˣ,
      star (kl3 p ((B : ZMod p) * (h : ZMod p))) *
        kl3 p ((B : ZMod p) * (h' : ZMod p))) =
      (if h = h' then (p : ℂ) else 0) - (correlationGramKappa p : ℂ) := by
  have he :
      (∑ B : (ZMod p)ˣ,
        star (kl3 p ((B : ZMod p) * (h : ZMod p))) *
          kl3 p ((B : ZMod p) * (h' : ZMod p))) =
        correlation p (h' : ZMod p) (h : ZMod p) 0 := by
    simp only [correlation, zero_mul, AddChar.map_zero_eq_one, mul_one]
    apply Finset.sum_congr rfl
    intro B _
    rw [mul_comm (B : ZMod p) (h : ZMod p),
      mul_comm (B : ZMod p) (h' : ZMod p)]
    ring
  rw [he, correlation_zero_eq_gram p _ _ h'.ne_zero h.ne_zero]
  by_cases hh : h = h'
  · simp [hh]
  · have hv : (h' : ZMod p) ≠ (h : ZMod p) := fun hv => hh (Units.ext hv).symm
    simp [hh, hv]

/-- Exact common-column contraction, allowing zero row parameters and
arbitrary additive frequencies. -/
theorem correlation_column_contraction (A A' c d : ZMod p) :
    (∑ B : (ZMod p)ˣ,
      correlation p A (B : ZMod p) c * star (correlation p A' (B : ZMod p) d)) =
      (p : ℂ) * correlation p A A' (c - d) -
        (correlationGramKappa p : ℂ) *
          correlationUnitFourier p A c * star (correlationUnitFourier p A' d) := by
  have hexpand :
      (∑ B : (ZMod p)ˣ,
        correlation p A (B : ZMod p) c * star (correlation p A' (B : ZMod p) d)) =
      ∑ h : (ZMod p)ˣ, ∑ h' : (ZMod p)ˣ,
        (kl3 p (A * (h : ZMod p)) * star (kl3 p (A' * (h' : ZMod p))) *
          ZMod.stdAddChar (c * (h : ZMod p) - d * (h' : ZMod p))) *
        ∑ B : (ZMod p)ˣ,
          star (kl3 p ((B : ZMod p) * (h : ZMod p))) *
            kl3 p ((B : ZMod p) * (h' : ZMod p)) := by
    simp only [correlation, star_sum, star_mul, star_star,
      PrimeGap186.star_stdAddChar, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm_cycle, Finset.sum_comm_cycle, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro h' _
    apply Finset.sum_congr rfl
    intro B _
    simp only [sub_eq_add_neg, AddChar.map_add_eq_mul,
      mul_comm, mul_left_comm, mul_assoc]
  have hdiag :
      (∑ h : (ZMod p)ˣ, ∑ h' : (ZMod p)ˣ,
        (kl3 p (A * (h : ZMod p)) * star (kl3 p (A' * (h' : ZMod p))) *
          ZMod.stdAddChar (c * (h : ZMod p) - d * (h' : ZMod p))) *
          (if h = h' then (p : ℂ) else 0)) =
        (p : ℂ) * correlation p A A' (c - d) := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      correlation, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [show c * (h : ZMod p) - d * (h : ZMod p) =
      (c - d) * (h : ZMod p) by ring]
    ring
  have hrank :
      (∑ h : (ZMod p)ˣ, ∑ h' : (ZMod p)ˣ,
        (kl3 p (A * (h : ZMod p)) * star (kl3 p (A' * (h' : ZMod p))) *
          ZMod.stdAddChar (c * (h : ZMod p) - d * (h' : ZMod p))) *
          (correlationGramKappa p : ℂ)) =
        (correlationGramKappa p : ℂ) *
          correlationUnitFourier p A c * star (correlationUnitFourier p A' d) := by
    simp only [correlationUnitFourier, star_sum, star_mul,
      PrimeGap186.star_stdAddChar, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro h' _
    simp only [sub_eq_add_neg, AddChar.map_add_eq_mul,
      mul_comm, mul_left_comm, mul_assoc]
  rw [hexpand]
  simp_rw [kl3_unit_gram p, mul_sub, Finset.sum_sub_distrib]
  rw [hdiag, hrank]

/-- Scaling both correlation parameters and the additive frequency by the
same nonzero element is a permutation of the summation variable. -/
theorem correlation_common_dilation (A B c s : ZMod p) (hs : s ≠ 0) :
    correlation p (s * A) (s * B) (s * c) = correlation p A B c := by
  unfold correlation
  refine Fintype.sum_equiv (Equiv.mulLeft (Units.mk0 s hs)) _ _ ?_
  intro h
  simp only [Equiv.coe_mulLeft, Units.val_mul, Units.val_mk0,
    mul_comm, mul_left_comm, mul_assoc]

/-- The one-factor Fourier sum has the same simultaneous scaling symmetry. -/
theorem correlationUnitFourier_common_dilation (A c s : ZMod p) (hs : s ≠ 0) :
    correlationUnitFourier p (s * A) (s * c) = correlationUnitFourier p A c := by
  unfold correlationUnitFourier
  refine Fintype.sum_equiv (Equiv.mulLeft (Units.mk0 s hs)) _ _ ?_
  intro h
  simp only [Equiv.coe_mulLeft, Units.val_mul, Units.val_mk0,
    mul_comm, mul_left_comm]

/-- Exact contraction with a nonzero dilation in the second column parameter.
This form has no division and permits arbitrary, including zero, row
parameters and additive frequencies. -/
theorem correlation_dilated_column_contraction (A A' c d β : ZMod p) (hβ : β ≠ 0) :
    (∑ B : (ZMod p)ˣ,
      correlation p A (B : ZMod p) c *
        star (correlation p A' (β * (B : ZMod p)) d)) =
      (p : ℂ) * correlation p (β * A) A' (β * c - d) -
        (correlationGramKappa p : ℂ) *
          correlationUnitFourier p A c * star (correlationUnitFourier p A' d) := by
  have he :
      (∑ B : (ZMod p)ˣ,
        correlation p A (B : ZMod p) c *
          star (correlation p A' (β * (B : ZMod p)) d)) =
      ∑ B : (ZMod p)ˣ,
        correlation p (β * A) (B : ZMod p) (β * c) *
          star (correlation p A' (B : ZMod p) d) := by
    refine Fintype.sum_equiv (Equiv.mulLeft (Units.mk0 β hβ)) _ _ ?_
    intro B
    simp only [Equiv.coe_mulLeft, Units.val_mul, Units.val_mk0]
    rw [correlation_common_dilation p A (B : ZMod p) c β hβ]
  rw [he, correlation_column_contraction,
    correlationUnitFourier_common_dilation p A c β hβ]

/-- The vector appearing in the second rank-one correction to the Gram matrix. -/
def correlationGramVector (A : (ZMod p)ˣ) : ℂ :=
  PrimeGap186.unnormalizedKloosterman2 p (-(A : ZMod p)) - (p : ℂ)⁻¹

/-- Entrywise form of `C C* = p² I - κ(p J + U U*)`, for the actual
correlation matrix on the nonzero parameters. -/
theorem correlation_gram_entry (A A' : (ZMod p)ˣ) :
    (∑ B : (ZMod p)ˣ,
      correlation p (A : ZMod p) (B : ZMod p) 1 *
        star (correlation p (A' : ZMod p) (B : ZMod p) 1)) =
      (if A = A' then (p : ℂ) ^ 2 else 0) -
        (correlationGramKappa p : ℂ) *
          ((p : ℂ) + correlationGramVector p A * star (correlationGramVector p A')) := by
  rw [correlation_column_contraction, sub_self,
    correlation_zero_eq_gram p _ _ A.ne_zero A'.ne_zero,
    correlationUnitFourier_eval p _ 1 A.ne_zero,
    correlationUnitFourier_eval p _ 1 A'.ne_zero]
  simp only [one_ne_zero, ite_false, div_one, correlationGramVector]
  by_cases hAA : A = A'
  · subst A'
    simp only [ite_true]
    ring
  · have hv : (A : ZMod p) ≠ (A' : ZMod p) := fun hv => hAA (Units.ext hv)
    rw [ite_eq_right hAA, ite_eq_right hv]
    ring

/-- The actual correlation, with both matrix indices ranging over units. -/
def correlationUnitMatrix : Matrix (ZMod p)ˣ (ZMod p)ˣ ℂ :=
  fun A B => correlation p (A : ZMod p) (B : ZMod p) 1

/-- The Gram identity as an equality of actual complex matrices. -/
theorem correlation_gram_matrix :
    correlationUnitMatrix p * (correlationUnitMatrix p)ᴴ =
      (p : ℂ) ^ 2 • (1 : Matrix (ZMod p)ˣ (ZMod p)ˣ ℂ) -
      (correlationGramKappa p : ℂ) •
        ((p : ℂ) • Matrix.of (fun (_ _ : (ZMod p)ˣ) => (1 : ℂ)) +
          Matrix.vecMulVec (correlationGramVector p) (fun A => star (correlationGramVector p A))) := by
  ext A A'
  simpa only [correlationUnitMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
    Matrix.of_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
    mul_ite, mul_one, mul_zero] using correlation_gram_entry p A A'

omit [Fact p.Prime] in
theorem gram_complex_norm_sq (z : ℂ) :
    ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  rw [← Complex.normSq_eq_norm_sq]
  exact (Complex.mul_conj z).symm

/-- Exact energy of every complex linear combination of the correlation
rows, including both nonnegative rank-one deductions. -/
theorem correlation_row_energy (v : (ZMod p)ˣ → ℂ) :
    (∑ B : (ZMod p)ˣ,
      ‖∑ A : (ZMod p)ˣ, v A * correlationUnitMatrix p A B‖ ^ 2) =
      (p : ℝ) ^ 2 * ∑ A : (ZMod p)ˣ, ‖v A‖ ^ 2 -
      correlationGramKappa p *
        ((p : ℝ) * ‖∑ A : (ZMod p)ˣ, v A‖ ^ 2 +
          ‖∑ A : (ZMod p)ˣ, v A * correlationGramVector p A‖ ^ 2) := by
  have hexpand :
      (∑ B : (ZMod p)ˣ,
        (∑ A : (ZMod p)ˣ, v A * correlationUnitMatrix p A B) *
          star (∑ A : (ZMod p)ˣ, v A * correlationUnitMatrix p A B)) =
      ∑ A : (ZMod p)ˣ, ∑ A' : (ZMod p)ˣ,
        (v A * star (v A')) *
          ∑ B : (ZMod p)ˣ, correlationUnitMatrix p A B *
            star (correlationUnitMatrix p A' B) := by
    simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm_cycle, Finset.sum_comm_cycle, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro A' _
    apply Finset.sum_congr rfl
    intro B _
    ring
  have hdiag :
      (∑ A : (ZMod p)ˣ, ∑ A' : (ZMod p)ˣ,
        (v A * star (v A')) * (if A = A' then (p : ℂ) ^ 2 else 0)) =
      (p : ℂ) ^ 2 * ∑ A : (ZMod p)ˣ, v A * star (v A) := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    ring
  have hrank :
      (∑ A : (ZMod p)ˣ, ∑ A' : (ZMod p)ˣ,
        (v A * star (v A')) * ((correlationGramKappa p : ℂ) *
          ((p : ℂ) + correlationGramVector p A * star (correlationGramVector p A')))) =
      (correlationGramKappa p : ℂ) *
        ((p : ℂ) * ((∑ A : (ZMod p)ˣ, v A) * star (∑ A : (ZMod p)ˣ, v A)) +
          (∑ A : (ZMod p)ˣ, v A * correlationGramVector p A) *
            star (∑ A : (ZMod p)ˣ, v A * correlationGramVector p A)) := by
    simp only [mul_add, Finset.sum_add_distrib, star_sum, star_mul,
      Finset.mul_sum, Finset.sum_mul]
    congr 1
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro A' _
      ring
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro A' _
      ring
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_add]
  simp_rw [gram_complex_norm_sq]
  simp only [Complex.ofReal_pow, Complex.ofReal_natCast]
  rw [hexpand]
  simp_rw [correlationUnitMatrix, correlation_gram_entry, mul_sub, Finset.sum_sub_distrib]
  rw [hdiag, hrank]

/-- Every row combination has Euclidean energy at most `p²` times its
coefficient energy, with no character-sum estimate. -/
theorem correlation_row_energy_le (v : (ZMod p)ˣ → ℂ) :
    (∑ B : (ZMod p)ˣ,
      ‖∑ A : (ZMod p)ˣ, v A * correlationUnitMatrix p A B‖ ^ 2) ≤
      (p : ℝ) ^ 2 * ∑ A : (ZMod p)ˣ, ‖v A‖ ^ 2 := by
  rw [correlation_row_energy]
  exact sub_le_self _ (mul_nonneg (correlationGramKappa_nonneg p)
    (add_nonneg (mul_nonneg (Nat.cast_nonneg p) (sq_nonneg _)) (sq_nonneg _)))

/-- The actual unit correlation matrix has Euclidean operator norm at most
`p`.  This is not a norm bound for its nonlinear torus pullback. -/
theorem correlationUnitMatrix_norm_le : ‖correlationUnitMatrix p‖ ≤ (p : ℝ) := by
  have hstar : ‖(correlationUnitMatrix p)ᴴ‖ ≤ (p : ℝ) := by
    rw [Matrix.l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg p) fun x => ?_
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg p) (norm_nonneg _))).mp
    change ‖(toLp 2 ((correlationUnitMatrix p)ᴴ *ᵥ x) : EuclideanSpace ℂ (ZMod p)ˣ)‖ ^ 2 ≤ _
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq]
    have he (B : (ZMod p)ˣ) :
        ((correlationUnitMatrix p)ᴴ *ᵥ x) B =
          star (∑ A : (ZMod p)ˣ, star (x A) * correlationUnitMatrix p A B) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
        star_sum, star_mul, star_star]
    simp_rw [he, norm_star]
    simpa only [norm_star] using correlation_row_energy_le p (fun A => star (x A))
  simpa only [Matrix.l2_opNorm_conjTranspose] using hstar

#print axioms correlationGramKappa
#print axioms correlationGramKappa_nonneg
#print axioms correlationUnitFourier
#print axioms correlationUnitFourier_eval
#print axioms correlation_zero_eq_gram
#print axioms kl3_unit_gram
#print axioms correlation_column_contraction
#print axioms correlation_common_dilation
#print axioms correlationUnitFourier_common_dilation
#print axioms correlation_dilated_column_contraction
#print axioms correlationGramVector
#print axioms correlation_gram_entry
#print axioms correlationUnitMatrix
#print axioms correlation_gram_matrix
#print axioms gram_complex_norm_sq
#print axioms correlation_row_energy
#print axioms correlation_row_energy_le
#print axioms correlationUnitMatrix_norm_le

end PrimeGap182.TypeIII
