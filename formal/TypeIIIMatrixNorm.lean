import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!+# The fourth-moment operator step for the Type III matrix

All matrices here are actual finite rectangular complex matrices. Matrix
norms use the Euclidean operator norm, explicitly selected by the scope
below. The fourth moment retains the complex four-cycle before any bounds
are applied. No estimate for individual entries or Fourier modes is assumed.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix ComplexConjugate WithLp

namespace PrimeGap182.TypeIII

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def frobeniusSquare (A : Matrix m n ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

omit [DecidableEq m] [DecidableEq n] in
theorem frobeniusSquare_nonneg (A : Matrix m n ℂ) : 0 ≤ frobeniusSquare A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq n] in
theorem row_cauchy (f g : n → ℂ) :
    ‖∑ j, f j * g j‖ ^ 2 ≤ (∑ j, ‖f j‖ ^ 2) * ∑ j, ‖g j‖ ^ 2 := by
  have h : ‖∑ j, f j * g j‖ ≤ ∑ j, ‖f j‖ * ‖g j‖ := by
    simpa only [norm_mul] using norm_sum_le Finset.univ (fun j => f j * g j)
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖f j‖) (fun j => ‖g j‖))

omit [DecidableEq m] [DecidableEq n] in
theorem mulVec_norm_sq_le (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    ‖(toLp 2 (A *ᵥ x) : EuclideanSpace ℂ m)‖ ^ 2 ≤ frobeniusSquare A * ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ i, (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => row_cauchy (A i) x
    _ = _ := by simp only [frobeniusSquare, Finset.sum_mul]

omit [DecidableEq m] in
theorem operator_norm_le_frobenius (A : Matrix m n ℂ) :
    ‖A‖ ≤ Real.sqrt (frobeniusSquare A) := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  change ‖(toLp 2 (A *ᵥ x) : EuclideanSpace ℂ m)‖ ^ 2 ≤ _
  rw [mul_pow, Real.sq_sqrt (frobeniusSquare_nonneg A)]
  exact mulVec_norm_sq_le A x

def fourthMoment (A : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ i', ‖∑ j, A i j * star (A i' j)‖ ^ 2

omit [DecidableEq m] [DecidableEq n] in
theorem fourthMoment_nonneg (A : Matrix m n ℂ) : 0 ≤ fourthMoment A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq m] [DecidableEq n] in
theorem fourthMoment_eq_frobeniusSquare (A : Matrix m n ℂ) :
    fourthMoment A = frobeniusSquare (A * Aᴴ) := by
  rfl

/-- The coefficient-norm estimate used before frequency completion. -/
theorem operator_norm_fourth_le_fourthMoment (A : Matrix m n ℂ) :
    ‖A‖ ^ 4 ≤ fourthMoment A := by
  have hnorm : ‖A * Aᴴ‖ = ‖A‖ * ‖A‖ := by
    simpa only [conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] using
      Matrix.l2_opNorm_conjTranspose_mul_self Aᴴ
  have h := operator_norm_le_frobenius (A * Aᴴ)
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [Real.sq_sqrt (frobeniusSquare_nonneg _), ← fourthMoment_eq_frobeniusSquare,
    hnorm] at hs
  nlinarith only [hs]

omit [DecidableEq m] [DecidableEq n] in
/-- An exact identity in ℂ, including every off-diagonal four-cycle. -/
theorem fourthMoment_four_cycle (A : Matrix m n ℂ) :
    (fourthMoment A : ℂ) =
      ∑ i, ∑ i', ∑ j, ∑ j',
        A i j * star (A i' j) * A i' j' * star (A i j') := by
  have hnorm (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    rw [← Complex.normSq_eq_norm_sq]
    exact (Complex.mul_conj z).symm
  simp only [fourthMoment, Complex.ofReal_sum]
  simp_rw [hnorm, star_sum, star_mul, star_star,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro i' _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro j' _
  ring

section Masks

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def classProjection (v : n → κ) (c : κ) (x : EuclideanSpace ℂ n) :
    EuclideanSpace ℂ n := toLp 2 (fun j => if v j = c then x j else 0)

def blockMask (u : m → κ) (v : n → κ) (A : Matrix m n ℂ) : Matrix m n ℂ :=
  fun i j => if u i = v j then A i j else 0

omit [DecidableEq m] [DecidableEq n] in
theorem classProjection_norm_partition (v : n → κ) (x : EuclideanSpace ℂ n) :
    (∑ c, ‖classProjection v c x‖ ^ 2) = ‖x‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, classProjection]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ c : κ, ‖(if v j = c then x j else (0 : ℂ))‖ ^ 2) = ‖x j‖ ^ 2
  rw [Finset.sum_eq_single (v j)]
  · simp
  · intro c _ hc
    simp [Ne.symm hc]
  · simp

omit [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype κ] in
theorem blockMask_mulVec_apply (u : m → κ) (v : n → κ)
    (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) (i : m) :
    (blockMask u v A *ᵥ x) i = (A *ᵥ classProjection v (u i) x) i := by
  simp only [Matrix.mulVec, dotProduct, blockMask, classProjection]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : u i = v j
  · simp [h]
  · simp [h, Ne.symm h]

omit [DecidableEq m] in
theorem blockMask_mulVec_norm_sq (u : m → κ) (v : n → κ)
    (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    ‖(toLp 2 (blockMask u v A *ᵥ x) : EuclideanSpace ℂ m)‖ ^ 2 ≤
      ‖A‖ ^ 2 * ‖x‖ ^ 2 := by
  have hpoint (i : m) :
      ‖(blockMask u v A *ᵥ x) i‖ ^ 2 ≤
        ∑ c, ‖(A *ᵥ classProjection v c x) i‖ ^ 2 := by
    rw [blockMask_mulVec_apply]
    exact Finset.single_le_sum
      (f := fun c => ‖(A *ᵥ classProjection v c x) i‖ ^ 2)
      (fun c _ => sq_nonneg _) (Finset.mem_univ (u i))
  calc
    _ = ∑ i, ‖(blockMask u v A *ᵥ x) i‖ ^ 2 := EuclideanSpace.norm_sq_eq _
    _ ≤ ∑ i, ∑ c, ‖(A *ᵥ classProjection v c x) i‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = ∑ c, ‖(toLp 2 (A *ᵥ classProjection v c x) : EuclideanSpace ℂ m)‖ ^ 2 := by
      rw [Finset.sum_comm]
      simp only [EuclideanSpace.norm_sq_eq]
    _ ≤ ∑ c, ‖A‖ ^ 2 * ‖classProjection v c x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro c _
      have h := Matrix.l2_opNorm_mulVec A (classProjection v c x)
      have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
      simpa only [mul_pow, EuclideanSpace.equiv, PiLp.coe_symm_continuousLinearEquiv] using hs
    _ = ‖A‖ ^ 2 * ‖x‖ ^ 2 := by
      rw [← Finset.mul_sum, classProjection_norm_partition]

omit [DecidableEq m] in
/-- Matching row and column classes is a contractive Schur mask for the
Euclidean operator norm, including noninjective class maps. -/
theorem blockMask_operator_norm_le (u : m → κ) (v : n → κ)
    (A : Matrix m n ℂ) : ‖blockMask u v A‖ ≤ ‖A‖ := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun x => ?_
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg A) (norm_nonneg x))).mp
  change ‖(toLp 2 (blockMask u v A *ᵥ x) : EuclideanSpace ℂ m)‖ ^ 2 ≤ _
  rw [mul_pow]
  exact blockMask_mulVec_norm_sq u v A x

end Masks

#print axioms operator_norm_le_frobenius
#print axioms operator_norm_fourth_le_fourthMoment
#print axioms fourthMoment_four_cycle
#print axioms classProjection_norm_partition
#print axioms blockMask_operator_norm_le

end PrimeGap182.TypeIII
