import TypeIIIMatrixNorm
import TypeIIIBaselineBridge
import TypeIIISubpower

/-!
# The actual zero-frequency local factors as contractive matching-block multipliers

The exact local correlation formula is proved in the baseline bridge. Its equality mask
is implemented as orthogonal row/column block matching on the genuine Euclidean matrix
norm. No pointwise nonzero-frequency Deligne estimate is used here.
-/

open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A real affine combination of the matching-block mask and the identity mask. -/
def affineMatchingMultiplier {κ : Type*} (u : m → κ) (v : n → κ)
    (a b : ℝ) (A : Matrix m n ℂ) : Matrix m n ℂ :=
  fun i j => ((if u i = v j then (a : ℂ) else 0) - b) * A i j

omit [DecidableEq m] in
/-- Its actual operator norm has the expected total-variation bound. -/
theorem affineMatchingMultiplier_norm_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    (u : m → κ) (v : n → κ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (A : Matrix m n ℂ) : ‖affineMatchingMultiplier u v a b A‖ ≤ (a + b) * ‖A‖ := by
  have heq : affineMatchingMultiplier u v a b A =
      (a : ℂ) • blockMask u v A - (b : ℂ) • A := by
    ext i j
    simp only [affineMatchingMultiplier, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, blockMask]
    split_ifs <;> ring
  rw [heq]
  calc
    _ ≤ ‖(a : ℂ) • blockMask u v A‖ + ‖(b : ℂ) • A‖ := norm_sub_le _ _
    _ = a * ‖blockMask u v A‖ + b * ‖A‖ := by
      rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * ‖A‖ + b * ‖A‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (blockMask_operator_norm_le u v A) ha) le_rfl
    _ = _ := by ring

/-- The exact lower-order correction in the local zero-frequency formula. -/
def zeroCorrelationCorrection (p : ℕ) : ℝ := 1 + (p : ℝ)⁻¹ + ((p : ℝ)⁻¹) ^ 2

theorem zeroCorrelationCorrection_nonneg (p : ℕ) : 0 ≤ zeroCorrelationCorrection p := by
  unfold zeroCorrelationCorrection
  positivity

theorem zeroCorrelationCorrection_le_three (p : ℕ) (hp : 1 ≤ p) :
    zeroCorrelationCorrection p ≤ 3 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hinv : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1
  have hi0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
  unfold zeroCorrelationCorrection
  nlinarith

/-- Multiplication by the actual local zero-frequency correlation. -/
def zeroCorrelationMultiplier (p : ℕ) [Fact p.Prime]
    (u : m → ZMod p) (v : n → ZMod p) (A : Matrix m n ℂ) : Matrix m n ℂ :=
  fun i j => correlation p (u i) (v j) 0 * A i j

omit [DecidableEq m] in
/-- The correction and matching-block cost of the actual local zero-frequency factor. -/
theorem zeroCorrelationMultiplier_norm_le (p : ℕ) [Fact p.Prime]
    (u : m → ZMod p) (v : n → ZMod p) (hu : ∀ i, u i ≠ 0) (hv : ∀ j, v j ≠ 0)
    (A : Matrix m n ℂ) :
    ‖zeroCorrelationMultiplier p u v A‖ ≤ ((p : ℝ) + zeroCorrelationCorrection p) * ‖A‖ := by
  have heq : zeroCorrelationMultiplier p u v A =
      affineMatchingMultiplier u v p (zeroCorrelationCorrection p) A := by
    ext i j
    rw [zeroCorrelationMultiplier, correlation_zero p (u i) (v j) (hu i) (hv j)]
    simp only [affineMatchingMultiplier, zeroCorrelationCorrection, Complex.ofReal_add,
      Complex.ofReal_one, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_pow]
    ring
  rw [heq]
  exact affineMatchingMultiplier_norm_le u v (Nat.cast_nonneg p)
    (zeroCorrelationCorrection_nonneg p) A

omit [DecidableEq m] in
theorem zeroCorrelationMultiplier_norm_le_four_mul (p : ℕ) [Fact p.Prime]
    (u : m → ZMod p) (v : n → ZMod p) (hu : ∀ i, u i ≠ 0) (hv : ∀ j, v j ≠ 0)
    (A : Matrix m n ℂ) : ‖zeroCorrelationMultiplier p u v A‖ ≤ 4 * p * ‖A‖ := by
  have hp : 1 ≤ p := NeZero.one_le
  apply (zeroCorrelationMultiplier_norm_le p u v hu hv A).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg A)
  have hh := zeroCorrelationCorrection_le_three p hp
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  linarith

/-- The product of actual local zero-frequency correlation multipliers. -/
def zeroCorrelationProduct {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, Fact (q i).Prime]
    (u : ∀ t, m → ZMod (q t)) (v : ∀ t, n → ZMod (q t)) (A : Matrix m n ℂ) : Matrix m n ℂ :=
  fun i j => (∏ t, correlation (q t) (u t i) (v t j) 0) * A i j

omit [DecidableEq m] in
/-- All zero-frequency local factors cost at most `4^ω * e` on operator norm. -/
theorem zeroCorrelationProduct_norm_le {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, Fact (q i).Prime]
    (u : ∀ t, m → ZMod (q t)) (v : ∀ t, n → ZMod (q t))
    (hu : ∀ t i, u t i ≠ 0) (hv : ∀ t j, v t j ≠ 0) (A : Matrix m n ℂ) :
    ‖zeroCorrelationProduct q u v A‖ ≤
      (4 : ℝ) ^ Fintype.card ι * ((∏ t, q t : ℕ) : ℝ) * ‖A‖ := by
  let T (S : Finset ι) : Matrix m n ℂ :=
    fun i j => (∏ t ∈ S, correlation (q t) (u t i) (v t j) 0) * A i j
  have hfin (S : Finset ι) :
      ‖T S‖ ≤ (∏ t ∈ S, 4 * (q t : ℝ)) * ‖A‖ := by
    induction S using Finset.induction_on with
    | empty => simp only [T, Finset.prod_empty, one_mul, le_refl]
    | @insert t S ht ih =>
      rw [Finset.prod_insert ht]
      have heq : T (insert t S) = zeroCorrelationMultiplier (q t) (u t) (v t) (T S) := by
        ext i j
        simp only [T, Finset.prod_insert ht, zeroCorrelationMultiplier]
        ring
      rw [heq]
      apply (zeroCorrelationMultiplier_norm_le_four_mul (q t) (u t) (v t) (hu t) (hv t) _).trans
      have hh := mul_le_mul_of_nonneg_left ih (show 0 ≤ 4 * (q t : ℝ) by positivity)
      simpa only [mul_assoc] using hh
  have hh := hfin Finset.univ
  have heq : T Finset.univ = zeroCorrelationProduct q u v A := rfl
  rw [heq] at hh
  simpa only [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Nat.cast_prod] using hh

/-- Uniform subpower absorption for the primes at which the shared frequency vanishes.
The constant is independent of the matrix dimensions and of the residue labels. -/
theorem exists_zeroCorrelationProduct_subpower {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ι m n : Type} [Fintype ι] [Fintype m] [Fintype n]
      [DecidableEq n] (q : ι → ℕ) [∀ t, Fact (q t).Prime] [NeZero (∏ t, q t)],
      Pairwise (fun i j => (q i).Coprime (q j)) →
      ∀ (u : ∀ t, m → ZMod (q t)) (v : ∀ t, n → ZMod (q t)),
      (∀ t i, u t i ≠ 0) → (∀ t j, v t j ≠ 0) → ∀ A : Matrix m n ℂ,
      ‖zeroCorrelationProduct q u v A‖ ≤
        K * ((∏ t, q t : ℕ) : ℝ) ^ (1 + ε) * ‖A‖ := by
  obtain ⟨K, hK, hbound⟩ :=
    PrimeGap186.exists_primeFactors_power_bound (show (1 : ℝ) ≤ 4 by norm_num) hε
  refine ⟨K, hK, ?_⟩
  intro ι m n _ _ _ _ q _ _ hcp u v hu hv A
  have hp : 0 < ((∏ t, q t : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (∏ t, q t))
  have hpow : (4 : ℝ) ^ Fintype.card ι ≤ K * ((∏ t, q t : ℕ) : ℝ) ^ ε :=
    (pow_le_pow_right₀ (by norm_num) (card_prime_family_le_primeFactors q hcp)).trans
      (hbound _ (NeZero.ne _))
  calc
    _ ≤ (4 : ℝ) ^ Fintype.card ι * ((∏ t, q t : ℕ) : ℝ) * ‖A‖ :=
      zeroCorrelationProduct_norm_le q u v hu hv A
    _ ≤ (K * ((∏ t, q t : ℕ) : ℝ) ^ ε) * ((∏ t, q t : ℕ) : ℝ) * ‖A‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpow hp.le) (norm_nonneg A)
    _ = _ := by rw [Real.rpow_add hp, Real.rpow_one]; ring

#print axioms affineMatchingMultiplier_norm_le
#print axioms zeroCorrelationMultiplier_norm_le
#print axioms zeroCorrelationProduct_norm_le
#print axioms exists_zeroCorrelationProduct_subpower

end

end PrimeGap182.TypeIII
