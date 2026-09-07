import TypeIIIZeroSchur

/-!
# Cubic matching masks on complete matrix intervals

The matching labels may be zero and may repeat. This allows one to keep the entire
row/column intervals while imposing the original unit restrictions in the coefficient
vectors. The proof uses matching-block compression, never a pointwise matrix-entry bound.
-/

open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

theorem affineMatchingMultiplier_prime_norm_le (p : ℕ) [Fact p.Prime]
    (u : m → ZMod p) (v : n → ZMod p) (A : Matrix m n ℂ) :
    ‖affineMatchingMultiplier u v p (zeroCorrelationCorrection p) A‖ ≤ 4 * p * ‖A‖ := by
  apply (affineMatchingMultiplier_norm_le u v (Nat.cast_nonneg p)
    (zeroCorrelationCorrection_nonneg p) A).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg A)
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (NeZero.one_le : 1 ≤ p)
  have hc := zeroCorrelationCorrection_le_three p NeZero.one_le
  linarith

/-- The product of the exact prime matching multipliers. It is defined on all rows,
including rows excluded later by the arithmetic coefficient masks. -/
def primeMatchingProduct {ι : Type*} [Fintype ι] (q : ι → ℕ)
    [∀ t, Fact (q t).Prime] (u : ∀ t, m → ZMod (q t)) (v : ∀ t, n → ZMod (q t))
    (A : Matrix m n ℂ) : Matrix m n ℂ :=
  fun i j => (∏ t, ((if u t i = v t j then (q t : ℂ) else 0) -
    (zeroCorrelationCorrection (q t) : ℂ))) * A i j

theorem primeMatchingProduct_norm_le {ι : Type*} [Fintype ι] (q : ι → ℕ)
    [∀ t, Fact (q t).Prime] (u : ∀ t, m → ZMod (q t)) (v : ∀ t, n → ZMod (q t))
    (A : Matrix m n ℂ) :
    ‖primeMatchingProduct q u v A‖ ≤
      (4 : ℝ) ^ Fintype.card ι * ((∏ t, q t : ℕ) : ℝ) * ‖A‖ := by
  let T (S : Finset ι) : Matrix m n ℂ :=
    fun i j => (∏ t ∈ S, ((if u t i = v t j then (q t : ℂ) else 0) -
      (zeroCorrelationCorrection (q t) : ℂ))) * A i j
  have hfin (S : Finset ι) : ‖T S‖ ≤ (∏ t ∈ S, 4 * (q t : ℝ)) * ‖A‖ := by
    induction S using Finset.induction_on with
    | empty => simp only [T, Finset.prod_empty, one_mul, le_refl]
    | @insert t S ht ih =>
      rw [Finset.prod_insert ht]
      have heq : T (insert t S) =
          affineMatchingMultiplier (u t) (v t) (q t) (zeroCorrelationCorrection (q t)) (T S) := by
        ext i j
        simp only [T, affineMatchingMultiplier, Finset.prod_insert ht, Complex.ofReal_natCast]
        ring
      rw [heq]
      apply (affineMatchingMultiplier_prime_norm_le (q t) (u t) (v t) (T S)).trans
      have hh := mul_le_mul_of_nonneg_left ih (show 0 ≤ 4 * (q t : ℝ) by positivity)
      simpa only [mul_assoc] using hh
  have hh := hfin Finset.univ
  have heq : T Finset.univ = primeMatchingProduct q u v A := rfl
  rw [heq] at hh
  simpa only [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Nat.cast_prod] using hh

/-- The matching product has uniform cost `e^(1+ε)` without any unit condition on its labels. -/
theorem exists_primeMatchingProduct_subpower {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ι m n : Type} [Fintype ι] [Fintype m] [Fintype n]
      [DecidableEq n] (q : ι → ℕ) [∀ t, Fact (q t).Prime] [NeZero (∏ t, q t)],
      Pairwise (fun i j => (q i).Coprime (q j)) →
      ∀ (u : ∀ t, m → ZMod (q t)) (v : ∀ t, n → ZMod (q t)) (A : Matrix m n ℂ),
      ‖primeMatchingProduct q u v A‖ ≤
        K * ((∏ t, q t : ℕ) : ℝ) ^ (1 + ε) * ‖A‖ := by
  obtain ⟨K, hK, hbound⟩ :=
    PrimeGap186.exists_primeFactors_power_bound (show (1 : ℝ) ≤ 4 by norm_num) hε
  refine ⟨K, hK, ?_⟩
  intro ι m n _ _ _ _ q _ _ hcp u v A
  have hp : 0 < ((∏ t, q t : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (∏ t, q t))
  have hpow : (4 : ℝ) ^ Fintype.card ι ≤ K * ((∏ t, q t : ℕ) : ℝ) ^ ε :=
    (pow_le_pow_right₀ (by norm_num) (card_prime_family_le_primeFactors q hcp)).trans
      (hbound _ (NeZero.ne _))
  calc
    _ ≤ (4 : ℝ) ^ Fintype.card ι * ((∏ t, q t : ℕ) : ℝ) * ‖A‖ :=
      primeMatchingProduct_norm_le q u v A
    _ ≤ (K * ((∏ t, q t : ℕ) : ℝ) ^ ε) * ((∏ t, q t : ℕ) : ℝ) * ‖A‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpow hp.le) (norm_nonneg A)
    _ = _ := by rw [Real.rpow_add hp, Real.rpow_one]; ring

#print axioms affineMatchingMultiplier_prime_norm_le
#print axioms primeMatchingProduct_norm_le
#print axioms exists_primeMatchingProduct_subpower

end

end PrimeGap182.TypeIII
