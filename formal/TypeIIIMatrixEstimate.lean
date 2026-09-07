import TypeIIIMatrixFourthMoment
import TypeIIIMatrixPowerArithmetic
import TypeIIISubpower
import TypeIIIQuarterRoot

/-!
# The Type III matrix estimate, uniform in the actual squarefree modulus

Every finite sum, interval, residue, matrix norm, and arithmetic averaging step is explicit.
Only `LocalFourierHypothesis`, the new local finite-field proposition, remains an input.
The fixed cutoff is removed by trivial finite sums, without using the public Deligne axioms.
-/

open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace PrimeGap182.TypeIII

noncomputable section

universe u

/-- The explicit three-term fourth-moment bound for the actual squarefree kernel matrix. -/
theorem integerKernelMatrix_three_term_bound
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) [∀ i, Fact (q i).Prime] [NeZero (∏ i, q i)]
    (hcp : Pairwise (fun i j => (q i).Coprime (q j))) {C : ℝ} (hC : 0 ≤ C) {D : ℕ}
    (hlocal : LocalFourierHypothesis C D 0)
    (α : ∀ i, ZMod (q i)) (hα : ∀ i, α i ≠ 0)
    (A B Ah Ak : ℤ) (M R : ℕ) :
    (∑ x ∈ Finset.range R, ∑ y ∈ Finset.range R,
      ‖integerKernelMatrix q α A B M M ((Ah + x : ℤ) : ZMod (∏ i, q i))
        ((Ak + y : ℤ) : ZMod (∏ i, q i))‖ ^ 4) ≤
      (C ^ Fintype.card ι * maskComplexity D (Fintype.card ι)) *
        64 * ((∏ i, q i).divisors.card : ℝ) ^ 2 *
          (1 + Real.log ((∏ i, q i : ℕ) : ℝ)) ^ 2 *
        ((R : ℝ) ^ 2 * (M : ℝ) ^ 3 * ((∏ i, q i : ℕ) : ℝ) ^ 2 +
          (M : ℝ) ^ 4 * ((∏ i, q i : ℕ) : ℝ) ^ 3 +
            (R : ℝ) ^ 2 * (M : ℝ) ^ 4 * ((∏ i, q i : ℕ) : ℝ) *
              Real.sqrt ((∏ i, q i : ℕ) : ℝ)) := by
  have hs : (1 : ℝ) ≤ (∏ i, q i : ℕ) := by exact_mod_cast (NeZero.one_le : 1 ≤ ∏ i, q i)
  have hT : (1 : ℝ) ≤ (∏ i, q i).divisors.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (NeZero.ne _)⟩
  have hh := integerKernelMatrix_fourth_moment_bound q hcp hC hlocal α hα A B Ah Ak M M R R
  have hp : 0 ≤ C ^ Fintype.card ι * maskComplexity D (Fintype.card ι) := by
    unfold maskComplexity
    positivity
  have hpow := mul_le_mul_of_nonneg_left (matrix_raw_bound_le_three_terms hs hT M R) hp
  apply hh.trans
  convert hpow using 1
  ring

/-- Uniform subpower fourth-moment bound. The constant precedes the modulus, interval
locations, and dimensions, as required by the analytic application. -/
theorem LocalFourierHypothesis.exists_matrix_fourth_moment_bound
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
        (q : ι → ℕ) [∀ i, Fact (q i).Prime] [NeZero (∏ i, q i)],
        Pairwise (fun i j => (q i).Coprime (q j)) →
        ∀ (α : ∀ i, ZMod (q i)), (∀ i, α i ≠ 0) →
        ∀ (A B Ah Ak : ℤ) (M R : ℕ),
        (∑ x ∈ Finset.range R, ∑ y ∈ Finset.range R,
          ‖integerKernelMatrix q α A B M M ((Ah + x : ℤ) : ZMod (∏ i, q i))
            ((Ak + y : ℤ) : ZMod (∏ i, q i))‖ ^ 4) ≤
          K * ((∏ i, q i : ℕ) : ℝ) ^ ε *
            ((R : ℝ) ^ 2 * (M : ℝ) ^ 3 * ((∏ i, q i : ℕ) : ℝ) ^ 2 +
              (M : ℝ) ^ 4 * ((∏ i, q i : ℕ) : ℝ) ^ 3 +
                (R : ℝ) ^ 2 * (M : ℝ) ^ 4 * ((∏ i, q i : ℕ) : ℝ) *
                  Real.sqrt ((∏ i, q i : ℕ) : ℝ)) := by
  let C' := trivialEnlargedLocalConstant C p₀
  have hC' : 0 ≤ C' := trivialEnlargedLocalConstant_nonneg hC p₀
  have hall : LocalFourierHypothesis C' D 0 := hlocal.remove_small_primes_trivial hC
  let a := max 1 (C' * (5 * ((max D 1 : ℕ) : ℝ) ^ 2))
  obtain ⟨K, hK, hb⟩ := exists_primeFactor_divisor_log_subpower
    (show 1 ≤ a from le_max_left _ _) hε
  refine ⟨K, hK, ?_⟩
  intro ι _ _ q _ _ hcp α hα A B Ah Ak M R
  have hh := integerKernelMatrix_three_term_bound q hcp hC' hall α hα A B Ah Ak M R
  have hmask := family_maskConstant_le_primeFactor_power q hcp hC' D
  have hrest : 0 ≤ 64 * ((∏ i, q i).divisors.card : ℝ) ^ 2 *
      (1 + Real.log ((∏ i, q i : ℕ) : ℝ)) ^ 2 := by positivity
  have hfac := mul_le_mul_of_nonneg_right hmask hrest
  have hfac' : (C' ^ Fintype.card ι * maskComplexity D (Fintype.card ι)) *
      64 * ((∏ i, q i).divisors.card : ℝ) ^ 2 *
        (1 + Real.log ((∏ i, q i : ℕ) : ℝ)) ^ 2 ≤ K * ((∏ i, q i : ℕ) : ℝ) ^ ε := by
    apply (show _ ≤ a ^ (∏ i, q i).primeFactors.card * 64 *
        ((∏ i, q i).divisors.card : ℝ) ^ 2 *
          (1 + Real.log ((∏ i, q i : ℕ) : ℝ)) ^ 2 from by
      simpa only [a, mul_assoc] using hfac).trans
    exact hb _ (NeZero.ne _)
  exact hh.trans (mul_le_mul_of_nonneg_right hfac' (by positivity))

#print axioms integerKernelMatrix_three_term_bound
#print axioms LocalFourierHypothesis.exists_matrix_fourth_moment_bound

/-- The manuscript's matrix proposition, for the actual squarefree kernel and actual
Euclidean operator norm. All constants are uniform in the modulus and interval locations;
the only unproved input is the explicitly quantified local finite-field proposition. -/
theorem LocalFourierHypothesis.exists_matrix_estimate
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
        (q : ι → ℕ) [∀ i, Fact (q i).Prime] [NeZero (∏ i, q i)],
        Pairwise (fun i j => (q i).Coprime (q j)) →
        ∀ (α : ∀ i, ZMod (q i)), (∀ i, α i ≠ 0) →
        ∀ (A B Ah Ak : ℤ) (M R : ℕ), 0 < R →
        ((∑ x ∈ Finset.range R, ∑ y ∈ Finset.range R,
          ‖integerKernelMatrix q α A B M M ((Ah + x : ℤ) : ZMod (∏ i, q i))
            ((Ak + y : ℤ) : ZMod (∏ i, q i))‖ ^ 4) / (R : ℝ) ^ 2) ^ (1 / 4 : ℝ) ≤
          K * ((∏ i, q i : ℕ) : ℝ) ^ ε *
            matrixThreeScale M R ((∏ i, q i : ℕ) : ℝ) := by
  obtain ⟨K, hK, hbound⟩ := hlocal.exists_matrix_fourth_moment_bound hC
    (show 0 < 4 * ε by positivity)
  refine ⟨K ^ (1 / 4 : ℝ), Real.rpow_pos_of_pos hK _, ?_⟩
  intro ι _ _ q _ _ hcp α hα A B Ah Ak M R hR
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hs0 : (0 : ℝ) ≤ (∏ i, q i : ℕ) := Nat.cast_nonneg _
  have hh := normalized_quarter_root_bound
    (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)))
    (show 0 ≤ K * ((∏ i, q i : ℕ) : ℝ) ^ (4 * ε) by positivity)
    (Nat.cast_nonneg M) hR' hs0 (hbound q hcp α hα A B Ah Ak M R)
  rw [Real.mul_rpow hK.le (Real.rpow_nonneg hs0 _), ← Real.rpow_mul hs0] at hh
  simpa only [show (4 * ε) * (1 / 4 : ℝ) = ε by ring] using hh

#print axioms LocalFourierHypothesis.exists_matrix_estimate

end

end PrimeGap182.TypeIII
