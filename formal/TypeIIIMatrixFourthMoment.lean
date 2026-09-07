import TypeIIIIntegerKernel
import TypeIIIMatrixNorm
import TypeIIIFourIndexSum

/-!
# The actual squarefree-kernel matrix fourth moment

The signed outer sum of each four-cycle is retained before applying completion.  Equal
integer rows and columns use the repeated-index branch of the new local proposition.
The other cycles use its finite-exceptional branch and the proved integer discriminant
average. No old pair-correlation bound is needed for this matrix theorem.
-/

open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Averaging the actual Euclidean matrix norm retains the signed sum of each four-cycle. -/
theorem sum_operator_norm_fourth_le_cycle_sums
    {ρ m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (R : Finset ρ) (K : ρ → Matrix m n ℂ) :
    (∑ r ∈ R, ‖K r‖ ^ 4) ≤
      ∑ i, ∑ i', ∑ j, ∑ j',
        ‖∑ r ∈ R, K r i j * star (K r i' j) * K r i' j' * star (K r i j')‖ := by
  have hcast : ((∑ r ∈ R, fourthMoment (K r) : ℝ) : ℂ) =
      ∑ i, ∑ i', ∑ j, ∑ j',
        ∑ r ∈ R, K r i j * star (K r i' j) * K r i' j' * star (K r i j') := by
    rw [Complex.ofReal_sum]
    simp_rw [fourthMoment_four_cycle]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i' hi'
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    exact Finset.sum_comm
  have hnonneg : 0 ≤ ∑ r ∈ R, fourthMoment (K r) :=
    Finset.sum_nonneg (fun r _ => fourthMoment_nonneg (K r))
  calc
    _ ≤ ∑ r ∈ R, fourthMoment (K r) :=
      Finset.sum_le_sum (fun r _ => operator_norm_fourth_le_fourthMoment (K r))
    _ = ‖((∑ r ∈ R, fourthMoment (K r) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ = _ := congrArg norm hcast
    _ ≤ _ := by
      apply norm_sum_le_of_le
      intro i hi
      apply norm_sum_le_of_le
      intro i' hi'
      apply norm_sum_le_of_le
      intro j hj
      exact norm_sum_le _ _

section ActualMatrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (q : ι → ℕ) [∀ i, Fact (q i).Prime] [NeZero (∏ i, q i)]

/-- Actual consecutive integer rows, including any rows whose residue is a nonunit. -/
abbrev IntegerIntervalIndex (A : ℤ) (N : ℕ) := ↥(Finset.Ico A (A + N))

theorem sum_integerIntervalIndex {E : Type*} [AddCommMonoid E]
    (A : ℤ) (N : ℕ) [Fintype (IntegerIntervalIndex A N)] (f : ℤ → E) :
    (∑ i : IntegerIntervalIndex A N, f i.val) = ∑ i ∈ Finset.Ico A (A + N), f i := by
  exact (Finset.sum_subtype (Finset.Ico A (A + N)) (fun _ => Iff.rfl) f).symm

/-- The genuine integer-indexed kernel matrix at an outer residue pair. -/
def integerKernelMatrix (α : ∀ i, ZMod (q i)) (A B : ℤ) (N M : ℕ)
    (x y : ZMod (∏ i, q i)) : Matrix (IntegerIntervalIndex A N) (IntegerIntervalIndex B M) ℂ :=
  fun i j => integerKernel q α i.val j.val x y

omit [DecidableEq ι] in
/-- The matrix norm is bounded by the completed signed cycles over the actual row and
column intervals. No restriction is removed from a signed cycle. -/
theorem integerKernelMatrix_sum_fourth_le_cycles
    (α : ∀ i, ZMod (q i)) (A B Ah Ak : ℤ) (N M Nh Nk : ℕ) :
    (∑ x ∈ Finset.range Nh, ∑ y ∈ Finset.range Nk,
      ‖integerKernelMatrix q α A B N M ((Ah + x : ℤ) : ZMod (∏ i, q i))
        ((Ak + y : ℤ) : ZMod (∏ i, q i))‖ ^ 4) ≤
      ∑ i ∈ Finset.Ico A (A + N), ∑ i' ∈ Finset.Ico A (A + N),
        ∑ j ∈ Finset.Ico B (B + M), ∑ j' ∈ Finset.Ico B (B + M),
          ‖intervalRectangleSum (∏ i, q i) Ah Ak Nh Nk
            (integerFourCycle q α i i' j j')‖ := by
  let K (r : ℕ × ℕ) := integerKernelMatrix q α A B N M
    ((Ah + r.1 : ℤ) : ZMod (∏ i, q i)) ((Ak + r.2 : ℤ) : ZMod (∏ i, q i))
  let g (i i' j j' : ℤ) := ‖intervalRectangleSum (∏ i, q i) Ah Ak Nh Nk
    (integerFourCycle q α i i' j j')‖
  have hh := sum_operator_norm_fourth_le_cycle_sums
    ((Finset.range Nh).product (Finset.range Nk)) K
  have hh' : (∑ x ∈ Finset.range Nh, ∑ y ∈ Finset.range Nk,
      ‖integerKernelMatrix q α A B N M ((Ah + x : ℤ) : ZMod (∏ i, q i))
        ((Ak + y : ℤ) : ZMod (∏ i, q i))‖ ^ 4) ≤
      ∑ i : IntegerIntervalIndex A N, ∑ i' : IntegerIntervalIndex A N,
        ∑ j : IntegerIntervalIndex B M, ∑ j' : IntegerIntervalIndex B M,
          g i.val i'.val j.val j'.val := by
    simpa only [K, integerKernelMatrix, Finset.product_eq_sprod, Finset.sum_product,
      g, intervalRectangleSum, integerFourCycle] using hh
  apply hh'.trans_eq
  calc
    _ = ∑ i ∈ Finset.Ico A (A + N), ∑ i' : IntegerIntervalIndex A N,
        ∑ j : IntegerIntervalIndex B M, ∑ j' : IntegerIntervalIndex B M,
          g i i'.val j.val j'.val :=
      sum_integerIntervalIndex A N (fun i => ∑ i' : IntegerIntervalIndex A N,
        ∑ j : IntegerIntervalIndex B M, ∑ j' : IntegerIntervalIndex B M,
          g i i'.val j.val j'.val)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [sum_integerIntervalIndex A N (fun i' => ∑ j : IntegerIntervalIndex B M,
        ∑ j' : IntegerIntervalIndex B M, g i i' j.val j'.val)]
      apply Finset.sum_congr rfl
      intro i' hi'
      rw [sum_integerIntervalIndex B M (fun j => ∑ j' : IntegerIntervalIndex B M,
        g i i' j j'.val)]
      apply Finset.sum_congr rfl
      intro j hj
      exact sum_integerIntervalIndex B M (fun j' => g i i' j j')

/-- An explicit finite bound for the actual rectangular matrix fourth moment.  The
finite-field hypothesis is stated as an argument; gcd averaging and all analytic finite
sum manipulations are proved here. The repeated-index contribution requires no baseline
pair-correlation hypothesis. -/
theorem integerKernelMatrix_fourth_moment_bound
    (hcp : Pairwise (fun i j => (q i).Coprime (q j))) {C : ℝ} (hC : 0 ≤ C) {D : ℕ}
    (hlocal : LocalFourierHypothesis C D 0)
    (α : ∀ i, ZMod (q i)) (hα : ∀ i, α i ≠ 0)
    (A B Ah Ak : ℤ) (N M Nh Nk : ℕ) :
    (∑ x ∈ Finset.range Nh, ∑ y ∈ Finset.range Nk,
      ‖integerKernelMatrix q α A B N M ((Ah + x : ℤ) : ZMod (∏ i, q i))
        ((Ak + y : ℤ) : ZMod (∏ i, q i))‖ ^ 4) ≤
      C ^ Fintype.card ι * maskComplexity D (Fintype.card ι) *
        ((((N : ℝ) * (M : ℝ) ^ 2 + (N : ℝ) ^ 2 * (M : ℝ)) *
          squarefreeCompletionShape ((∏ i, q i : ℕ) : ℝ) ((∏ i, q i : ℕ) : ℝ) Nh Nk) +
          (N : ℝ) ^ 2 * (M : ℝ) ^ 2 *
            ((((∏ i, q i : ℕ) : ℝ) ^ 3 * (1 + Real.log ((∏ i, q i : ℕ) : ℝ)) ^ 2) +
              4 * ((∏ i, q i).divisors.card : ℝ) ^ 2 *
                (2 * ((Nh : ℝ) + Nk) * ((∏ i, q i : ℕ) : ℝ) ^ 2 *
                  (1 + Real.log ((∏ i, q i : ℕ) : ℝ)) +
                    4 * Nh * Nk * ((∏ i, q i : ℕ) : ℝ) * Real.sqrt ((∏ i, q i : ℕ) : ℝ)))) := by
  let s := ∏ i, q i
  let U := Finset.Ico A (A + N)
  let V := Finset.Ico B (B + M)
  let P := C ^ Fintype.card ι * maskComplexity D (Fintype.card ι)
  let f (i i' j j' : ℤ) :=
    ‖intervalRectangleSum s Ah Ak Nh Nk (integerFourCycle q α i i' j j')‖
  have hs : 0 < s := NeZero.pos _
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hP : 0 ≤ P := by dsimp [P, maskComplexity]; positivity
  have hdiag : ∀ i ∈ U, ∀ i' ∈ U, ∀ j ∈ V, ∀ j' ∈ V,
      i = i' ∨ j = j' → f i i' j j' ≤ P * squarefreeCompletionShape s s Nh Nk := by
    intro i hi i' hi' j hj j' hj' heq
    have hh := integerFourCycle_interval_bound q hcp hC hlocal α hα i i' j j' Ah Ak Nh Nk
    rcases heq with rfl | rfl
    · simpa only [sub_self, zero_mul, Int.zero_gcd, Int.natAbs_natCast] using hh
    · simpa only [sub_self, mul_zero, Int.zero_gcd, Int.natAbs_natCast] using hh
  have hsplit := four_index_sum_le_diagonal_and_offdiag U V f
    (mul_nonneg hP (squarefreeCompletionShape_nonneg hs1 Nh Nk)) hdiag
  have hoff :
      (∑ i ∈ U, ∑ i' ∈ U.erase i, ∑ j ∈ V, ∑ j' ∈ V.erase j, f i i' j j') ≤
        P * ((N : ℝ) ^ 2 * (M : ℝ) ^ 2 *
          ((s : ℝ) ^ 3 * (1 + Real.log s) ^ 2 +
            4 * (s.divisors.card : ℝ) ^ 2 *
              (2 * ((Nh : ℝ) + Nk) * (s : ℝ) ^ 2 * (1 + Real.log s) +
                4 * Nh * Nk * s * Real.sqrt s))) := by
    calc
      _ ≤ ∑ i ∈ U, ∑ i' ∈ U.erase i, ∑ j ∈ V, ∑ j' ∈ V.erase j,
          P * squarefreeCompletionShape s (Int.gcd ((i - i') * (j - j')) (s : ℤ)) Nh Nk := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro i' hi'
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro j' hj'
        exact integerFourCycle_interval_bound q hcp hC hlocal α hα i i' j j' Ah Ak Nh Nk
      _ = P * (∑ i ∈ U, ∑ i' ∈ U.erase i, ∑ j ∈ V, ∑ j' ∈ V.erase j,
          squarefreeCompletionShape s (Int.gcd ((i - i') * (j - j')) (s : ℤ)) Nh Nk) := by
        simp only [← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (interval_offdiag_completionShape_sum s N M hs A B Nh Nk) hP
  have hmat := integerKernelMatrix_sum_fourth_le_cycles q α A B Ah Ak N M Nh Nk
  apply hmat.trans
  have hsum := hsplit.trans (add_le_add le_rfl hoff)
  simp only [U, V, Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast] at hsum
  convert hsum using 1
  dsimp only [P, s, f]
  ring

end ActualMatrix

#print axioms sum_operator_norm_fourth_le_cycle_sums
#print axioms integerKernelMatrix_sum_fourth_le_cycles
#print axioms integerKernelMatrix_fourth_moment_bound

end

end PrimeGap182.TypeIII
