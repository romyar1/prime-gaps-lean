import TypeIIIIntegerGCD
import TypeIIISmallPrimes

/-!
# The actual integer-indexed product kernel, with nonunit rows and columns zeroed

This is the kernel used by the matrix fourth-moment argument.  The local nonzero-index
hypotheses are discharged on its active rows and columns.  On the other rows or columns the
matrix is identically zero, including every outer residue.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ι : Type*} [Fintype ι]
variable (q : ι → ℕ) [∀ i, Fact (q i).Prime] [NeZero (∏ i, q i)]

/-- An integer row or column is active exactly when all of its local residues are nonzero. -/
def unitIntegerIndex (m : ℤ) : Prop := ∀ i, (m : ZMod (q i)) ≠ 0

def integerKernel (α : ∀ i, ZMod (q i)) (m n : ℤ) (x y : ZMod (∏ i, q i)) : ℂ :=
  if unitIntegerIndex q m ∧ unitIntegerIndex q n then
    squarefreeKernel q α (fun i => (m : ZMod (q i))) (fun i => (n : ZMod (q i))) x y
  else 0

def integerFourCycle (α : ∀ i, ZMod (q i)) (m m' n n' : ℤ)
    (x y : ZMod (∏ i, q i)) : ℂ :=
  integerKernel q α m n x y * star (integerKernel q α m' n x y) *
    integerKernel q α m' n' x y * star (integerKernel q α m n' x y)

omit [NeZero (∏ i, q i)] in
theorem integerFourCycle_eq (α : ∀ i, ZMod (q i)) (m m' n n' : ℤ)
    (x y : ZMod (∏ i, q i)) :
    integerFourCycle q α m m' n n' x y =
      if unitIntegerIndex q m ∧ unitIntegerIndex q m' ∧
          unitIntegerIndex q n ∧ unitIntegerIndex q n' then
        squarefreeFourCycle q α (fun i => (m : ZMod (q i))) (fun i => (m' : ZMod (q i)))
          (fun i => (n : ZMod (q i))) (fun i => (n' : ZMod (q i))) x y
      else 0 := by
  by_cases hm : unitIntegerIndex q m <;> by_cases hm' : unitIntegerIndex q m' <;>
    by_cases hn : unitIntegerIndex q n <;> by_cases hn' : unitIntegerIndex q n' <;>
    simp [integerFourCycle, integerKernel, hm, hm', hn, hn', squarefreeFourCycle]

/-- A uniform pointwise bound for every cycle, including cycles in the zeroed rows. -/
theorem integerFourCycle_norm_le (hbase : BaselineLocalInputs)
    (α : ∀ i, ZMod (q i)) (hα : ∀ i, α i ≠ 0) (m m' n n' : ℤ)
    (x y : ZMod (∏ i, q i)) :
    ‖integerFourCycle q α m m' n n' x y‖ ≤
      (6561 : ℝ) ^ Fintype.card ι * ((∏ i, q i : ℕ) : ℝ) ^ 2 := by
  rw [integerFourCycle_eq]
  by_cases hv : unitIntegerIndex q m ∧ unitIntegerIndex q m' ∧
      unitIntegerIndex q n ∧ unitIntegerIndex q n'
  · rw [ite_eq_left hv, squarefreeFourCycle_eq_crtProduct]
    simp only [crtProduct, norm_prod]
    calc
      _ ≤ ∏ i, 6561 * (q i : ℝ) ^ 2 := by
        apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro i hi
        exact fourCycle_norm_le_baseline_inputs hbase (q i) (α i) m m' n n'
          (x.val : ZMod (q i)) (y.val : ZMod (q i))
          (hα i) (hv.1 i) (hv.2.1 i) (hv.2.2.1 i) (hv.2.2.2 i)
      _ = _ := by
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Finset.prod_pow, Nat.cast_prod]
  · rw [ite_eq_right hv, norm_zero]
    positivity

variable [DecidableEq ι]

/-- The actual integer-indexed incomplete cycle bound with the discriminant gcd. -/
theorem integerFourCycle_interval_bound
    (hcp : Pairwise (fun i j => (q i).Coprime (q j))) {C : ℝ} (hC : 0 ≤ C) {D : ℕ}
    (hlocal : LocalFourierHypothesis C D 0)
    (α : ∀ i, ZMod (q i)) (hα : ∀ i, α i ≠ 0) (m m' n n' : ℤ)
    (Ah Ak : ℤ) (Nh Nk : ℕ) :
    ‖intervalRectangleSum (∏ i, q i) Ah Ak Nh Nk (integerFourCycle q α m m' n n')‖ ≤
      C ^ Fintype.card ι * maskComplexity D (Fintype.card ι) *
        squarefreeCompletionShape ((∏ i, q i : ℕ) : ℝ)
          (Int.gcd ((m - m') * (n - n')) ((∏ i, q i : ℕ) : ℤ)) Nh Nk := by
  have hs : (1 : ℝ) ≤ (∏ i, q i : ℕ) :=
    by exact_mod_cast (show 1 ≤ ∏ i, q i from NeZero.one_le)
  have hfactor : 0 ≤ C ^ Fintype.card ι * maskComplexity D (Fintype.card ι) := by
    unfold maskComplexity
    positivity
  by_cases hv : unitIntegerIndex q m ∧ unitIntegerIndex q m' ∧
      unitIntegerIndex q n ∧ unitIntegerIndex q n'
  · have heq : integerFourCycle q α m m' n n' =
        squarefreeFourCycle q α (fun i => (m : ZMod (q i))) (fun i => (m' : ZMod (q i)))
          (fun i => (n : ZMod (q i))) (fun i => (n' : ZMod (q i))) := by
      funext x y
      rw [integerFourCycle_eq, ite_eq_left hv]
    rw [heq]
    have hh := hlocal.squarefree_interval_bound q hC hcp
      (fun i => (Fact.out : (q i).Prime).pos) α _ _ _ _ hα hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
      Ah Ak Nh Nk
    simp only [← Nat.cast_prod] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ hfactor
    apply squarefreeCompletionShape_mono_gcd hs
    exact_mod_cast repeatedResidueFactor_le_gcd q hcp m m' n n'
  · have heq : integerFourCycle q α m m' n n' = fun _ _ => 0 := by
      funext x y
      rw [integerFourCycle_eq, ite_eq_right hv]
    rw [heq]
    simp only [intervalRectangleSum, Finset.sum_const_zero, norm_zero]
    exact mul_nonneg hfactor (squarefreeCompletionShape_nonneg hs Nh Nk)

#print axioms integerFourCycle_eq
#print axioms integerFourCycle_norm_le
#print axioms integerFourCycle_interval_bound

end

end PrimeGap182.TypeIII
