import TypeIIIBaselineBridge

/-!
# Exact symmetries and positivity in the repeated-index Type III branch

The statements in this file concern the actual finite sums.  No Fourier estimate,
geometric hypothesis, or additional finite-field estimate is used.  In particular,
positivity controls the origin and the norm by the origin; it does not give the
nonzero-frequency cancellation required by `CurveExceptionalFourierBound`.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The rank-three sum conjugates by negating its argument, including at zero. -/
theorem kl3_star_eq_neg (t : ZMod p) :
    star (kl3 p t) = kl3 p (-t) := by
  unfold kl3
  simp only [star_mul, star_inv₀, star_natCast, star_sum,
    PrimeGap186.star_stdAddChar]
  rw [mul_comm]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft (-1 : (ZMod p)ˣ)) _ _ ?_
  intro u
  refine Fintype.sum_equiv (Equiv.mulLeft (-1 : (ZMod p)ˣ)) _ _ ?_
  intro v
  simp only [Equiv.coe_mulLeft, Units.val_neg, neg_one_mul]
  congr 1
  simp only [neg_mul_neg, neg_div]
  ring

/-- Interchanging the two correlation parameters reverses both signs. -/
theorem correlation_swap_neg (A B c : ZMod p) :
    correlation p (-B) (-A) c = correlation p A B c := by
  unfold correlation
  apply Finset.sum_congr rfl
  intro h _
  simp only [neg_mul, ← kl3_star_eq_neg, star_star]
  ring

/-- The actual kernel is transposed by negating the common parameter and
interchanging the physical variables. -/
theorem kernel_transpose (α m n r₁ r₂ : ZMod p) :
    kernel p (-α) n m r₂ r₁ = kernel p α m n r₁ r₂ := by
  unfold kernel
  simp only [or_comm (a := r₂ = 0) (b := r₁ = 0)]
  split_ifs
  · rfl
  · simpa only [neg_mul, neg_div] using correlation_swap_neg p
      (α * r₂ / (m * r₁ ^ 2)) (α * r₁ / (n * r₂ ^ 2)) 1

/-- Transposition preserves the actual four-cycle after swapping its indices. -/
theorem fourCycle_transpose (α m m' n n' r₁ r₂ : ZMod p) :
    fourCycle p (-α) n n' m m' r₂ r₁ =
      fourCycle p α m m' n n' r₁ r₂ := by
  simp only [fourCycle, kernel_transpose]
  ring

/-- The repeated-row cycle is the product of two squared absolute values. -/
theorem fourCycle_repeated_row (α m n n' r₁ r₂ : ZMod p) :
    fourCycle p α m m n n' r₁ r₂ =
      ((‖kernel p α m n r₁ r₂‖ ^ 2 *
        ‖kernel p α m n' r₁ r₂‖ ^ 2 : ℝ) : ℂ) := by
  simp only [fourCycle, Complex.ofReal_mul,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self,
    Complex.star_def]
  ring

/-- The repeated-column cycle is the product of two squared absolute values. -/
theorem fourCycle_repeated_column (α m m' n r₁ r₂ : ZMod p) :
    fourCycle p α m m' n n r₁ r₂ =
      ((‖kernel p α m n r₁ r₂‖ ^ 2 *
        ‖kernel p α m' n r₁ r₂‖ ^ 2 : ℝ) : ℂ) := by
  simp only [fourCycle, Complex.ofReal_mul,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self,
    Complex.star_def]
  ring

/-- The row/column transposition is also exact in the unnormalized Fourier
variables, with no sign convention left implicit. -/
theorem fourier₂_fourCycle_transpose (α m m' n n' h k : ZMod p) :
    fourier₂ p (fourCycle p (-α) n n' m m') k h =
      fourier₂ p (fourCycle p α m m' n n') h k := by
  unfold fourier₂
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [fourCycle_transpose, add_comm]

/-- In the repeated branch the cycle takes values in the nonnegative reals. -/
theorem fourCycle_repeated_eq_norm (α m m' n n' r₁ r₂ : ZMod p)
    (hrep : m = m' ∨ n = n') :
    fourCycle p α m m' n n' r₁ r₂ =
      (‖fourCycle p α m m' n n' r₁ r₂‖ : ℂ) := by
  rcases hrep with h | h
  · subst m'
    rw [fourCycle_repeated_row]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  · subst n'
    rw [fourCycle_repeated_column]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- The origin is the exact total mass in the repeated branch. -/
theorem fourier₂_repeated_origin (α m m' n n' : ZMod p)
    (hrep : m = m' ∨ n = n') :
    fourier₂ p (fourCycle p α m m' n n') 0 0 =
      ((∑ x : ZMod p, ∑ y : ZMod p,
        ‖fourCycle p α m m' n n' x y‖ : ℝ) : ℂ) := by
  simp only [fourier₂, zero_mul, add_zero, AddChar.map_zero_eq_one,
    mul_one, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  exact fourCycle_repeated_eq_norm p α m m' n n' x y hrep

/-- The Fourier norm never exceeds the origin mass in the repeated branch.
This inequality alone provides no cancellation away from the origin. -/
theorem fourier₂_repeated_norm_le_origin (α m m' n n' h k : ZMod p)
    (hrep : m = m' ∨ n = n') :
    ‖fourier₂ p (fourCycle p α m m' n n') h k‖ ≤
      ‖fourier₂ p (fourCycle p α m m' n n') 0 0‖ := by
  rw [fourier₂_repeated_origin p α m m' n n' hrep]
  have hsum : 0 ≤ ∑ x : ZMod p, ∑ y : ZMod p,
      ‖fourCycle p α m m' n n' x y‖ := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsum]
  unfold fourier₂
  apply norm_sum_le_of_le
  intro x _
  apply norm_sum_le_of_le
  intro y _
  simp only [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one, le_refl]

#print axioms kl3_star_eq_neg
#print axioms correlation_swap_neg
#print axioms kernel_transpose
#print axioms fourCycle_transpose
#print axioms fourCycle_repeated_row
#print axioms fourCycle_repeated_column
#print axioms fourier₂_fourCycle_transpose
#print axioms fourCycle_repeated_eq_norm
#print axioms fourier₂_repeated_origin
#print axioms fourier₂_repeated_norm_le_origin

end

end PrimeGap182.TypeIII
