import TypeIIIExactSpectrum
import TypeIIIRepeatedAlgebra

/-!
# Parameter symmetries of the actual Type III Fourier transform

The unit changes of variables below reduce the common parameter and the first
row index to one. A further anisotropic dilation changes the remaining column
parameters by a common cube. These are identities for the original finite
sums, including their zero extensions and positive Fourier phases.

They reduce the parameter space for a proof or computation; they do not assert
the uniform cancellation estimate in `LocalFourierHypothesis`.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open scoped BigOperators Classical

variable (p : ℕ) [Fact p.Prime]

/-- The correlation is real for every choice of its three parameters. -/
theorem correlation_star (A B c : ZMod p) :
    star (correlation p A B c) = correlation p A B c := by
  unfold correlation
  simp only [star_sum, star_mul, star_star, PrimeGap186.star_stdAddChar]
  refine Fintype.sum_equiv (Equiv.mulLeft (-1 : (ZMod p)ˣ)) _ _ ?_
  intro h
  simp only [Equiv.coe_mulLeft, Units.val_neg, neg_one_mul, mul_neg,
    ← kl3_star_eq_neg, star_star]
  ring

/-- Reality also holds on the axes, where the actual kernel is zero. -/
theorem kernel_star (α m n x y : ZMod p) :
    star (kernel p α m n x y) = kernel p α m n x y := by
  unfold kernel
  split_ifs
  · exact star_zero _
  · exact correlation_star p _ _ _

/-- All four factors of the original cycle are real. -/
theorem fourCycle_star (α m m' n n' x y : ZMod p) :
    star (fourCycle p α m m' n n' x y) =
      fourCycle p α m m' n n' x y := by
  simp only [fourCycle, star_mul, kernel_star]
  ring

/-- Swapping the two rows preserves the actual cycle. -/
theorem fourCycle_swap_rows (α m m' n n' x y : ZMod p) :
    fourCycle p α m' m n n' x y = fourCycle p α m m' n n' x y := by
  simp only [fourCycle, kernel_star]
  ring

/-- Swapping the two columns preserves the actual cycle. -/
theorem fourCycle_swap_columns (α m m' n n' x y : ZMod p) :
    fourCycle p α m m' n' n x y = fourCycle p α m m' n n' x y := by
  simp only [fourCycle, kernel_star]
  ring

/-- A common physical dilation normalizes the common parameter and divides
both matrix indices by the same nonzero reference index. -/
theorem kernel_normalize_parameters (α q m n x y : ZMod p)
    (hα : α ≠ 0) (hq : q ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0) :
    kernel p α m n ((α / q) * x) ((α / q) * y) =
      kernel p 1 (m / q) (n / q) x y := by
  have ht : α / q ≠ 0 := div_ne_zero hα hq
  by_cases hx : x = 0
  · subst x
    simp
  by_cases hy : y = 0
  · subst y
    simp
  rw [kernel, ite_eq_right (not_or.mpr
      ⟨mul_ne_zero ht hx, mul_ne_zero ht hy⟩),
    kernel, ite_eq_right (not_or.mpr ⟨hx, hy⟩)]
  congr 1 <;> field_simp

/-- Two of the five nonzero parameters can be normalized to one. -/
theorem fourCycle_normalize_parameters (α m m' n n' x y : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0)
    (hn : n ≠ 0) (hn' : n' ≠ 0) :
    fourCycle p α m m' n n' ((α / m) * x) ((α / m) * y) =
      fourCycle p 1 1 (m' / m) (n / m) (n' / m) x y := by
  simp only [fourCycle,
    kernel_normalize_parameters p α m m n x y hα hm hm hn,
    kernel_normalize_parameters p α m m' n x y hα hm hm' hn,
    kernel_normalize_parameters p α m m' n' x y hα hm hm' hn',
    kernel_normalize_parameters p α m m n' x y hα hm hm hn',
    div_self hm]

/-- The frequency change in the parameter normalization is multiplication
by `α/m`, with no Fourier normalization factor. -/
theorem fourier₂_fourCycle_normalize_parameters (α m m' n n' h k : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0)
    (hn : n ≠ 0) (hn' : n' ≠ 0) :
    fourier₂ p (fourCycle p α m m' n n') h k =
      fourier₂ p (fourCycle p 1 1 (m' / m) (n / m) (n' / m))
        ((α / m) * h) ((α / m) * k) := by
  have ht : α / m ≠ 0 := div_ne_zero hα hm
  have he := exact_fourier₂_scale p (fourCycle p α m m' n n')
    (α / m) (α / m) ((α / m) * h) ((α / m) * k) ht ht
  have hh : ((α / m) * h) / (α / m) = h := by field_simp
  have hk : ((α / m) * k) / (α / m) = k := by field_simp
  rw [hh, hk] at he
  rw [← he]
  congr 1
  funext x y
  exact fourCycle_normalize_parameters p α m m' n n' x y hα hm hm' hn hn'

/-- The dilation `(x,y) ↦ (a*x,a²*y)` fixes the common parameter and
row index and multiplies the column index by a cube. -/
theorem kernel_cubic_dilation (m n a x y : ZMod p)
    (hm : m ≠ 0) (hn : n ≠ 0) (ha : a ≠ 0) :
    kernel p 1 m n (a * x) (a ^ 2 * y) =
      kernel p 1 m (n * a ^ 3) x y := by
  by_cases hx : x = 0
  · subst x
    simp
  by_cases hy : y = 0
  · subst y
    simp
  rw [kernel, ite_eq_right (not_or.mpr
      ⟨mul_ne_zero ha hx, mul_ne_zero (pow_ne_zero _ ha) hy⟩),
    kernel, ite_eq_right (not_or.mpr ⟨hx, hy⟩)]
  congr 1 <;> field_simp

/-- The same cube rescales both columns of the whole rectangle. -/
theorem fourCycle_cubic_dilation (m m' n n' a x y : ZMod p)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0)
    (ha : a ≠ 0) :
    fourCycle p 1 m m' n n' (a * x) (a ^ 2 * y) =
      fourCycle p 1 m m' (n * a ^ 3) (n' * a ^ 3) x y := by
  simp only [fourCycle,
    kernel_cubic_dilation p m n a x y hm hn ha,
    kernel_cubic_dilation p m' n a x y hm' hn ha,
    kernel_cubic_dilation p m' n' a x y hm' hn' ha,
    kernel_cubic_dilation p m n' a x y hm hn' ha]

/-- Cubic parameter changes preserve the complete spectrum up to the
corresponding invertible change of the two frequencies. -/
theorem fourier₂_fourCycle_cubic_dilation (m m' n n' a h k : ZMod p)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0)
    (ha : a ≠ 0) :
    fourier₂ p (fourCycle p 1 m m' n n') h k =
      fourier₂ p (fourCycle p 1 m m' (n * a ^ 3) (n' * a ^ 3))
        (a * h) (a ^ 2 * k) := by
  have he := exact_fourier₂_scale p (fourCycle p 1 m m' n n')
    a (a ^ 2) (a * h) (a ^ 2 * k) ha (pow_ne_zero _ ha)
  have hh : (a * h) / a = h := by field_simp
  have hk : (a ^ 2 * k) / a ^ 2 = k := by field_simp
  rw [hh, hk] at he
  rw [← he]
  congr 1
  funext x y
  exact fourCycle_cubic_dilation p m m' n n' a x y hm hm' hn hn' ha

#print axioms correlation_star
#print axioms kernel_star
#print axioms fourCycle_star
#print axioms fourCycle_swap_rows
#print axioms fourCycle_swap_columns
#print axioms kernel_normalize_parameters
#print axioms fourCycle_normalize_parameters
#print axioms fourier₂_fourCycle_normalize_parameters
#print axioms kernel_cubic_dilation
#print axioms fourCycle_cubic_dilation
#print axioms fourier₂_fourCycle_cubic_dilation

end PrimeGap182.TypeIII
