import TypeIIICorrelationMeans
import TypeIIICenteringEstimate
import TypeIIITraceIdentity

/-!
# Exact centering identity for the actual Type III Fourier coefficient

The original four-cycle is the product of two row pairs at multiplicatively
related columns.  Subtracting the exact row mean in both factors gives a
centered rectangle.  This file preserves the nonlinear torus substitution,
the full positive Fourier phase, and the zero extension on both axes.
It proves the literal difference identity and no estimate for either term.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open scoped BigOperators Classical

variable (p : ℕ) [Fact p.Prime]

/-- The actual row-pair rectangle after subtracting its exact column mean
from both factors. -/
def centeredCorrelationRectangle (a b A B : (ZMod p)ˣ) : ℂ :=
  (correlationRowPair p a A B - correlationRowMean p a A) *
    star (correlationRowPair p a A (b * B) - correlationRowMean p a A)

/-- The centered rectangle with the actual nonlinear physical coordinates
and the original positive Fourier phase. -/
def centeredTypeIIIFourier (α m m' n n' : (ZMod p)ˣ) (h k : ZMod p) : ℂ :=
  ∑ xy : (ZMod p)ˣ × (ZMod p)ˣ,
    centeredCorrelationRectangle p (m / m') (n / n')
      ((α / m) * (exactUnitTorusMap p xy).1)
      ((α / n) * (exactUnitTorusMap p xy).2) *
        ZMod.stdAddChar (h * (xy.1 : ZMod p) + k * (xy.2 : ZMod p))

/-- Subtracting the exact column mean leaves each row pair with zero
unit-column sum. -/
theorem correlationRowPair_centered_sum_zero (a A : (ZMod p)ˣ) :
    (∑ B : (ZMod p)ˣ, (correlationRowPair p a A B - correlationRowMean p a A)) = 0 := by
  have hcount : (p : ℂ) - 1 ≠ 0 := by
    exact_mod_cast (ne_of_gt (correlation_unit_count_pos p))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    correlation_units_card_complex, correlationRowMean]
  rw [← mul_assoc, mul_inv_cancel₀ hcount, one_mul, sub_self]

/-- The literal four-factor rectangle represented by the two row pairs. -/
theorem correlationRowPair_rectangle (a b A B : (ZMod p)ˣ) :
    correlationRowPair p a A B * star (correlationRowPair p a A (b * B)) =
      correlationUnitMatrix p A B * star (correlationUnitMatrix p (a * A) B) *
        correlationUnitMatrix p (a * A) (b * B) * star (correlationUnitMatrix p A (b * B)) := by
  simp only [correlationRowPair, star_mul, star_star]
  ring

/-- The original kernel on unit physical coordinates, as a correlation
matrix entry with the exact monomial arguments. -/
theorem kernel_units_eq_correlationUnitMatrix (α m n x y : (ZMod p)ˣ) :
    kernel p (α : ZMod p) (m : ZMod p) (n : ZMod p) (x : ZMod p) (y : ZMod p) =
      correlationUnitMatrix p ((α / m) * (y / x ^ 2)) ((α / n) * (x / y ^ 2)) := by
  rw [kernel, ite_eq_right (not_or.mpr ⟨x.ne_zero, y.ne_zero⟩), correlationUnitMatrix]
  simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
  congr 1 <;> simp only [div_eq_mul_inv, mul_inv] <;> ring

/-- The unit ratio connecting one row or column parameter to another. -/
theorem correlation_unit_parameter_ratio (z z' c u : (ZMod p)ˣ) :
    (z / z') * ((c / z) * u) = (c / z') * u := by
  apply Units.ext
  simp only [Units.val_mul, Units.val_div_eq_div_val]
  field_simp

/-- The actual four-cycle on the physical unit torus is precisely the
row-pair rectangle at the substituted correlation parameters. -/
theorem fourCycle_eq_rowPair_rectangle (α m m' n n' : (ZMod p)ˣ)
    (xy : (ZMod p)ˣ × (ZMod p)ˣ) :
    fourCycle p (α : ZMod p) (m : ZMod p) (m' : ZMod p) (n : ZMod p) (n' : ZMod p)
      (xy.1 : ZMod p) (xy.2 : ZMod p) =
      correlationRowPair p (m / m')
        ((α / m) * (exactUnitTorusMap p xy).1)
        ((α / n) * (exactUnitTorusMap p xy).2) *
      star (correlationRowPair p (m / m')
        ((α / m) * (exactUnitTorusMap p xy).1)
        ((n / n') * ((α / n) * (exactUnitTorusMap p xy).2))) := by
  rw [correlationRowPair_rectangle]
  simp only [fourCycle, kernel_units_eq_correlationUnitMatrix,
    correlation_unit_parameter_ratio, exactUnitTorusMap]

/-- Removing both zero axes from the original full-field Fourier sum is
exact because the actual four-cycle vanishes on each axis. -/
theorem fourier₂_fourCycle_eq_unit_sum (α m m' n n' h k : ZMod p) :
    fourier₂ p (fourCycle p α m m' n n') h k =
      ∑ xy : (ZMod p)ˣ × (ZMod p)ˣ,
        fourCycle p α m m' n n' (xy.1 : ZMod p) (xy.2 : ZMod p) *
          ZMod.stdAddChar (h * (xy.1 : ZMod p) + k * (xy.2 : ZMod p)) := by
  simp only [fourier₂, Fintype.sum_prod_type]
  rw [PrimeGap186.sum_units_eq_sum_sub_zero p (fun x : ZMod p =>
    ∑ y : (ZMod p)ˣ, fourCycle p α m m' n n' x (y : ZMod p) *
      ZMod.stdAddChar (h * x + k * (y : ZMod p)))]
  simp only [fourCycle_zero_left, zero_mul, Finset.sum_const_zero, sub_zero]
  apply Finset.sum_congr rfl
  intro x _
  rw [PrimeGap186.sum_units_eq_sum_sub_zero p (fun y : ZMod p =>
    fourCycle p α m m' n n' x y * ZMod.stdAddChar (h * x + k * y))]
  simp only [fourCycle_zero_right, zero_mul, sub_zero]

/-- The full actual Fourier transform written in the row-pair coordinates
that are subsequently centered. -/
theorem fourier₂_fourCycle_eq_unit_rowPair_sum (α m m' n n' : (ZMod p)ˣ)
    (h k : ZMod p) :
    fourier₂ p
      (fourCycle p (α : ZMod p) (m : ZMod p) (m' : ZMod p) (n : ZMod p) (n' : ZMod p)) h k =
      ∑ xy : (ZMod p)ˣ × (ZMod p)ˣ,
        (correlationRowPair p (m / m')
          ((α / m) * (exactUnitTorusMap p xy).1)
          ((α / n) * (exactUnitTorusMap p xy).2) *
        star (correlationRowPair p (m / m')
          ((α / m) * (exactUnitTorusMap p xy).1)
          ((n / n') * ((α / n) * (exactUnitTorusMap p xy).2)))) *
        ZMod.stdAddChar (h * (xy.1 : ZMod p) + k * (xy.2 : ZMod p)) := by
  rw [fourier₂_fourCycle_eq_unit_sum]
  apply Finset.sum_congr rfl
  intro xy _
  rw [fourCycle_eq_rowPair_rectangle]

/-- Exact arithmetic centering identity for the original Type III Fourier
coefficient, with no exceptional-set or cancellation hypothesis. -/
theorem fourier₂_fourCycle_sub_centeredTypeIIIFourier (α m m' n n' : (ZMod p)ˣ)
    (h k : ZMod p) :
    fourier₂ p
      (fourCycle p (α : ZMod p) (m : ZMod p) (m' : ZMod p) (n : ZMod p) (n' : ZMod p)) h k -
      centeredTypeIIIFourier p α m m' n n' h k =
      ∑ xy : (ZMod p)ˣ × (ZMod p)ˣ,
        rowCenteringError (correlationRowPair p (m / m')) (correlationRowMean p (m / m'))
          (Equiv.mulLeft (n / n'))
          ((α / m) * (exactUnitTorusMap p xy).1)
          ((α / n) * (exactUnitTorusMap p xy).2) *
        ZMod.stdAddChar (h * (xy.1 : ZMod p) + k * (xy.2 : ZMod p)) := by
  rw [fourier₂_fourCycle_eq_unit_rowPair_sum, centeredTypeIIIFourier,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro xy _
  simp only [rowCenteringError, centeredCorrelationRectangle, Equiv.coe_mulLeft, sub_mul]

#print axioms centeredCorrelationRectangle
#print axioms centeredTypeIIIFourier
#print axioms correlationRowPair_centered_sum_zero
#print axioms correlationRowPair_rectangle
#print axioms kernel_units_eq_correlationUnitMatrix
#print axioms correlation_unit_parameter_ratio
#print axioms fourCycle_eq_rowPair_rectangle
#print axioms fourier₂_fourCycle_eq_unit_sum
#print axioms fourier₂_fourCycle_eq_unit_rowPair_sum
#print axioms fourier₂_fourCycle_sub_centeredTypeIIIFourier

end PrimeGap182.TypeIII
