import TypeIIICorrelationFourier
import IncidenceCompletion

/-!
# Exact Fourier reduction for the actual nonlinear Type III four-cycle

This file supplies an equality between the manuscript's actual transform and
an explicit finite sum involving the scalar toric transform.  It proves no
finite-field estimate and assumes no local Fourier bound.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open scoped BigOperators

variable (p : ℕ) [Fact p.Prime]

/-- Positive Fourier inversion, with the two inverse cardinality factors. -/
theorem exact_fourier₂_inversion (f : ZMod p → ZMod p → ℂ) (x y : ZMod p) :
    ((p : ℂ) ^ 2)⁻¹ * ∑ a : ZMod p, ∑ b : ZMod p,
      fourier₂ p f a b * ZMod.stdAddChar (-(a * x + b * y)) = f x y := by
  have h := PrimeGap182Audit.incidenceJointDFT_inversion
    (fun z : ZMod p × ZMod p => f (-z.1) (-z.2)) (-x, -y)
  have ht (a b : ZMod p) :
      PrimeGap182Audit.incidenceJointDFT
        (fun z : ZMod p × ZMod p => f (-z.1) (-z.2)) (a, b) =
      fourier₂ p f a b := by
    simp only [PrimeGap182Audit.incidenceJointDFT,
      PrimeGap182Audit.incidenceJointChar, Fintype.sum_prod_type, fourier₂]
    refine Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ ?_
    intro u
    refine Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ ?_
    intro v
    rfl
  simpa only [Fintype.sum_prod_type, ht, PrimeGap182Audit.incidenceJointChar,
    neg_neg, mul_neg, ← neg_add] using h

/-- Pull back a function by the determinant-three monomial map and extend by
zero off the torus. -/
def exactTorusPullback (f : ZMod p → ZMod p → ℂ) (x y : ZMod p) : ℂ :=
  if x = 0 ∨ y = 0 then 0 else f (y / x ^ 2) (x / y ^ 2)

/-- Nonlinear Fourier completion.  Both variables of the original function
remain, with their exact phases and normalization. -/
theorem exact_torus_pullback_fourier (f : ZMod p → ZMod p → ℂ) (h k : ZMod p) :
    fourier₂ p (exactTorusPullback p f) h k =
      ((p : ℂ) ^ 2)⁻¹ * ∑ a : ZMod p, ∑ b : ZMod p,
        fourier₂ p f a b * toricPhaseFourier p (-a) (-b) h k := by
  classical
  have hu : fourier₂ p (exactTorusPullback p f) h k =
      ∑ x : (ZMod p)ˣ, ∑ y : (ZMod p)ˣ,
        f ((y : ZMod p) / (x : ZMod p) ^ 2)
          ((x : ZMod p) / (y : ZMod p) ^ 2) *
            ZMod.stdAddChar (h * (x : ZMod p) + k * (y : ZMod p)) := by
    simp only [fourier₂, exactTorusPullback]
    rw [PrimeGap186.sum_units_eq_sum_ite p (fun x : ZMod p =>
      ∑ y : (ZMod p)ˣ, f ((y : ZMod p) / x ^ 2) (x / (y : ZMod p) ^ 2) *
        ZMod.stdAddChar (h * x + k * (y : ZMod p)))]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x = 0
    · simp [hx]
    · rw [ite_eq_left hx, PrimeGap186.sum_units_eq_sum_ite p (fun y : ZMod p =>
        f (y / x ^ 2) (x / y ^ 2) * ZMod.stdAddChar (h * x + k * y))]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y = 0 <;> simp [hx, hy]
  rw [hu]
  conv_lhs =>
    arg 2
    ext x
    arg 2
    ext y
    rw [← exact_fourier₂_inversion p f]
  simp only [toricPhaseFourier, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm_cycle]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm_cycle]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [mul_assoc, mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

/-- The rectangle before the nonlinear change of variables. -/
def exactCorrelationRectangle (α m m' n n' u v : ZMod p) : ℂ :=
  correlation p (α * u / m) (α * v / n) 1 *
    star (correlation p (α * u / m') (α * v / n) 1) *
    correlation p (α * u / m') (α * v / n') 1 *
    star (correlation p (α * u / m) (α * v / n') 1)

/-- The actual arithmetic four-cycle is exactly this zero-extended pullback. -/
theorem exact_fourCycle_eq_pullback (α m m' n n' : ZMod p) :
    fourCycle p α m m' n n' =
      exactTorusPullback p (exactCorrelationRectangle p α m m' n n') := by
  classical
  funext x y
  by_cases hxy : x = 0 ∨ y = 0
  · simp [fourCycle, kernel, exactTorusPullback, hxy]
  · simp only [fourCycle, kernel, exactTorusPullback, ite_eq_right hxy,
      exactCorrelationRectangle]
    have he (a b c : ZMod p) : α * (c / b ^ 2) / a = α * c / (a * b ^ 2) := by
      simp only [div_eq_mul_inv, mul_inv]
      ring
    simp only [he]

/-- Exact reduction of the full target transform to a finite scalar toric
sum.  No norm, inequality, or exceptional-set premise enters this identity. -/
theorem exact_fourCycle_fourier (α m m' n n' h k : ZMod p) :
    fourier₂ p (fourCycle p α m m' n n') h k =
      ((p : ℂ) ^ 2)⁻¹ * ∑ a : ZMod p, ∑ b : ZMod p,
        fourier₂ p (exactCorrelationRectangle p α m m' n n') a b *
          toricPhaseFourier p (-a) (-b) h k := by
  rw [exact_fourCycle_eq_pullback, exact_torus_pullback_fourier]

#print axioms exact_fourier₂_inversion
#print axioms exact_torus_pullback_fourier
#print axioms exact_fourCycle_eq_pullback
#print axioms exact_fourCycle_fourier

end PrimeGap182.TypeIII
