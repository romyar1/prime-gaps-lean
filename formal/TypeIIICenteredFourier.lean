import TypeIIICenteringEstimate
import TypeIIICorrelationMeans
import TypeIIITorusFiberBound
import TypeIIICenteringIdentity

/-!
# An acceptable centering error for the actual Type III Fourier sum

The exact Gram identity controls the absolute mass of the row-pair means.
Together with the three-element fiber bound for the nonlinear torus map,
this proves that subtracting those means changes the Fourier sum by at
most `32 p³`. The remaining centered sum is not estimated here.

The estimate uses exact finite-sum identities and elementary norm
inequalities. In particular, no pointwise Weil bound is a premise.
-/

noncomputable section

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

variable (p : ℕ) [Fact p.Prime]

/-- The total centering error for the actual correlation rectangle. -/
theorem correlationCenteringError_sum_norm_le (a b : (ZMod p)ˣ) (ha : a ≠ 1) :
    (∑ A : (ZMod p)ˣ, ∑ B : (ZMod p)ˣ,
      ‖rowCenteringError (correlationRowPair p a) (correlationRowMean p a)
        (Equiv.mulLeft b) A B‖) ≤
      6 * correlationGramKappa p * (p : ℝ) ^ 3 := by
  have hμ (A : (ZMod p)ˣ) :
      (Fintype.card (ZMod p)ˣ : ℝ) * ‖correlationRowMean p a A‖ ≤ (p : ℝ) ^ 2 := by
    rw [correlation_units_card_real p]
    exact correlationRowMean_norm_mul_le p a A
  calc
    _ ≤ 3 * (p : ℝ) ^ 2 * (2 * correlationGramKappa p * (p : ℝ)) :=
      rowCenteringError_total_mass_le
        (correlationRowPair p a) (correlationRowMean p a) (Equiv.mulLeft b)
        ((p : ℝ) ^ 2) (2 * correlationGramKappa p * (p : ℝ)) (sq_nonneg _)
        (correlationRowPair_abs_sum_le p a) hμ (correlationRowMean_sum_norm_le p a ha)
    _ = _ := by ring

/-- Independent unit scalings of the row and column preserve the error mass. -/
theorem correlationCenteringError_scaled_sum_norm (a b c d : (ZMod p)ˣ) :
    (∑ ab : (ZMod p)ˣ × (ZMod p)ˣ,
      ‖rowCenteringError (correlationRowPair p a) (correlationRowMean p a)
        (Equiv.mulLeft b) (c * ab.1) (d * ab.2)‖) =
      ∑ A : (ZMod p)ˣ, ∑ B : (ZMod p)ˣ,
        ‖rowCenteringError (correlationRowPair p a) (correlationRowMean p a)
          (Equiv.mulLeft b) A B‖ := by
  rw [Fintype.sum_prod_type]
  refine Fintype.sum_equiv (Equiv.mulLeft c) _ _ ?_
  intro A
  exact Fintype.sum_equiv (Equiv.mulLeft d) _ _ (fun _ => rfl)

/-- The precise error constant after the determinant-three torus pullback,
with arbitrary complex weights of norm at most one. -/
theorem correlationCenteringError_pullback_norm_le_kappa
    (a b c d : (ZMod p)ˣ) (ha : a ≠ 1)
    (w : ((ZMod p)ˣ × (ZMod p)ˣ) → ℂ) (hw : ∀ xy, ‖w xy‖ ≤ 1) :
    ‖∑ xy : (ZMod p)ˣ × (ZMod p)ˣ,
      rowCenteringError (correlationRowPair p a) (correlationRowMean p a)
        (Equiv.mulLeft b)
        (c * (exactUnitTorusMap p xy).1) (d * (exactUnitTorusMap p xy).2) * w xy‖ ≤
      18 * correlationGramKappa p * (p : ℝ) ^ 3 := by
  calc
    _ ≤ 3 * ∑ ab : (ZMod p)ˣ × (ZMod p)ˣ,
        ‖rowCenteringError (correlationRowPair p a) (correlationRowMean p a)
          (Equiv.mulLeft b) (c * ab.1) (d * ab.2)‖ :=
      norm_sum_exactUnitTorusMap_mul_le_three p
        (fun ab => rowCenteringError (correlationRowPair p a) (correlationRowMean p a)
          (Equiv.mulLeft b) (c * ab.1) (d * ab.2)) w hw
    _ = 3 * ∑ A : (ZMod p)ˣ, ∑ B : (ZMod p)ˣ,
        ‖rowCenteringError (correlationRowPair p a) (correlationRowMean p a)
          (Equiv.mulLeft b) A B‖ := by rw [correlationCenteringError_scaled_sum_norm]
    _ ≤ 3 * (6 * correlationGramKappa p * (p : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left (correlationCenteringError_sum_norm_le p a b ha) (by norm_num)
    _ = _ := by ring

/-- A uniform `32 p³` bound for the actual centering error, including the
nonlinear pullback and arbitrary weights of norm at most one. -/
theorem correlationCenteringError_pullback_norm_le
    (a b c d : (ZMod p)ˣ) (ha : a ≠ 1)
    (w : ((ZMod p)ˣ × (ZMod p)ˣ) → ℂ) (hw : ∀ xy, ‖w xy‖ ≤ 1) :
    ‖∑ xy : (ZMod p)ˣ × (ZMod p)ˣ,
      rowCenteringError (correlationRowPair p a) (correlationRowMean p a)
        (Equiv.mulLeft b)
        (c * (exactUnitTorusMap p xy).1) (d * (exactUnitTorusMap p xy).2) * w xy‖ ≤
      32 * (p : ℝ) ^ 3 := by
  calc
    _ ≤ 18 * correlationGramKappa p * (p : ℝ) ^ 3 :=
      correlationCenteringError_pullback_norm_le_kappa p a b c d ha w hw
    _ ≤ 32 * (p : ℝ) ^ 3 := by
      have hp : 0 ≤ (p : ℝ) ^ 3 := pow_nonneg (Nat.cast_nonneg p) _
      have hk := mul_le_mul_of_nonneg_right (correlationGramKappa_le_seven_quarters p) hp
      nlinarith

/-- Subtracting the actual row-pair means changes the original Fourier
coefficient by at most `32 p³`. The zero axes, positive Fourier phase,
all five unit parameters, and every prime-field frequency are retained.
Only the row indices must be distinct; no bound on the centered coefficient
is assumed or concluded. -/
theorem fourier₂_fourCycle_sub_centered_norm_le
    (α m m' n n' : (ZMod p)ˣ) (h k : ZMod p) (hmm : m ≠ m') :
    ‖fourier₂ p (fourCycle p (α : ZMod p) (m : ZMod p) (m' : ZMod p)
        (n : ZMod p) (n' : ZMod p)) h k -
      centeredTypeIIIFourier p α m m' n n' h k‖ ≤ 32 * (p : ℝ) ^ 3 := by
  rw [fourier₂_fourCycle_sub_centeredTypeIIIFourier]
  exact correlationCenteringError_pullback_norm_le p
    (m / m') (n / n') (α / m) (α / n) (fun he => hmm (div_eq_one.mp he))
    (fun xy => ZMod.stdAddChar (h * (xy.1 : ZMod p) + k * (xy.2 : ZMod p)))
    (fun _ => by simp only [ZMod.stdAddChar_apply, Circle.norm_coe, le_refl])

#print axioms correlationCenteringError_sum_norm_le
#print axioms correlationCenteringError_scaled_sum_norm
#print axioms correlationCenteringError_pullback_norm_le_kappa
#print axioms correlationCenteringError_pullback_norm_le
#print axioms fourier₂_fourCycle_sub_centered_norm_le

end PrimeGap182.TypeIII
