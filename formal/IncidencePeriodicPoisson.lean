import IncidenceShearedPoisson

/-!
# Poisson completion against an actual periodic response

This is an identity for the integer-lattice sum of a smooth profile times an
arbitrary function on the residue pairs. It does not postulate a completed
window, a matrix estimate, or cancellation of any zero residue.
-/

noncomputable section

namespace PrimeGap182Audit

open scoped BigOperators SchwartzMap FourierTransform

variable {q : ℕ} [NeZero q]

def incidenceIntegerResidue (q : ℕ) (z : ℤ × ℤ) : ZMod q × ZMod q :=
  ((z.1 : ZMod q), (z.2 : ZMod q))

@[simp] theorem incidenceJointChar_norm (ξ z : ZMod q × ZMod q) :
    ‖incidenceJointChar ξ z‖ = 1 := by
  simp only [incidenceJointChar, ZMod.stdAddChar_apply, Circle.norm_coe]

/-- Absolute summability survives multiplication by any finite periodic response. -/
theorem incidencePeriodicMul_norm_summable (w : ℤ × ℤ → ℂ)
    (hw : Summable (fun z => ‖w z‖)) (f : ZMod q × ZMod q → ℂ) :
    Summable (fun z => ‖w z * f (incidenceIntegerResidue q z)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun z => ?_) (hw.mul_right (∑ r, ‖f r‖))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun r _ => norm_nonneg (f r)) (Finset.mem_univ _))
    (norm_nonneg _)

/-- Fourier inversion with the signs arranged for the Gram modes. -/
theorem incidenceJoint_reverse_inversion (f : ZMod q × ZMod q → ℂ)
    (z : ZMod q × ZMod q) :
    ((q : ℂ) ^ 2)⁻¹ * ∑ ξ,
      (∑ r, incidenceJointChar ξ r * f r) * incidenceJointChar ξ (-z) = f z := by
  have hsum : (∑ ξ, (∑ r, incidenceJointChar ξ r * f r) * incidenceJointChar ξ (-z)) =
      (q : ℂ) ^ 2 * f z := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      _ = ∑ r, f r * ∑ ξ, incidenceJointChar ξ (r - z) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ξ _
        rw [← incidenceJointChar_sub]
        ring
      _ = _ := by simp only [incidenceJointChar_sum, sub_eq_zero]; simp [mul_comm]
  rw [hsum, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (NeZero.ne _)), one_mul]

set_option maxHeartbeats 600000 in
/-- Exact finite Fourier completion of an absolutely summable lattice weight. -/
theorem incidencePeriodic_completion (w : ℤ × ℤ → ℂ)
    (hw : Summable (fun z => ‖w z‖)) (f : ZMod q × ZMod q → ℂ) :
    (∑' z : ℤ × ℤ, w z * f (incidenceIntegerResidue q z)) =
      ((q : ℂ) ^ 2)⁻¹ * ∑ ξ,
        (∑ r, incidenceJointChar ξ r * f r) *
          ∑' z : ℤ × ℤ, w z * incidenceJointChar ξ (-incidenceIntegerResidue q z) := by
  have hs (ξ : ZMod q × ZMod q) :
      Summable (fun z : ℤ × ℤ => w z * incidenceJointChar ξ (-incidenceIntegerResidue q z)) := by
    apply Summable.of_norm
    simpa only [norm_mul, incidenceJointChar_norm, mul_one] using hw
  calc
    _ = ∑' z : ℤ × ℤ, w z * (((q : ℂ) ^ 2)⁻¹ *
        ∑ ξ, (∑ r, incidenceJointChar ξ r * f r) *
          incidenceJointChar ξ (-incidenceIntegerResidue q z)) := by
      simp only [incidenceJoint_reverse_inversion]
    _ = ((q : ℂ) ^ 2)⁻¹ * ∑' z : ℤ × ℤ,
        ∑ ξ, (∑ r, incidenceJointChar ξ r * f r) *
          (w z * incidenceJointChar ξ (-incidenceIntegerResidue q z)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro z
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ξ _
      ring
    _ = _ := by
      rw [Summable.tsum_finsetSum (fun ξ _ => (hs ξ).mul_left _)]
      simp only [tsum_mul_left]

/-- The finite additive character is the actual real character on integer lifts. -/
theorem incidenceJointChar_integer (ξ : ZMod q × ZMod q) (z : ℤ × ℤ) :
    incidenceJointChar ξ (-incidenceIntegerResidue q z) =
      incidenceRealChar (-((ξ.1.val : ℝ) / q) * (z.1 : ℝ) -
        ((ξ.2.val : ℝ) / q) * (z.2 : ℝ)) := by
  have hz : ξ.1 * -(z.1 : ZMod q) + ξ.2 * -(z.2 : ZMod q) =
      ((-((ξ.1.val : ℤ) * z.1 + (ξ.2.val : ℤ) * z.2) : ℤ) : ZMod q) := by
    simp only [Int.cast_neg, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_zmod_val]
    ring
  change ZMod.stdAddChar (ξ.1 * -(z.1 : ZMod q) + ξ.2 * -(z.2 : ZMod q)) = _
  rw [hz, ZMod.stdAddChar_coe]
  simp only [incidenceRealChar, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

set_option maxHeartbeats 600000 in
/-- Poisson completion of an actual sheared Schwartz window against any periodic response. -/
theorem incidencePeriodic_poisson (u v : 𝓢(ℝ, ℂ)) (τ : ℝ)
    (f : ZMod q × ZMod q → ℂ) :
    (∑' z : ℤ × ℤ, u (z.1 : ℝ) * v ((z.2 : ℝ) - τ * (z.1 : ℝ)) *
      f (incidenceIntegerResidue q z)) =
      ((q : ℂ) ^ 2)⁻¹ * ∑ ξ : ZMod q × ZMod q,
        (∑ r, incidenceJointChar ξ r * f r) *
          ∑' z : ℤ × ℤ, incidenceShearedFourier u v τ
            ((ξ.1.val : ℝ) / q) ((ξ.2.val : ℝ) / q) z := by
  have hw : Summable (fun z : ℤ × ℤ =>
      ‖u (z.1 : ℝ) * v ((z.2 : ℝ) - τ * (z.1 : ℝ))‖) := by
    have hs := (incidenceShearedPhysical_summable u v τ 0 0).norm
    simpa only [incidenceShearedPhysical, neg_zero, zero_mul, sub_zero,
      incidenceRealChar_zero, mul_one] using hs
  rw [incidencePeriodic_completion _ hw f]
  congr 1
  apply Finset.sum_congr rfl
  intro ξ _
  congr 1
  simpa only [incidenceShearedPhysical, incidenceJointChar_integer] using
    incidencePoisson_sheared u v τ ((ξ.1.val : ℝ) / q) ((ξ.2.val : ℝ) / q)

#print axioms incidencePeriodicMul_norm_summable
#print axioms incidenceJoint_reverse_inversion
#print axioms incidencePeriodic_completion
#print axioms incidenceJointChar_integer
#print axioms incidencePeriodic_poisson

end PrimeGap182Audit
