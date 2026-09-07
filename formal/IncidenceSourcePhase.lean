import IncidenceAffineWindow

/-!
# Exact conversion of the reduced source phase to the incidence kernel

The reciprocal phase is the baseline's actual zero-extended unit phase.
Cancellation is proved with the pole masks present, including nonunit rows.
The displayed source substitution is e=tE and λ=t·r, with r=w₂a a unit
modulo the remaining oscillatory modulus.
-/

noncomputable section

namespace PrimeGap182Audit

open scoped BigOperators

variable {q : ℕ} [NeZero q]

theorem incidenceReciprocalPhase_cancel_unit (u : (ZMod q)ˣ) (A x : ZMod q) :
    PrimeGap186.reciprocalUnitPhase q (A * (u : ZMod q)) (x * (u : ZMod q)) =
      PrimeGap186.reciprocalUnitPhase q A x := by
  classical
  by_cases hx : IsUnit x
  · rw [PrimeGap186.reciprocalUnitPhase, PrimeGap186.reciprocalUnitPhase,
      ite_eq_left (hx.mul u.isUnit), ite_eq_left hx,
      PrimeGap186.sourcePhase_inv_mul x (u : ZMod q) hx u.isUnit, ZMod.inv_coe_unit]
    congr 1
    calc
      _ = A * (((u : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) * x⁻¹) := by ring
      _ = _ := by rw [Units.mul_inv]; ring
  · have hxu : ¬ IsUnit (x * (u : ZMod q)) := by simpa only [IsUnit.mul_iff, u.isUnit, and_true]
    simp only [PrimeGap186.reciprocalUnitPhase, ite_eq_right hxu, ite_eq_right hx]

theorem incidenceReciprocalPhase_unit_denominator (u : (ZMod q)ˣ) (A x : ZMod q) :
    PrimeGap186.reciprocalUnitPhase q A ((u : ZMod q) * x) =
      PrimeGap186.reciprocalUnitPhase q (A * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) x := by
  have h := incidenceReciprocalPhase_cancel_unit u
    (A * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) x
  simpa only [mul_assoc, Units.inv_mul, mul_one, mul_comm (u : ZMod q) x] using h

theorem incidenceMatrixMod_eq_reciprocalPhase (A E γ b : ZMod q) :
    incidenceMatrixMod A (E, γ) b =
      PrimeGap186.reciprocalUnitPhase q A (E * (γ + E * b)) := rfl

set_option maxHeartbeats 600000 in
/-- The exact reduced source phase, with every pole mask retained. -/
theorem incidenceSource_phase (s t r : (ZMod q)ˣ) (A E γ k B : ZMod q) :
    PrimeGap186.reciprocalUnitPhase q (A * ((t * r : (ZMod q)ˣ) : ZMod q))
      ((s : ZMod q) * ((t : ZMod q) * E) *
        (γ * ((t * r : (ZMod q)ˣ) : ZMod q) + ((t : ZMod q) * E) * (k + B))) =
      incidenceMatrixMod (A * (((s * t)⁻¹ : (ZMod q)ˣ) : ZMod q))
        (E, γ) ((k + B) * ((r⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
  let D : ZMod q := E * (γ + E * ((k + B) * ((r⁻¹ : (ZMod q)ˣ) : ZMod q)))
  have hden : (s : ZMod q) * ((t : ZMod q) * E) *
      (γ * ((t * r : (ZMod q)ˣ) : ZMod q) + ((t : ZMod q) * E) * (k + B)) =
      (((s * t : (ZMod q)ˣ) : ZMod q) * D) * ((t * r : (ZMod q)ˣ) : ZMod q) := by
    dsimp [D]
    have hr : (r : ZMod q) * ((r⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := Units.mul_inv r
    linear_combination -((s : ZMod q) * (t : ZMod q) ^ 2 * E ^ 2 * (k + B)) * hr
  rw [hden, incidenceReciprocalPhase_cancel_unit,
    incidenceReciprocalPhase_unit_denominator, incidenceMatrixMod_eq_reciprocalPhase]

omit [NeZero q] in
/-- The new coefficient is a unit whenever the original coefficient is a unit. -/
theorem incidenceSource_coefficient_isUnit (s t : (ZMod q)ˣ) (A : ZMod q) (hA : IsUnit A) :
    IsUnit (A * (((s * t)⁻¹ : (ZMod q)ˣ) : ZMod q)) := hA.mul ((s * t)⁻¹).isUnit

#print axioms incidenceReciprocalPhase_cancel_unit
#print axioms incidenceReciprocalPhase_unit_denominator
#print axioms incidenceMatrixMod_eq_reciprocalPhase
#print axioms incidenceSource_phase
#print axioms incidenceSource_coefficient_isUnit

end PrimeGap182Audit
