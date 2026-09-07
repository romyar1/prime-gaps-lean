import IncidenceSourcePhase

/-!
# The actual CRT and pole-mask factors in the Type II source phase

The zero-extended reciprocal phase is split before any row restrictions
are discarded. A zero local numerator leaves an input unit mask, not a
factor equal to one on all inputs. The fixed q₀ phase is a coefficient
multiplier of norm one. The change of the remaining shift is modular.
-/

noncomputable section

namespace PrimeGap182Audit

open scoped BigOperators

/-- CRT for the actual zero-extended reciprocal phase at any numerator. -/
theorem incidenceReciprocalPhase_crt {m n : ℕ} [NeZero m] [NeZero n]
    (hmn : m.Coprime n) (A x : ZMod (m * n)) :
    PrimeGap186.reciprocalUnitPhase (m * n) A x =
      PrimeGap186.reciprocalUnitPhase m (incidenceCRTScaledLeft hmn A)
        (incidenceCRTLeft hmn x) *
      PrimeGap186.reciprocalUnitPhase n (incidenceCRTScaledRight hmn A)
        (incidenceCRTRight hmn x) := by
  simpa only [incidenceMatrixMod, PrimeGap186.reciprocalUnitPhase,
    map_one, map_zero, mul_zero, add_zero, one_mul] using
      incidenceMatrixMod_crt hmn A (1, x) 0

/-- The surviving local factor at numerator zero, with its pole mask. -/
theorem incidenceReciprocalPhase_zero_numerator {q : ℕ} [NeZero q] (x : ZMod q) :
    PrimeGap186.reciprocalUnitPhase q 0 x = if IsUnit x then 1 else 0 := by
  classical
  simp only [PrimeGap186.reciprocalUnitPhase, zero_mul, AddChar.map_zero_eq_one]

theorem incidenceReciprocalPhase_norm_of_unit {q : ℕ} [NeZero q]
    (A x : ZMod q) (hx : IsUnit x) :
    ‖PrimeGap186.reciprocalUnitPhase q A x‖ = 1 := by
  simp only [PrimeGap186.reciprocalUnitPhase, ite_eq_left hx,
    ZMod.stdAddChar_apply, Circle.norm_coe]

/-- A zero numerator on the left CRT factor leaves precisely the stated
input mask when its row factor is a unit. No factor depending on m occurs. -/
theorem incidenceSource_zero_crt_factor {m n : ℕ} [NeZero m] [NeZero n]
    (hmn : m.Coprime n) (A x : ZMod (m * n))
    (u : (ZMod m)ˣ) (k B : ZMod m)
    (hA : incidenceCRTLeft hmn A = 0)
    (hx : incidenceCRTLeft hmn x = (u : ZMod m) * (k + B)) :
    PrimeGap186.reciprocalUnitPhase (m * n) A x =
      (if IsUnit (k + B) then 1 else 0) *
        PrimeGap186.reciprocalUnitPhase n (incidenceCRTScaledRight hmn A)
          (incidenceCRTRight hmn x) := by
  classical
  rw [incidenceReciprocalPhase_crt hmn]
  have hzero : incidenceCRTScaledLeft hmn A = 0 := by
    simp only [incidenceCRTScaledLeft, hA, mul_zero]
  rw [hzero, incidenceReciprocalPhase_zero_numerator, hx]
  simp only [IsUnit.mul_iff, u.isUnit, true_and]

/-- The q₀ factor is independent of the other row coordinates after the
compatibility line and row residue class are fixed. -/
theorem incidenceSource_fixed_crt_factor {m n : ℕ} [NeZero m] [NeZero n]
    (hmn : m.Coprime n) (A ell c e n₁ B : ZMod (m * n))
    (c₀ e₀ ζ B₀ : ZMod m)
    (hc : incidenceCRTLeft hmn c = c₀)
    (he : incidenceCRTLeft hmn e = e₀)
    (hn : incidenceCRTLeft hmn n₁ = ζ * e₀)
    (hB : incidenceCRTLeft hmn B = B₀)
    (hu : IsUnit (c₀ * e₀ ^ 2 * (ζ + B₀))) :
    PrimeGap186.reciprocalUnitPhase (m * n) (A * ell)
        (c * e * (n₁ + B * e)) =
      ZMod.stdAddChar
        (((n : ZMod m)⁻¹ * incidenceCRTLeft hmn A * incidenceCRTLeft hmn ell) *
          (c₀ * e₀ ^ 2 * (ζ + B₀))⁻¹) *
        PrimeGap186.reciprocalUnitPhase n
          ((m : ZMod n)⁻¹ * incidenceCRTRight hmn A * incidenceCRTRight hmn ell)
          (incidenceCRTRight hmn c * incidenceCRTRight hmn e *
            (incidenceCRTRight hmn n₁ + incidenceCRTRight hmn B *
              incidenceCRTRight hmn e)) := by
  have hden : incidenceCRTLeft hmn (c * e * (n₁ + B * e)) =
      c₀ * e₀ ^ 2 * (ζ + B₀) := by
    simp only [map_mul, map_add, hc, he, hn, hB]
    ring
  rw [incidenceReciprocalPhase_crt hmn, hden]
  conv_lhs =>
    lhs
    rw [PrimeGap186.reciprocalUnitPhase, ite_eq_left hu]
  simp only [incidenceCRTScaledLeft, incidenceCRTScaledRight, map_mul, map_add, mul_assoc]

/-- The source shift is modular: its numerator need not be divisible by
the integer represented by u. -/
theorem incidenceSource_modular_shift {q : ℕ} [NeZero q]
    (u : (ZMod q)ˣ) (A c e n₂ B ζ : ZMod q) :
    PrimeGap186.reciprocalUnitPhase q A
        (c * e * (ζ * e + (u : ZMod q) * n₂ + B * e)) =
      PrimeGap186.reciprocalUnitPhase q
        (A * ((u⁻¹ : (ZMod q)ˣ) : ZMod q))
        (c * e * (n₂ + (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * (B + ζ)) * e)) := by
  have hden : c * e * (ζ * e + (u : ZMod q) * n₂ + B * e) =
      (u : ZMod q) *
        (c * e * (n₂ + (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * (B + ζ)) * e)) := by
    have hu : (u : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := Units.mul_inv u
    linear_combination -(c * e ^ 2 * (B + ζ)) * hu
  rw [hden, incidenceReciprocalPhase_unit_denominator]

/-- Coefficient-only unit phases preserve the actual coefficient energy. -/
theorem incidenceSource_coefficient_phase_energy {ι : Type*} [Fintype ι]
    (c θ : ι → ℂ) (hθ : ∀ i, ‖θ i‖ = 1) :
    (∑ i, ‖θ i * c i‖ ^ 2) = ∑ i, ‖c i‖ ^ 2 := by
  simp only [norm_mul, hθ, one_mul]

#print axioms incidenceReciprocalPhase_crt
#print axioms incidenceReciprocalPhase_zero_numerator
#print axioms incidenceReciprocalPhase_norm_of_unit
#print axioms incidenceSource_zero_crt_factor
#print axioms incidenceSource_fixed_crt_factor
#print axioms incidenceSource_modular_shift
#print axioms incidenceSource_coefficient_phase_energy

end PrimeGap182Audit
