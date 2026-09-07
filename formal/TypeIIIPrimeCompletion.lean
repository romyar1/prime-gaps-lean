import TypeIIIIntervalCompletion

/-!
# Completed interval bounds for the actual prime-modulus four-cycle

These are proved consequences of the explicit new local Fourier hypotheses. They are not
proofs of those hypotheses. The actual integer intervals, actual four-cycle, finite exceptional
set and polynomial-curve fiber bounds are all retained in the statements and derivation.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

@[simp] theorem intervalFourier_zero
    (s : ℕ) [NeZero s] (A : ℤ) (N : ℕ) : intervalFourier s A N 0 = (N : ℂ) := by
  simp only [intervalFourier, mul_zero, neg_zero, AddChar.map_zero_eq_one,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

@[simp] theorem frequencyMass_origin
    (s : ℕ) [NeZero s] (Ah Ak : ℤ) (Nh Nk : ℕ) :
    frequencyMass s Ah Ak Nh Nk {(0, 0)} = (Nh : ℝ) * Nk := by
  simp [frequencyMass]

private theorem product_total_mass_le
    (s : ℕ) [NeZero s] (Ah Ak : ℤ) (Nh Nk : ℕ) :
    (∑ h : ZMod s, ‖intervalFourier s Ah Nh h‖) *
      (∑ k : ZMod s, ‖intervalFourier s Ak Nk k‖) ≤
        intervalMassBound s 1 Nh * intervalMassBound s 1 Nk :=
  mul_le_mul (intervalFourier_total_l1 s Ah Nh) (intervalFourier_total_l1 s Ak Nk)
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (intervalMassBound_nonneg s 1 Nh)

private theorem completion_factor (p : ℕ) [Fact p.Prime] (C : ℝ) :
    ((p : ℝ)⁻¹) ^ 2 * (C * (p : ℝ) ^ 3) = C * p := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp

/-- Finite exceptional frequencies give a proved incomplete four-cycle bound. -/
theorem FiniteExceptionalFourierBound.interval_sum
    (p : ℕ) [Fact p.Prime] {C : ℝ} {D : ℕ} {α m m' n n' : ZMod p}
    (hC : 0 ≤ C) (hbound : FiniteExceptionalFourierBound p C D α m m' n n')
    (Ah Ak : ℤ) (Nh Nk : ℕ) :
    ‖intervalRectangleSum p Ah Ak Nh Nk (fourCycle p α m m' n n')‖ ≤
      C * p * (intervalMassBound p 1 Nh * intervalMassBound p 1 Nk +
        Real.sqrt (p : ℝ) * ((D : ℝ) * Nh * Nk)) := by
  classical
  obtain ⟨Z, hZ, hF⟩ := hbound
  have hh := intervalRectangleSum_norm_le_two_indicators p Ah Ak Nh Nk
    (fourCycle p α m m' n n') Z ∅ (C * (p : ℝ) ^ 3) (Real.sqrt (p : ℝ)) 0
    (by
      intro h k
      simpa only [zero_mul, add_zero] using hF h k)
  simp only [zero_mul, add_zero, completion_factor] at hh
  have hmass : frequencyMass p Ah Ak Nh Nk Z ≤ (D : ℝ) * Nh * Nk := by
    apply (frequencyMass_le_card p Ah Ak Nh Nk Z).trans
    gcongr
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (Nat.cast_nonneg _))
  exact add_le_add (product_total_mass_le p Ah Ak Nh Nk)
    (mul_le_mul_of_nonneg_left hmass (Real.sqrt_nonneg _))

/-- A bounded-degree exceptional curve gives the corresponding incomplete four-cycle
bound. Its fiber estimate is derived from the actual polynomial witness. -/
theorem CurveExceptionalFourierBound.interval_sum
    (p : ℕ) [Fact p.Prime] {C : ℝ} {D : ℕ} {α m m' n n' : ZMod p}
    (hC : 0 ≤ C) (hbound : CurveExceptionalFourierBound p C D α m m' n n')
    (Ah Ak : ℤ) (Nh Nk : ℕ) :
    ‖intervalRectangleSum p Ah Ak Nh Nk (fourCycle p α m m' n n')‖ ≤
      C * p * (intervalMassBound p 1 Nh * intervalMassBound p 1 Nk +
        Real.sqrt (p : ℝ) *
          ((D : ℝ) * ((Nh : ℝ) * intervalMassBound p 1 Nk) +
            (D : ℝ) * ((Nk : ℝ) * intervalMassBound p 1 Nh)) +
        (p : ℝ) * ((Nh : ℝ) * Nk)) := by
  classical
  obtain ⟨E, hE, hF⟩ := hbound.finite_fibers p
  have hh := intervalRectangleSum_norm_le_two_indicators p Ah Ak Nh Nk
    (fourCycle p α m m' n n') E {(0, 0)}
    (C * (p : ℝ) ^ 3) (Real.sqrt (p : ℝ)) p
    (by
      intro h k
      simpa only [Finset.mem_singleton, Prod.mk.injEq] using hF h k)
  rw [completion_factor, frequencyMass_origin] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (Nat.cast_nonneg _))
  apply add_le_add _ le_rfl
  exact add_le_add (product_total_mass_le p Ah Ak Nh Nk)
    (mul_le_mul_of_nonneg_left
      (frequencyMass_le_of_boundedVerticalFibers p D Ah Ak Nh Nk E hE)
      (Real.sqrt_nonneg _))

#print axioms FiniteExceptionalFourierBound.interval_sum
#print axioms CurveExceptionalFourierBound.interval_sum

end

end PrimeGap182.TypeIII
