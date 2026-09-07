import TypeIIILocalRectangles

/-!
# The local finite-field input supplies actual mask data

The input remains the explicit finite-exceptional or geometric-curve Fourier bound for the
actual Kloosterman four-cycle.  The bounded-fiber and CRT-scaling consequences are proved
before being packaged for the positive completion theorem.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime]

theorem FiniteExceptionalFourierBound.localMaskData
    {C : ℝ} {D : ℕ} {α m m' n n' : ZMod p}
    (hbound : FiniteExceptionalFourierBound p C D α m m' n n') (u : (ZMod p)ˣ) :
    ∃ E : LocalMaskData p D, E.repeated = false ∧
      ∀ h k : ZMod p,
        ‖fourier₂ p (fourCycle p α m m' n n') ((u : ZMod p) * h) ((u : ZMod p) * k)‖ ≤
          C * (p : ℝ) ^ 3 * localExceptionalEnvelope E h k := by
  obtain ⟨Z, hZ, hF⟩ := hbound
  let E : LocalMaskData p D :=
    { repeated := false
      finiteSet := scaledPairSet p u Z
      curveSet := ∅
      badVertical := ∅
      finite_card := (scaledPairSet_card p u Z).trans_le hZ
      vertical_card := by simp only [Finset.card_empty, Nat.zero_le]
      fiber_card := by intros; simp }
  refine ⟨E, rfl, ?_⟩
  intro h k
  simpa only [E, localExceptionalEnvelope, Bool.false_eq_true, ite_false,
    mem_scaledPairSet, add_zero] using hF ((u : ZMod p) * h) ((u : ZMod p) * k)

theorem CurveExceptionalFourierBound.localMaskData
    {C : ℝ} {D : ℕ} {α m m' n n' : ZMod p}
    (hbound : CurveExceptionalFourierBound p C D α m m' n n') (u : (ZMod p)ˣ) :
    ∃ E : LocalMaskData p D, E.repeated = true ∧
      ∀ h k : ZMod p,
        ‖fourier₂ p (fourCycle p α m m' n n') ((u : ZMod p) * h) ((u : ZMod p) * k)‖ ≤
          C * (p : ℝ) ^ 3 * localExceptionalEnvelope E h k := by
  obtain ⟨Z, hZ, hF⟩ := hbound.finite_fibers p
  obtain ⟨V, hV, hf⟩ := scaledPairSet_boundedVerticalFibers p u D Z hZ
  let E : LocalMaskData p D :=
    { repeated := true
      finiteSet := ∅
      curveSet := scaledPairSet p u Z
      badVertical := V
      finite_card := by simp only [Finset.card_empty, Nat.zero_le]
      vertical_card := hV
      fiber_card := hf }
  have hz (x : ZMod p) : (u : ZMod p) * x = 0 ↔ x = 0 := by
    constructor
    · intro hx
      apply (unitScale p u).injective
      simpa only [unitScale_apply, mul_zero] using hx
    · intro hx
      rw [hx, mul_zero]
  refine ⟨E, rfl, ?_⟩
  intro h k
  simpa only [E, localExceptionalEnvelope, ite_true, mem_scaledPairSet, hz] using
    hF ((u : ZMod p) * h) ((u : ZMod p) * k)

/-- The repetition flag is the actual equality of the row or column residues. -/
theorem localMaskData_of_localFourier
    {C : ℝ} {D : ℕ} (α m m' n n' : ZMod p) (u : (ZMod p)ˣ)
    (hbound : ((m ≠ m' ∧ n ≠ n') → FiniteExceptionalFourierBound p C D α m m' n n') ∧
      ((m = m' ∨ n = n') → CurveExceptionalFourierBound p C D α m m' n n')) :
    ∃ E : LocalMaskData p D, E.repeated = decide (m = m' ∨ n = n') ∧
      ∀ h k : ZMod p,
        ‖fourier₂ p (fourCycle p α m m' n n') ((u : ZMod p) * h) ((u : ZMod p) * k)‖ ≤
          C * (p : ℝ) ^ 3 * localExceptionalEnvelope E h k := by
  by_cases hr : m = m' ∨ n = n'
  · obtain ⟨E, hE, hF⟩ := (hbound.2 hr).localMaskData p u
    exact ⟨E, by simpa only [decide_eq_true hr] using hE, hF⟩
  · have hn : m ≠ m' ∧ n ≠ n' := not_or.mp hr
    obtain ⟨E, hE, hF⟩ := (hbound.1 hn).localMaskData p u
    exact ⟨E, by simpa only [decide_eq_false hr] using hE, hF⟩

#print axioms FiniteExceptionalFourierBound.localMaskData
#print axioms CurveExceptionalFourierBound.localMaskData
#print axioms localMaskData_of_localFourier

end

end PrimeGap182.TypeIII
