import TypeIIIRepeatedAlgebra
import TypeIIISmallPrimes

/-!
# Reductions for the actual repeated-index Fourier estimate

Swapping the two polynomial variables transports the exceptional curve with
the same degree bound.  The repeated-column branch is therefore implied by
the repeated-row branch at the same uniform constants.  Independently, the
origin bound follows from the already isolated baseline local inputs.

These are exact reductions, not a proof of the remaining nonzero-frequency
estimate.  No statement in this module supplies its exceptional curve.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- Swap the coordinates of an actual exceptional polynomial. -/
def repeatedPlaneSwap
    (P : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p))) :
    MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p)) :=
  MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) P

theorem repeatedPlaneSwap_ne_zero
    {P : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p))} (hP : P ≠ 0) :
    repeatedPlaneSwap p P ≠ 0 := by
  exact fun h => hP ((MvPolynomial.rename_eq_zero_iff_of_injective P
    (Equiv.swap (0 : Fin 2) 1).injective).mp h)

theorem repeatedPlaneSwap_totalDegree_le
    (P : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p))) :
    (repeatedPlaneSwap p P).totalDegree ≤ P.totalDegree :=
  MvPolynomial.totalDegree_rename_le _ _

theorem planeEval_repeatedPlaneSwap
    (P : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p))) (h k : ZMod p) :
    planeEval p (repeatedPlaneSwap p P) h k = planeEval p P k h := by
  simp only [planeEval, repeatedPlaneSwap, MvPolynomial.eval_rename]
  congr 2
  funext i
  fin_cases i <;> simp

/-- The exact transpose transports a genuinely nonzero curve and preserves
its fixed degree and Fourier constants. -/
theorem CurveExceptionalFourierBound.of_transpose
    {C : ℝ} {D : ℕ} {α m m' n n' : ZMod p}
    (hbound : CurveExceptionalFourierBound p C D (-α) n n' m m') :
    CurveExceptionalFourierBound p C D α m m' n n' := by
  obtain ⟨P, hP, hD, hF⟩ := hbound
  refine ⟨repeatedPlaneSwap p P, repeatedPlaneSwap_ne_zero p hP,
    (repeatedPlaneSwap_totalDegree_le p P).trans hD, ?_⟩
  intro h k
  have hf := hF k h
  rw [fourier₂_fourCycle_transpose] at hf
  simpa only [planeEval_repeatedPlaneSwap, and_comm] using hf

/-- To treat every repeated index, it suffices to prove the repeated-row
case for all nonzero parameters.  The common constants are unchanged. -/
theorem repeated_curve_of_rows
    {C : ℝ} {D : ℕ}
    (hrows : ∀ α m n n' : ZMod p,
      α ≠ 0 → m ≠ 0 → n ≠ 0 → n' ≠ 0 →
        CurveExceptionalFourierBound p C D α m m n n')
    (α m m' n n' : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0)
    (hrep : m = m' ∨ n = n') :
    CurveExceptionalFourierBound p C D α m m' n n' := by
  rcases hrep with h | h
  · subst m'
    exact hrows α m n n' hα hm hn hn'
  · subst n'
    exact (hrows (-α) n m m' (neg_ne_zero.mpr hα) hn hm hm').of_transpose p

/-- The original baseline inputs give the correct `p^4` origin scale with
one constant uniform in the prime and every nonzero parameter.  The same
coarse inequality holds at all frequencies and all index multiplicities. -/
theorem fourier₂_fourCycle_le_baseline_fourth_power
    (hbase : BaselineLocalInputs)
    (α m m' n n' h k : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    ‖fourier₂ p (fourCycle p α m m' n n') h k‖ ≤ 6561 * (p : ℝ) ^ 4 := by
  calc
    _ ≤ (p : ℝ) ^ 2 * (6561 * (p : ℝ) ^ 2) :=
      fourier₂_norm_le_uniform p _ _
        (fun x y => fourCycle_norm_le_baseline_inputs hbase p α m m' n n' x y
          hα hm hm' hn hn') h k
    _ = _ := by ring

/-- Once the nonzero-frequency estimates have been established for an
actual nonzero polynomial, the origin needs no new finite-field input.
The premise here is the precise remaining estimate, not a proved input. -/
theorem curveExceptional_of_nonzero_frequencies
    (hbase : BaselineLocalInputs) {C : ℝ} (hC : 6561 ≤ C) {D : ℕ}
    (α m m' n n' : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0)
    (P : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p)))
    (hP : P ≠ 0) (hD : P.totalDegree ≤ D)
    (hF : ∀ h k : ZMod p, ¬ (h = 0 ∧ k = 0) →
      ‖fourier₂ p (fourCycle p α m m' n n') h k‖ ≤
        C * (p : ℝ) ^ 3 *
          (1 + Real.sqrt (p : ℝ) * if planeEval p P h k = 0 then 1 else 0)) :
    CurveExceptionalFourierBound p C D α m m' n n' := by
  have hC0 : 0 ≤ C := by linarith
  refine ⟨P, hP, hD, ?_⟩
  intro h k
  by_cases hzero : h = 0 ∧ k = 0
  · obtain ⟨rfl, rfl⟩ := hzero
    simp only [and_self, ite_true]
    calc
      _ ≤ 6561 * (p : ℝ) ^ 4 :=
        fourier₂_fourCycle_le_baseline_fourth_power p hbase α m m' n n' 0 0
          hα hm hm' hn hn'
      _ ≤ C * (p : ℝ) ^ 4 := mul_le_mul_of_nonneg_right hC (by positivity)
      _ = (C * (p : ℝ) ^ 3) * (p : ℝ) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        split_ifs <;> nlinarith [Real.sqrt_nonneg (p : ℝ)]
  · simpa only [ite_eq_right hzero, mul_zero, add_zero] using hF h k hzero

#print axioms repeatedPlaneSwap_ne_zero
#print axioms repeatedPlaneSwap_totalDegree_le
#print axioms planeEval_repeatedPlaneSwap
#print axioms CurveExceptionalFourierBound.of_transpose
#print axioms repeated_curve_of_rows
#print axioms fourier₂_fourCycle_le_baseline_fourth_power
#print axioms curveExceptional_of_nonzero_frequencies

end

end PrimeGap182.TypeIII
