import TypeIIIGeometricAssembly
import TypeIIIBoundary

/-!
# Arithmetic assembly of fifteen actual corrected Type III estimates

This theorem restores the omitted physical points and combines the fifteen
finite exceptional sets. Its input inequalities are written directly for
`actualRestrictedCoreSubproduct`, using the original arithmetic kernel.
Those inequalities are still unproved here. In particular this file neither
constructs `LocalFourierHypothesis` nor supplies its missing sheaf theory.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

/-- Exact end-stage arithmetic assembly. The hypotheses `hcore` retain all
fifteen genuine corrected-core Fourier estimates as visible obligations. -/
theorem finiteExceptionalFourierBound_of_actual_core_bounds
    (hbase : BaselineLocalInputs) (p : ℕ) [Fact p.Prime]
    (C : ℝ) (hC : 0 ≤ C) (Dphys Dcore : ℕ)
    (U : Finset (ZMod p × ZMod p))
    (hU : (Finset.univ \ U).card ≤ 2 * Dphys * p)
    (α m m' n n' : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0)
    (hn : n ≠ 0) (hn' : n' ≠ 0)
    (Z : Finset (Fin 4) → Finset (ZMod p × ZMod p))
    (hZ : ∀ S ∈ nonemptyCoreSubsets, (Z S).card ≤ Dcore)
    (hcore : ∀ S ∈ nonemptyCoreSubsets, ∀ h k : ZMod p,
      ‖fourier₂ p (actualRestrictedCoreSubproduct p U α m m' n n' S) h k‖ ≤
        C * (p : ℝ) ^ 3 *
          (1 + Real.sqrt (p : ℝ) * if (h, k) ∈ Z S then 1 else 0)) :
    FiniteExceptionalFourierBound p (81 + 175 * C + 13122 * Dphys)
      (15 * Dcore) α m m' n n' := by
  let Zall := assembledCoreExceptionalSet p Z
  refine ⟨Zall, assembledCoreExceptionalSet_card_le p Z Dcore hZ, ?_⟩
  intro h k
  let E : ℝ := 1 + Real.sqrt (p : ℝ) * if (h, k) ∈ Zall then 1 else 0
  have hE : 1 ≤ E := by
    dsimp only [E]
    exact le_add_of_nonneg_right (by positivity)
  have hE₀ : 0 ≤ E := le_trans zero_le_one hE
  have hp₀ : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast (NeZero.one_le : 1 ≤ p)
  have hp₂ : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (p : ℝ)) (sub_nonneg.mpr hp₁)]
  have hCp : 0 ≤ C * (p : ℝ) ^ 3 := mul_nonneg hC (pow_nonneg hp₀ _)
  have hcores : ∀ S ∈ nonemptyCoreSubsets,
      ‖fourier₂ p (actualRestrictedCoreSubproduct p U α m m' n n' S) h k‖ ≤
        C * (p : ℝ) ^ 3 * E := by
    intro S hS
    apply (hcore S hS h k).trans
    apply mul_le_mul_of_nonneg_left _ hCp
    by_cases hpair : (h, k) ∈ Z S
    · have hall : (h, k) ∈ Zall := core_exceptional_subset_assembled p Z S hS hpair
      simp only [E, ite_eq_left hpair, ite_eq_left hall, le_refl]
    · simp only [ite_eq_right hpair, mul_zero, add_zero]
      exact hE
  have hrestricted := actual_fourCycle_fourier_le_of_core_bounds p U α m m' n n' h k
    (C * (p : ℝ) ^ 3 * E) (mul_nonneg hCp hE₀) hcores
  have hboundary := raw_fourCycle_physicalBoundary_norm_le hbase p Dphys
    (Finset.univ \ U) hU α m m' n n' hα hm hm' hn hn' h k
  change ‖fourier₂ p (fourCycle p α m m' n n') h k‖ ≤
    (81 + 175 * C + 13122 * Dphys) * (p : ℝ) ^ 3 * E
  rw [fourier₂_eq_restriction_add_boundary p U]
  apply (norm_add_le _ _).trans
  have hrestricted' :
      ‖fourier₂ p (physicalRestriction p U (fourCycle p α m m' n n')) h k‖ ≤
        81 * (p : ℝ) ^ 2 + 175 * (C * (p : ℝ) ^ 3 * E) := by
    exact hrestricted
  apply (add_le_add hrestricted' hboundary).trans
  have hpE : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ 3 * E := by
    exact hp₂.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hE (pow_nonneg hp₀ 3))
  have hbE : 13122 * (Dphys : ℝ) * (p : ℝ) ^ 3 ≤
      13122 * (Dphys : ℝ) * (p : ℝ) ^ 3 * E := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hE
      (by positivity : 0 ≤ 13122 * (Dphys : ℝ) * (p : ℝ) ^ 3)
  nlinarith [mul_le_mul_of_nonneg_left hpE (by norm_num : (0 : ℝ) ≤ 81)]

#print axioms finiteExceptionalFourierBound_of_actual_core_bounds

end

end PrimeGap182.TypeIII
