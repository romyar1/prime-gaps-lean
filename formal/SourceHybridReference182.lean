import SourceBoundary182

/-! Exact actual-mask nesting and the signed physical hybrid polynomial.
The true sharp-deficit parameter is retained; at the binary reference masks
the two mixed terms cancel its dependence exactly. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

theorem trialActualBase_subset_enlarged (Y : Fin 38 → FiniteMeasure ℝ) :
    TrialActualBase Y → TrialActualEnlarged Y := by
  rintro ⟨hShell, hcap, hrow⟩
  exact ⟨trialBase_subset_enlarged Y hShell, hcap,
    fun R hR => hrow R (List.mem_append_right _ hR)⟩

theorem trialEnlarged_subset_subtraction_shell (Y : Fin 38 → FiniteMeasure ℝ) :
    TrialShellDomain 2 Y → TrialShellDomain 3 Y := by
  rw [trialEnlarged_grid_iff]
  rintro ⟨hr, hcap⟩
  apply (trialShellDomain_grid_iff 3 Y).mpr
  by_cases hlow : (∑ i, trialCellIndex (Y i)) + 38 ≤ 352736
  · refine ⟨⟨0, 352736, 246256⟩, by decide, ?_⟩
    refine ⟨by change _ < 393177; omega, by change 0 < _ + 38; omega, hlow, ?_⟩
    apply trialCapAllowed_mono _ hcap
    apply mul_le_mul_of_nonneg_right _ trialMesh_pos.le
    split_ifs <;> norm_num
  · refine ⟨⟨352736, 371709, 186491⟩, by decide, ?_⟩
    refine ⟨by change _ < 393177; omega, by change 352736 < _ + 38; omega,
      by change _ + 38 ≤ 371709; omega, ?_⟩
    apply trialCapAllowed_mono _ hcap
    apply mul_le_mul_of_nonneg_right _ trialMesh_pos.le
    split_ifs <;> norm_num
    omega

set_option maxRecDepth 10000 in
theorem trialSubtraction_inner_witness :
    ∃ i : Fin trialNewSourceRows.length,
      let R := trialNewSourceRows.get i
      R.order = 2 ∧ R.innerCore ≤ trialSubtractionSourceRow.outerCore ∧
        R.activation ≤ trialSubtractionSourceRow.activation ∧
        R.innerThreshold ≤ trialSubtractionSourceRow.outerThreshold := by
  refine ⟨⟨14, by decide⟩, ?_⟩
  decide +kernel

theorem trialActualEnlarged_subset_subtraction (Y : Fin 38 → FiniteMeasure ℝ) :
    TrialActualEnlarged Y → TrialActualSubtraction Y := by
  rintro ⟨hShell, hcap, hrows⟩
  have hs := trialEnlarged_subset_subtraction_shell Y hShell
  refine ⟨hs, hcap, trialSubtraction_shell_total Y hs, ?_⟩
  obtain ⟨i, hi⟩ := trialSubtraction_inner_witness
  let R := trialNewSourceRows.get i
  have hR : TrialInnerRowAllowed R Y := hrows R (List.get_mem _ i)
  have horder : R.order = 2 := hi.1
  rcases hR with hOne | hcore | hbad
  · omega
  · exact Or.inl (hcore.trans (Rat.cast_le.mpr hi.2.1))
  · right
    apply measure_mono_null _ hbad
    intro p hp
    change (trialSubtractionSourceRow.activation : ℝ) < p ∧
      (trialSubtractionSourceRow.outerThreshold : ℝ) < (trialWeightedMeasure Y).real (Set.Ici p) + p at hp
    change (R.activation : ℝ) < p ∧
      (if R.order ≤ 2 then (R.innerThreshold : ℝ) < (trialWeightedMeasure Y).real (Set.Ici p) + p
        else _) 
    rw [ite_eq_left (by omega : R.order ≤ 2)]
    exact ⟨(Rat.cast_le.mpr hi.2.2.1).trans_lt hp.1, (Rat.cast_le.mpr hi.2.2.2).trans_lt hp.2⟩

theorem trialActualFaceMasks_nested (Y : Fin 38 → FiniteMeasure ℝ) :
    (trialActualBaseMask Y = 0 ∨ trialActualBaseMask Y = 1) ∧
    (trialActualEnlargedMask Y = 0 ∨ trialActualEnlargedMask Y = 1) ∧
    (trialActualSubtractionMask Y = 0 ∨ trialActualSubtractionMask Y = 1) ∧
    trialActualBaseMask Y ≤ trialActualEnlargedMask Y ∧
    trialActualEnlargedMask Y ≤ trialActualSubtractionMask Y := by
  have hbe := trialActualBase_subset_enlarged Y
  have hec := trialActualEnlarged_subset_subtraction Y
  unfold trialActualBaseMask trialActualEnlargedMask trialActualSubtractionMask
  split_ifs <;> simp_all

def trialPhysicalHybridPolynomial (κ K U B C H : ℝ) : ℝ :=
  2 * U * B - B ^ 2 +
    2 * (1 - (trialLambda : ℝ)) * (1 - κ) * (U - B) * H +
    2 * (1 - (trialLambda : ℝ)) * κ * (C - B) * H -
    ((1 - (trialLambda : ℝ)) ^ 2 +
      (1 - (trialLambda : ℝ)) ^ 2 * (trialKappa : ℝ) / trialHybridLoss) * H ^ 2 -
    trialHybridLoss * K * (U - C) ^ 2

theorem trialHybrid_parameter_cancellation :
    (1 - (trialLambda : ℝ)) ^ 2 +
      (1 - (trialLambda : ℝ)) ^ 2 * (trialKappa : ℝ) / trialHybridLoss =
        1 - (trialLambda : ℝ) := by
  norm_num [trialLambda, trialKappa, trialHybridLoss]

theorem trialPhysicalHybridPolynomial_reference (κ U : ℝ) (Y : Fin 38 → FiniteMeasure ℝ) :
    trialPhysicalHybridPolynomial κ (trialFaceKernel Y) U
      (trialActualBaseMask Y * U) (trialActualSubtractionMask Y * U)
      ((trialActualEnlargedMask Y - trialActualBaseMask Y) * U) =
        trialActualFaceMultiplier Y * U ^ 2 := by
  obtain ⟨hb, he, hc, hbe, hec⟩ := trialActualFaceMasks_nested Y
  unfold trialPhysicalHybridPolynomial
  rw [trialHybrid_parameter_cancellation]
  unfold trialActualFaceMultiplier
  rcases hb with hb | hb <;> rcases he with he | he <;> rcases hc with hc | hc
  all_goals rw [hb, he] at hbe
  all_goals rw [he, hc] at hec
  all_goals rw [hb, he, hc]
  all_goals linarith only [hbe, hec]

#print axioms trialActualFaceMasks_nested
#print axioms trialPhysicalHybridPolynomial_reference

end PrimeGap182
