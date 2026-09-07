import SourceActualCover182

/-! A measurable soft partition of the actual bad outer set. The
partition is formed from true events before comparison to count kernels. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace PrimeGap182

def trialOuterBadMask (X : Fin 39 → FiniteMeasure ℝ) : ℝ :=
  if TrialShellDomain 0 X ∧ ¬ TrialActualOuter X then 1 else 0

def trialOuterCoverSum (X : Fin 39 → FiniteMeasure ℝ) : ℝ :=
  ∑ j : Fin 60, trialOuterCoverIndicator j X

def trialOuterPartition (j : Fin 60) (X : Fin 39 → FiniteMeasure ℝ) : ℝ :=
  trialOuterBadMask X * trialOuterCoverIndicator j X / trialOuterCoverSum X

theorem measurable_trialOuterBadMask : Measurable trialOuterBadMask :=
  Measurable.ite ((measurableSet_trialShellDomain 0).inter measurableSet_trialActualOuter.compl)
    measurable_const measurable_const

theorem measurable_trialOuterCoverSum : Measurable trialOuterCoverSum :=
  Finset.measurable_sum _ fun j _ => measurable_trialOuterCoverIndicator j

theorem measurable_trialOuterPartition (j : Fin 60) : Measurable (trialOuterPartition j) :=
  (measurable_trialOuterBadMask.mul (measurable_trialOuterCoverIndicator j)).div
    measurable_trialOuterCoverSum

theorem trialOuterBadMask_bounds (X : Fin 39 → FiniteMeasure ℝ) :
    0 ≤ trialOuterBadMask X ∧ trialOuterBadMask X ≤ 1 := by
  unfold trialOuterBadMask
  split_ifs <;> norm_num

theorem trialOuterCoverSum_nonneg (X : Fin 39 → FiniteMeasure ℝ) : 0 ≤ trialOuterCoverSum X :=
  Finset.sum_nonneg fun j _ => (trialOuterCoverIndicator_le_kernel j X).1

theorem trialOuterCoverSum_one_le (X : Fin 39 → FiniteMeasure ℝ)
    (j : Fin 60) (hE : TrialOuterCoverEvent j X) : 1 ≤ trialOuterCoverSum X := by
  have hI : trialOuterCoverIndicator j X = 1 :=
    Set.indicator_of_mem (s := {Y | TrialOuterCoverEvent j Y}) hE _
  simpa only [trialOuterCoverSum, hI] using Finset.single_le_sum
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin 60))) =>
      (trialOuterCoverIndicator_le_kernel k X).1) (Finset.mem_univ j)

theorem trialOuterPartition_bounds (j : Fin 60) (X : Fin 39 → FiniteMeasure ℝ) :
    0 ≤ trialOuterPartition j X ∧
      trialOuterPartition j X ≤ trialOuterCoverIndicator j X ∧ trialOuterPartition j X ≤ 1 := by
  have h0 : 0 ≤ trialOuterPartition j X := div_nonneg
    (mul_nonneg (trialOuterBadMask_bounds X).1 (trialOuterCoverIndicator_le_kernel j X).1)
    (trialOuterCoverSum_nonneg X)
  by_cases hE : TrialOuterCoverEvent j X
  · have hI : trialOuterCoverIndicator j X = 1 :=
      Set.indicator_of_mem (s := {Y | TrialOuterCoverEvent j Y}) hE _
    have hS : 1 ≤ trialOuterCoverSum X := trialOuterCoverSum_one_le X j hE
    have hle : trialOuterPartition j X ≤ 1 := by
      rw [trialOuterPartition, hI, mul_one]
      apply (div_le_one (lt_of_lt_of_le zero_lt_one hS)).mpr
      exact (trialOuterBadMask_bounds X).2.trans hS
    exact ⟨h0, by simpa only [hI] using hle, hle⟩
  · have hI : trialOuterCoverIndicator j X = 0 :=
      Set.indicator_of_notMem (s := {Y | TrialOuterCoverEvent j Y}) hE _
    simp only [trialOuterPartition, hI, mul_zero, zero_div, le_refl, zero_le_one, and_self]

theorem trialOuterPartition_zero_of_not_event (j : Fin 60) (X : Fin 39 → FiniteMeasure ℝ)
    (hE : ¬ TrialOuterCoverEvent j X) : trialOuterPartition j X = 0 := by
  have hI : trialOuterCoverIndicator j X = 0 :=
    Set.indicator_of_notMem (s := {Y | TrialOuterCoverEvent j Y}) hE _
  simp only [trialOuterPartition, hI, mul_zero, zero_div]

theorem trialOuterPartition_sum_ae :
    ∀ᵐ X ∂trialProductMeasure 39, (∑ j : Fin 60, trialOuterPartition j X) = trialOuterBadMask X := by
  filter_upwards [trialActualOuter_covered_ae] with X hcover
  by_cases hB : TrialShellDomain 0 X ∧ ¬ TrialActualOuter X
  · obtain ⟨j, hj⟩ := (hcover hB.1).resolve_left hB.2
    have hS : trialOuterCoverSum X ≠ 0 :=
      (lt_of_lt_of_le zero_lt_one (trialOuterCoverSum_one_le X j hj)).ne'
    simp only [trialOuterPartition]
    rw [← Finset.sum_div, ← Finset.mul_sum]
    change trialOuterBadMask X * trialOuterCoverSum X / trialOuterCoverSum X = trialOuterBadMask X
    exact mul_div_cancel_right₀ _ hS
  · simp only [trialOuterPartition, trialOuterBadMask, hB, ite_false, zero_mul, zero_div,
      Finset.sum_const_zero]

theorem trialSourceResidual_badMask (X : Fin 39 → FiniteMeasure ℝ) :
    trialStepFunction X - trialSourceStepFunction X = trialOuterBadMask X * trialStepFunction X := by
  by_cases hs : TrialShellDomain 0 X
  · by_cases ha : TrialActualOuter X <;>
      simp only [trialSourceStepFunction, trialActualOuterMask, trialOuterBadMask, hs, ha,
        not_true_eq_false, not_false_eq_true, true_and, ite_true, ite_false,
        one_mul, zero_mul, sub_self, sub_zero]
  · have hF : trialStepFunction X = 0 := by
      by_contra hn
      exact hs (trialStepFunction_support X hn).1
    simp only [trialSourceStepFunction, hF, mul_zero, sub_self]

theorem trialSourceResidual_square_badMask (X : Fin 39 → FiniteMeasure ℝ) :
    (trialStepFunction X - trialSourceStepFunction X) ^ 2 =
      trialOuterBadMask X * trialStepFunction X ^ 2 := by
  rw [trialSourceResidual_badMask]
  unfold trialOuterBadMask
  split_ifs <;> norm_num

theorem trialOuterPartition_residual_ae :
    ∀ᵐ X ∂trialProductMeasure 39,
      (∑ j : Fin 60, trialOuterPartition j X * trialStepFunction X) =
        trialStepFunction X - trialSourceStepFunction X ∧
      (∑ j : Fin 60, trialOuterPartition j X * trialStepFunction X ^ 2) =
        (trialStepFunction X - trialSourceStepFunction X) ^ 2 := by
  filter_upwards [trialOuterPartition_sum_ae] with X hsum
  constructor
  · rw [← Finset.sum_mul, hsum]
    exact (trialSourceResidual_badMask X).symm
  · rw [← Finset.sum_mul, hsum]
    exact (trialSourceResidual_square_badMask X).symm

#print axioms measurable_trialOuterPartition
#print axioms trialOuterPartition_bounds
#print axioms trialOuterPartition_sum_ae
#print axioms trialOuterPartition_residual_ae

end PrimeGap182
