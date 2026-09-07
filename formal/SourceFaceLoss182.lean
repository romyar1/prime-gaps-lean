import SourceFaceMasks182

/-! The actual positive face loss is dominated almost everywhere by the
137 literal coefficient-weighted source kernels. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace PrimeGap182

def trialInnerEventSum (role : Fin 5) (X : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  ∑ j : Fin 137, if trialSourceInnerRole j = role then trialInnerCoverIndicator j X else 0

theorem trialInnerEventSum_nonneg (role : Fin 5) (X : Fin 38 → FiniteMeasure ℝ) :
    0 ≤ trialInnerEventSum role X := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact (trialInnerCoverIndicator_le_kernel j X).1
  · exact le_rfl

theorem trialInnerEventSum_one_le (role : Fin 5) (X : Fin 38 → FiniteMeasure ℝ)
    (j : Fin 137) (hj : trialSourceInnerRole j = role) (hE : TrialInnerCoverEvent j X) :
    1 ≤ trialInnerEventSum role X := by
  have hI : trialInnerCoverIndicator j X = 1 :=
    Set.indicator_of_mem (s := {Y | TrialInnerCoverEvent j Y}) hE _
  have hsum := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 137)))
    (f := fun k => if trialSourceInnerRole k = role then trialInnerCoverIndicator k X else 0)
    (fun k _ => by
      split_ifs
      · exact (trialInnerCoverIndicator_le_kernel k X).1
      · exact le_rfl) (Finset.mem_univ j)
  simpa only [trialInnerEventSum, hj, ite_true, hI] using hsum

theorem trialLadderFailure_le_events_ae (side : Fin 2) :
    ∀ᵐ X ∂trialProductMeasure 38,
      trialMask (if side = 0 then 1 else 2) X * (1 - trialLadderInnerMask side X) ≤
        trialMask (if side = 0 then 1 else 2) X *
          trialInnerEventSum (if side = 0 then 1 else 2) X := by
  filter_upwards [trialLadderInner_covered_ae side] with X hcover
  by_cases hs : TrialShellDomain (if side = 0 then 1 else 2) X
  · rw [trialMask, ite_eq_left hs, one_mul, one_mul]
    rcases hcover hs with hr | ⟨j, hj, hE⟩
    · simpa only [trialLadderInnerMask, hr, ite_true, sub_self] using
        trialInnerEventSum_nonneg (if side = 0 then 1 else 2) X
    · have hsum := trialInnerEventSum_one_le _ X j hj hE
      by_cases hr : TrialLadderInnerRowsAllowed side X
      · simpa only [trialLadderInnerMask, hr, ite_true, sub_self] using
          trialInnerEventSum_nonneg (if side = 0 then 1 else 2) X
      · simpa only [trialLadderInnerMask, hr, ite_false, sub_zero] using hsum
  · simp only [trialMask, hs, ite_false, zero_mul, le_refl]

theorem trialSubtractionFailure_le_events_ae :
    ∀ᵐ X ∂trialProductMeasure 38,
      trialSubtractionFailure X ≤ trialMask 3 X * trialInnerEventSum 3 X := by
  filter_upwards [trialSubtractionRow_covered_ae] with X hcover
  unfold trialSubtractionFailure
  by_cases hs : TrialShellDomain 3 X
  · rw [trialMask, ite_eq_left hs, one_mul, one_mul]
    rcases hcover hs with hr | ⟨j, hj, hE⟩
    · simpa only [trialSubtractionRowMask, hr, ite_true, sub_self] using trialInnerEventSum_nonneg 3 X
    · have hsum := trialInnerEventSum_one_le 3 X j hj hE
      unfold trialSubtractionRowMask
      split_ifs
      · simpa only [sub_self] using trialInnerEventSum_nonneg 3 X
      · simpa only [sub_zero] using hsum
  · simp only [trialMask, hs, ite_false, zero_mul, le_refl]

theorem trialInnerEventSum_weighted (X : Fin 38 → FiniteMeasure ℝ) :
    (7 / 625 : ℝ) * trialMask 1 X * trialInnerEventSum 1 X +
      trialMask 2 X * trialInnerEventSum 2 X +
        (trialSourceEpsilonUpper : ℝ) * trialMask 3 X * trialInnerEventSum 3 X =
    ∑ j : Fin 137, ((trialInnerCertificates j).coefficientUpper : ℝ) *
      trialMask (trialSourceInnerRole j) X * trialInnerCoverIndicator j X := by
  simp only [trialInnerEventSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  obtain ⟨hrole, hcoef⟩ := trialInnerCoefficients_by_role j
  rw [hcoef]
  rcases hrole with h | h | h <;>
    simp only [h, ite_true, ite_false, Fin.reduceEq, mul_zero, one_mul, zero_add, add_zero,
      Rat.cast_div, Rat.cast_ofNat, Rat.cast_one]

theorem trialInnerWeighted_events_le_kernels (X : Fin 38 → FiniteMeasure ℝ) :
    (∑ j : Fin 137, ((trialInnerCertificates j).coefficientUpper : ℝ) *
      trialMask (trialSourceInnerRole j) X * trialInnerCoverIndicator j X) ≤
    ∑ j : Fin 137, ((trialInnerCertificates j).coefficientUpper : ℝ) * trialSourceInnerWeight j X := by
  apply Finset.sum_le_sum
  intro j _
  have hc : (0 : ℝ) ≤ ((trialInnerCertificates j).coefficientUpper : ℝ) :=
    Rat.cast_nonneg.mpr (trialInnerData_normalization j).2.1
  have hm : 0 ≤ trialMask (trialSourceInnerRole j) X := by
    rcases trialMask_values (trialSourceInnerRole j) X with h | h <;> simp only [h] <;> norm_num
  simpa only [trialSourceInnerWeight, mul_assoc] using
    mul_le_mul_of_nonneg_left (trialInnerCoverIndicator_le_kernel j X).2 (mul_nonneg hc hm)

theorem trialFaceLoss_le_sourceKernels_ae :
    ∀ᵐ X ∂trialProductMeasure 38,
      trialCapFaceMultiplier X - trialActualFaceMultiplier X ≤
        ∑ j : Fin 137, ((trialInnerCertificates j).coefficientUpper : ℝ) *
          trialSourceInnerWeight j X := by
  filter_upwards [trialLadderFailure_le_events_ae 0, trialLadderFailure_le_events_ae 1,
    trialSubtractionFailure_le_events_ae] with X ho hn hc
  change trialOldInnerFailure X ≤ trialMask 1 X * trialInnerEventSum 1 X at ho
  change trialNewInnerFailure X ≤ trialMask 2 X * trialInnerEventSum 2 X at hn
  have hε : (0 : ℝ) ≤ (trialSourceEpsilonUpper : ℝ) := trialSourceEnvelope_constants.1
  calc
    _ ≤ (7 / 625 : ℝ) * trialOldInnerFailure X + trialNewInnerFailure X +
        (trialSourceEpsilonUpper : ℝ) * trialSubtractionFailure X := trialFaceLoss_le_three_failures X
    _ ≤ (7 / 625 : ℝ) * (trialMask 1 X * trialInnerEventSum 1 X) +
        trialMask 2 X * trialInnerEventSum 2 X +
        (trialSourceEpsilonUpper : ℝ) * (trialMask 3 X * trialInnerEventSum 3 X) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left ho (by norm_num)) hn)
        (mul_le_mul_of_nonneg_left hc hε)
    _ = ∑ j : Fin 137, ((trialInnerCertificates j).coefficientUpper : ℝ) *
        trialMask (trialSourceInnerRole j) X * trialInnerCoverIndicator j X := by
      simpa only [mul_assoc] using trialInnerEventSum_weighted X
    _ ≤ _ := trialInnerWeighted_events_le_kernels X

#print axioms trialLadderFailure_le_events_ae
#print axioms trialSubtractionFailure_le_events_ae
#print axioms trialInnerEventSum_weighted
#print axioms trialFaceLoss_le_sourceKernels_ae

end PrimeGap182
