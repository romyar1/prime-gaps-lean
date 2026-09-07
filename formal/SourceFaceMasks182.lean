import SourceActualCover182

/-! Exact factorization of actual inner masks, and the positive loss
envelope with the original old/new/subtraction coefficients. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace PrimeGap182

def trialLadderInnerMask (side : Fin 2) (X : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  if TrialLadderInnerRowsAllowed side X then 1 else 0

def trialSubtractionRowMask (X : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  if TrialOuterRowAllowed trialSubtractionSourceRow X then 1 else 0

def trialOldInnerFailure (X : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  trialMask 1 X * (1 - trialLadderInnerMask 0 X)

def trialNewInnerFailure (X : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  trialMask 2 X * (1 - trialLadderInnerMask 1 X)

def trialSubtractionFailure (X : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  trialMask 3 X * (1 - trialSubtractionRowMask X)

theorem trialActualBase_iff_rows (X : Fin 38 → FiniteMeasure ℝ) :
    TrialActualBase X ↔ TrialShellDomain 1 X ∧
      TrialLadderInnerRowsAllowed 0 X ∧ TrialLadderInnerRowsAllowed 1 X := by
  constructor
  · rintro ⟨hs, _, hr⟩
    exact ⟨hs, fun R hR => hr R (List.mem_append_left _ hR),
      fun R hR => hr R (List.mem_append_right _ hR)⟩
  · rintro ⟨hs, ho, hn⟩
    refine ⟨hs, (trialShellDomain_cap 1 hs).2, ?_⟩
    intro R hR
    exact (List.mem_append.mp hR).elim (ho R) (hn R)

theorem trialActualEnlarged_iff_rows (X : Fin 38 → FiniteMeasure ℝ) :
    TrialActualEnlarged X ↔ TrialShellDomain 2 X ∧ TrialLadderInnerRowsAllowed 1 X := by
  constructor
  · rintro ⟨hs, _, hr⟩
    exact ⟨hs, hr⟩
  · rintro ⟨hs, hr⟩
    exact ⟨hs, (trialShellDomain_cap 2 hs).2, hr⟩

theorem trialSubtraction_shell_total (X : Fin 38 → FiniteMeasure ℝ)
    (hs : TrialShellDomain 3 X) : trialTotalMass X ≤ (trialSubtractionRadius : ℝ) :=
  sourceShell_total_le 3 trialSubtractionRadius (by decide +kernel) X hs

theorem trialActualSubtraction_iff_row (X : Fin 38 → FiniteMeasure ℝ) :
    TrialActualSubtraction X ↔ TrialShellDomain 3 X ∧
      TrialOuterRowAllowed trialSubtractionSourceRow X := by
  constructor
  · rintro ⟨hs, _, _, hr⟩
    exact ⟨hs, hr⟩
  · rintro ⟨hs, hr⟩
    exact ⟨hs, (trialShellDomain_cap 3 hs).2, trialSubtraction_shell_total X hs, hr⟩

theorem trialActualFaceMasks_factor (X : Fin 38 → FiniteMeasure ℝ) :
    trialActualBaseMask X = trialMask 1 X * trialLadderInnerMask 0 X * trialLadderInnerMask 1 X ∧
    trialActualEnlargedMask X = trialMask 2 X * trialLadderInnerMask 1 X ∧
    trialActualSubtractionMask X = trialMask 3 X * trialSubtractionRowMask X := by
  constructor
  · simp only [trialActualBaseMask, trialActualBase_iff_rows, trialMask, trialLadderInnerMask]
    split_ifs <;> simp_all
  constructor
  · simp only [trialActualEnlargedMask, trialActualEnlarged_iff_rows, trialMask, trialLadderInnerMask]
    split_ifs <;> simp_all
  · simp only [trialActualSubtractionMask, trialActualSubtraction_iff_row, trialMask, trialSubtractionRowMask]
    split_ifs <;> simp_all

theorem trialInnerFailure_nonneg (X : Fin 38 → FiniteMeasure ℝ) :
    0 ≤ trialOldInnerFailure X ∧ 0 ≤ trialNewInnerFailure X ∧ 0 ≤ trialSubtractionFailure X := by
  unfold trialOldInnerFailure trialNewInnerFailure trialSubtractionFailure
    trialMask trialLadderInnerMask trialSubtractionRowMask
  split_ifs <;> norm_num

theorem trialFaceLoss_le_three_failures (X : Fin 38 → FiniteMeasure ℝ) :
    trialCapFaceMultiplier X - trialActualFaceMultiplier X ≤
      (7 / 625 : ℝ) * trialOldInnerFailure X + trialNewInnerFailure X +
        (trialSourceEpsilonUpper : ℝ) * trialSubtractionFailure X := by
  have hl : (0 : ℝ) ≤ (trialLambda : ℝ) := by norm_num [trialLambda]
  have hlU : (trialLambda : ℝ) ≤ 7 / 625 := by norm_num [trialLambda]
  have hk : 0 ≤ trialHybridLoss * trialFaceKernel X :=
    mul_nonneg trialHybridLoss_nonneg (trialFaceKernel_bounds X).1
  have hkU : trialHybridLoss * trialFaceKernel X ≤ (trialSourceEpsilonUpper : ℝ) :=
    (mul_le_mul_of_nonneg_left (trialFaceKernel_bounds X).2.le trialHybridLoss_nonneg).trans
      trialSourceEnvelope_constants.2.2.2.1
  have hmask := trialMask_base_le_enlarged X
  have hn0 : 0 ≤ trialMask 2 X := by
    rcases trialMask_values 2 X with h | h <;> simp only [h] <;> norm_num
  obtain ⟨hb, hn, hc⟩ := trialActualFaceMasks_factor X
  rw [trialCapFaceMultiplier, trialActualFaceMultiplier, hb, hn, hc]
  have hold := (trialInnerFailure_nonneg X).1
  have hsub := (trialInnerFailure_nonneg X).2.2
  have hreplaceO := mul_le_mul_of_nonneg_right hlU hold
  have hreplaceC := mul_le_mul_of_nonneg_right hkU hsub
  have hmid :
      (trialLambda : ℝ) * trialMask 1 X - (trialLambda : ℝ) *
          (trialMask 1 X * trialLadderInnerMask 0 X * trialLadderInnerMask 1 X) +
        (1 - (trialLambda : ℝ)) * trialMask 2 X -
          (1 - (trialLambda : ℝ)) * (trialMask 2 X * trialLadderInnerMask 1 X) ≤
      (trialLambda : ℝ) * trialOldInnerFailure X + trialNewInnerFailure X := by
    unfold trialOldInnerFailure trialNewInnerFailure trialLadderInnerMask
    split_ifs <;> simp only [mul_zero, mul_one, sub_zero, sub_self, add_zero,
      zero_add] <;> nlinarith only [hmask, hl, mul_nonneg hl hn0]
  simp only [trialOldInnerFailure] at hreplaceO
  simp only [trialSubtractionFailure] at hreplaceC
  simp only [trialOldInnerFailure, trialNewInnerFailure] at hmid
  simp only [trialOldInnerFailure, trialNewInnerFailure, trialSubtractionFailure]
  nlinarith only [hmid, hreplaceO, hreplaceC]

set_option maxRecDepth 10000 in
theorem trialInnerCoefficients_by_role : ∀ j : Fin 137,
    (trialSourceInnerRole j = 1 ∨ trialSourceInnerRole j = 2 ∨ trialSourceInnerRole j = 3) ∧
    (trialInnerCertificates j).coefficientUpper =
      if trialSourceInnerRole j = 1 then 7 / 625
      else if trialSourceInnerRole j = 2 then 1 else trialSourceEpsilonUpper := by
  decide +kernel

#print axioms trialActualFaceMasks_factor
#print axioms trialFaceLoss_le_three_failures
#print axioms trialInnerCoefficients_by_role

end PrimeGap182
