import SourceHybridReference182
import PhysicalRestoration182

/-! A robust positive physical margin for a slightly larger sharp-deficit bound.
The loss parameter and the original numerical source certificates are unchanged.
This file proves the exact rational margin; the analytic upper bound on the
actual sharp deficit is established separately.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

def trialConvexKappaBound : ℚ := 11696 / 125000000

def trialAdditionalSharpLoss : ℝ :=
  (1 - (trialLambda : ℝ)) ^ 2 / trialHybridLoss *
    ((trialConvexKappaBound : ℝ) - (trialKappa : ℝ))

theorem trialAdditionalSharpLoss_bounds :
    0 < trialAdditionalSharpLoss ∧
      4 * (trialRhoStar : ℝ) * trialAdditionalSharpLoss < (32 / 10 ^ 6 : ℝ) := by
  norm_num [trialAdditionalSharpLoss, trialConvexKappaBound, trialLambda,
    trialKappa, trialHybridLoss, trialRhoStar]

def trialAddedFaceWeight (Y : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  (trialActualEnlargedMask Y - trialActualBaseMask Y) ^ 2

theorem measurable_trialAddedFaceWeight : Measurable trialAddedFaceWeight :=
  (measurable_trialActualEnlargedMask.sub measurable_trialActualBaseMask).pow_const 2

theorem trialAddedFaceWeight_bounds (Y : Fin 38 → FiniteMeasure ℝ) :
    0 ≤ trialAddedFaceWeight Y ∧ trialAddedFaceWeight Y ≤ 1 := by
  obtain ⟨hb, he, _, _, _⟩ := trialActualFaceMasks_nested Y
  unfold trialAddedFaceWeight
  rcases hb with hb | hb <;> rcases he with he | he <;> rw [hb, he] <;> norm_num

theorem trialSource_root_le :
    trialRootPair trialSourceStepFunction trialSourceStepFunction ≤ trialRootEnergy := by
  have hres : 0 ≤ trialRootPair trialResidual trialResidual :=
    integral_nonneg (fun X => mul_self_nonneg (trialResidual X))
  linarith only [trialProjection_root_identity, hres]

theorem trialAddedFace_energy_le :
    trialFacePair trialAddedFaceWeight trialSourceStepFunction trialSourceStepFunction ≤
      (4 * (trialRhoStar : ℝ)) * trialRootEnergy := by
  have hbound : ∃ B : ℝ, ∀ Y, ‖trialAddedFaceWeight Y‖ ≤ B := by
    refine ⟨1, fun Y => ?_⟩
    rw [Real.norm_of_nonneg (trialAddedFaceWeight_bounds Y).1]
    exact (trialAddedFaceWeight_bounds Y).2
  have hh := trialFacePair_upper measurable_trialAddedFaceWeight hbound
    (by norm_num : (0 : ℝ) ≤ 1) (fun Y => (trialAddedFaceWeight_bounds Y).2)
    trial_regular_source
  simp only [mul_one] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left trialSource_root_le
    (mul_nonneg (by norm_num) trialRhoStar_pos.le))

def trialPerturbedRestoredEnergy : ℝ :=
  trialRestoredEnergy - trialAdditionalSharpLoss *
    trialFacePair trialAddedFaceWeight trialSourceStepFunction trialSourceStepFunction

theorem trialPerturbedRestoredEnergy_margin (h : PhysicalSourceBounds182) :
    (33 / 10 ^ 6 : ℝ) < trialPerturbedRestoredEnergy / trialRootEnergy := by
  have hE := trialRootEnergy_pos h.cap
  have hbase := (lt_div_iff₀ hE).mp (physical_restored_energy_margin182 h)
  have hloss := mul_le_mul_of_nonneg_left trialAddedFace_energy_le
    trialAdditionalSharpLoss_bounds.1.le
  have hcost := mul_lt_mul_of_pos_right trialAdditionalSharpLoss_bounds.2 hE
  have hloss' : trialAdditionalSharpLoss *
      trialFacePair trialAddedFaceWeight trialSourceStepFunction trialSourceStepFunction <
        (32 / 10 ^ 6 : ℝ) * trialRootEnergy := by
    nlinarith only [hloss, hcost]
  apply (lt_div_iff₀ hE).mpr
  unfold trialPerturbedRestoredEnergy
  linarith only [hbase, hloss', hE]

theorem trialPerturbedRestoredEnergy_pos (h : PhysicalSourceBounds182) :
    0 < trialPerturbedRestoredEnergy := by
  have hp : 0 < trialPerturbedRestoredEnergy / trialRootEnergy :=
    lt_trans (by norm_num) (trialPerturbedRestoredEnergy_margin h)
  exact (div_pos_iff_of_pos_right (trialRootEnergy_pos h.cap)).mp hp

def trialPerturbedHybridPolynomial (κ K U B C H : ℝ) : ℝ :=
  trialPhysicalHybridPolynomial κ K U B C H - trialAdditionalSharpLoss * H ^ 2

theorem trialPerturbedHybridPolynomial_reference (κ U : ℝ)
    (Y : Fin 38 → FiniteMeasure ℝ) :
    trialPerturbedHybridPolynomial κ (trialFaceKernel Y) U
      (trialActualBaseMask Y * U) (trialActualSubtractionMask Y * U)
      ((trialActualEnlargedMask Y - trialActualBaseMask Y) * U) =
        (trialActualFaceMultiplier Y - trialAdditionalSharpLoss * trialAddedFaceWeight Y) * U ^ 2 := by
  unfold trialPerturbedHybridPolynomial
  rw [trialPhysicalHybridPolynomial_reference]
  unfold trialAddedFaceWeight
  ring

theorem trialPerturbedHybridPolynomial_eq (κ K U B C H : ℝ) :
    trialPerturbedHybridPolynomial κ K U B C H =
      2 * U * B - B ^ 2 +
        2 * (1 - (trialLambda : ℝ)) * (1 - κ) * (U - B) * H +
        2 * (1 - (trialLambda : ℝ)) * κ * (C - B) * H -
        ((1 - (trialLambda : ℝ)) ^ 2 +
          (1 - (trialLambda : ℝ)) ^ 2 * (trialConvexKappaBound : ℝ) / trialHybridLoss) * H ^ 2 -
        trialHybridLoss * K * (U - C) ^ 2 := by
  unfold trialPerturbedHybridPolynomial trialPhysicalHybridPolynomial trialAdditionalSharpLoss
  ring

#print axioms trialAdditionalSharpLoss_bounds
#print axioms trialPerturbedRestoredEnergy_margin
#print axioms trialPerturbedRestoredEnergy_pos
#print axioms trialPerturbedHybridPolynomial_reference
#print axioms trialPerturbedHybridPolynomial_eq

end PrimeGap182
