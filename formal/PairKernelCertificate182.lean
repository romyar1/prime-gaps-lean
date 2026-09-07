import PhysicalTrial182

/-!
The literal 1024-bin pair kernel: its exact rational global bound and the
continuous-density domination.  The finite sum is reduced by the Lean kernel;
the independent Python calculation is not an assumption of any theorem.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

def trialPairMaxRadius : ℚ :=
  trialRhoStar * ((trialCellCount - 1 + 38 : ℕ) : ℚ) * trialMesh

def trialPairMaxDenominator (i : Fin 1024) : ℚ :=
  min (trialRoughness - trialAuxiliaryRetreat)
    ((1 - trialPairBinUpper i) / 2 - trialPairMaxRadius - trialAuxiliaryRetreat)

/-- A second upward rounding makes the finite upper certificate inexpensive. -/
def trialPairTermCeiling (i : Fin 1024) : ℤ :=
  ⌈(trialPairWeight i / trialPairMaxDenominator i) * 10 ^ 12⌉

theorem trialPairMaxRadius_value :
    trialPairMaxRadius = (271194479226469 / 983040000000000 : ℚ) := by
  norm_num [trialPairMaxRadius, trialCellCount, trialIntervals, trialDimension,
    trialRhoStar, trialMesh, trialRadius]

theorem trialPairBin_margins (i : Fin 1024) :
    0 < trialPairBinSize ∧
    2 * trialRoughness < trialPairBinUpper i ∧
    trialPairBinUpper i ≤ trialMinorantA ∧
    0 ≤ (trialPairBinUpper i - 2 * trialRoughness) / trialRoughness ∧
    (trialPairBinUpper i - 2 * trialRoughness) / trialRoughness < 1 ∧
    (16929629573531 / 983040000000000 : ℚ) ≤ trialPairMaxDenominator i := by
  have hi0 : (0 : ℚ) ≤ (i.val : ℚ) := Nat.cast_nonneg _
  have hi1 : (i.val : ℚ) ≤ 1023 := by exact_mod_cast Nat.le_pred_of_lt i.isLt
  rw [trialPairMaxDenominator, trialPairMaxRadius_value]
  norm_num [trialPairBinSize, trialPairBinUpper, trialMinorantA, trialRoughness,
    trialPairBins, trialAuxiliaryRetreat, le_min_iff]
  all_goals repeat' constructor
  all_goals nlinarith

theorem trialPairMaxDenominator_pos (i : Fin 1024) :
    0 < trialPairMaxDenominator i :=
  lt_of_lt_of_le (by norm_num) (trialPairBin_margins i).2.2.2.2.2

set_option maxRecDepth 2048 in
theorem trialPairTermCeiling_double_sum :
    (∑ b : Fin 32, ∑ k : Fin 32,
      trialPairTermCeiling (finProdFinEquiv (b, k))) = (2193542878327 : ℤ) := by
  decide +kernel

theorem trialPairTermCeiling_sum :
    (∑ i : Fin 1024, trialPairTermCeiling i) = (2193542878327 : ℤ) := by
  rw [PrimeGap186.sum_fin_mul_eq_sum_fin_prod (m := 32) (n := 32),
    trialPairTermCeiling_double_sum]

theorem trialPairMaxSum_bound :
    (∑ i : Fin 1024, trialPairWeight i / trialPairMaxDenominator i) ≤
      (2193542878327 / 1000000000000 : ℚ) := by
  have hceil (i : Fin 1024) :
      trialPairWeight i / trialPairMaxDenominator i ≤
        (trialPairTermCeiling i : ℚ) / 10 ^ 12 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 10 ^ 12)).2
    exact Int.le_ceil _
  calc
    _ ≤ ∑ i : Fin 1024, (trialPairTermCeiling i : ℚ) / 10 ^ 12 :=
      Finset.sum_le_sum fun i _ => hceil i
    _ = (2193542878327 / 1000000000000 : ℚ) := by
      rw [← Finset.sum_div, ← Int.cast_sum, trialPairTermCeiling_sum]
      norm_num

#print axioms trialPairTermCeiling_double_sum
#print axioms trialPairMaxSum_bound

end PrimeGap182
