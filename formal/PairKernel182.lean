import PairDensity182
import PairKernelCertificate182

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

theorem trialPairRawWeight_nonneg (i : Fin 1024) : 0 ≤ trialPairRawWeight i := by
  have hm := trialPairBin_margins i
  have hlog := trialLogUpper_nonneg _ hm.2.2.2.1 hm.2.2.2.2.1
  have hstep := hm.1
  have hs : 0 < trialPairBinUpper i := lt_trans (by norm_num [trialRoughness]) hm.2.1
  have hden : (0 : ℚ) < 2 / 5 - trialHingeThreshold := by norm_num [trialHingeThreshold]
  dsimp only [trialPairRawWeight]
  positivity

theorem trialPairRawWeight_le_weight (i : Fin 1024) :
    trialPairRawWeight i ≤ trialPairWeight i := by
  unfold trialPairWeight
  exact (le_div_iff₀ (by norm_num : (0 : ℚ) < 10 ^ 25)).2 (Int.le_ceil _)

theorem trialPairWeight_nonneg (i : Fin 1024) : 0 ≤ trialPairWeight i :=
  (trialPairRawWeight_nonneg i).trans (trialPairRawWeight_le_weight i)

theorem trialKernelRadius_le_max (j : ℕ) : trialKernelRadius j ≤ trialPairMaxRadius := by
  have hstop : trialKernelStop j ≤ trialCellCount := Nat.min_le_left _ _
  have hidx : trialKernelStop j - 1 + 38 ≤ trialCellCount - 1 + 38 := by omega
  have hcast : ((trialKernelStop j - 1 + 38 : ℕ) : ℚ) ≤
      ((trialCellCount - 1 + 38 : ℕ) : ℚ) := by exact_mod_cast hidx
  have hrho : (0 : ℚ) ≤ trialRhoStar := by norm_num [trialRhoStar]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcast hrho) trialMesh_pos.le

theorem trialPairDenominator_lower (j : ℕ) (i : Fin 1024) :
    trialPairMaxDenominator i ≤
      min (trialRoughness - trialAuxiliaryRetreat)
        ((1 - trialPairBinUpper i) / 2 - trialKernelRadius j - trialAuxiliaryRetreat) := by
  apply min_le_min le_rfl
  linarith [trialKernelRadius_le_max j]

theorem trialPairKernelRat_nonneg (j : ℕ) : 0 ≤ trialPairKernelRat j := by
  unfold trialPairKernelRat
  split_ifs
  · apply Finset.sum_nonneg
    intro i _
    exact div_nonneg (trialPairWeight_nonneg i)
      ((trialPairMaxDenominator_pos i).le.trans (trialPairDenominator_lower j i))
  · rfl

theorem trialPairKernelRat_bound (j : ℕ) :
    trialPairKernelRat j ≤ (2193542878327 / 1000000000000 : ℚ) := by
  unfold trialPairKernelRat
  split_ifs
  · apply le_trans _ trialPairMaxSum_bound
    apply Finset.sum_le_sum
    intro i _
    exact div_le_div_of_nonneg_left (trialPairWeight_nonneg i)
      (trialPairMaxDenominator_pos i) (trialPairDenominator_lower j i)
  · norm_num

theorem trialPairKernel_bounds (j : ℕ) :
    0 ≤ trialPairKernel j ∧ trialPairKernel j < (1097 / 500 : ℝ) := by
  constructor
  · exact Rat.cast_nonneg.mpr (trialPairKernelRat_nonneg j)
  · have hb : trialPairKernel j ≤ (2193542878327 / 1000000000000 : ℝ) := by
      simpa only [trialPairKernel, Rat.cast_div, Rat.cast_ofNat] using
        (Rat.cast_le (K := ℝ)).mpr (trialPairKernelRat_bound j)
    exact hb.trans_lt (by norm_num)

theorem trialFaceKernel_bounds (Y : Fin 38 → FiniteMeasure ℝ) :
    0 ≤ trialFaceKernel Y ∧ trialFaceKernel Y < (1097 / 500 : ℝ) :=
  trialPairKernel_bounds _

#print axioms trialPairKernel_bounds
#print axioms trialFaceKernel_bounds

end PrimeGap182
