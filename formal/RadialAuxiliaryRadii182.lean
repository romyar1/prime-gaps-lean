import PairKernelDomination182
import RadialBlocks182
import SharpAuxiliaryArrays182

/-!
The actual auxiliary radii for all 1024 pair bins and 512 retained radial
blocks.  Each radius keeps its own CRT margin.  The bin integral uses the
hinge at the upper endpoint, as in the arithmetic majorant, and is bounded
by the literal upward-rounded kernel weight.
-/

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter PrimeGap186 PrimeGap182

namespace PrimeGap182Analytic

def radialSieveRadius182 (b : Fin 512) : ℝ :=
  (trialKernelRadius (b.val * 768) : ℝ)

def radialAuxiliaryRadius182 (j : Fin 1024) (b : Fin 512) : ℝ :=
  trialPairAuxRadius (radialSieveRadius182 b) (trialPairBinUpper j : ℝ)

theorem pairBinRight182_eq (j : Fin 1024) :
    pairBinRight (8639 / 50000) (41361 / 100000) j = (trialPairBinUpper j : ℝ) := by
  norm_num [pairBinRight, trialPairBinUpper, trialPairBinSize, trialRoughness,
    trialMinorantA, trialPairBins, Nat.cast_add, Nat.cast_one]

theorem pairBinLeft182_eq (j : Fin 1024) :
    pairBinLeft (8639 / 50000) (41361 / 100000) j = trialPairPartition j.val := by
  rw [pairBinLeft, pairBinRight182_eq, ← trialPairPartition_succ]
  have h := trialPairPartition_width j.val
  norm_num [trialPairBinSize, trialMinorantA, trialRoughness, trialPairBins] at h
  linarith only [h]

theorem pairBin182_margins (j : Fin 1024) :
    2 * (8639 / 50000 : ℝ) ≤ pairBinLeft (8639 / 50000) (41361 / 100000) j ∧
    pairBinLeft (8639 / 50000) (41361 / 100000) j <
      pairBinRight (8639 / 50000) (41361 / 100000) j ∧
    pairBinRight (8639 / 50000) (41361 / 100000) j ≤ 41361 / 100000 := by
  rw [pairBinLeft182_eq, pairBinRight182_eq]
  have hl := trialPairPartition_mem j.val j.isLt.le
  have hu := trialPairBin_margins j
  have hw := trialPairPartition_width j.val
  rw [trialPairPartition_succ] at hw
  have hw0 : (0 : ℝ) < (trialPairBinSize : ℝ) := Rat.cast_pos.mpr hu.1
  refine ⟨by simpa only [trialRoughness, Rat.cast_div, Rat.cast_ofNat] using hl.1,
    by linarith only [hw, hw0], ?_⟩
  simpa only [trialMinorantA, Rat.cast_div, Rat.cast_ofNat] using
    (Rat.cast_le (K := ℝ)).mpr hu.2.2.1

theorem radialSieveRadius182_nonneg (b : Fin 512) : 0 ≤ radialSieveRadius182 b := by
  unfold radialSieveRadius182
  apply Rat.cast_nonneg.mpr
  unfold trialKernelRadius
  exact mul_nonneg (mul_nonneg (by norm_num [trialRhoStar]) (Nat.cast_nonneg _))
    trialMesh_pos.le

theorem radialAuxiliaryRadius182_pos (j : Fin 1024) (b : Fin 512) :
    0 < radialAuxiliaryRadius182 j b :=
  trialPairAuxRadius_pos (Rat.cast_le.mpr (trialKernelRadius_le_max _))
    (Rat.cast_le.mpr (trialPairBin_margins j).2.2.1)

theorem radialAuxiliaryRadius182_lt_coefficient_cap (j : Fin 1024) (b : Fin 512) :
    radialAuxiliaryRadius182 j b < 17277 / 100000 := by
  have h := min_le_left
    ((trialRoughness : ℝ) - (trialAuxiliaryRetreat : ℝ))
    ((1 - (trialPairBinUpper j : ℝ)) / 2 - radialSieveRadius182 b -
      (trialAuxiliaryRetreat : ℝ))
  change radialAuxiliaryRadius182 j b ≤
    (trialRoughness : ℝ) - (trialAuxiliaryRetreat : ℝ) at h
  exact h.trans_lt (by norm_num [trialRoughness, trialAuxiliaryRetreat])

theorem radialAuxiliaryRadius182_lt_roughness (j : Fin 1024) (b : Fin 512) :
    radialAuxiliaryRadius182 j b < 8639 / 50000 :=
  (radialAuxiliaryRadius182_lt_coefficient_cap j b).trans (by norm_num)

theorem radialAuxiliaryRadius182_crt_margin (j : Fin 1024) (b : Fin 512) :
    pairBinRight (8639 / 50000) (41361 / 100000) j +
      2 * (radialSieveRadius182 b + radialAuxiliaryRadius182 j b) < 1 := by
  rw [pairBinRight182_eq]
  have h := min_le_right
    ((trialRoughness : ℝ) - (trialAuxiliaryRetreat : ℝ))
    ((1 - (trialPairBinUpper j : ℝ)) / 2 - radialSieveRadius182 b -
      (trialAuxiliaryRetreat : ℝ))
  change radialAuxiliaryRadius182 j b ≤
    (1 - (trialPairBinUpper j : ℝ)) / 2 - radialSieveRadius182 b -
      (trialAuxiliaryRetreat : ℝ) at h
  norm_num [trialAuxiliaryRetreat] at h
  linarith only [h]

theorem radialSieveRadius182_covers_block (b : Fin 512)
    (Y : Fin 38 → FiniteMeasure ℝ) (hb : trialFaceBlockMask b Y = 1) :
    (trialRhoStar : ℝ) * (∑ i, (Y i).mass : ℝ) ≤ radialSieveRadius182 b := by
  have hc : trialFaceCellSum Y < trialCellCount ∧ trialFaceCellSum Y / 768 = b.val := by
    by_contra hn
    simp [trialFaceBlockMask, hn] at hb
  have hdiv : b.val * 768 / 768 = b.val := by omega
  have hstop : trialKernelStop (trialFaceCellSum Y) = trialKernelStop (b.val * 768) := by
    simp only [trialKernelStop, trialKernelBlock_eq, hc.2, hdiv]
  have hrad : trialKernelRadius (trialFaceCellSum Y) = trialKernelRadius (b.val * 768) := by
    simp only [trialKernelRadius, hstop]
  have hm := trialFaceMass_le_kernelRadius Y hc.1
  change _ ≤ (trialKernelRadius (trialFaceCellSum Y) : ℝ) at hm
  simpa only [hrad, radialSieveRadius182] using hm

theorem radialAuxiliaryRadius182_kernel_sum (b : Fin 512) :
    (∑ j : Fin 1024, (trialPairWeight j : ℝ) / radialAuxiliaryRadius182 j b) =
      trialPairKernel (b.val * 768) := by
  have hb : b.val * 768 < trialCellCount := by
    rw [trialCellCount_eq]
    have h := b.isLt
    omega
  simp only [trialPairKernel, trialPairKernelRat, ite_eq_left hb, Rat.cast_sum,
    Rat.cast_div, Rat.cast_min, Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat,
    radialAuxiliaryRadius182, trialPairAuxRadius, radialSieveRadius182]

def pairBinMass182 (j : Fin 1024) : ℝ :=
  ∫ s in pairBinLeft (8639 / 50000) (41361 / 100000) j..
    pairBinRight (8639 / 50000) (41361 / 100000) j,
    Real.log ((s - (8639 / 50000)) / (8639 / 50000)) / s

theorem pairBinMass182_nonneg (j : Fin 1024) : 0 ≤ pairBinMass182 j := by
  apply intervalIntegral.integral_nonneg (pairBin182_margins j).2.1.le
  intro s hs
  exact pairLogDensity_nonneg _ _ (by norm_num)
    ((pairBin182_margins j).1.trans hs.1)

theorem pairBinMass182_weight_bound (j : Fin 1024) :
    pairHinge (19 / 50) (pairBinRight (8639 / 50000) (41361 / 100000) j) *
      pairBinMass182 j ≤ (trialPairWeight j : ℝ) := by
  let L : ℝ := trialPairPartition j.val
  let U : ℝ := (trialPairBinUpper j : ℝ)
  let f : ℝ → ℝ := fun s => Real.log ((s - (trialRoughness : ℝ)) /
    (trialRoughness : ℝ)) / s
  have hl := trialPairPartition_mem j.val j.isLt.le
  have hu : U ∈ Set.Icc (2 * (trialRoughness : ℝ)) (trialMinorantA : ℝ) := by
    simpa only [trialPairPartition_succ, U] using
      trialPairPartition_mem (j.val + 1) j.isLt
  have hlu : L ≤ U := by
    simpa only [pairBinLeft182_eq, pairBinRight182_eq, L, U] using
      (pairBin182_margins j).2.1.le
  have hmono : MonotoneOn f (Set.Icc (2 * (trialRoughness : ℝ)) (trialMinorantA : ℝ)) :=
    pairLogDensity_monotone _ _ (by norm_num [trialRoughness])
      (by norm_num [trialMinorantA, trialRoughness])
  have hint : IntervalIntegrable f volume L U := by
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hlu]
    exact hmono.mono (Set.Icc_subset_Icc hl.1 hu.2)
  have hib : (∫ s in L..U, f s) ≤ (U - L) * f U := by
    calc
      _ ≤ ∫ _s in L..U, f U :=
        intervalIntegral.integral_mono_on hlu hint intervalIntegrable_const
          (fun s hs => hmono ⟨hl.1.trans hs.1, hs.2.trans hu.2⟩ hu hs.2)
      _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]
  have hw : U - L = (trialPairBinSize : ℝ) := by
    simpa only [trialPairPartition_succ, L, U] using trialPairPartition_width j.val
  have hh : 0 ≤ pairHinge (trialHingeThreshold : ℝ) U :=
    pairHinge_nonneg _ _ (by norm_num [trialHingeThreshold])
  have hmass : pairBinMass182 j = ∫ s in L..U, f s := by
    simp only [pairBinMass182, pairBinLeft182_eq, pairBinRight182_eq, L, U, f,
      trialRoughness, Rat.cast_div, Rat.cast_ofNat]
  rw [pairBinRight182_eq, hmass]
  rw [show (19 / 50 : ℝ) = (trialHingeThreshold : ℝ) by norm_num [trialHingeThreshold]]
  change pairHinge (trialHingeThreshold : ℝ) U * (∫ s in L..U, f s) ≤ _
  calc
    _ ≤ pairHinge (trialHingeThreshold : ℝ) U * ((U - L) * f U) :=
      mul_le_mul_of_nonneg_left hib hh
    _ = (trialPairBinSize : ℝ) * trialPairDensity U := by
      rw [hw]
      change _ = (trialPairBinSize : ℝ) * (pairHinge (trialHingeThreshold : ℝ) U * f U)
      ring
    _ ≤ _ := trialPairBin_endpoint_bound j

theorem radial_pair_bin_energy_le_kernel (b : Fin 512) :
    (∑ j : Fin 1024,
      pairHinge (19 / 50) (pairBinRight (8639 / 50000) (41361 / 100000) j) *
        pairBinMass182 j / radialAuxiliaryRadius182 j b) ≤
      trialPairKernel (b.val * 768) := by
  rw [← radialAuxiliaryRadius182_kernel_sum]
  exact Finset.sum_le_sum fun j _ =>
    div_le_div_of_nonneg_right (pairBinMass182_weight_bound j)
      (radialAuxiliaryRadius182_pos j b).le

#print axioms radialAuxiliaryRadius182_crt_margin
#print axioms radialSieveRadius182_covers_block
#print axioms pairBinMass182_weight_bound
#print axioms radial_pair_bin_energy_le_kernel

end PrimeGap182Analytic
