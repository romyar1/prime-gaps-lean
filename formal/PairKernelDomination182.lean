import PairKernel182

/-!
The continuous pair integral is bounded by the actual 1024-bin, 512-block
kernel.  This proves the upper-quadrature direction, including the auxiliary
retreat and the rounding direction.  No pair-distribution estimate is assumed
or proved in this module.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

def trialPairAuxRadius (q s : ℝ) : ℝ :=
  min ((trialRoughness : ℝ) - (trialAuxiliaryRetreat : ℝ))
    ((1 - s) / 2 - q - (trialAuxiliaryRetreat : ℝ))

def trialPairContinuousKernel (q : ℝ) : ℝ :=
  ∫ s in 2 * (trialRoughness : ℝ)..(trialMinorantA : ℝ),
    trialPairDensity s / trialPairAuxRadius q s

def trialPairPartition (i : ℕ) : ℝ :=
  2 * (trialRoughness : ℝ) + (i : ℝ) * (trialPairBinSize : ℝ)

theorem trialPairPartition_zero : trialPairPartition 0 = 2 * (trialRoughness : ℝ) := by
  simp [trialPairPartition]

theorem trialPairPartition_last : trialPairPartition 1024 = (trialMinorantA : ℝ) := by
  norm_num [trialPairPartition, trialPairBinSize, trialMinorantA,
    trialPairBins, trialRoughness]

theorem trialPairPartition_succ (i : Fin 1024) :
    trialPairPartition (i.val + 1) = (trialPairBinUpper i : ℝ) := by
  simp only [trialPairPartition, trialPairBinUpper, Rat.cast_add, Rat.cast_mul,
    Rat.cast_ofNat, Rat.cast_natCast]

theorem trialPairPartition_width (i : ℕ) :
    trialPairPartition (i + 1) - trialPairPartition i = (trialPairBinSize : ℝ) := by
  simp only [trialPairPartition, Nat.cast_add, Nat.cast_one]
  ring

theorem trialPairPartition_mem (i : ℕ) (hi : i ≤ 1024) :
    trialPairPartition i ∈ Set.Icc (2 * (trialRoughness : ℝ)) (trialMinorantA : ℝ) := by
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hi1 : (i : ℝ) ≤ 1024 := by exact_mod_cast hi
  norm_num [trialPairPartition, trialPairBinSize, trialPairBins, trialRoughness,
    trialMinorantA]
  linarith

theorem trialPairAuxRadius_pos {q s : ℝ}
    (hq : q ≤ (trialPairMaxRadius : ℝ)) (hs : s ≤ (trialMinorantA : ℝ)) :
    0 < trialPairAuxRadius q s := by
  rw [trialPairMaxRadius_value] at hq
  norm_num [trialMinorantA] at hs
  norm_num [trialPairAuxRadius, trialRoughness, trialAuxiliaryRetreat, lt_min_iff]
  linarith

theorem trialPairAuxRadius_antitone (q : ℝ) : Antitone (trialPairAuxRadius q) := by
  intro x y hxy
  apply min_le_min le_rfl
  linarith

theorem trialPairAuxRadius_antitone_radial (s : ℝ) :
    Antitone (fun q => trialPairAuxRadius q s) := by
  intro x y hxy
  apply min_le_min le_rfl
  linarith

theorem trialPairIntegrand_monotone (q : ℝ) (hq : q ≤ (trialPairMaxRadius : ℝ)) :
    MonotoneOn (fun s => trialPairDensity s / trialPairAuxRadius q s)
      (Set.Icc (2 * (trialRoughness : ℝ)) (trialMinorantA : ℝ)) := by
  intro x hx y hy hxy
  calc
    _ ≤ trialPairDensity y / trialPairAuxRadius q x :=
      div_le_div_of_nonneg_right (trialPairDensity_monotone hx hy hxy)
        (trialPairAuxRadius_pos hq hx.2).le
    _ ≤ trialPairDensity y / trialPairAuxRadius q y :=
      div_le_div_of_nonneg_left (trialPairDensity_nonneg hy.1)
        (trialPairAuxRadius_pos hq hy.2) (trialPairAuxRadius_antitone q hxy)

theorem trialPairIntegrand_intervalIntegrable (q : ℝ)
    (hq : q ≤ (trialPairMaxRadius : ℝ)) {a b : ℝ}
    (ha : a ∈ Set.Icc (2 * (trialRoughness : ℝ)) (trialMinorantA : ℝ))
    (hb : b ∈ Set.Icc (2 * (trialRoughness : ℝ)) (trialMinorantA : ℝ))
    (hab : a ≤ b) :
    IntervalIntegrable (fun s => trialPairDensity s / trialPairAuxRadius q s) volume a b := by
  apply MonotoneOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  exact (trialPairIntegrand_monotone q hq).mono (Set.Icc_subset_Icc ha.1 hb.2)

theorem trialPairBin_endpoint_bound (i : Fin 1024) :
    (trialPairBinSize : ℝ) * trialPairDensity (trialPairBinUpper i : ℝ) ≤
      (trialPairWeight i : ℝ) := by
  have hm := trialPairBin_margins i
  have hs : (0 : ℝ) < (trialPairBinUpper i : ℝ) :=
    Rat.cast_pos.mpr (lt_trans (by norm_num [trialRoughness]) hm.2.1)
  have hd : (0 : ℝ) ≤ (trialPairBinSize : ℝ) := Rat.cast_nonneg.mpr hm.1.le
  have hh : 0 ≤ PrimeGap182Analytic.pairHinge (trialHingeThreshold : ℝ)
      (trialPairBinUpper i : ℝ) :=
    PrimeGap182Analytic.pairHinge_nonneg _ _ (by norm_num [trialHingeThreshold])
  let x : ℚ := (trialPairBinUpper i - 2 * trialRoughness) / trialRoughness
  have harg : 1 + (x : ℝ) =
      ((trialPairBinUpper i : ℝ) - (trialRoughness : ℝ)) / (trialRoughness : ℝ) := by
    dsimp only [x]
    push_cast
    field_simp [show (trialRoughness : ℝ) ≠ 0 by norm_num [trialRoughness]]
    ring
  have hlog := trialLogUpper_dominates x hm.2.2.2.1 hm.2.2.2.2.1
  rw [harg] at hlog
  calc
    _ ≤ (trialPairBinSize : ℝ) *
        (PrimeGap182Analytic.pairHinge (trialHingeThreshold : ℝ)
          (trialPairBinUpper i : ℝ) *
          ((trialLogUpper x : ℝ) / (trialPairBinUpper i : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlog hs.le) hh) hd
    _ = (trialPairRawWeight i : ℝ) := by
      simp only [trialPairRawWeight, PrimeGap182Analytic.pairHinge,
        Rat.cast_div, Rat.cast_mul, Rat.cast_max, Rat.cast_sub, Rat.cast_ofNat,
        Rat.cast_zero, x]
      ring
    _ ≤ (trialPairWeight i : ℝ) := Rat.cast_le.mpr (trialPairRawWeight_le_weight i)

theorem trialPairBin_integral_bound (i : Fin 1024) (j : ℕ) (q : ℝ)
    (hq : q ≤ (trialKernelRadius j : ℝ)) :
    (∫ s in trialPairPartition i.val..trialPairPartition (i.val + 1),
      trialPairDensity s / trialPairAuxRadius q s) ≤
      (trialPairWeight i : ℝ) /
        trialPairAuxRadius (trialKernelRadius j : ℝ) (trialPairBinUpper i : ℝ) := by
  have hqmax : q ≤ (trialPairMaxRadius : ℝ) :=
    hq.trans (Rat.cast_le.mpr (trialKernelRadius_le_max j))
  have hstep : (0 : ℝ) < (trialPairBinSize : ℝ) :=
    Rat.cast_pos.mpr (trialPairBin_margins i).1
  have hl := trialPairPartition_mem i.val i.isLt.le
  have hu := trialPairPartition_mem (i.val + 1) i.isLt
  have hlu : trialPairPartition i.val ≤ trialPairPartition (i.val + 1) := by
    linarith [trialPairPartition_width i.val]
  have huint : (trialPairBinUpper i : ℝ) ∈
      Set.Icc (2 * (trialRoughness : ℝ)) (trialMinorantA : ℝ) := by
    rwa [trialPairPartition_succ] at hu
  have hden : 0 < trialPairAuxRadius (trialKernelRadius j : ℝ) (trialPairBinUpper i : ℝ) :=
    trialPairAuxRadius_pos (Rat.cast_le.mpr (trialKernelRadius_le_max j)) huint.2
  have hint := trialPairIntegrand_intervalIntegrable q hqmax hl hu hlu
  have hpoint (s : ℝ) (hs : s ∈ Set.Icc (trialPairPartition i.val)
      (trialPairPartition (i.val + 1))) :
      trialPairDensity s / trialPairAuxRadius q s ≤
        trialPairDensity (trialPairBinUpper i : ℝ) /
          trialPairAuxRadius (trialKernelRadius j : ℝ) (trialPairBinUpper i : ℝ) := by
    have hs' : s ∈ Set.Icc (2 * (trialRoughness : ℝ)) (trialMinorantA : ℝ) :=
      ⟨hl.1.trans hs.1, hs.2.trans hu.2⟩
    have hsu : s ≤ (trialPairBinUpper i : ℝ) := by
      simpa only [trialPairPartition_succ] using hs.2
    calc
      _ ≤ trialPairDensity (trialPairBinUpper i : ℝ) / trialPairAuxRadius q s :=
        div_le_div_of_nonneg_right (trialPairDensity_monotone hs' huint hsu)
          (trialPairAuxRadius_pos hqmax hs'.2).le
      _ ≤ _ := div_le_div_of_nonneg_left (trialPairDensity_nonneg huint.1) hden
        ((trialPairAuxRadius_antitone_radial _ hq).trans (trialPairAuxRadius_antitone q hsu))
  calc
    _ ≤ ∫ _s in trialPairPartition i.val..trialPairPartition (i.val + 1),
        trialPairDensity (trialPairBinUpper i : ℝ) /
          trialPairAuxRadius (trialKernelRadius j : ℝ) (trialPairBinUpper i : ℝ) :=
      intervalIntegral.integral_mono_on hlu hint intervalIntegrable_const hpoint
    _ = ((trialPairBinSize : ℝ) * trialPairDensity (trialPairBinUpper i : ℝ)) /
        trialPairAuxRadius (trialKernelRadius j : ℝ) (trialPairBinUpper i : ℝ) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, trialPairPartition_width]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (trialPairBin_endpoint_bound i) hden.le

theorem trialPairContinuousKernel_le (j : ℕ) (hj : j < trialCellCount) (q : ℝ)
    (hq : q ≤ (trialKernelRadius j : ℝ)) :
    trialPairContinuousKernel q ≤ trialPairKernel j := by
  have hqmax : q ≤ (trialPairMaxRadius : ℝ) :=
    hq.trans (Rat.cast_le.mpr (trialKernelRadius_le_max j))
  have hint (i : ℕ) (hi : i < 1024) :
      IntervalIntegrable (fun s => trialPairDensity s / trialPairAuxRadius q s) volume
        (trialPairPartition i) (trialPairPartition (i + 1)) := by
    apply trialPairIntegrand_intervalIntegrable q hqmax
      (trialPairPartition_mem i hi.le) (trialPairPartition_mem (i + 1) hi)
    have hstep : (0 : ℝ) < (trialPairBinSize : ℝ) :=
      Rat.cast_pos.mpr (trialPairBin_margins ⟨i, hi⟩).1
    linarith [trialPairPartition_width i]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [trialPairPartition_zero, trialPairPartition_last] at hsum
  unfold trialPairContinuousKernel
  rw [← hsum]
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    ∫ s in trialPairPartition i..trialPairPartition (i + 1),
      trialPairDensity s / trialPairAuxRadius q s)]
  calc
    _ ≤ ∑ i : Fin 1024, (trialPairWeight i : ℝ) /
        trialPairAuxRadius (trialKernelRadius j : ℝ) (trialPairBinUpper i : ℝ) :=
      Finset.sum_le_sum fun i _ => trialPairBin_integral_bound i j q hq
    _ = trialPairKernel j := by
      simp only [trialPairKernel, trialPairKernelRat, ite_eq_left hj, Rat.cast_sum, Rat.cast_div,
        Rat.cast_min, Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat, trialPairAuxRadius]

theorem trialPairContinuousKernel_nonneg (q : ℝ) (hq : q ≤ (trialPairMaxRadius : ℝ)) :
    0 ≤ trialPairContinuousKernel q := by
  apply intervalIntegral.integral_nonneg (by norm_num [trialRoughness, trialMinorantA])
  intro s hs
  exact div_nonneg (trialPairDensity_nonneg hs.1) (trialPairAuxRadius_pos hq hs.2).le

theorem trialKernelStop_gt (j : ℕ) (hj : j < trialCellCount) : j < trialKernelStop j := by
  apply lt_min hj
  rw [trialKernelBlock_eq]
  simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ j (by norm_num : 0 < 768)

theorem trialFaceMass_le_kernelRadius (Y : Fin 38 → FiniteMeasure ℝ)
    (hY : (∑ i, trialCellIndex (Y i)) < trialCellCount) :
    (trialRhoStar : ℝ) * (∑ i, (Y i).mass : ℝ) ≤
      (trialKernelRadius (∑ i, trialCellIndex (Y i)) : ℝ) := by
  have hm : (0 : ℝ) < (trialMesh : ℝ) := Rat.cast_pos.mpr trialMesh_pos
  have hcell (i : Fin 38) : (Y i).mass ≤
      ((trialCellIndex (Y i) : ℝ) + 1) * (trialMesh : ℝ) := by
    apply (div_le_iff₀ hm).mp
    exact (Nat.lt_floor_add_one ((Y i).mass / (trialMesh : ℝ))).le
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 38))) => hcell i)
  have hmass : (∑ i, (Y i).mass : ℝ) ≤
      ((∑ i, trialCellIndex (Y i) : ℕ) + 38 : ℕ) * (trialMesh : ℝ) := by
    simpa only [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_add,
      Nat.cast_sum, Nat.cast_ofNat] using hsum
  have hj := trialKernelStop_gt (∑ i, trialCellIndex (Y i)) hY
  have hi : (∑ i, trialCellIndex (Y i)) + 38 ≤
      trialKernelStop (∑ i, trialCellIndex (Y i)) - 1 + 38 := by omega
  have hir : (((∑ i, trialCellIndex (Y i)) + 38 : ℕ) : ℝ) ≤
      ((trialKernelStop (∑ i, trialCellIndex (Y i)) - 1 + 38 : ℕ) : ℝ) := by
    exact_mod_cast hi
  have hrho : (0 : ℝ) ≤ (trialRhoStar : ℝ) := by norm_num [trialRhoStar]
  calc
    _ ≤ (trialRhoStar : ℝ) *
        (((trialKernelStop (∑ i, trialCellIndex (Y i)) - 1 + 38 : ℕ) : ℝ) *
          (trialMesh : ℝ)) :=
      mul_le_mul_of_nonneg_left (hmass.trans (mul_le_mul_of_nonneg_right hir hm.le)) hrho
    _ = _ := by simp only [trialKernelRadius, Rat.cast_mul, Rat.cast_natCast]; ring

theorem trialPairContinuousKernel_le_faceKernel (Y : Fin 38 → FiniteMeasure ℝ)
    (hY : (∑ i, trialCellIndex (Y i)) < trialCellCount) :
    trialPairContinuousKernel ((trialRhoStar : ℝ) * (∑ i, (Y i).mass : ℝ)) ≤
      trialFaceKernel Y :=
  trialPairContinuousKernel_le _ hY _ (trialFaceMass_le_kernelRadius Y hY)

#print axioms trialPairBin_endpoint_bound
#print axioms trialPairBin_integral_bound
#print axioms trialPairContinuousKernel_le
#print axioms trialPairContinuousKernel_le_faceKernel

end PrimeGap182
