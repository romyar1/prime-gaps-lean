import SourceCountGeometry182

/-! The literal radial face envelope and source-local signed Cauchy bound.
The quadratic estimate retains the complete signed sum before squaring.
Its owner-event assumption is the concrete mass reservation from the
source geometry; the numerical count itself is proved, not assumed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

theorem trialSourceEnvelope_constants :
    (0 : ℝ) ≤ (trialSourceEpsilonUpper : ℝ) ∧
    (trialSourceEpsilonUpper : ℝ) ≤ (trialSourceEnlargementWeight : ℝ) ∧
    (trialSourceEnlargementWeight : ℝ) ≤ 1 ∧
    trialHybridLoss * (1097 / 500) ≤ (trialSourceEpsilonUpper : ℝ) ∧
    1 - (trialLambda : ℝ) ≤ (trialSourceEnlargementWeight : ℝ) := by
  norm_num [trialSourceEpsilonUpper, trialSourceEnlargementWeight,
    trialHybridLoss, trialKappa, trialLambda]

theorem trialMask_base_zero_of_source_radius (Y : Fin 38 → FiniteMeasure ℝ)
    (h : ¬ trialSourceCellSum Y ≤ 355047) : trialMask 1 Y = 0 := by
  have hn : ¬ TrialShellDomain 1 Y := fun hY => h ((trialBase_grid_iff Y).mp hY).1
  simp only [trialMask, hn, ite_false]

theorem trialMask_enlarged_zero_of_source_radius (Y : Fin 38 → FiniteMeasure ℝ)
    (h : ¬ trialSourceCellSum Y ≤ 359896) : trialMask 2 Y = 0 := by
  have hn : ¬ TrialShellDomain 2 Y := fun hY => h ((trialEnlarged_grid_iff Y).mp hY).1
  simp only [trialMask, hn, ite_false]

theorem trialSourceFaceWeight_epsilon_le (Y : Fin 38 → FiniteMeasure ℝ) :
    (trialSourceEpsilonUpper : ℝ) ≤ trialSourceFaceWeight Y := by
  have h := trialSourceEnvelope_constants
  unfold trialSourceFaceWeight
  split_ifs
  · exact h.2.1.trans h.2.2.1
  · exact h.2.1
  · exact le_rfl

/-- The exact source envelope bounds both the cap multiplier and the
actual multiplier, including their negative parts. -/
theorem trialFaceMultiplier_abs_le_sourceFaceWeight (Y : Fin 38 → FiniteMeasure ℝ) :
    |trialActualFaceMultiplier Y| ≤ trialSourceFaceWeight Y ∧
      |trialCapFaceMultiplier Y| ≤ trialSourceFaceWeight Y := by
  have hb := trialFaceMultiplier_bounds Y
  have he := trialSourceEnvelope_constants
  have hlo : -(trialSourceEpsilonUpper : ℝ) ≤ trialActualFaceMultiplier Y := by
    linarith [he.2.2.2.1]
  have hlow : -trialSourceFaceWeight Y ≤ trialActualFaceMultiplier Y :=
    (neg_le_neg (trialSourceFaceWeight_epsilon_le Y)).trans hlo
  have hl : (trialLambda : ℝ) ≤ (1 : ℝ) := by norm_num [trialLambda]
  have hm2 : trialMask 2 Y ≤ 1 := by
    rcases trialMask_values 2 Y with h | h <;> simp [h]
  have hm3 : trialMask 3 Y ≤ 1 := by
    rcases trialMask_values 3 Y with h | h <;> simp [h]
  have hK : 0 ≤ trialHybridLoss * trialFaceKernel Y :=
    mul_nonneg trialHybridLoss_nonneg (trialFaceKernel_bounds Y).1
  have htail : trialHybridLoss * trialFaceKernel Y * trialMask 3 Y ≤
      trialHybridLoss * trialFaceKernel Y := mul_le_of_le_one_right hK hm3
  have hupper : trialCapFaceMultiplier Y ≤ trialSourceFaceWeight Y := by
    by_cases hbase : trialSourceCellSum Y ≤ 355047
    · simpa only [trialSourceFaceWeight, hbase, ite_true] using hb.2.2.1
    · have hz1 := trialMask_base_zero_of_source_radius Y hbase
      by_cases hlarge : trialSourceCellSum Y ≤ 359896
      · simp only [trialSourceFaceWeight, hbase, hlarge, ite_false, ite_true]
        have hmain := mul_le_of_le_one_right (sub_nonneg.mpr hl) hm2
        simp only [trialCapFaceMultiplier, hz1, mul_zero, zero_add]
        linarith [he.2.2.2.2]
      · have hz2 := trialMask_enlarged_zero_of_source_radius Y hlarge
        simp only [trialSourceFaceWeight, hbase, hlarge, ite_false]
        simp only [trialCapFaceMultiplier, hz1, hz2, mul_zero, zero_add]
        linarith [he.1]
  exact ⟨abs_le.mpr ⟨hlow, hb.2.1.trans hupper⟩,
    abs_le.mpr ⟨hlow.trans hb.2.1, hupper⟩⟩

theorem trialSourceFaceWeight_sum_bound (X : Fin 39 → FiniteMeasure ℝ) :
    (∑ i : Fin 39, trialSourceFaceWeight (i.removeNth X)) ≤
      39 * (trialSourceEpsilonUpper : ℝ) +
        (1 - (trialSourceEpsilonUpper : ℝ)) * (trialSourceEligible X).card := by
  classical
  have hterm (i : Fin 39) : trialSourceFaceWeight (i.removeNth X) ≤
      (trialSourceEpsilonUpper : ℝ) + (1 - (trialSourceEpsilonUpper : ℝ)) *
        (if i ∈ trialSourceEligible X then (1 : ℝ) else 0) := by
    by_cases hi : i ∈ trialSourceEligible X
    · simpa only [hi, ite_true, mul_one, add_sub_cancel] using
        (trialSourceFaceWeight_bounds (i.removeNth X)).2
    · have hn : ¬ trialSourceCellSum (i.removeNth X) ≤ 359896 := by
        simpa only [trialSourceEligible, Finset.mem_filter, Finset.mem_univ, true_and] using hi
      have hn' : ¬ trialSourceCellSum (i.removeNth X) ≤ 355047 := by omega
      simp only [trialSourceFaceWeight, hn, hn', hi, ite_false, mul_zero, add_zero, le_refl]
  have hc : (∑ i : Fin 39, if i ∈ trialSourceEligible X then (1 : ℝ) else 0) =
      ((trialSourceEligible X).card : ℝ) := by
    simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  calc
    _ ≤ ∑ i : Fin 39, ((trialSourceEpsilonUpper : ℝ) +
        (1 - (trialSourceEpsilonUpper : ℝ)) *
          (if i ∈ trialSourceEligible X then (1 : ℝ) else 0)) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hc]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_ofNat]

theorem sourceCountAt_factor_le (r : TrialOuterCertificateData)
    (hf : ∀ b : Fin r.counts.length, 0 ≤ (r.counts.get b).factor)
    (b : Fin r.counts.length) (n : ℕ)
    (hb : (r.counts.get b).first ≤ n ∧ n ≤ (r.counts.get b).last) :
    ((r.counts.get b).factor : ℝ) ≤ trialSourceCountAt r n := by
  have hnon : ∀ c ∈ (Finset.univ : Finset (Fin r.counts.length)),
      (0 : ℝ) ≤ if (r.counts.get c).first ≤ n ∧ n ≤ (r.counts.get c).last then
        ((r.counts.get c).factor : ℝ) else 0 := by
    intro c _
    split_ifs
    · exact Rat.cast_nonneg.mpr (hf c)
    · exact le_rfl
  have h := Finset.single_le_sum hnon (Finset.mem_univ b)
  rw [ite_eq_left hb] at h
  exact h

theorem trialSourceCountMultiplier_dominates (j : Fin 60)
    (X : Fin 39 → FiniteMeasure ℝ)
    (hDomain : TrialSourceDomain (trialOuterCertificates j).cover X)
    (hOwner : TrialSourceOwnerEvent (trialOuterCertificates j) X) :
    (∑ i : Fin 39, trialSourceFaceWeight (i.removeNth X)) ≤
      trialSourceCountMultiplier j X := by
  obtain ⟨b, hb⟩ := trialSourceCount_band_exists j X hDomain
  have hcount := trialSourceCountBand_dominates j b X hDomain hb hOwner
  have hdata := trialOuterCountBand_bounds j b
  have he : (trialSourceEpsilonUpper : ℝ) ≤ 1 :=
    trialSourceEnvelope_constants.2.1.trans trialSourceEnvelope_constants.2.2.1
  apply (trialSourceFaceWeight_sum_bound X).trans
  apply le_trans _ (sourceCountAt_factor_le (trialOuterCertificates j)
    (fun c => (trialOuterCountBand_bounds j c).1) b
      (trialSourceCountIndex (trialOuterCertificates j) X) hb)
  have hfactor : (((trialOuterCertificates j).counts.get b).factor : ℝ) =
      39 * (trialSourceEpsilonUpper : ℝ) + (1 - (trialSourceEpsilonUpper : ℝ)) *
        ((trialOuterCertificates j).counts.get b).count := by
    exact_mod_cast hdata.2.2.2
  rw [hfactor]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcount)
    (sub_nonneg.mpr he))

theorem source_signed_weighted_square_le {ι : Type*} [Fintype ι]
    (a V w : ι → ℝ) (L : ℝ) (hw : ∀ i, |a i| ≤ w i)
    (hL : (∑ i, w i) ≤ L) :
    (∑ i, a i * V i) ^ 2 ≤ L * ∑ i, w i * V i ^ 2 := by
  have hw0 (i : ι) : 0 ≤ w i := (abs_nonneg _).trans (hw i)
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset ι)
    (r := fun i => a i * V i) (f := w) (g := fun i => w i * V i ^ 2)
    (fun i _ => hw0 i) (fun i _ => mul_nonneg (hw0 i) (sq_nonneg _)) (fun i _ => by
      have hai : a i ^ 2 ≤ w i ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (hw0 i)).mpr (hw i)
      nlinarith only [mul_le_mul_of_nonneg_right hai (sq_nonneg (V i))])
  exact hs.trans (mul_le_mul_of_nonneg_right hL
    (Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (sq_nonneg _)))

/-- Exact pointwise source-local estimate for every signed erased profile. -/
theorem trialCapPullback_square_le_source_local (j : Fin 60)
    (X : Fin 39 → FiniteMeasure ℝ)
    (hDomain : TrialSourceDomain (trialOuterCertificates j).cover X)
    (hOwner : TrialSourceOwnerEvent (trialOuterCertificates j) X)
    (V : Fin 39 → ℝ) :
    (∑ i : Fin 39, trialCapFaceMultiplier (i.removeNth X) * V i) ^ 2 ≤
      trialSourceCountMultiplier j X *
        ∑ i : Fin 39, trialSourceFaceWeight (i.removeNth X) * V i ^ 2 :=
  source_signed_weighted_square_le _ V _ _
    (fun i => (trialFaceMultiplier_abs_le_sourceFaceWeight (i.removeNth X)).2)
    (trialSourceCountMultiplier_dominates j X hDomain hOwner)

#print axioms trialFaceMultiplier_abs_le_sourceFaceWeight
#print axioms trialSourceCountMultiplier_dominates
#print axioms source_signed_weighted_square_le
#print axioms trialCapPullback_square_le_source_local

end PrimeGap182
