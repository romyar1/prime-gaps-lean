import SourceArithmetic182
import SourceDenseData182

/-! Dense divisibility deduced from the actual source owner inequalities.
The common self-pair and enlarged subtraction pair are included. -/

noncomputable section
open PrimeGap186
open scoped BigOperators NNReal

namespace PrimeGap182

theorem trialSourceRow_lcm_dense (row : TrialSourceRow) (S T : ℚ)
    (hg : TrialSourceRowGeometry row S T) (R : ℝ) (hR : 1 < R)
    (D E : ℕ) (hD : Squarefree D) (hE : Squarefree E)
    (hS : logSize R D ≤ (S : ℝ)) (hT : logSize R E ≤ (T : ℝ))
    (ho : TrialOuterOwnerBound row R D) (hi : TrialInnerOwnerBound row R E)
    (hq : R ^ (row.lowerBand : ℝ) < (D.lcm E : ℝ)) :
    ∃ hξ : 1 ≤ R ^ (row.activation : ℝ),
      Nonempty (DenseDivisibilityWitness ⟨R ^ (row.activation : ℝ), hξ⟩ row.order (D.lcm E)) := by
  rcases hg with ⟨hξ, _hA, _hC, _hL, hord, hcO, hcI, hb⟩
  have hξr : 0 ≤ (row.activation : ℝ) := by exact_mod_cast hξ
  have hcOr : (row.outerCore : ℝ) ≤ (row.lowerBand : ℝ) - (T : ℝ) := by exact_mod_cast hcO
  have hcIr : (row.innerCore : ℝ) ≤ (row.lowerBand : ℝ) - (S : ℝ) := by exact_mod_cast hcI
  refine ⟨Real.one_le_rpow hR.le hξr, ?_⟩
  unfold TrialOuterOwnerBound at ho
  unfold TrialInnerOwnerBound at hi
  by_cases hl : row.order ≤ 2
  · rw [ite_eq_left hl] at hb ho
    have hAo : (row.outerThreshold : ℝ) ≤
        (row.lowerBand : ℝ) - (T : ℝ) + (row.activation : ℝ) := by exact_mod_cast hb.1
    have hAi : (row.innerThreshold : ℝ) ≤
        (row.lowerBand : ℝ) - (S : ℝ) + (row.activation : ℝ) := by exact_mod_cast hb.2.1
    have hos := ho.imp (fun h => h.trans hcOr) (fun h => h.trans hAo)
    rcases hord with hone | htwo | hthree
    · have hguard : 2 * (T : ℝ) ≤ (row.lowerBand : ℝ) + (row.activation : ℝ) := by
        exact_mod_cast hb.2.2.1 hone
      simpa only [hone] using denseDivisibility_lcm_one_of_owner_bound hR hξr hD hE
        hS hT hguard hos hq
    · have hnot : row.order ≠ 1 := by omega
      have hi' := hi.resolve_left hnot
      rw [ite_eq_left hl] at hi'
      have his := hi'.imp (fun h => h.trans hcIr) (fun h => h.trans hAi)
      have hg1 : 2 * (S : ℝ) - (T : ℝ) ≤ (row.lowerBand : ℝ) + (row.activation : ℝ) := by
        exact_mod_cast (hb.2.2.2 htwo).1
      have hg2 : 2 * (T : ℝ) - (S : ℝ) ≤ (row.lowerBand : ℝ) + (row.activation : ℝ) := by
        exact_mod_cast (hb.2.2.2 htwo).2
      simpa only [htwo] using denseDivisibility_lcm_two_of_owner_bounds hR hξr hD hE
        hS hT hg1 hg2 hos his hq
    · omega
  · have hthree : row.order = 3 := by omega
    have hnot : row.order ≠ 1 := by omega
    have hi' := hi.resolve_left hnot
    rw [ite_eq_right hl] at hb ho hi'
    let ηD : ℝ := (row.outerThreshold : ℝ) - ((row.lowerBand : ℝ) - (T : ℝ))
    let ηE : ℝ := (row.innerThreshold : ℝ) - ((row.lowerBand : ℝ) - (S : ℝ))
    have hAe : (row.lowerBand : ℝ) - (T : ℝ) + ηD = (row.outerThreshold : ℝ) := by dsimp [ηD]; ring
    have hCe : (row.lowerBand : ℝ) - (S : ℝ) + ηE = (row.innerThreshold : ℝ) := by dsimp [ηE]; ring
    have hbudget : ((row.lowerBand : ℝ) - (T : ℝ) + ηD) +
        ((row.lowerBand : ℝ) - (S : ℝ) + ηE) ≤ (row.lowerBand : ℝ) + (row.activation : ℝ) := by
      rw [hAe, hCe]
      exact_mod_cast hb
    have hos := ho.imp (fun h => h.trans hcOr) id
    have his := hi'.imp (fun h => h.trans hcIr) id
    rw [← hAe, ← hCe] at hos his
    simpa only [hthree] using denseDivisibility_lcm_three_of_nonlinear_owner_bounds hR hξr
      hD hE hS hT (physicalOuterOwner (trialOwnerPlateau row))
      (physicalInnerOwner (trialOwnerPlateau row)) (physicalOuter_mono _) (physicalInner_mono _)
      (physicalOwner_sum _) hbudget hos his hq

theorem trialInnerOwnerBound_mono_two (row : TrialSourceRow) (ho : row.order = 2)
    (R : ℝ) (hR : 1 < R) (D : ℕ) (h : TrialInnerOwnerBound row R D)
    (c ξ A : ℝ) (hc : (row.innerCore : ℝ) ≤ c) (hξ : (row.activation : ℝ) ≤ ξ)
    (hA : (row.innerThreshold : ℝ) ≤ A) :
    logSize R D ≤ c ∨ (primeFragmentOwner id R ξ D : ℝ) ≤ A := by
  unfold TrialInnerOwnerBound at h
  have hn : row.order ≠ 1 := by omega
  have hlow : row.order ≤ 2 := by omega
  have hh := h.resolve_left hn
  rw [ite_eq_left hlow] at hh
  rcases hh with hcore | howner
  · exact Or.inl (hcore.trans hc)
  right
  have hsub : activatedPrimeFactors R ξ D ⊆ activatedPrimeFactors R (row.activation : ℝ) D :=
    Finset.monotone_filter_right _ (fun p _ hp =>
      (Real.rpow_le_rpow_of_exponent_le hR.le hξ).trans_lt hp)
  have hm : primeFragmentOwner id R ξ D ≤ primeFragmentOwner id R (row.activation : ℝ) D :=
    Finset.sup_mono hsub
  exact (show (primeFragmentOwner id R ξ D : ℝ) ≤
    (primeFragmentOwner id R (row.activation : ℝ) D : ℝ) by exact_mod_cast hm).trans
      (howner.trans hA)

theorem trialCommonSource_lcm_dense (R : ℝ) (hR : 1 < R)
    (D E : ℕ) (hD : Squarefree D) (hE : Squarefree E)
    (hS : logSize R D ≤ (trialEnlargedRadius : ℝ))
    (hT : logSize R E ≤ (trialEnlargedRadius : ℝ))
    (ho : TrialInnerOwnerBound trialCommonInnerRow R D)
    (hi : TrialInnerOwnerBound trialCommonInnerRow R E)
    (hq : R ^ (((1 / 2) / trialRho : ℚ) : ℝ) < (D.lcm E : ℝ)) :
    ∃ hξ : 1 ≤ R ^ ((trialCommonSourceDelta / trialRho : ℚ) : ℝ),
      Nonempty (DenseDivisibilityWitness
        ⟨R ^ ((trialCommonSourceDelta / trialRho : ℚ) : ℝ), hξ⟩ 2 (D.lcm E)) := by
  rcases trialCommonSource_geometry with ⟨horder, hc, hact, hbound, hbudget, hξ, _hupper⟩
  have hξr : 0 ≤ ((trialCommonSourceDelta / trialRho : ℚ) : ℝ) := by exact_mod_cast hξ.le
  have hb : 0 ≤ (((1 / 2) / trialRho : ℚ) : ℝ) - (trialEnlargedRadius : ℝ) +
      ((trialCommonSourceDelta / trialRho : ℚ) : ℝ) := by exact_mod_cast hbudget
  have hw (N : ℕ) (hn : TrialInnerOwnerBound trialCommonInnerRow R N) :
      logSize R N ≤ (((1 / 2) / trialRho : ℚ) : ℝ) - (trialEnlargedRadius : ℝ) ∨
        (primeFragmentOwner id R ((trialCommonSourceDelta / trialRho : ℚ) : ℝ) N : ℝ) ≤
          (((1 / 2) / trialRho : ℚ) : ℝ) - (trialEnlargedRadius : ℝ) +
            ((trialCommonSourceDelta / trialRho : ℚ) : ℝ) :=
    trialInnerOwnerBound_mono_two trialCommonInnerRow horder R hR N hn _ _ _
      (by exact_mod_cast hc) (by exact_mod_cast hact) (by exact_mod_cast hbound)
  exact ⟨Real.one_le_rpow hR.le hξr,
    denseDivisibility_lcm_two_of_common_owner_bounds hR hξr hb hD hE hS hT (hw D ho) (hw E hi) hq⟩

theorem trialSubtractionSource_inner_owner (R : ℝ) (hR : 1 < R) (E : ℕ)
    (h : TrialInnerOwnerBound trialCommonInnerRow R E) :
    TrialInnerOwnerBound trialSubtractionSourceRow R E := by
  rcases trialSubtractionSource_geometry with
    ⟨_, _, _, _, _, _, _, hc, hξ, hA⟩
  have h := trialInnerOwnerBound_mono_two trialCommonInnerRow trialCommonSource_geometry.1 R hR E h
    (trialSubtractionSourceRow.innerCore : ℝ) (trialSubtractionSourceRow.activation : ℝ)
    (trialSubtractionSourceRow.innerThreshold : ℝ)
    (by exact_mod_cast hc) (by exact_mod_cast hξ) (by exact_mod_cast hA)
  exact Or.inr h

#print axioms trialSourceRow_lcm_dense
#print axioms trialInnerOwnerBound_mono_two
#print axioms trialCommonSource_lcm_dense
#print axioms trialSubtractionSource_inner_owner

end PrimeGap182
