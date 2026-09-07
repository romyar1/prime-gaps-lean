import SourcePartitionCauchy182
import TrialCapForm182
import SourceRestorationData182

/-! Positive energy for the actual restored 39-coordinate trial. The only
premise in the final theorem is the bundle of 262 explicitly defined finite
physical integral bounds. Source coverage, erasure adjunction, the signed
quadratic expansion, and the operator bounds are proved here or imported as
proved theorems. This is not a prime-distribution or DHL theorem. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

def trialRestoredEnergy : ℝ :=
  trialFacePair trialActualFaceMultiplier trialSourceStepFunction trialSourceStepFunction -
    trialRootPair trialSourceStepFunction trialSourceStepFunction

theorem trialFacePair_scaled_add_diag
    {w : (Fin 38 → FiniteMeasure ℝ) → ℝ} (hw : Measurable w)
    (hwb : ∃ B : ℝ, ∀ Y, ‖w Y‖ ≤ B)
    {f g : (Fin 39 → FiniteMeasure ℝ) → ℝ}
    (hf : TrialRegularProfile f) (hg : TrialRegularProfile g) (a : ℝ) :
    trialFacePair w (fun X => a * f X + g X) (fun X => a * f X + g X) =
      a ^ 2 * trialFacePair w f f + 2 * a * trialFacePair w f g + trialFacePair w g g := by
  rw [trialFacePair_add_left hw hwb (hf.const_mul a) hg ((hf.const_mul a).add hg),
    trialFacePair_add_right hw hwb (hf.const_mul a) hg (hf.const_mul a),
    trialFacePair_add_right hw hwb (hf.const_mul a) hg hg]
  simp only [trialFacePair_const_mul_left, trialFacePair_const_mul_right]
  rw [trialFacePair_symm w g f]
  ring

theorem trialFacePair_sub_diag
    {w : (Fin 38 → FiniteMeasure ℝ) → ℝ} (hw : Measurable w)
    (hwb : ∃ B : ℝ, ∀ Y, ‖w Y‖ ≤ B)
    {f g : (Fin 39 → FiniteMeasure ℝ) → ℝ}
    (hf : TrialRegularProfile f) (hg : TrialRegularProfile g) :
    trialFacePair w (fun X => f X - g X) (fun X => f X - g X) =
      trialFacePair w f f - 2 * trialFacePair w g f + trialFacePair w g g := by
  rw [trialFacePair_sub_left hw hwb hf hg (hf.sub hg),
    trialFacePair_sub_right hw hwb hf hg hf, trialFacePair_sub_right hw hwb hf hg hg]
  rw [trialFacePair_symm w f g]
  ring

theorem trialProjection_root_identity :
    trialRootEnergy - trialRootPair trialSourceStepFunction trialSourceStepFunction =
      trialRootPair trialResidual trialResidual := by
  have hsource : Integrable (fun X => trialSourceStepFunction X * trialSourceStepFunction X)
      (trialProductMeasure 39) := by simpa only [pow_two] using trial_regular_source.integrable_sq
  unfold trialRootEnergy trialRootPair
  rw [← integral_sub integrable_trialStepFunction_sq hsource]
  apply integral_congr_ae
  filter_upwards [] with X
  by_cases hX : TrialActualOuter X <;>
    simp only [trialResidual, trialSourceStepFunction, trialActualOuterMask, hX, ite_true,
      ite_false, one_mul, zero_mul] <;> ring

theorem trialRestoredEnergy_expansion :
    trialRestoredEnergy =
      (trialFacePair trialCapFaceMultiplier trialStepFunction trialStepFunction - trialRootEnergy) -
        trialFacePair trialFaceLossFunction trialStepFunction trialStepFunction -
        2 * trialFacePair trialCapFaceMultiplier trialResidual trialStepFunction +
        2 * trialFacePair trialFaceLossFunction trialResidual trialStepFunction +
        trialFacePair trialActualFaceMultiplier trialResidual trialResidual +
        trialRootPair trialResidual trialResidual := by
  have heq : (fun X => trialStepFunction X - trialResidual X) = trialSourceStepFunction := by
    funext X
    dsimp only [trialResidual]
    ring
  have hT := trialFacePair_sub_diag measurable_trialActualFaceMultiplier trialActualFaceMultiplier_bounded
    trial_regular_step trial_regular_residual
  rw [heq] at hT
  have hDF := trialFacePair_loss_eq trial_regular_step trial_regular_step
  have hDe := trialFacePair_loss_eq trial_regular_residual trial_regular_step
  have hI := trialProjection_root_identity
  unfold trialRestoredEnergy
  linarith only [hT, hDF, hDe, hI]

theorem trialFaceLoss_young {f g : (Fin 39 → FiniteMeasure ℝ) → ℝ}
    (hf : TrialRegularProfile f) (hg : TrialRegularProfile g) :
    -(trialSourceCommonT : ℝ) * trialRootPair f f -
      ((trialSourceGammaUpper : ℝ) / (trialSourceCommonT : ℝ)) *
        trialFacePair trialFaceLossFunction g g ≤
      2 * trialFacePair trialFaceLossFunction f g := by
  let a : ℝ := (trialSourceCommonT : ℝ) / (trialSourceGammaUpper : ℝ)
  have hΓ := trialSource_form_constants.2.2.2.1
  have ht : 0 < (trialSourceCommonT : ℝ) := by norm_num [trialSourceCommonT]
  have hpos := trialFacePair_nonneg trialFaceLossFunction (fun Y => (trialFaceLossFunction_bounds Y).1)
    (fun X => a * f X + g X)
  rw [trialFacePair_scaled_add_diag measurable_trialFaceLossFunction trialFaceLossFunction_bounded hf hg a]
    at hpos
  have hupper := mul_le_mul_of_nonneg_left (trialFacePair_loss_upper hf) (sq_nonneg a)
  have hpre : 0 ≤ a ^ 2 * ((trialSourceGammaUpper : ℝ) * trialRootPair f f) +
      2 * a * trialFacePair trialFaceLossFunction f g + trialFacePair trialFaceLossFunction g g := by
    linarith only [hpos, hupper]
  have hs := mul_nonneg (div_pos hΓ ht).le hpre
  have hid : ((trialSourceGammaUpper : ℝ) / (trialSourceCommonT : ℝ)) *
      (a ^ 2 * ((trialSourceGammaUpper : ℝ) * trialRootPair f f) +
        2 * a * trialFacePair trialFaceLossFunction f g + trialFacePair trialFaceLossFunction g g) =
      (trialSourceCommonT : ℝ) * trialRootPair f f +
        2 * trialFacePair trialFaceLossFunction f g +
        ((trialSourceGammaUpper : ℝ) / (trialSourceCommonT : ℝ)) *
          trialFacePair trialFaceLossFunction g g := by
    dsimp only [a]
    field_simp
  rw [hid] at hs
  linarith only [hs]

theorem trialFaceLoss_normalized (h : PhysicalCapBounds182) :
    trialFacePair trialFaceLossFunction trialStepFunction trialStepFunction / trialRootEnergy =
      trialNormalizedFaceLoss := by
  have hE := trialRootEnergy_pos h
  unfold trialFacePair trialNormalizedFaceLoss trialFaceLossIntegral trialFaceIntegral trialSquareIntegral
  change ((trialRhoStar : ℝ) * ∑ i : Fin 39,
      ∫ Y, trialFaceLossFunction Y * trialMarginal i Y * trialMarginal i Y ∂trialProductMeasure 38) /
        trialRootEnergy = _
  simp only [mul_assoc, ← pow_two]
  change (_ * _) / trialRootEnergy = (_ * (_ / trialPhysicalNormalizer)) /
    (trialRootEnergy / trialPhysicalNormalizer)
  field_simp [hE.ne', trialPhysicalNormalizer_pos.ne']

theorem trialRestoredEnergy_normalized_lower (h : PhysicalSourceBounds182) :
    trialCapQuotient - 1 - (trialRestorationPenalty : ℝ) ≤ trialRestoredEnergy / trialRootEnergy := by
  have hE := trialRootEnergy_pos h.cap
  have hΓ := trialSource_form_constants.2.2.2.1
  have ht : 0 < (trialSourceCommonT : ℝ) := by norm_num [trialSourceCommonT]
  have hγ := trialSource_form_constants.2.2.1
  have hδ := trialSource_form_constants.2.2.2.2.1
  have htg := trialSource_form_constants.2.2.2.2.2
  have hD : trialFacePair trialFaceLossFunction trialStepFunction trialStepFunction ≤
      (trialSourceInnerTotalUpper : ℝ) * trialRootEnergy := by
    apply (div_le_iff₀ hE).mp
    rw [trialFaceLoss_normalized h.cap]
    exact trialNormalizedFaceLoss_le h
  have hD' := mul_le_mul_of_nonneg_left hD (div_pos hΓ ht).le
  have hcross := trialResidual_cap_cross_le h
  have hmass := trialResidual_energy_le h
  have hmass' := mul_le_mul_of_nonneg_left hmass (sub_nonneg.mpr htg.le)
  have hyoung := trialFaceLoss_young trial_regular_residual trial_regular_step
  have hlower := trialFacePair_actual_lower trial_regular_residual
  have hexp := trialRestoredEnergy_expansion
  have hcap := trialCapForm_quotient h.cap
  have hcap' : trialFacePair trialCapFaceMultiplier trialStepFunction trialStepFunction =
      trialCapQuotient * trialRootEnergy := (div_eq_iff hE.ne').mp hcap
  apply (le_div_iff₀ hE).mpr
  have hpenalty : (trialRestorationPenalty : ℝ) =
      (trialSourceInnerTotalUpper : ℝ) +
        (trialSourceGammaUpper : ℝ) * (trialSourceInnerTotalUpper : ℝ) / (trialSourceCommonT : ℝ) +
        2 * ∑ j : Fin 60, ((trialOuterCertificates j).sqrtUpper : ℝ) +
        ((trialSourceCommonT : ℝ) - (1 - (trialSourceDeltaUpper : ℝ))) *
          ∑ j : Fin 60, ((trialOuterCertificates j).normalizedA : ℝ) := by
    simp only [trialRestorationPenalty, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
      Rat.cast_sum, Rat.cast_ofNat, Rat.cast_sub, hγ]
  rw [hpenalty]
  have halg : (trialCapQuotient - 1 -
      ((trialSourceInnerTotalUpper : ℝ) +
        (trialSourceGammaUpper : ℝ) * (trialSourceInnerTotalUpper : ℝ) / (trialSourceCommonT : ℝ) +
        2 * ∑ j : Fin 60, ((trialOuterCertificates j).sqrtUpper : ℝ) +
        ((trialSourceCommonT : ℝ) - (1 - (trialSourceDeltaUpper : ℝ))) *
          ∑ j : Fin 60, ((trialOuterCertificates j).normalizedA : ℝ))) * trialRootEnergy =
      (trialFacePair trialCapFaceMultiplier trialStepFunction trialStepFunction - trialRootEnergy) -
        (trialSourceInnerTotalUpper : ℝ) * trialRootEnergy -
        ((trialSourceGammaUpper : ℝ) / (trialSourceCommonT : ℝ)) *
          ((trialSourceInnerTotalUpper : ℝ) * trialRootEnergy) -
        2 * (trialRootEnergy * ∑ j : Fin 60, ((trialOuterCertificates j).sqrtUpper : ℝ)) -
        ((trialSourceCommonT : ℝ) - (1 - (trialSourceDeltaUpper : ℝ))) *
          (trialRootEnergy * ∑ j : Fin 60, ((trialOuterCertificates j).normalizedA : ℝ)) := by
    rw [hcap']
    ring
  rw [halg]
  linarith only [hexp, hyoung, hlower, hD, hD', hcross, hmass']

/-- Positive energy of the literal restored profile, conditional only on the
262 scalar integral leaves in `PhysicalSourceBounds182`. -/
theorem physical_restored_energy_margin182 (h : PhysicalSourceBounds182) :
    (65213759 / 10 ^ 12 : ℝ) < trialRestoredEnergy / trialRootEnergy := by
  have hcap := trialCapQuotient_surplus h.cap
  have hlower := trialRestoredEnergy_normalized_lower h
  linarith only [trialRestoration_margin_real, hcap, hlower]

theorem physical_restored_energy_positive182 (h : PhysicalSourceBounds182) :
    0 < trialRestoredEnergy := by
  have hnorm : 0 < trialRestoredEnergy / trialRootEnergy :=
    lt_trans (by norm_num) (physical_restored_energy_margin182 h)
  exact (div_pos_iff_of_pos_right (trialRootEnergy_pos h.cap)).mp hnorm

#print axioms trialRestoredEnergy_expansion
#print axioms trialFaceLoss_young
#print axioms trialRestoredEnergy_normalized_lower
#print axioms physical_restored_energy_margin182
#print axioms physical_restored_energy_positive182

end PrimeGap182
