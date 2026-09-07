import PhysicalForms182

/-! Bilinear identities, positivity, and norm estimates for the actual physical
face form. These statements use the constructed erasure integrals. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

theorem trialRhoStar_pos : 0 < (trialRhoStar : ℝ) := by norm_num [trialRhoStar]

theorem trialCapFaceMultiplier_bounded :
    ∃ B : ℝ, ∀ Y, ‖trialCapFaceMultiplier Y‖ ≤ B := by
  refine ⟨1, fun Y => ?_⟩
  rw [Real.norm_eq_abs]
  exact (trialFaceMultiplier_abs_le_sourceFaceWeight Y).2.trans (trialSourceFaceWeight_bounds Y).2

theorem trialActualFaceMultiplier_bounded :
    ∃ B : ℝ, ∀ Y, ‖trialActualFaceMultiplier Y‖ ≤ B := by
  refine ⟨1, fun Y => ?_⟩
  rw [Real.norm_eq_abs]
  exact (trialFaceMultiplier_abs_le_sourceFaceWeight Y).1.trans (trialSourceFaceWeight_bounds Y).2

theorem trialFaceLossFunction_bounded :
    ∃ B : ℝ, ∀ Y, ‖trialFaceLossFunction Y‖ ≤ B := by
  refine ⟨1 + (trialSourceEpsilonUpper : ℝ), fun Y => ?_⟩
  rw [Real.norm_of_nonneg (trialFaceLossFunction_bounds Y).1]
  exact (trialFaceLossFunction_bounds Y).2

section Algebra

variable {w : (Fin 38 → FiniteMeasure ℝ) → ℝ}
  (hw : Measurable w) (hwb : ∃ B : ℝ, ∀ Y, ‖w Y‖ ≤ B)
  {f g h : (Fin 39 → FiniteMeasure ℝ) → ℝ}
  (hf : TrialRegularProfile f) (hg : TrialRegularProfile g) (hh : TrialRegularProfile h)

include hw hwb hf hg hh

theorem trialFacePair_add_left :
    trialFacePair w (fun X => f X + g X) h = trialFacePair w f h + trialFacePair w g h := by
  unfold trialFacePair
  simp only [trialErasure_add hf hg, mul_add, add_mul]
  simp_rw [integral_add (integrable_trialFacePair_integrand hw hwb hf hh _)
    (integrable_trialFacePair_integrand hw hwb hg hh _)]
  rw [Finset.sum_add_distrib, mul_add]

theorem trialFacePair_sub_left :
    trialFacePair w (fun X => f X - g X) h = trialFacePair w f h - trialFacePair w g h := by
  unfold trialFacePair
  simp only [trialErasure_sub hf hg, mul_sub, sub_mul]
  simp_rw [integral_sub (integrable_trialFacePair_integrand hw hwb hf hh _)
    (integrable_trialFacePair_integrand hw hwb hg hh _)]
  rw [Finset.sum_sub_distrib, mul_sub]

theorem trialFacePair_add_right :
    trialFacePair w h (fun X => f X + g X) = trialFacePair w h f + trialFacePair w h g := by
  rw [trialFacePair_symm w h, trialFacePair_add_left hw hwb hf hg hh,
    trialFacePair_symm w f h, trialFacePair_symm w g h]

theorem trialFacePair_sub_right :
    trialFacePair w h (fun X => f X - g X) = trialFacePair w h f - trialFacePair w h g := by
  rw [trialFacePair_symm w h, trialFacePair_sub_left hw hwb hf hg hh,
    trialFacePair_symm w f h, trialFacePair_symm w g h]

end Algebra

theorem trialFacePair_const_mul_left (w : (Fin 38 → FiniteMeasure ℝ) → ℝ)
    (f g : (Fin 39 → FiniteMeasure ℝ) → ℝ) (a : ℝ) :
    trialFacePair w (fun X => a * f X) g = a * trialFacePair w f g := by
  unfold trialFacePair
  simp only [trialErasure_const_mul]
  simp_rw [show ∀ Y i, w Y * (a * trialErasure f i Y) * trialErasure g i Y =
    a * (w Y * trialErasure f i Y * trialErasure g i Y) by intros; ring]
  simp only [integral_const_mul, ← Finset.mul_sum]
  ring

theorem trialFacePair_const_mul_right (w : (Fin 38 → FiniteMeasure ℝ) → ℝ)
    (f g : (Fin 39 → FiniteMeasure ℝ) → ℝ) (a : ℝ) :
    trialFacePair w f (fun X => a * g X) = a * trialFacePair w f g := by
  rw [trialFacePair_symm w f, trialFacePair_const_mul_left, trialFacePair_symm w g f]

theorem trialFacePair_sub_weight
    {w v : (Fin 38 → FiniteMeasure ℝ) → ℝ} (hw : Measurable w) (hv : Measurable v)
    (hwb : ∃ B : ℝ, ∀ Y, ‖w Y‖ ≤ B) (hvb : ∃ B : ℝ, ∀ Y, ‖v Y‖ ≤ B)
    {f g : (Fin 39 → FiniteMeasure ℝ) → ℝ}
    (hf : TrialRegularProfile f) (hg : TrialRegularProfile g) :
    trialFacePair (fun Y => w Y - v Y) f g = trialFacePair w f g - trialFacePair v f g := by
  unfold trialFacePair
  simp only [sub_mul]
  simp_rw [integral_sub (integrable_trialFacePair_integrand hw hwb hf hg _)
    (integrable_trialFacePair_integrand hv hvb hf hg _)]
  rw [Finset.sum_sub_distrib, mul_sub]

theorem trialFacePair_nonneg (w : (Fin 38 → FiniteMeasure ℝ) → ℝ)
    (hw : ∀ Y, 0 ≤ w Y) (f : (Fin 39 → FiniteMeasure ℝ) → ℝ) :
    0 ≤ trialFacePair w f f := by
  apply mul_nonneg trialRhoStar_pos.le
  apply Finset.sum_nonneg
  intro i _
  exact integral_nonneg fun Y => by
    change (0 : ℝ) ≤ w Y * trialErasure f i Y * trialErasure f i Y
    simpa only [← mul_assoc, pow_two] using mul_nonneg (hw Y) (sq_nonneg (trialErasure f i Y))

theorem integrable_trialErasure_sq {f : (Fin 39 → FiniteMeasure ℝ) → ℝ}
    (hf : TrialRegularProfile f) (i : Fin 39) :
    Integrable (fun Y => trialErasure f i Y ^ 2) (trialProductMeasure 38) := by
  simpa only [pow_two] using trial_integrable_bounded_product
    (measurable_trialErasure hf i) (measurable_trialErasure hf i)
    (bounded_trialErasure hf i) (bounded_trialErasure hf i)

theorem trialFacePair_upper {w : (Fin 38 → FiniteMeasure ℝ) → ℝ}
    (hw : Measurable w) (hwb : ∃ B : ℝ, ∀ Y, ‖w Y‖ ≤ B)
    {B : ℝ} (hB : 0 ≤ B) (hle : ∀ Y, w Y ≤ B)
    {f : (Fin 39 → FiniteMeasure ℝ) → ℝ} (hf : TrialRegularProfile f) :
    trialFacePair w f f ≤ (4 * (trialRhoStar : ℝ) * B) * trialRootPair f f := by
  have hI (i : Fin 39) :
      (∫ Y, w Y * trialErasure f i Y * trialErasure f i Y ∂trialProductMeasure 38) ≤
        B * ∫ Y, trialErasure f i Y ^ 2 ∂trialProductMeasure 38 := by
    rw [← integral_const_mul]
    apply integral_mono (integrable_trialFacePair_integrand hw hwb hf hf i)
      ((integrable_trialErasure_sq hf i).const_mul B)
    intro Y
    simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_right (hle Y)
      (sq_nonneg (trialErasure f i Y))
  calc
    _ ≤ (trialRhoStar : ℝ) * ∑ i : Fin 39,
        B * ∫ Y, trialErasure f i Y ^ 2 ∂trialProductMeasure 38 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hI i) trialRhoStar_pos.le
    _ = ((trialRhoStar : ℝ) * B) * ∑ i : Fin 39,
        ∫ Y, trialErasure f i Y ^ 2 ∂trialProductMeasure 38 := by rw [← Finset.mul_sum]; ring
    _ ≤ ((trialRhoStar : ℝ) * B) * (4 * trialRootPair f f) :=
      mul_le_mul_of_nonneg_left (trialErasure_energy_bound hf) (mul_nonneg trialRhoStar_pos.le hB)
    _ = _ := by ring

theorem trialFacePair_lower {w : (Fin 38 → FiniteMeasure ℝ) → ℝ}
    (hw : Measurable w) (hwb : ∃ B : ℝ, ∀ Y, ‖w Y‖ ≤ B)
    {B : ℝ} (hB : 0 ≤ B) (hle : ∀ Y, -B ≤ w Y)
    {f : (Fin 39 → FiniteMeasure ℝ) → ℝ} (hf : TrialRegularProfile f) :
    -(4 * (trialRhoStar : ℝ) * B) * trialRootPair f f ≤ trialFacePair w f f := by
  have hnb : ∃ C : ℝ, ∀ Y, ‖-w Y‖ ≤ C := by
    obtain ⟨C, hC⟩ := hwb
    exact ⟨C, fun Y => by simpa only [norm_neg] using hC Y⟩
  have hn := trialFacePair_upper hw.neg hnb hB (fun Y => neg_le.mpr (hle Y)) hf
  change trialFacePair (fun Y => -w Y) f f ≤ _ at hn
  have heq : trialFacePair (fun Y => -w Y) f f = -trialFacePair w f f := by
    unfold trialFacePair
    simp only [neg_mul, integral_neg, Finset.sum_neg_distrib, mul_neg]
  rw [heq] at hn
  linarith

theorem trialFacePair_loss_eq {f g : (Fin 39 → FiniteMeasure ℝ) → ℝ}
    (hf : TrialRegularProfile f) (hg : TrialRegularProfile g) :
    trialFacePair trialFaceLossFunction f g =
      trialFacePair trialCapFaceMultiplier f g - trialFacePair trialActualFaceMultiplier f g :=
  trialFacePair_sub_weight measurable_trialCapFaceMultiplier measurable_trialActualFaceMultiplier
    trialCapFaceMultiplier_bounded trialActualFaceMultiplier_bounded hf hg

theorem trialSource_form_constants :
    (trialSourceGammaUpper : ℝ) = 4 * (trialRhoStar : ℝ) * (1 + (trialSourceEpsilonUpper : ℝ)) ∧
    (trialSourceDeltaUpper : ℝ) = 4 * (trialRhoStar : ℝ) * (trialSourceEpsilonUpper : ℝ) ∧
    (trialSourceGammaLower : ℝ) = 1 - (trialSourceDeltaUpper : ℝ) ∧
    0 < (trialSourceGammaUpper : ℝ) ∧ (trialSourceDeltaUpper : ℝ) < 1 ∧
    1 - (trialSourceDeltaUpper : ℝ) < (trialSourceCommonT : ℝ) := by
  norm_num [trialSourceGammaUpper, trialSourceDeltaUpper, trialSourceGammaLower,
    trialRhoStar, trialSourceEpsilonUpper, trialSourceCommonT]

theorem trialFacePair_loss_upper {f : (Fin 39 → FiniteMeasure ℝ) → ℝ}
    (hf : TrialRegularProfile f) :
    trialFacePair trialFaceLossFunction f f ≤ (trialSourceGammaUpper : ℝ) * trialRootPair f f := by
  rw [trialSource_form_constants.1]
  exact trialFacePair_upper measurable_trialFaceLossFunction trialFaceLossFunction_bounded
    (by norm_num [trialSourceEpsilonUpper]) (fun Y => (trialFaceLossFunction_bounds Y).2) hf

theorem trialFacePair_actual_lower {f : (Fin 39 → FiniteMeasure ℝ) → ℝ}
    (hf : TrialRegularProfile f) :
    -(trialSourceDeltaUpper : ℝ) * trialRootPair f f ≤ trialFacePair trialActualFaceMultiplier f f := by
  rw [trialSource_form_constants.2.1]
  apply trialFacePair_lower measurable_trialActualFaceMultiplier trialActualFaceMultiplier_bounded
    (by norm_num [trialSourceEpsilonUpper]) _ hf
  intro Y
  exact (neg_le_neg trialSourceEnvelope_constants.2.2.2.1).trans (trialFaceMultiplier_bounds Y).1

theorem trialCapPullback_adjoint {f : (Fin 39 → FiniteMeasure ℝ) → ℝ}
    (hf : TrialRegularProfile f) :
    (∫ X, f X * trialCapPullback X ∂trialProductMeasure 39) =
      trialFacePair trialCapFaceMultiplier f trialStepFunction := by
  have hi (i : Fin 39) : Measurable (fun X : Fin 39 → FiniteMeasure ℝ => i.removeNth X) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply (i.succAbove j)
  have hb (i : Fin 39) := trial_bounded_mul trialCapFaceMultiplier_bounded (bounded_trialMarginal i)
  have hm (i : Fin 39) := measurable_trialCapFaceMultiplier.mul (measurable_trialMarginal i)
  have hI (i : Fin 39) : Integrable (fun X => f X *
      (trialCapFaceMultiplier (i.removeNth X) * trialMarginal i (i.removeNth X)))
        (trialProductMeasure 39) :=
    trial_integrable_bounded_product hf.measurable ((hm i).comp (hi i)) hf.bounded
      (by obtain ⟨B, hB⟩ := hb i; exact ⟨B, fun X => hB (i.removeNth X)⟩)
  calc
    _ = (trialRhoStar : ℝ) * ∫ X, ∑ i : Fin 39, f X *
        (trialCapFaceMultiplier (i.removeNth X) * trialMarginal i (i.removeNth X))
          ∂trialProductMeasure 39 := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with X
      change f X * ((trialRhoStar : ℝ) * ∑ i : Fin 39,
        trialCapFaceMultiplier (i.removeNth X) * trialMarginal i (i.removeNth X)) = _
      rw [← Finset.mul_sum]
      ring
    _ = (trialRhoStar : ℝ) * ∑ i : Fin 39, ∫ X, f X *
        (trialCapFaceMultiplier (i.removeNth X) * trialMarginal i (i.removeNth X))
          ∂trialProductMeasure 39 := by rw [integral_finsetSum _ fun i _ => hI i]
    _ = _ := by
      unfold trialFacePair
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [trialErasure_adjoint hf i (H := fun Y => trialCapFaceMultiplier Y * trialMarginal i Y)
        (hm i) (hb i)]
      apply integral_congr_ae
      filter_upwards [] with Y
      change trialErasure f i Y * (trialCapFaceMultiplier Y * trialErasure trialStepFunction i Y) = _
      ring

#print axioms trialFacePair_loss_upper
#print axioms trialFacePair_actual_lower
#print axioms trialCapPullback_adjoint

end PrimeGap182
