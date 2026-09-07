import SourceFaceLoss182

/-! The normalized actual face-loss integral is bounded by the literal
inner numerical certificate. The true-event cover is already a theorem. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

def trialFaceLossFunction (X : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  trialCapFaceMultiplier X - trialActualFaceMultiplier X

def trialFaceLossIntegral : ℝ := trialFaceIntegral trialFaceLossFunction

def trialNormalizedFaceLoss : ℝ :=
  (trialRhoStar : ℝ) * trialFaceLossIntegral / trialSquareIntegral

theorem measurable_trialCapFaceMultiplier : Measurable trialCapFaceMultiplier :=
  (((measurable_trialMask 1).const_mul (trialLambda : ℝ)).add
    ((measurable_trialMask 2).const_mul (1 - (trialLambda : ℝ)))).add
      ((measurable_trialFaceKernel.const_mul trialHybridLoss).mul (measurable_trialMask 3)) |>.sub
        (measurable_trialFaceKernel.const_mul trialHybridLoss)

theorem measurable_trialActualFaceMultiplier : Measurable trialActualFaceMultiplier :=
  ((measurable_trialActualBaseMask.const_mul (trialLambda : ℝ)).add
    (measurable_trialActualEnlargedMask.const_mul (1 - (trialLambda : ℝ)))).add
      ((measurable_trialFaceKernel.const_mul trialHybridLoss).mul measurable_trialActualSubtractionMask) |>.sub
        (measurable_trialFaceKernel.const_mul trialHybridLoss)

theorem measurable_trialFaceLossFunction : Measurable trialFaceLossFunction :=
  measurable_trialCapFaceMultiplier.sub measurable_trialActualFaceMultiplier

theorem trialFaceLossFunction_bounds (X : Fin 38 → FiniteMeasure ℝ) :
    0 ≤ trialFaceLossFunction X ∧ trialFaceLossFunction X ≤ 1 + (trialSourceEpsilonUpper : ℝ) := by
  have h := trialFaceMultiplier_bounds X
  exact ⟨sub_nonneg.mpr h.2.1, h.2.2.2.trans
    (add_le_add le_rfl trialSourceEnvelope_constants.2.2.2.1)⟩

theorem integrable_trialFaceLoss (i : Fin 39) :
    Integrable (fun X => trialFaceLossFunction X * trialMarginal i X ^ 2) (trialProductMeasure 38) := by
  obtain ⟨B, hB⟩ := bounded_trialMarginal i
  exact trial_integrable_bounded_weight_square _ _ _ measurable_trialFaceLossFunction
    (measurable_trialMarginal i)
    (fun X => by simpa only [Real.norm_eq_abs, abs_of_nonneg (trialFaceLossFunction_bounds X).1]
      using (trialFaceLossFunction_bounds X).2) hB

theorem trialFaceLossIntegral_nonneg : 0 ≤ trialFaceLossIntegral := by
  apply div_nonneg _ trialPhysicalNormalizer_pos.le
  apply Finset.sum_nonneg
  intro i _
  exact integral_nonneg fun X => mul_nonneg (trialFaceLossFunction_bounds X).1 (sq_nonneg _)

theorem trialFaceLossIntegral_le_source :
    trialFaceLossIntegral ≤ ∑ j : Fin 137,
      ((trialInnerCertificates j).coefficientUpper : ℝ) * trialSourceInnerMass j := by
  have hI (i : Fin 39) :
      (∫ X, trialFaceLossFunction X * trialMarginal i X ^ 2 ∂trialProductMeasure 38) ≤
        ∑ j : Fin 137, ((trialInnerCertificates j).coefficientUpper : ℝ) *
          ∫ X, trialSourceInnerWeight j X * trialMarginal i X ^ 2 ∂trialProductMeasure 38 := by
    have hR (j : Fin 137) : Integrable (fun X =>
        ((trialInnerCertificates j).coefficientUpper : ℝ) *
          (trialSourceInnerWeight j X * trialMarginal i X ^ 2)) (trialProductMeasure 38) :=
      (integrable_trialSourceInnerMass j i).const_mul _
    calc
      _ ≤ ∫ X, ∑ j : Fin 137, ((trialInnerCertificates j).coefficientUpper : ℝ) *
          (trialSourceInnerWeight j X * trialMarginal i X ^ 2) ∂trialProductMeasure 38 := by
        apply integral_mono_ae (integrable_trialFaceLoss i) (integrable_finsetSum _ (fun j _ => hR j))
        filter_upwards [trialFaceLoss_le_sourceKernels_ae] with X hX
        have h := mul_le_mul_of_nonneg_right hX (sq_nonneg (trialMarginal i X))
        simpa only [trialFaceLossFunction, Finset.sum_mul, mul_assoc] using h
      _ = _ := by
        rw [integral_finsetSum _ (fun j _ => hR j)]
        exact Finset.sum_congr rfl (fun j _ => integral_const_mul _ _)
  have hRaw := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 39))) => hI i)
  rw [Finset.sum_comm] at hRaw
  simp only [← Finset.mul_sum] at hRaw
  have h := div_le_div_of_nonneg_right hRaw trialPhysicalNormalizer_pos.le
  simpa only [trialFaceLossIntegral, trialFaceIntegral, trialSourceInnerMass,
    Finset.sum_div, mul_div_assoc] using h

theorem trialNormalizedFaceLoss_le (h : PhysicalSourceBounds182) :
    trialNormalizedFaceLoss ≤ (trialSourceInnerTotalUpper : ℝ) := by
  have hρ : (0 : ℝ) ≤ (trialRhoStar : ℝ) := by norm_num [trialRhoStar]
  calc
    _ ≤ (trialRhoStar : ℝ) * (∑ j : Fin 137,
        ((trialInnerCertificates j).coefficientUpper : ℝ) * trialSourceInnerMass j) /
          trialSquareIntegral := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left trialFaceLossIntegral_le_source hρ) (trialSquareIntegral_pos h.cap).le
    _ = trialSourceInnerLoss := by
      simp only [trialSourceInnerLoss, Finset.mul_sum, Finset.sum_div, mul_assoc]
    _ ≤ _ := trialSourceInnerLoss_le h

#print axioms integrable_trialFaceLoss
#print axioms trialFaceLossIntegral_le_source
#print axioms trialNormalizedFaceLoss_le

end PrimeGap182
