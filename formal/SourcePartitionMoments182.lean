import SourcePartition182
import SourceIntegralLoss182

/-! The actual partition moments A and M, with the full signed cap
pullback and the literal outer integral normalization. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace PrimeGap182

def trialRootEnergy : ℝ := ∫ X, trialStepFunction X ^ 2 ∂trialProductMeasure 39

def trialCapPullback (X : Fin 39 → FiniteMeasure ℝ) : ℝ :=
  (trialRhoStar : ℝ) * ∑ i : Fin 39,
    trialCapFaceMultiplier (i.removeNth X) * trialMarginal i (i.removeNth X)

def trialOuterPartitionA (j : Fin 60) : ℝ :=
  (∫ X, trialOuterPartition j X * trialStepFunction X ^ 2 ∂trialProductMeasure 39) / trialRootEnergy

def trialOuterPartitionM (j : Fin 60) : ℝ :=
  (∫ X, trialOuterPartition j X * trialCapPullback X ^ 2 ∂trialProductMeasure 39) / trialRootEnergy

theorem trialRootEnergy_pos (h : PhysicalCapBounds182) : 0 < trialRootEnergy := by
  have hs := trialSquareIntegral_pos h
  change 0 < trialRootEnergy / trialPhysicalNormalizer at hs
  exact (div_pos_iff_of_pos_right trialPhysicalNormalizer_pos).mp hs

theorem measurable_trialCapPullback : Measurable trialCapPullback := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  have he : Measurable (fun X : Fin 39 → FiniteMeasure ℝ => i.removeNth X) :=
    measurable_pi_lambda _ fun k => measurable_pi_apply (i.succAbove k)
  exact (measurable_trialCapFaceMultiplier.comp he).mul ((measurable_trialMarginal i).comp he)

theorem bounded_trialCapPullback : ∃ B : ℝ, ∀ X, ‖trialCapPullback X‖ ≤ B := by
  choose B hB using (fun i : Fin 39 => bounded_trialMarginal i)
  refine ⟨|(trialRhoStar : ℝ)| * ∑ i : Fin 39, |B i|, ?_⟩
  intro X
  change ‖(trialRhoStar : ℝ) * ∑ i : Fin 39,
    trialCapFaceMultiplier (i.removeNth X) * trialMarginal i (i.removeNth X)‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    _ ≤ ∑ i : Fin 39, ‖trialCapFaceMultiplier (i.removeNth X) *
        trialMarginal i (i.removeNth X)‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      have hw : ‖trialCapFaceMultiplier (i.removeNth X)‖ ≤ 1 := by
        rw [Real.norm_eq_abs]
        exact (trialFaceMultiplier_abs_le_sourceFaceWeight _).2.trans (trialSourceFaceWeight_bounds _).2
      have hv : ‖trialMarginal i (i.removeNth X)‖ ≤ |B i| :=
        (hB i _).trans (le_abs_self _)
      rw [norm_mul]
      simpa only [one_mul] using mul_le_mul hw hv (norm_nonneg _) zero_le_one

theorem integrable_trialOuterPartition_square (j : Fin 60)
    (f : (Fin 39 → FiniteMeasure ℝ) → ℝ) (hf : Measurable f)
    (hb : ∃ B : ℝ, ∀ X, ‖f X‖ ≤ B) :
    Integrable (fun X => trialOuterPartition j X * f X ^ 2) (trialProductMeasure 39) := by
  obtain ⟨B, hB⟩ := hb
  exact trial_integrable_bounded_weight_square _ _ _ (measurable_trialOuterPartition j) hf
    (fun X => by simpa only [Real.norm_eq_abs, abs_of_nonneg (trialOuterPartition_bounds j X).1]
      using (trialOuterPartition_bounds j X).2.2) hB

theorem bounded_trialStepFunction : ∃ B : ℝ, ∀ X, ‖trialStepFunction X‖ ≤ B := by
  obtain ⟨B, _, hB⟩ := trialStepFunction_finite_range.isBounded.exists_pos_norm_le
  exact ⟨B, fun X => hB _ ⟨X, rfl⟩⟩

theorem trialOuterPartition_root_le_kernel (j : Fin 60) :
    (∫ X, trialOuterPartition j X * trialStepFunction X ^ 2 ∂trialProductMeasure 39) ≤
      ∫ X, trialSourceKernel (trialOuterCertificates j).cover X * trialStepFunction X ^ 2
        ∂trialProductMeasure 39 := by
  apply integral_mono (integrable_trialOuterPartition_square j _ measurable_trialStepFunction
    bounded_trialStepFunction) (integrable_trialSourceOuterRoot j)
  intro X
  exact mul_le_mul_of_nonneg_right
    ((trialOuterPartition_bounds j X).2.1.trans (trialOuterCoverIndicator_le_kernel j X).2)
      (sq_nonneg _)

theorem trialOuterPartition_pullback_pointwise (j : Fin 60) (X : Fin 39 → FiniteMeasure ℝ) :
    trialOuterPartition j X * trialCapPullback X ^ 2 ≤
      (trialRhoStar : ℝ) ^ 2 * ∑ i : Fin 39,
        trialSourceOuterWeight j i X * trialMarginal i (i.removeNth X) ^ 2 := by
  by_cases hE : TrialOuterCoverEvent j X
  · have hc := trialCapPullback_square_on_outer_event j X hE
      (fun i => trialMarginal i (i.removeNth X))
    have hK : 1 ≤ trialSourceKernel (trialOuterCertificates j).cover X := by
      simpa only [trialSourceKernel, hE.1, ite_true] using hE.2.1
    have hmass : 0 ≤ trialSourceCountMultiplier j X * ∑ i : Fin 39,
        trialSourceFaceWeight (i.removeNth X) * trialMarginal i (i.removeNth X) ^ 2 :=
      mul_nonneg (trialSourceCountMultiplier_bounds j X).1
        (Finset.sum_nonneg fun i _ => mul_nonneg (trialSourceFaceWeight_bounds _).1 (sq_nonneg _))
    calc
      _ ≤ trialCapPullback X ^ 2 := mul_le_of_le_one_left (sq_nonneg _) (trialOuterPartition_bounds j X).2.2
      _ ≤ (trialRhoStar : ℝ) ^ 2 * (trialSourceCountMultiplier j X * ∑ i : Fin 39,
          trialSourceFaceWeight (i.removeNth X) * trialMarginal i (i.removeNth X) ^ 2) := by
        simpa only [trialCapPullback, mul_pow] using mul_le_mul_of_nonneg_left hc (sq_nonneg (trialRhoStar : ℝ))
      _ ≤ (trialRhoStar : ℝ) ^ 2 * (trialSourceKernel (trialOuterCertificates j).cover X *
          (trialSourceCountMultiplier j X * ∑ i : Fin 39,
            trialSourceFaceWeight (i.removeNth X) * trialMarginal i (i.removeNth X) ^ 2)) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hmass hK) (sq_nonneg _)
      _ = _ := by simp only [Finset.mul_sum, trialSourceOuterWeight, mul_assoc]
  · rw [trialOuterPartition_zero_of_not_event j X hE, zero_mul]
    apply mul_nonneg (sq_nonneg _)
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg ((trialSourceOuterWeight_regular j i).2.choose_spec.2 X).1 (sq_nonneg _)

theorem trialOuterPartition_pullback_integral_le (j : Fin 60) :
    (∫ X, trialOuterPartition j X * trialCapPullback X ^ 2 ∂trialProductMeasure 39) ≤
      (trialRhoStar : ℝ) ^ 2 * ∑ i : Fin 39,
        ∫ X, trialSourceOuterWeight j i X * trialMarginal i (i.removeNth X) ^ 2
          ∂trialProductMeasure 39 := by
  have hR := (integrable_finsetSum (Finset.univ : Finset (Fin 39))
    (fun i _ => integrable_trialSourceOuterFace j i)).const_mul ((trialRhoStar : ℝ) ^ 2)
  calc
    _ ≤ ∫ X, (trialRhoStar : ℝ) ^ 2 * ∑ i : Fin 39,
        trialSourceOuterWeight j i X * trialMarginal i (i.removeNth X) ^ 2
          ∂trialProductMeasure 39 := integral_mono
      (integrable_trialOuterPartition_square j _ measurable_trialCapPullback bounded_trialCapPullback)
      hR (trialOuterPartition_pullback_pointwise j)
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => integrable_trialSourceOuterFace j i)]

theorem trialOuterPartitionA_le (h : PhysicalSourceBounds182) (j : Fin 60) :
    trialOuterPartitionA j ≤ ((trialOuterCertificates j).normalizedA : ℝ) := by
  have hE := trialRootEnergy_pos h.cap
  calc
    _ ≤ (∫ X, trialSourceKernel (trialOuterCertificates j).cover X * trialStepFunction X ^ 2
        ∂trialProductMeasure 39) / trialRootEnergy :=
      div_le_div_of_nonneg_right (trialOuterPartition_root_le_kernel j) hE.le
    _ = trialSourceOuterRoot j / (39 * trialSquareIntegral) := by
      unfold trialSourceOuterRoot trialSquareIntegral
      change _ / trialRootEnergy = (39 * _ / trialPhysicalNormalizer) /
        (39 * (trialRootEnergy / trialPhysicalNormalizer))
      field_simp [trialPhysicalNormalizer_pos.ne', hE.ne']
    _ ≤ _ := trialSourceOuterRoot_normalized h j

theorem trialOuterPartitionM_le (h : PhysicalSourceBounds182) (j : Fin 60) :
    trialOuterPartitionM j ≤ ((trialOuterCertificates j).normalizedM : ℝ) := by
  have hE := trialRootEnergy_pos h.cap
  calc
    _ ≤ ((trialRhoStar : ℝ) ^ 2 * ∑ i : Fin 39,
        ∫ X, trialSourceOuterWeight j i X * trialMarginal i (i.removeNth X) ^ 2
          ∂trialProductMeasure 39) / trialRootEnergy :=
      div_le_div_of_nonneg_right (trialOuterPartition_pullback_integral_le j) hE.le
    _ = (trialRhoStar : ℝ) ^ 2 * trialSourceOuterFace j / trialSquareIntegral := by
      unfold trialSourceOuterFace trialSquareIntegral
      change (_ * _) / trialRootEnergy = (_ * (_ / trialPhysicalNormalizer)) /
        (trialRootEnergy / trialPhysicalNormalizer)
      field_simp [trialPhysicalNormalizer_pos.ne', hE.ne']
    _ ≤ _ := trialSourceOuterFace_normalized h j

#print axioms trialOuterPartition_pullback_pointwise
#print axioms trialOuterPartition_pullback_integral_le
#print axioms trialOuterPartitionA_le
#print axioms trialOuterPartitionM_le

end PrimeGap182
