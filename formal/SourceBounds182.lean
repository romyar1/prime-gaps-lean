import SourceKernels182

/-! The 262 finite numerical premises, stated for actual fragment-law integrals.

The 120 outer and 137 inner source bounds below are inequalities, not axioms.
The five cap inequalities are exactly `PhysicalCapBounds182`. The source
root includes its recorded factor 39. The outer face already sums over all
coordinates and includes the full-configuration local count multiplier.
No further factor 39 is inserted when normalizing that face bound.

The source expectations are proved integrable. These finite premises do
not assert a source-event cover, an L² restoration theorem, or DHL[39,2].
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

def trialSourceOuterWeight (j : Fin 60) (i : Fin 39)
    (X : Fin 39 → FiniteMeasure ℝ) : ℝ :=
  trialSourceKernel (trialOuterCertificates j).cover X * trialSourceCountMultiplier j X *
    trialSourceFaceWeight (i.removeNth X)

def trialSourceInnerRole (j : Fin 137) : Fin 5 :=
  if (trialInnerCertificates j).cover.family.val < 4 then 1
  else if (trialInnerCertificates j).cover.family.val < 6 then 2 else 3

def trialSourceInnerWeight (j : Fin 137) (Y : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  trialMask (trialSourceInnerRole j) Y * trialSourceKernel (trialInnerCertificates j).cover Y

def trialSourceOuterRoot (j : Fin 60) : ℝ :=
  39 * (∫ X, trialSourceKernel (trialOuterCertificates j).cover X * trialStepFunction X ^ 2
    ∂trialProductMeasure 39) / trialPhysicalNormalizer

def trialSourceOuterFace (j : Fin 60) : ℝ :=
  (∑ i : Fin 39, ∫ X, trialSourceOuterWeight j i X * trialMarginal i (i.removeNth X) ^ 2
    ∂trialProductMeasure 39) / trialPhysicalNormalizer

def trialSourceInnerMass (j : Fin 137) : ℝ :=
  (∑ i : Fin 39, ∫ Y, trialSourceInnerWeight j Y * trialMarginal i Y ^ 2
    ∂trialProductMeasure 38) / trialPhysicalNormalizer

theorem trialSourceOuterWeight_regular (j : Fin 60) (i : Fin 39) :
    Measurable (trialSourceOuterWeight j i) ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ X, 0 ≤ trialSourceOuterWeight j i X ∧ trialSourceOuterWeight j i X ≤ B := by
  obtain ⟨hK, B, hB, hb⟩ := trialSourceKernel_regular _ (trialOuterCover_regular j) 39
  constructor
  · change Measurable (fun X : Fin 39 → FiniteMeasure ℝ =>
      trialSourceKernel (trialOuterCertificates j).cover X * trialSourceCountMultiplier j X *
        trialSourceFaceWeight (fun k : Fin 38 => X (i.succAbove k)))
    apply Measurable.mul
    · exact hK.mul (measurable_trialSourceCountMultiplier j)
    · apply measurable_trialSourceFaceWeight.comp
      exact measurable_pi_lambda _ fun k => measurable_pi_apply (i.succAbove k)
  refine ⟨B * (39 * (trialOuterCertificates j).counts.length), by positivity, ?_⟩
  intro X
  obtain ⟨hk0, hkB⟩ := hb X
  obtain ⟨hc0, hcB⟩ := trialSourceCountMultiplier_bounds j X
  obtain ⟨hw0, hwB⟩ := trialSourceFaceWeight_bounds (i.removeNth X)
  exact ⟨mul_nonneg (mul_nonneg hk0 hc0) hw0,
    (mul_le_of_le_one_right (mul_nonneg hk0 hc0) hwB).trans
      (mul_le_mul hkB hcB hc0 hB)⟩

theorem trialSourceInnerWeight_regular (j : Fin 137) :
    Measurable (trialSourceInnerWeight j) ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ Y, 0 ≤ trialSourceInnerWeight j Y ∧ trialSourceInnerWeight j Y ≤ B := by
  obtain ⟨hK, B, hB, hb⟩ := trialSourceKernel_regular _ (trialInnerCover_regular j) 38
  refine ⟨(measurable_trialMask _).mul hK, B, hB, ?_⟩
  intro Y
  rcases trialMask_values (trialSourceInnerRole j) Y with h | h
  · simp only [trialSourceInnerWeight, h, zero_mul, le_refl, true_and]
    exact hB
  · simpa only [trialSourceInnerWeight, h, one_mul] using hb Y

theorem trial_integrable_bounded_weight_square {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (w f : α → ℝ)
    (hw : Measurable w) (hf : Measurable f) {B C : ℝ}
    (hB : ∀ x, ‖w x‖ ≤ B) (hC : ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun x => w x * f x ^ 2) μ := by
  apply Integrable.of_bound (hw.mul (hf.pow_const 2)).aestronglyMeasurable
    (|B| * |C| ^ 2)
  apply ae_of_all
  intro x
  change ‖w x * f x ^ 2‖ ≤ _
  rw [norm_mul, norm_pow]
  exact mul_le_mul ((hB x).trans (le_abs_self B))
    (pow_le_pow_left₀ (norm_nonneg _) ((hC x).trans (le_abs_self C)) 2)
    (pow_nonneg (norm_nonneg _) 2) (abs_nonneg _)

theorem integrable_trialSourceOuterRoot (j : Fin 60) :
    Integrable (fun X => trialSourceKernel (trialOuterCertificates j).cover X *
      trialStepFunction X ^ 2) (trialProductMeasure 39) := by
  obtain ⟨hK, B, _, hb⟩ := trialSourceKernel_regular _ (trialOuterCover_regular j) 39
  obtain ⟨C, _, hC⟩ := trialStepFunction_finite_range.isBounded.exists_pos_norm_le
  exact trial_integrable_bounded_weight_square _ _ _ hK measurable_trialStepFunction
    (fun X => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hb X).1] using (hb X).2)
    (fun X => hC _ ⟨X, rfl⟩)

theorem integrable_trialSourceOuterFace (j : Fin 60) (i : Fin 39) :
    Integrable (fun X => trialSourceOuterWeight j i X * trialMarginal i (i.removeNth X) ^ 2)
      (trialProductMeasure 39) := by
  obtain ⟨hw, B, _, hb⟩ := trialSourceOuterWeight_regular j i
  obtain ⟨C, hC⟩ := bounded_trialMarginal i
  have he : Measurable (fun X : Fin 39 → FiniteMeasure ℝ => i.removeNth X) :=
    measurable_pi_lambda _ fun k => measurable_pi_apply (i.succAbove k)
  exact trial_integrable_bounded_weight_square _ _ _ hw ((measurable_trialMarginal i).comp he)
    (fun X => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hb X).1] using (hb X).2)
    (fun X => hC (i.removeNth X))

theorem integrable_trialSourceInnerMass (j : Fin 137) (i : Fin 39) :
    Integrable (fun Y => trialSourceInnerWeight j Y * trialMarginal i Y ^ 2)
      (trialProductMeasure 38) := by
  obtain ⟨hw, B, _, hb⟩ := trialSourceInnerWeight_regular j
  obtain ⟨C, hC⟩ := bounded_trialMarginal i
  exact trial_integrable_bounded_weight_square _ _ _ hw (measurable_trialMarginal i)
    (fun Y => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hb Y).1] using (hb Y).2) hC

theorem trialSourceOuterRoot_nonneg (j : Fin 60) : 0 ≤ trialSourceOuterRoot j := by
  obtain ⟨_, B, _, hb⟩ := trialSourceKernel_regular _ (trialOuterCover_regular j) 39
  exact div_nonneg (mul_nonneg (by norm_num)
    (integral_nonneg fun X => mul_nonneg (hb X).1 (sq_nonneg _))) trialPhysicalNormalizer_pos.le

theorem trialSourceOuterFace_nonneg (j : Fin 60) : 0 ≤ trialSourceOuterFace j := by
  apply div_nonneg _ trialPhysicalNormalizer_pos.le
  apply Finset.sum_nonneg
  intro i _
  obtain ⟨_, B, _, hb⟩ := trialSourceOuterWeight_regular j i
  exact integral_nonneg fun X => mul_nonneg (hb X).1 (sq_nonneg _)

theorem trialSourceInnerMass_nonneg (j : Fin 137) : 0 ≤ trialSourceInnerMass j := by
  obtain ⟨_, B, _, hb⟩ := trialSourceInnerWeight_regular j
  exact div_nonneg (Finset.sum_nonneg fun i _ =>
    integral_nonneg fun Y => mul_nonneg (hb Y).1 (sq_nonneg _)) trialPhysicalNormalizer_pos.le

/-- Exactly 262 scalar inequalities on the literal trial; none is an axiom. -/
structure PhysicalSourceBounds182 : Prop where
  cap : PhysicalCapBounds182
  outerRoot : ∀ j : Fin 60, trialSourceOuterRoot j ≤ (trialOuterCertificates j).rootUpper
  outerFace : ∀ j : Fin 60, trialSourceOuterFace j ≤ (trialOuterCertificates j).faceUpper
  innerMass : ∀ j : Fin 137, trialSourceInnerMass j ≤ (trialInnerCertificates j).faceUpper

theorem trialSourceOuterRoot_normalized (h : PhysicalSourceBounds182) (j : Fin 60) :
    trialSourceOuterRoot j / (39 * trialSquareIntegral) ≤
      ((trialOuterCertificates j).normalizedA : ℝ) := by
  have hd : (0 : ℝ) < (trialDenominatorLower : ℝ) := by norm_num [trialDenominatorLower]
  have hU : (0 : ℝ) ≤ ((trialOuterCertificates j).rootUpper : ℝ) :=
    Rat.cast_nonneg.mpr (trialOuterData_normalization j).1
  have heq : ((trialOuterCertificates j).rootUpper : ℝ) =
      39 * (trialDenominatorLower : ℝ) * ((trialOuterCertificates j).normalizedA : ℝ) := by
    exact_mod_cast (trialOuterData_normalization j).2.2.2.1
  calc
    _ ≤ ((trialOuterCertificates j).rootUpper : ℝ) / (39 * trialSquareIntegral) :=
      div_le_div_of_nonneg_right (h.outerRoot j) (mul_nonneg (by norm_num) (trialSquareIntegral_pos h.cap).le)
    _ ≤ ((trialOuterCertificates j).rootUpper : ℝ) / (39 * (trialDenominatorLower : ℝ)) :=
      div_le_div_of_nonneg_left hU (mul_pos (by norm_num) hd)
        (mul_le_mul_of_nonneg_left h.cap.denominator_lower (by norm_num))
    _ = _ := by rw [heq]; field_simp

theorem trialSourceOuterFace_normalized (h : PhysicalSourceBounds182) (j : Fin 60) :
    (trialRhoStar : ℝ) ^ 2 * trialSourceOuterFace j / trialSquareIntegral ≤
      ((trialOuterCertificates j).normalizedM : ℝ) := by
  have hd : (0 : ℝ) < (trialDenominatorLower : ℝ) := by norm_num [trialDenominatorLower]
  have hU : (0 : ℝ) ≤ ((trialOuterCertificates j).faceUpper : ℝ) :=
    Rat.cast_nonneg.mpr (trialOuterData_normalization j).2.1
  have heq : (trialRhoStar : ℝ) ^ 2 * ((trialOuterCertificates j).faceUpper : ℝ) =
      (trialDenominatorLower : ℝ) * ((trialOuterCertificates j).normalizedM : ℝ) := by
    exact_mod_cast (trialOuterData_normalization j).2.2.2.2.1
  calc
    _ ≤ (trialRhoStar : ℝ) ^ 2 * ((trialOuterCertificates j).faceUpper : ℝ) /
        trialSquareIntegral := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (h.outerFace j) (sq_nonneg _)) (trialSquareIntegral_pos h.cap).le
    _ ≤ (trialRhoStar : ℝ) ^ 2 * ((trialOuterCertificates j).faceUpper : ℝ) /
        (trialDenominatorLower : ℝ) := div_le_div_of_nonneg_left
      (mul_nonneg (sq_nonneg _) hU) hd h.cap.denominator_lower
    _ = _ := by rw [heq]; field_simp

theorem trialSourceInnerMass_normalized (h : PhysicalSourceBounds182) (j : Fin 137) :
    (trialRhoStar : ℝ) * ((trialInnerCertificates j).coefficientUpper : ℝ) *
      trialSourceInnerMass j / trialSquareIntegral ≤
        ((trialInnerCertificates j).normalizedB : ℝ) := by
  have hd : (0 : ℝ) < (trialDenominatorLower : ℝ) := by norm_num [trialDenominatorLower]
  have hρ : (0 : ℝ) ≤ (trialRhoStar : ℝ) := by norm_num [trialRhoStar]
  have hU : (0 : ℝ) ≤ ((trialInnerCertificates j).faceUpper : ℝ) :=
    Rat.cast_nonneg.mpr (trialInnerData_normalization j).1
  have hcoef : (0 : ℝ) ≤ ((trialInnerCertificates j).coefficientUpper : ℝ) :=
    Rat.cast_nonneg.mpr (trialInnerData_normalization j).2.1
  have heq : (trialRhoStar : ℝ) * ((trialInnerCertificates j).coefficientUpper : ℝ) *
      ((trialInnerCertificates j).faceUpper : ℝ) =
        (trialDenominatorLower : ℝ) * ((trialInnerCertificates j).normalizedB : ℝ) := by
    exact_mod_cast (trialInnerData_normalization j).2.2
  calc
    _ ≤ (trialRhoStar : ℝ) * ((trialInnerCertificates j).coefficientUpper : ℝ) *
        ((trialInnerCertificates j).faceUpper : ℝ) / trialSquareIntegral :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (h.innerMass j)
        (mul_nonneg hρ hcoef)) (trialSquareIntegral_pos h.cap).le
    _ ≤ (trialRhoStar : ℝ) * ((trialInnerCertificates j).coefficientUpper : ℝ) *
        ((trialInnerCertificates j).faceUpper : ℝ) / (trialDenominatorLower : ℝ) :=
      div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg hρ hcoef) hU) hd h.cap.denominator_lower
    _ = _ := by rw [heq]; field_simp

def trialSourceInnerLoss : ℝ :=
  ∑ j : Fin 137, (trialRhoStar : ℝ) * ((trialInnerCertificates j).coefficientUpper : ℝ) *
    trialSourceInnerMass j / trialSquareIntegral

theorem trialSourceInnerLoss_le (h : PhysicalSourceBounds182) :
    trialSourceInnerLoss ≤ (trialSourceInnerTotalUpper : ℝ) := by
  calc
    _ ≤ ∑ j : Fin 137, ((trialInnerCertificates j).normalizedB : ℝ) :=
      Finset.sum_le_sum fun j _ => trialSourceInnerMass_normalized h j
    _ = _ := by exact_mod_cast trialInnerData_total

#print axioms integrable_trialSourceOuterRoot
#print axioms integrable_trialSourceOuterFace
#print axioms integrable_trialSourceInnerMass
#print axioms trialSourceOuterRoot_normalized
#print axioms trialSourceOuterFace_normalized
#print axioms trialSourceInnerMass_normalized
#print axioms trialSourceInnerLoss_le

end PrimeGap182
