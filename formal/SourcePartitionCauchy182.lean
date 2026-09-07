import PhysicalBilinear182

/-! Weighted Cauchy--Schwarz for the actual soft source partition.  The
recorded square-root bounds apply to the actual signed cap pullback. -/

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace PrimeGap182

theorem trial_weighted_cauchy {d : ℕ}
    (q f g : (Fin d → FiniteMeasure ℝ) → ℝ)
    (hq : Measurable q) (hf : Measurable f) (hg : Measurable g)
    (hq0 : ∀ X, 0 ≤ q X)
    (hff : Integrable (fun X => q X * f X ^ 2) (trialProductMeasure d))
    (hgg : Integrable (fun X => q X * g X ^ 2) (trialProductMeasure d)) :
    (∫ X, q X * f X * g X ∂trialProductMeasure d) ^ 2 ≤
      (∫ X, q X * f X ^ 2 ∂trialProductMeasure d) *
        ∫ X, q X * g X ^ 2 ∂trialProductMeasure d := by
  let u := fun X => Real.sqrt (q X) * f X
  let v := fun X => Real.sqrt (q X) * g X
  have hu : MemLp u 2 (trialProductMeasure d) := by
    apply (memLp_two_iff_integrable_sq (hq.sqrt.mul hf).aestronglyMeasurable).mpr
    apply hff.congr
    filter_upwards [] with X
    change q X * f X ^ 2 = (Real.sqrt (q X) * f X) ^ 2
    rw [mul_pow, Real.sq_sqrt (hq0 X)]
  have hv : MemLp v 2 (trialProductMeasure d) := by
    apply (memLp_two_iff_integrable_sq (hq.sqrt.mul hg).aestronglyMeasurable).mpr
    apply hgg.congr
    filter_upwards [] with X
    change q X * g X ^ 2 = (Real.sqrt (q X) * g X) ^ 2
    rw [mul_pow, Real.sq_sqrt (hq0 X)]
  have huu : ⟪hu.toLp u, hu.toLp u⟫_ℝ =
      ∫ X, q X * f X ^ 2 ∂trialProductMeasure d := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp] with X hX
    rw [hX, Real.inner_apply]
    change (Real.sqrt (q X) * f X) * (Real.sqrt (q X) * f X) = _
    calc
      _ = Real.sqrt (q X) ^ 2 * f X ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (hq0 X)]
  have hvv : ⟪hv.toLp v, hv.toLp v⟫_ℝ =
      ∫ X, q X * g X ^ 2 ∂trialProductMeasure d := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv.coeFn_toLp] with X hX
    rw [hX, Real.inner_apply]
    change (Real.sqrt (q X) * g X) * (Real.sqrt (q X) * g X) = _
    calc
      _ = Real.sqrt (q X) ^ 2 * g X ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (hq0 X)]
  have huv : ⟪hu.toLp u, hv.toLp v⟫_ℝ =
      ∫ X, q X * f X * g X ∂trialProductMeasure d := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with X hX hY
    rw [hX, hY, Real.inner_apply]
    change (Real.sqrt (q X) * f X) * (Real.sqrt (q X) * g X) = _
    calc
      _ = Real.sqrt (q X) ^ 2 * f X * g X := by ring
      _ = _ := by rw [Real.sq_sqrt (hq0 X)]
  have h := real_inner_mul_inner_self_le (hu.toLp u) (hv.toLp v)
  rw [huu, hvv, huv, ← pow_two] at h
  exact h

theorem trialOuterPartition_cross_le (h : PhysicalSourceBounds182) (j : Fin 60) :
    (∫ X, trialOuterPartition j X * trialStepFunction X * trialCapPullback X
      ∂trialProductMeasure 39) ≤ trialRootEnergy * ((trialOuterCertificates j).sqrtUpper : ℝ) := by
  have hE := trialRootEnergy_pos h.cap
  have hc := trial_weighted_cauchy (trialOuterPartition j) trialStepFunction trialCapPullback
    (measurable_trialOuterPartition j) measurable_trialStepFunction measurable_trialCapPullback
    (fun X => (trialOuterPartition_bounds j X).1)
    (integrable_trialOuterPartition_square j _ measurable_trialStepFunction bounded_trialStepFunction)
    (integrable_trialOuterPartition_square j _ measurable_trialCapPullback bounded_trialCapPullback)
  have ha := (div_le_iff₀ hE).mp (trialOuterPartitionA_le h j)
  have hm := (div_le_iff₀ hE).mp (trialOuterPartitionM_le h j)
  have ha0 : 0 ≤ ∫ X, trialOuterPartition j X * trialStepFunction X ^ 2
      ∂trialProductMeasure 39 := integral_nonneg fun X =>
    mul_nonneg (trialOuterPartition_bounds j X).1 (sq_nonneg _)
  have hm0 : 0 ≤ ∫ X, trialOuterPartition j X * trialCapPullback X ^ 2
      ∂trialProductMeasure 39 := integral_nonneg fun X =>
    mul_nonneg (trialOuterPartition_bounds j X).1 (sq_nonneg _)
  have hAa : 0 ≤ ((trialOuterCertificates j).normalizedA : ℝ) := by nlinarith
  have hN := trialOuterData_normalization j
  have hs : 0 ≤ ((trialOuterCertificates j).sqrtUpper : ℝ) := Rat.cast_nonneg.mpr hN.2.2.1
  have hsm : ((trialOuterCertificates j).normalizedA : ℝ) *
      ((trialOuterCertificates j).normalizedM : ℝ) ≤ ((trialOuterCertificates j).sqrtUpper : ℝ) ^ 2 := by
    exact_mod_cast hN.2.2.2.2.2
  have hproduct := mul_le_mul ha hm hm0 (mul_nonneg hAa hE.le)
  have hscale := mul_le_mul_of_nonneg_left hsm (sq_nonneg trialRootEnergy)
  have hr : 0 ≤ trialRootEnergy * ((trialOuterCertificates j).sqrtUpper : ℝ) := mul_nonneg hE.le hs
  nlinarith only [hc, hproduct, hscale, hr]

theorem integrable_trialOuterPartition_cross (j : Fin 60) :
    Integrable (fun X => trialOuterPartition j X * trialStepFunction X * trialCapPullback X)
      (trialProductMeasure 39) :=
  trial_integrable_bounded_product ((measurable_trialOuterPartition j).mul measurable_trialStepFunction)
    measurable_trialCapPullback
    (trial_bounded_mul ⟨1, fun X => by
      rw [Real.norm_of_nonneg (trialOuterPartition_bounds j X).1]
      exact (trialOuterPartition_bounds j X).2.2⟩ bounded_trialStepFunction)
    bounded_trialCapPullback

theorem trialResidual_cap_cross_le (h : PhysicalSourceBounds182) :
    trialFacePair trialCapFaceMultiplier trialResidual trialStepFunction ≤
      trialRootEnergy * ∑ j : Fin 60, ((trialOuterCertificates j).sqrtUpper : ℝ) := by
  rw [← trialCapPullback_adjoint trial_regular_residual]
  calc
    _ = ∫ X, ∑ j : Fin 60,
        trialOuterPartition j X * trialStepFunction X * trialCapPullback X ∂trialProductMeasure 39 := by
      apply integral_congr_ae
      filter_upwards [trialOuterPartition_residual_ae] with X hX
      rw [← Finset.sum_mul, hX.1]
      rfl
    _ = ∑ j : Fin 60, ∫ X,
        trialOuterPartition j X * trialStepFunction X * trialCapPullback X ∂trialProductMeasure 39 :=
      integral_finsetSum _ fun j _ => integrable_trialOuterPartition_cross j
    _ ≤ ∑ j : Fin 60, trialRootEnergy * ((trialOuterCertificates j).sqrtUpper : ℝ) :=
      Finset.sum_le_sum fun j _ => trialOuterPartition_cross_le h j
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem trialResidual_energy_le (h : PhysicalSourceBounds182) :
    trialRootPair trialResidual trialResidual ≤
      trialRootEnergy * ∑ j : Fin 60, ((trialOuterCertificates j).normalizedA : ℝ) := by
  have hE := trialRootEnergy_pos h.cap
  calc
    _ = ∫ X, ∑ j : Fin 60, trialOuterPartition j X * trialStepFunction X ^ 2
        ∂trialProductMeasure 39 := by
      apply integral_congr_ae
      filter_upwards [trialOuterPartition_residual_ae] with X hX
      rw [hX.2]
      simp only [trialResidual, pow_two]
    _ = ∑ j : Fin 60, ∫ X, trialOuterPartition j X * trialStepFunction X ^ 2
        ∂trialProductMeasure 39 :=
      integral_finsetSum _ fun j _ => integrable_trialOuterPartition_square j _
        measurable_trialStepFunction bounded_trialStepFunction
    _ ≤ ∑ j : Fin 60, ((trialOuterCertificates j).normalizedA : ℝ) * trialRootEnergy :=
      Finset.sum_le_sum fun j _ => (div_le_iff₀ hE).mp (trialOuterPartitionA_le h j)
    _ = _ := by rw [← Finset.sum_mul]; ring

#print axioms trial_weighted_cauchy
#print axioms trialOuterPartition_cross_le
#print axioms trialResidual_cap_cross_le
#print axioms trialResidual_energy_le

end PrimeGap182
