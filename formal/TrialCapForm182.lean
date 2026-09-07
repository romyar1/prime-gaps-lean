import PhysicalForms182

/-! Identification of the literal cap certificate with the actual cap face
quadratic form. The tail support mask is justified by the trial's inward cells. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

theorem trialShell_tail_of_insert (i : Fin 39) (Z : FiniteMeasure ℝ)
    (Y : Fin 38 → FiniteMeasure ℝ)
    (h : trialStepFunction (i.insertNth Z Y) ≠ 0) : TrialShellDomain 4 Y := by
  obtain ⟨hs, _, hc, _⟩ := trialStepFunction_support (i.insertNth Z Y) h
  obtain ⟨j, hj⟩ := hs
  have hr := hj.1
  have hsum : (∑ k : Fin 39, trialCellIndex ((i.insertNth Z Y : Fin 39 → FiniteMeasure ℝ) k)) =
      trialCellIndex Z + ∑ k : Fin 38, trialCellIndex (Y k) := by
    rw [Fin.sum_univ_succAbove _ i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  change (∑ k : Fin 39, trialCellIndex ((i.insertNth Z Y : Fin 39 → FiniteMeasure ℝ) k)) <
    trialCellCount at hr
  rw [hsum, trialCellCount_eq] at hr
  apply (trialShellDomain_grid_iff 4 Y).mpr
  refine ⟨⟨0, 393216, 246256⟩, by decide, ?_⟩
  change (∑ k, trialCellIndex (Y k)) < trialCellCount ∧
    0 < (∑ k, trialCellIndex (Y k)) + 38 ∧
    (∑ k, trialCellIndex (Y k)) + 38 ≤ 393216 ∧ TrialCapAllowed ((246256 : ℚ) * trialMesh) Y
  refine ⟨by rw [trialCellCount_eq]; omega, by omega, by omega, ?_⟩
  have heq : (246256 : ℚ) * trialMesh = trialLargestCap := by
    norm_num [trialMesh, trialRadius, trialIntervals, trialLargestCap]
  rw [heq]
  intro k
  simpa only [Fin.insertNth_apply_succAbove] using hc (i.succAbove k)

theorem trialMarginal_zero_outside_tail (i : Fin 39) (Y : Fin 38 → FiniteMeasure ℝ)
    (h : ¬ TrialShellDomain 4 Y) : trialMarginal i Y = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with Z
  by_contra hn
  exact h (trialShell_tail_of_insert i Z Y hn)

theorem trialCapFace_integrand (i : Fin 39) (Y : Fin 38 → FiniteMeasure ℝ) :
    trialCapFaceMultiplier Y * trialMarginal i Y ^ 2 =
      trialMask 1 Y * trialMarginal i Y ^ 2 + (1 - (trialLambda : ℝ)) *
        (trialMask 2 Y * (1 - trialMask 1 Y) * trialMarginal i Y ^ 2) -
          trialHybridLoss * (trialMask 4 Y * (1 - trialMask 3 Y) *
            trialFaceKernel Y * trialMarginal i Y ^ 2) := by
  by_cases hV : trialMarginal i Y = 0
  · simp only [hV, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero, sub_zero]
  have htail : trialMask 4 Y = 1 := by
    have hs : TrialShellDomain 4 Y := by
      by_contra hn
      exact hV (trialMarginal_zero_outside_tail i Y hn)
    simp only [trialMask, hs, ite_true]
  have hle := trialMask_base_le_enlarged Y
  unfold trialCapFaceMultiplier
  rw [htail]
  rcases trialMask_values 1 Y with h1 | h1 <;>
    rcases trialMask_values 2 Y with h2 | h2 <;> rw [h1, h2] at hle ⊢ <;>
      linarith only [hle]

theorem trialCapFace_sum_eq :
    (∑ i : Fin 39, ∫ Y, trialCapFaceMultiplier Y * trialMarginal i Y ^ 2
      ∂trialProductMeasure 38) =
      (∑ i : Fin 39, ∫ Y, trialMask 1 Y * trialMarginal i Y ^ 2 ∂trialProductMeasure 38) +
        (1 - (trialLambda : ℝ)) *
          (∑ i : Fin 39, ∫ Y, trialMask 2 Y * (1 - trialMask 1 Y) * trialMarginal i Y ^ 2
            ∂trialProductMeasure 38) -
        trialHybridLoss * (∑ i : Fin 39, ∫ Y, trialMask 4 Y * (1 - trialMask 3 Y) *
          trialFaceKernel Y * trialMarginal i Y ^ 2 ∂trialProductMeasure 38) := by
  have hI (i : Fin 39) :
      (∫ Y, trialCapFaceMultiplier Y * trialMarginal i Y ^ 2 ∂trialProductMeasure 38) =
        (∫ Y, trialMask 1 Y * trialMarginal i Y ^ 2 ∂trialProductMeasure 38) +
          (1 - (trialLambda : ℝ)) *
            (∫ Y, trialMask 2 Y * (1 - trialMask 1 Y) * trialMarginal i Y ^ 2
              ∂trialProductMeasure 38) -
          trialHybridLoss * (∫ Y, trialMask 4 Y * (1 - trialMask 3 Y) * trialFaceKernel Y *
            trialMarginal i Y ^ 2 ∂trialProductMeasure 38) := by
    simp_rw [trialCapFace_integrand]
    have hab : Integrable (fun Y => trialMask 1 Y * trialMarginal i Y ^ 2 +
        (1 - (trialLambda : ℝ)) *
          (trialMask 2 Y * (1 - trialMask 1 Y) * trialMarginal i Y ^ 2)) (trialProductMeasure 38) :=
      (integrable_trial_base_term i).add ((integrable_trial_enlargement_term i).const_mul _)
    rw [integral_sub hab ((integrable_trial_tail_term i).const_mul trialHybridLoss),
      integral_add (integrable_trial_base_term i)
        ((integrable_trial_enlargement_term i).const_mul _), integral_const_mul, integral_const_mul]
  simp_rw [hI]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

theorem trialCapForm_quotient (h : PhysicalCapBounds182) :
    trialFacePair trialCapFaceMultiplier trialStepFunction trialStepFunction / trialRootEnergy =
      trialCapQuotient := by
  have hE := trialRootEnergy_pos h
  have hN := trialPhysicalNormalizer_pos
  have hsum := trialCapFace_sum_eq
  unfold trialFacePair
  change ((trialRhoStar : ℝ) * ∑ i : Fin 39, ∫ Y,
    trialCapFaceMultiplier Y * trialMarginal i Y * trialMarginal i Y ∂trialProductMeasure 38) /
      trialRootEnergy = _
  simp only [mul_assoc, ← pow_two]
  rw [hsum]
  unfold trialCapQuotient trialBaseIntegral trialEnlargementIntegral trialTailIntegral
    trialFaceIntegral trialSquareIntegral
  change (_ * (_ + _ * _ - _ * _)) / trialRootEnergy =
    _ * (_ / trialPhysicalNormalizer + _ * (_ / trialPhysicalNormalizer) -
      _ * (_ / trialPhysicalNormalizer)) / (trialRootEnergy / trialPhysicalNormalizer)
  field_simp [hE.ne', hN.ne']

#print axioms trialMarginal_zero_outside_tail
#print axioms trialCapForm_quotient

end PrimeGap182
