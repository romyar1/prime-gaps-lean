import SourceQuadraticContinuity182
import SharpDeficitMargin182

/-! Positive smooth physical profiles for the slightly enlarged sharp
deficit bound. The only numerical input is the explicit 262-entry bundle
of actual finite integral bounds. Positivity is simultaneous in the true
deficit parameter, with exact transfer to the arithmetic coefficient law. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Topology

namespace PrimeGap182

theorem trialHybridCoefficient_actual_reference (κ : ℝ) (Y : Fin 38 → FiniteMeasure ℝ) :
    trialHybridCoefficient κ trialAdditionalSharpLoss (trialFaceKernel Y)
      (fun b => trialApproxFaceActual b Y) =
        trialActualFaceMultiplier Y - trialAdditionalSharpLoss * trialAddedFaceWeight Y := by
  change trialPhysicalHybridPolynomial κ (trialFaceKernel Y) 1
      (trialActualBaseMask Y) (trialActualSubtractionMask Y)
        (trialActualEnlargedMask Y - trialActualBaseMask Y) -
      trialAdditionalSharpLoss * (trialActualEnlargedMask Y - trialActualBaseMask Y) ^ 2 = _
  simpa only [trialPerturbedHybridPolynomial, mul_one, one_pow] using
    trialPerturbedHybridPolynomial_reference κ 1 Y

theorem trialPhysicalHybridEnergy_actual_reference (κ : ℝ) :
    trialPhysicalHybridEnergy κ trialAdditionalSharpLoss trialSourceStepFunction trialApproxFaceActual =
      trialPerturbedRestoredEnergy := by
  have hwb : ∃ B : ℝ, ∀ Y, ‖trialAddedFaceWeight Y‖ ≤ B := by
    refine ⟨1, fun Y => ?_⟩
    rw [Real.norm_of_nonneg (trialAddedFaceWeight_bounds Y).1]
    exact (trialAddedFaceWeight_bounds Y).2
  have hI (i : Fin 39) :
      (∫ Y, trialHybridCoefficient κ trialAdditionalSharpLoss (trialFaceKernel Y)
        (fun b => trialApproxFaceActual b Y) * trialErasure trialSourceStepFunction i Y ^ 2
          ∂trialProductMeasure 38) =
      (∫ Y, trialActualFaceMultiplier Y * trialErasure trialSourceStepFunction i Y *
        trialErasure trialSourceStepFunction i Y ∂trialProductMeasure 38) -
      trialAdditionalSharpLoss * (∫ Y, trialAddedFaceWeight Y *
        trialErasure trialSourceStepFunction i Y * trialErasure trialSourceStepFunction i Y
          ∂trialProductMeasure 38) := by
    have hW := integrable_trialFacePair_integrand measurable_trialActualFaceMultiplier
      trialActualFaceMultiplier_bounded trial_regular_source trial_regular_source i
    have hA := integrable_trialFacePair_integrand measurable_trialAddedFaceWeight hwb
      trial_regular_source trial_regular_source i
    calc
      _ = ∫ Y, (trialActualFaceMultiplier Y * trialErasure trialSourceStepFunction i Y *
          trialErasure trialSourceStepFunction i Y) - trialAdditionalSharpLoss *
            (trialAddedFaceWeight Y * trialErasure trialSourceStepFunction i Y *
              trialErasure trialSourceStepFunction i Y) ∂trialProductMeasure 38 := by
        apply integral_congr_ae
        exact ae_of_all _ fun Y => by
          dsimp only
          rw [trialHybridCoefficient_actual_reference]
          ring
      _ = _ := by rw [integral_sub hW (hA.const_mul _), integral_const_mul]
  unfold trialPhysicalHybridEnergy
  simp only [hI, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold trialPerturbedRestoredEnergy trialRestoredEnergy trialFacePair trialRootPair
  simp only [pow_two]
  ring

theorem physical_positive_smooth_profiles182 (h : PhysicalSourceBounds182) :
    ∃ P : TrialSmoothProfiles182, ∀ κ : ℝ, 0 ≤ κ → κ ≤ (trialConvexKappaBound : ℝ) →
      0 < trialPhysicalHybridEnergy κ trialAdditionalSharpLoss P.rootPhysical P.facePhysical := by
  have hpos := trialPerturbedRestoredEnergy_pos h
  obtain ⟨δ, hδ, hcont⟩ := trial_hybrid_energy_l2_continuous182
    (trialConvexKappaBound : ℝ) trialAdditionalSharpLoss (trialPerturbedRestoredEnergy / 2) (half_pos hpos)
  obtain ⟨P, hPmem, hPF, hPH⟩ := trial_source_supported_smooth_profiles_approx182 δ hδ
  refine ⟨P, fun κ hκ hκm => ?_⟩
  have hh := hcont κ hκ hκm P.rootPhysical P.facePhysical hPmem P.measurable_face
    (fun b Y => P.H_range b _) P.root_support_ae_trial hPF hPH
  rw [trialPhysicalHybridEnergy_actual_reference] at hh
  have hl := (abs_lt.mp hh).1
  linarith only [hl, hpos]

def trialCoefficientHybridEnergy (κ extra : ℝ) (P : TrialSmoothProfiles182) : ℝ :=
  (trialRhoStar : ℝ) * (∑ i : Fin 39, ∫ Y,
    trialHybridCoefficient κ extra (trialFaceKernel Y) (fun b => P.facePhysical b Y) *
      (∫ Z : FiniteMeasure ℝ, P.rootPhysical (i.insertNth Z Y)
        ∂trialAmbientMeasure PrimeGap182Analytic.selbergFragmentCap182) ^ 2
          ∂trialAmbientProduct PrimeGap182Analytic.selbergFragmentCap182 38) -
    ∫ X, P.rootPhysical X ^ 2 ∂trialAmbientProduct PrimeGap182Analytic.selbergFragmentCap182 39

theorem trialCoefficientHybridEnergy_transfer (κ extra : ℝ) (P : TrialSmoothProfiles182) :
    trialCoefficientHybridEnergy κ extra P =
      trialPhysicalHybridEnergy κ extra P.rootPhysical P.facePhysical := by
  unfold trialCoefficientHybridEnergy trialPhysicalHybridEnergy
  rw [P.root_square_transfer]
  congr 2
  exact Finset.sum_congr rfl (fun i _ => P.root_face_transfer _ i)

theorem physical_positive_smooth_coefficient_profiles182 (h : PhysicalSourceBounds182) :
    ∃ P : TrialSmoothProfiles182, ∀ κ : ℝ, 0 ≤ κ → κ ≤ (trialConvexKappaBound : ℝ) →
      0 < trialCoefficientHybridEnergy κ trialAdditionalSharpLoss P := by
  obtain ⟨P, hP⟩ := physical_positive_smooth_profiles182 h
  exact ⟨P, fun κ hκ hκm => by rw [trialCoefficientHybridEnergy_transfer]; exact hP κ hκ hκm⟩

theorem trialCoefficientHybridEnergy_eq_raw (κ : ℝ) (P : TrialSmoothProfiles182) :
    trialCoefficientHybridEnergy κ trialAdditionalSharpLoss P =
      (trialRhoStar : ℝ) * (∑ i : Fin 39, ∫ Y,
        let U := ∫ Z : FiniteMeasure ℝ, P.rootPhysical (i.insertNth Z Y)
          ∂trialAmbientMeasure PrimeGap182Analytic.selbergFragmentCap182
        trialPerturbedHybridPolynomial κ (trialFaceKernel Y) U
          (P.facePhysical 0 Y * U) (P.facePhysical 2 Y * U)
          ((P.facePhysical 1 Y - P.facePhysical 0 Y) * U)
        ∂trialAmbientProduct PrimeGap182Analytic.selbergFragmentCap182 38) -
        ∫ X, P.rootPhysical X ^ 2 ∂trialAmbientProduct PrimeGap182Analytic.selbergFragmentCap182 39 := by
  unfold trialCoefficientHybridEnergy
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  exact ae_of_all _ fun Y => (trialHybridCoefficient_factor κ trialAdditionalSharpLoss
    (trialFaceKernel Y) _ (fun b => P.facePhysical b Y)).symm

#print axioms trialPhysicalHybridEnergy_actual_reference
#print axioms physical_positive_smooth_profiles182
#print axioms physical_positive_smooth_coefficient_profiles182
#print axioms trialCoefficientHybridEnergy_eq_raw

end PrimeGap182
