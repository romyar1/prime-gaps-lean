import SourceBandBridge182

/-! Positive energy for the actual finite-band profiles, expressed in the
same marginal and masked faces used to sample the arithmetic arrays.
The only hypothesis at the positivity endpoint is the explicit finite
integral certificate bundle; no approximation or marginal identity is
assumed. -/

noncomputable section
open MeasureTheory Filter PrimeGap186 PrimeGap182Analytic
open scoped BigOperators Topology

namespace PrimeGap182
namespace TrialSmoothProfiles182

def bandHybridEnergy (P : TrialSmoothProfiles182) (κ : ℝ) : ℝ :=
  (trialRhoStar : ℝ) * (∑ i : Fin 39, ∫ Y,
    trialPerturbedHybridPolynomial κ (bandFaceKernel182 Y) (P.bandErasure i Y)
      (P.bandMaskedFace 0 i Y) (P.bandMaskedFace 2 i Y)
      (P.bandMaskedFace 1 i Y - P.bandMaskedFace 0 i Y)
      ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 P.a)) -
    ∫ X, P.F X ^ 2 ∂Measure.pi (fun _ : Fin 39 => selbergBandMeasure182 P.a)

theorem bandRootEnergy_pullback (P : TrialSmoothProfiles182) :
    (∫ X, P.F X ^ 2 ∂Measure.pi (fun _ : Fin 39 => selbergBandMeasure182 P.a)) =
      ∫ X, P.rootPhysical X ^ 2 ∂trialAmbientProduct selbergFragmentCap182 39 := by
  simpa only [selbergBandMeasure182, trialAmbientProduct, trialAmbientMeasure, rootPhysical] using
    PrimeGap182.Selberg.fragment_band_law_integral_pullback selbergFragmentCap182 P.a 39
      (fun X => P.F X ^ 2) (P.F_smooth.continuous.measurable.pow_const 2)

theorem bandKernel_pullback_ae (P : TrialSmoothProfiles182) :
    ∀ᵐ Y ∂trialAmbientProduct selbergFragmentCap182 38,
      bandFaceKernel182 (fun k => fragmentBandMasses P.a (Y k)) = trialFaceKernel Y := by
  have hc : ∀ᵐ c ∂selbergPhysicalMeasure182,
      c.restrict (Set.Ioc (0 : ℝ) selbergFragmentCap182) = c :=
    Measure.ae_smul_measure (ae_restrict_Ioc_fragmentLaw selbergFragmentCap182) _
  have hall : ∀ᵐ Y ∂trialAmbientProduct selbergFragmentCap182 38, ∀ k,
      (Y k).restrict (Set.Ioc (0 : ℝ) selbergFragmentCap182) = Y k :=
    eventually_all.mpr fun k => (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin 38 => selbergPhysicalMeasure182) (i := k)).eventually hc
  filter_upwards [hall] with Y hY
  apply bandFaceKernel182_pullback P.a P.strictMono.monotone Y
  simpa only [P.zero, P.last] using hY

theorem bandHybridFace_pullback (P : TrialSmoothProfiles182) (κ : ℝ) (i : Fin 39) :
    (∫ Y, trialPerturbedHybridPolynomial κ (bandFaceKernel182 Y) (P.bandErasure i Y)
      (P.bandMaskedFace 0 i Y) (P.bandMaskedFace 2 i Y)
      (P.bandMaskedFace 1 i Y - P.bandMaskedFace 0 i Y)
      ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 P.a)) =
    ∫ Y, trialPerturbedHybridPolynomial κ (trialFaceKernel Y) (P.coefficientErasure i Y)
      (P.facePhysical 0 Y * P.coefficientErasure i Y)
      (P.facePhysical 2 Y * P.coefficientErasure i Y)
      ((P.facePhysical 1 Y - P.facePhysical 0 Y) * P.coefficientErasure i Y)
      ∂trialAmbientProduct selbergFragmentCap182 38 := by
  let Ψ : (Fin 38 → Fin (P.m + 1) → ℝ) → (Fin 1 → ℝ) → ℝ := fun Y v =>
    trialPerturbedHybridPolynomial κ (bandFaceKernel182 Y) (v 0)
      (P.H 0 Y * v 0) (P.H 2 Y * v 0) ((P.H 1 Y - P.H 0 Y) * v 0)
  have hH (b : Fin 3) : Measurable (P.H b) := (P.H_smooth b).continuous.measurable
  have hK : Measurable (@bandFaceKernel182 P.m) := measurable_bandFaceKernel182
  have hΨ : Measurable (Function.uncurry Ψ) := by
    dsimp only [Function.uncurry, Ψ, trialPerturbedHybridPolynomial, trialPhysicalHybridPolynomial]
    fun_prop
  have hraw := PrimeGap182.Selberg.fragment_band_law_fiber_function_integral_pullback
    selbergFragmentCap182 P.a 38 1 i (fun _ => P.F)
    (fun _ => P.F_smooth.continuous.measurable) Ψ hΨ
  calc
    _ = ∫ Y, Ψ Y (fun _ : Fin 1 => P.bandErasure i Y)
        ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 P.a) := by
      apply integral_congr_ae
      exact ae_of_all _ fun Y => by
        dsimp only [Ψ, bandMaskedFace]
        congr 1
        ring
    _ = ∫ Y, Ψ (fun k => fragmentBandMasses P.a (Y k))
        (fun _ : Fin 1 => P.coefficientErasure i Y)
        ∂trialAmbientProduct selbergFragmentCap182 38 := by
      simpa only [bandErasure, coefficientErasure, rootPhysical,
        selbergBandMeasure182, selbergPhysicalMeasure182, trialAmbientProduct, trialAmbientMeasure]
        using hraw
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [P.bandKernel_pullback_ae] with Y hY
      dsimp only [Ψ, facePhysical]
      rw [hY]

theorem bandHybridEnergy_eq (P : TrialSmoothProfiles182) (κ : ℝ) :
    P.bandHybridEnergy κ = trialCoefficientHybridEnergy κ trialAdditionalSharpLoss P := by
  rw [trialCoefficientHybridEnergy_eq_raw]
  unfold bandHybridEnergy
  rw [P.bandRootEnergy_pullback]
  congr 2
  exact Finset.sum_congr rfl fun i _ => P.bandHybridFace_pullback κ i

#print axioms bandRootEnergy_pullback
#print axioms bandHybridFace_pullback
#print axioms bandHybridEnergy_eq

end TrialSmoothProfiles182

theorem physical_positive_admissible_band_profiles182 (h : PhysicalSourceBounds182) :
    ∃ P : TrialSmoothProfiles182, ∀ κ : ℝ, 0 ≤ κ → κ ≤ (trialConvexKappaBound : ℝ) →
      0 < P.bandHybridEnergy κ := by
  obtain ⟨P, hP⟩ := physical_positive_smooth_coefficient_profiles182 h
  exact ⟨P, fun κ hκ hκm => by rw [P.bandHybridEnergy_eq]; exact hP κ hκ hκm⟩

#print axioms physical_positive_admissible_band_profiles182

end PrimeGap182
