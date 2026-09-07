import SourceSmooth182

/-! Actual-law source support and cap transfer for the smooth profiles.
Band certificate hypotheses hold almost surely under the constructed
fragment laws; they are not assumptions on the final smooth profiles. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Topology

namespace PrimeGap182
namespace TrialSmoothProfiles182

theorem measurable_root (P : TrialSmoothProfiles182) : Measurable P.rootPhysical :=
  P.F_smooth.continuous.measurable.comp (measurable_pi_lambda _ fun i =>
    (PrimeGap186.measurable_fragmentBandMasses P.a).comp (measurable_pi_apply i))

theorem measurable_face (P : TrialSmoothProfiles182) (b : Fin 3) : Measurable (P.facePhysical b) :=
  (P.H_smooth b).continuous.measurable.comp (measurable_pi_lambda _ fun i =>
    (PrimeGap186.measurable_fragmentBandMasses P.a).comp (measurable_pi_apply i))

theorem root_memLp (P : TrialSmoothProfiles182) : MemLp P.rootPhysical 2 (trialProductMeasure 39) := by
  let : IsFiniteMeasure trialPhysicalMeasure := trialPhysicalMeasure_finite
  let B (X : Fin 39 → FiniteMeasure ℝ) := fun i => PrimeGap186.fragmentBandMasses P.a (X i)
  have hB : Measurable B := measurable_pi_lambda _ fun i =>
    (PrimeGap186.measurable_fragmentBandMasses P.a).comp (measurable_pi_apply i)
  have hF : MemLp P.F 2 (Measure.map B (trialProductMeasure 39)) :=
    P.F_smooth.continuous.memLp_of_hasCompactSupport P.F_compact
  exact hF.comp_of_map hB.aemeasurable

theorem root_source_ae (P : TrialSmoothProfiles182) :
    ∀ᵐ X ∂trialAmbientProduct PrimeGap182Analytic.selbergFragmentCap182 39,
      P.rootPhysical X ≠ 0 →
        TrialRowsAllowed trialApproxOuterRows [] X ∧ TrialCapAllowed trialLargestCap X ∧
          trialTotalMass X < (trialRadius : ℝ) := by
  have hs := PrimeGap186.trial_cap_law_ae_band_structure
    PrimeGap182Analytic.selbergFragmentCap182 39 P.a
  filter_upwards [hs] with X hX hF
  have hu := P.F_support (subset_closure hF)
  have hv := trialBandSourceDomain_sound trialApproxOuterRows [] trialApproxRows_seed.1
    (by simp) (trialRadius : ℝ) P.a P.strictMono P.zero P.seed X
    (by simpa only [P.zero, P.last] using hX.2.1) hX.2.2 hu
  exact ⟨hv.1, hv.2.1, hv.2.2.1⟩

theorem face_source_ae (P : TrialSmoothProfiles182) (b : Fin 3) :
    ∀ᵐ X ∂trialAmbientProduct PrimeGap182Analytic.selbergFragmentCap182 38,
      P.facePhysical b X ≠ 0 →
        TrialRowsAllowed (trialApproxFaceOuterRows b) (trialApproxFaceInnerRows b) X ∧
          TrialCapAllowed trialLargestCap X ∧ trialTotalMass X < (trialApproxFaceRadius b : ℝ) := by
  have hs := PrimeGap186.trial_cap_law_ae_band_structure
    PrimeGap182Analytic.selbergFragmentCap182 38 P.a
  filter_upwards [hs] with X hX hH
  have hu := P.H_support b (subset_closure hH)
  have hv := trialBandSourceDomain_sound (trialApproxFaceOuterRows b) (trialApproxFaceInnerRows b)
    (trialApproxRows_seed.2.1 b) (trialApproxRows_seed.2.2 b) (trialApproxFaceRadius b : ℝ)
    P.a P.strictMono P.zero P.seed X
    (by simpa only [P.zero, P.last] using hX.2.1) hX.2.2 hu
  exact ⟨hv.1, hv.2.1, hv.2.2.1⟩

theorem root_support_ae_trial (P : TrialSmoothProfiles182) :
    ∀ᵐ X ∂trialProductMeasure 39,
      (trialRadius : ℝ) < ∑ i : Fin 39, ((X i).mass : ℝ) → P.rootPhysical X = 0 := by
  have hle : trialProductMeasure 39 ≤
      trialAmbientProduct PrimeGap182Analytic.selbergFragmentCap182 39 := by
    rw [← (trialAmbient_pi_cap_restrict _ trial_coefficient_cap_gap.2.le 39).2]
    exact Measure.restrict_le_self
  filter_upwards [ae_mono hle P.root_source_ae] with X hX hrad
  by_contra hn
  exact not_lt_of_ge (hX hn).2.2.le hrad

theorem root_square_transfer (P : TrialSmoothProfiles182) :
    (∫ X, P.rootPhysical X ^ 2 ∂trialAmbientProduct PrimeGap182Analytic.selbergFragmentCap182 39) =
      ∫ X, P.rootPhysical X ^ 2 ∂trialProductMeasure 39 := by
  apply trialAmbient_integral_eq _ trial_coefficient_cap_gap.2.le 39
  filter_upwards [P.root_source_ae] with X hX hpow
  exact (hX (fun hz => hpow (by simp only [hz, zero_pow (by decide : 2 ≠ 0)]))).2.1

theorem root_face_transfer (P : TrialSmoothProfiles182)
    (w : (Fin 38 → FiniteMeasure ℝ) → ℝ) (i : Fin 39) :
    (∫ Y, w Y * (∫ Z : FiniteMeasure ℝ,
        P.rootPhysical (i.insertNth Z Y)
          ∂trialAmbientMeasure PrimeGap182Analytic.selbergFragmentCap182) ^ 2
        ∂trialAmbientProduct PrimeGap182Analytic.selbergFragmentCap182 38) =
      ∫ Y, w Y * trialErasure P.rootPhysical i Y ^ 2 ∂trialProductMeasure 38 := by
  have hcap : ∀ᵐ X ∂trialAmbientProduct PrimeGap182Analytic.selbergFragmentCap182 39,
      P.rootPhysical X ≠ 0 → TrialCapAllowed trialLargestCap X :=
    P.root_source_ae.mono fun _ h hX => (h hX).2.1
  simpa only [Fin.forall_fin_one, trialErasure] using
    trialAmbient_fiber_function_integral_eq PrimeGap182Analytic.selbergFragmentCap182
      trial_coefficient_cap_gap.2.le 38 1 i (fun _ : Fin 1 => P.rootPhysical)
      (fun Y z => w Y * z 0 ^ 2) (by intro Y; simp) (fun _ => hcap)

#print axioms root_source_ae
#print axioms face_source_ae
#print axioms root_face_transfer

end TrialSmoothProfiles182
end PrimeGap182
