import SourceBandSpecialization182

/-! Smooth finite-band profiles approximating the literal restored trial
and all three source masks.  Supports retain every actual source row, the
appropriate total radius, the atom cap, and exact radial cell support. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff

namespace PrimeGap182

structure TrialSmoothProfiles182 where
  m : ℕ
  a : Fin (m + 2) → ℝ
  F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ
  H : Fin 3 → (Fin 38 → Fin (m + 1) → ℝ) → ℝ
  strictMono : StrictMono a
  zero : a 0 = 0
  seed : a (0 : Fin (m + 1)).succ = (trialMesh : ℝ)
  last : a (Fin.last (m + 1)) = PrimeGap182Analytic.selbergFragmentCap182
  F_smooth : ContDiff ℝ ∞ F
  F_compact : HasCompactSupport F
  H_smooth : ∀ b, ContDiff ℝ ∞ (H b)
  H_compact : ∀ b, HasCompactSupport (H b)
  H_range : ∀ b v, 0 ≤ H b v ∧ H b v ≤ 1
  F_support : tsupport F ⊆ trialSourceBandDomain a
  H_support : ∀ b, tsupport (H b) ⊆ trialFaceBandDomain b a

namespace TrialSmoothProfiles182

def rootPhysical (P : TrialSmoothProfiles182) (X : Fin 39 → FiniteMeasure ℝ) : ℝ :=
  P.F (fun i => PrimeGap186.fragmentBandMasses P.a (X i))

def facePhysical (P : TrialSmoothProfiles182) (b : Fin 3) (Y : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  P.H b (fun i => PrimeGap186.fragmentBandMasses P.a (Y i))

theorem root_radial (P : TrialSmoothProfiles182)
    (v : Fin 39 → Fin (P.m + 1) → ℝ) (hv : P.F v ≠ 0) (i : Fin 39) :
    PrimeGap182Analytic.bandFaceCellSum182 (i.removeNth v) < trialCellCount :=
  trialBandCellInterior_removeNth v (P.F_support (subset_closure hv)).2.2.2.1 i

theorem face_radial (P : TrialSmoothProfiles182) (b : Fin 3)
    (v : Fin 38 → Fin (P.m + 1) → ℝ) (hv : P.H b v ≠ 0) :
    PrimeGap182Analytic.bandFaceCellSum182 v < trialCellCount :=
  trialBandCellInterior_face v (P.H_support b (subset_closure hv)).2.2.2.1

theorem product_smooth_compact (P : TrialSmoothProfiles182) (b : Fin 3) (i : Fin 39) :
    ContDiff ℝ ∞ (fun v => P.H b (i.removeNth v) * P.F v) ∧
      HasCompactSupport (fun v => P.H b (i.removeNth v) * P.F v) := by
  constructor
  · apply ContDiff.mul _ P.F_smooth
    apply (P.H_smooth b).comp
    change ContDiff ℝ ∞ (fun v : Fin 39 → Fin (P.m + 1) → ℝ =>
      fun j : Fin 38 => v (i.succAbove j))
    fun_prop
  · exact P.F_compact.mul_left

end TrialSmoothProfiles182

theorem trial_source_supported_smooth_profiles_approx182 (ε : ℝ) (hε : 0 < ε) :
    ∃ P : TrialSmoothProfiles182,
      MemLp P.rootPhysical 2 (trialProductMeasure 39) ∧
      (∫ X, (P.rootPhysical X - trialSourceStepFunction X) ^ 2 ∂trialProductMeasure 39) < ε ∧
      ∀ b : Fin 3,
        (∫ Y, (P.facePhysical b Y - trialApproxFaceActual b Y) ^ 2 ∂trialProductMeasure 38) < ε := by
  classical
  let : IsFiniteMeasure trialPhysicalMeasure := trialPhysicalMeasure_finite
  let κ := PrimeGap182Analytic.selbergFragmentCap182
  have hδκ : (trialMesh : ℝ) < κ := by
    norm_num [κ, PrimeGap182Analytic.selbergFragmentCap182, PrimeGap182Analytic.selbergRho182,
      trialMesh, trialRadius, trialIntervals]
  have hlargeκ : (trialLargestCap : ℝ) ≤ κ := by
    norm_num [κ, PrimeGap182Analytic.selbergFragmentCap182, PrimeGap182Analytic.selbergRho182,
      trialLargestCap]
  obtain ⟨m, a, hgeom, hmesh⟩ := PrimeGap186.trial_fine_band_sequence (trialMesh : ℝ) κ
    trial_seed_cap.1 hδκ
  let B39 (N : ℕ) (X : Fin 39 → FiniteMeasure ℝ) :=
    fun i => PrimeGap186.fragmentBandMasses (a N) (X i)
  let B38 (N : ℕ) (Y : Fin 38 → FiniteMeasure ℝ) :=
    fun i => PrimeGap186.fragmentBandMasses (a N) (Y i)
  let f (N : ℕ) := (trialSourceBandDomain (a N)).indicator
    (fun v => trialStepFunction (fun i => PrimeGap186.trialBandRepresentative (a N) (v i)))
  let g (b : Fin 3) (N : ℕ) := (trialFaceBandReferenceSet b (a N)).indicator (fun _ => (1 : ℝ))
  have hquarter : 0 < ε / 4 := div_pos hε (by norm_num)
  have houter : ∀ᶠ N in atTop,
      (∫ X, (f N (B39 N X) - trialSourceStepFunction X) ^ 2 ∂trialProductMeasure 39) < ε / 4 :=
    (trial_actual_source_band_exhaustion182 κ hlargeκ m a hgeom hmesh).eventually (gt_mem_nhds hquarter)
  have hinner : ∀ᶠ N in atTop, ∀ b : Fin 3,
      (∫ Y, (g b N (B38 N Y) - trialApproxFaceActual b Y) ^ 2 ∂trialProductMeasure 38) < ε / 4 :=
    Filter.eventually_all.mpr fun b =>
      (trial_actual_face_band_exhaustion182 κ hlargeκ m a hgeom hmesh b).eventually
        (gt_mem_nhds hquarter)
  obtain ⟨N, houterN, hinnerN⟩ := (houter.and hinner).exists
  have hB39 : Measurable (B39 N) := measurable_pi_lambda _ fun i =>
    (PrimeGap186.measurable_fragmentBandMasses (a N)).comp (measurable_pi_apply i)
  have hB38 : Measurable (B38 N) := measurable_pi_lambda _ fun i =>
    (PrimeGap186.measurable_fragmentBandMasses (a N)).comp (measurable_pi_apply i)
  let ν39 := Measure.map (B39 N) (trialProductMeasure 39)
  let ν38 := Measure.map (B38 N) (trialProductMeasure 38)
  have hfm : Measurable (f N) :=
    (measurable_trialStepFunction.comp (measurable_pi_lambda _ fun i =>
      (PrimeGap186.trialBandRepresentative_measurable (a N)).comp (measurable_pi_apply i))).indicator
      (trialSourceBandDomain_open (a N)).measurableSet
  obtain ⟨C, hC⟩ := trial_regular_step.bounded
  have hC0 : 0 ≤ C := (norm_nonneg (trialStepFunction (fun _ => 0))).trans (hC _)
  have hfb (v : Fin 39 → Fin (m N + 1) → ℝ) : ‖f N v‖ ≤ C :=
    (norm_indicator_le_norm_self _ _).trans (hC _)
  have hf : MemLp (f N) 2 ν39 :=
    MemLp.of_bound hfm.aestronglyMeasurable C (Filter.Eventually.of_forall hfb)
  have hτ : 0 < min (1 : ℝ) (ε / 8) := lt_min zero_lt_one (div_pos hε (by norm_num))
  obtain ⟨F, hFsmooth, hFcompact, hFsupport, hFerror⟩ :=
    PrimeGap186.trial_bounded_open_support_smooth_density hf hC0 hfb
      (trialSourceBandDomain_open (a N)) Set.support_indicator_subset hτ
  have hHchoice (b : Fin 3) :
      ∃ H : (Fin 38 → Fin (m N + 1) → ℝ) → ℝ,
        ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ trialFaceBandDomain b (a N) ∧
          (∀ v, 0 ≤ H v ∧ H v ≤ 1) ∧
          eLpNorm (g b N - H) 2 ν38 ≤ ENNReal.ofReal (min 1 (ε / 8)) :=
    PrimeGap186.trial_smooth_unit_cutoff_density (μ := ν38)
      (trialFaceBandReferenceSet_measurable b (a N)) (trialFaceBandDomain_open b (a N))
      (fun _ h => h.1) hτ
  choose H hHsmooth hHcompact hHsupport hHrange hHerror using hHchoice
  have hFmem : MemLp F 2 ν39 := hFsmooth.continuous.memLp_of_hasCompactSupport hFcompact
  have hHmem (b : Fin 3) : MemLp (H b) 2 ν38 :=
    (hHsmooth b).continuous.memLp_of_hasCompactSupport (hHcompact b)
  have hgmem (b : Fin 3) : MemLp (g b N) 2 ν38 :=
    (memLp_const (1 : ℝ)).indicator (trialFaceBandReferenceSet_measurable b (a N))
  have hMmem (b : Fin 3) : MemLp (trialApproxFaceActual b) 2 (trialProductMeasure 38) := by
    apply MemLp.of_bound (measurable_trialApproxFaceActual b).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun Y => by
      rcases trialApproxFaceActual_bits b Y with h | h <;> simp only [h, norm_zero, norm_one,
        zero_le_one, le_refl]
  let P : TrialSmoothProfiles182 :=
    ⟨m N, a N, F, H, (hgeom N).1, (hgeom N).2.1, (hgeom N).2.2.1, (hgeom N).2.2.2,
      hFsmooth, hFcompact, hHsmooth, hHcompact, hHrange, hFsupport, hHsupport⟩
  refine ⟨P, hFmem.comp_of_map hB39.aemeasurable, ?_, ?_⟩
  · exact PrimeGap186.trial_l2_band_dense_transfer (B39 N) hB39 (f N) F trialSourceStepFunction
      hf hFmem trialSourceStepFunction_memLp hε hFerror houterN
  · intro b
    exact PrimeGap186.trial_l2_band_dense_transfer (B38 N) hB38 (g b N) (H b) (trialApproxFaceActual b)
      (hgmem b) (hHmem b) (hMmem b) hε (hHerror b) (hinnerN b)

#print axioms trial_source_supported_smooth_profiles_approx182
#print axioms TrialSmoothProfiles182.root_radial
#print axioms TrialSmoothProfiles182.face_radial

end PrimeGap182
