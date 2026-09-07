import SourcePositive182
import PhysicalExceptionalMoment182

/-! The actual finite-band marginal and the three masked face profiles.
Continuity follows by dominated integration against the constructed band
law. The correction used by the arithmetic sieve is exactly the negative
C-masked marginal, with the prescribed source and radial support. -/

noncomputable section
open MeasureTheory Filter PrimeGap186 PrimeGap182Analytic
open scoped BigOperators Topology

namespace PrimeGap182
namespace TrialSmoothProfiles182

def bandErasure (P : TrialSmoothProfiles182) (i : Fin 39)
    (Y : Fin 38 → Fin (P.m + 1) → ℝ) : ℝ :=
  ∫ Z : Fin (P.m + 1) → ℝ, P.F (i.insertNth Z Y) ∂selbergBandMeasure182 P.a

def coefficientErasure (P : TrialSmoothProfiles182) (i : Fin 39)
    (Y : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  ∫ Z : FiniteMeasure ℝ, P.rootPhysical (i.insertNth Z Y) ∂selbergPhysicalMeasure182

def bandMaskedFace (P : TrialSmoothProfiles182) (b : Fin 3) (i : Fin 39)
    (Y : Fin 38 → Fin (P.m + 1) → ℝ) : ℝ := P.H b Y * P.bandErasure i Y

def exceptionalFace (P : TrialSmoothProfiles182) (i : Fin 39)
    (Y : Fin 38 → Fin (P.m + 1) → ℝ) : ℝ := -P.bandMaskedFace 2 i Y

theorem continuous_bandErasure (P : TrialSmoothProfiles182) (i : Fin 39) :
    Continuous (P.bandErasure i) := by
  obtain ⟨C, hC⟩ := P.F_compact.exists_bound_of_continuous P.F_smooth.continuous
  apply continuous_of_dominated (bound := fun _ => C)
  · intro Y
    exact (P.F_smooth.continuous.comp
      (continuous_id.finInsertNth i continuous_const)).aestronglyMeasurable
  · intro Y
    exact ae_of_all _ fun Z => hC (i.insertNth Z Y)
  · exact integrable_const C
  · exact ae_of_all _ fun Z => P.F_smooth.continuous.comp
      (continuous_const.finInsertNth i continuous_id)

theorem bounded_bandErasure (P : TrialSmoothProfiles182) (i : Fin 39) :
    Bornology.IsBounded (Set.range (P.bandErasure i)) := by
  obtain ⟨C, hC⟩ := P.F_compact.exists_bound_of_continuous P.F_smooth.continuous
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C * (selbergBandMeasure182 P.a).real Set.univ, ?_⟩
  rintro _ ⟨Y, rfl⟩
  exact norm_integral_le_of_norm_le_const (ae_of_all _ fun Z => hC (i.insertNth Z Y))

theorem continuous_bandMaskedFace (P : TrialSmoothProfiles182) (b : Fin 3) (i : Fin 39) :
    Continuous (P.bandMaskedFace b i) :=
  (P.H_smooth b).continuous.mul (P.continuous_bandErasure i)

theorem compact_bandMaskedFace (P : TrialSmoothProfiles182) (b : Fin 3) (i : Fin 39) :
    HasCompactSupport (P.bandMaskedFace b i) := (P.H_compact b).mul_right

theorem bandMaskedFace_source (P : TrialSmoothProfiles182) (b : Fin 3) (i : Fin 39)
    (Y : Fin 38 → Fin (P.m + 1) → ℝ) (hY : P.bandMaskedFace b i Y ≠ 0) :
    Y ∈ trialFaceBandDomain b P.a := by
  apply P.H_support b
  apply subset_closure
  intro hz
  exact hY (by simp only [bandMaskedFace, hz, zero_mul])

theorem continuous_exceptionalFace (P : TrialSmoothProfiles182) (i : Fin 39) :
    Continuous (P.exceptionalFace i) := (P.continuous_bandMaskedFace 2 i).neg

theorem compact_exceptionalFace (P : TrialSmoothProfiles182) (i : Fin 39) :
    HasCompactSupport (P.exceptionalFace i) := (P.compact_bandMaskedFace 2 i).neg

theorem bounded_exceptionalFace (P : TrialSmoothProfiles182) (i : Fin 39) :
    Bornology.IsBounded (Set.range (P.exceptionalFace i)) :=
  ((P.compact_exceptionalFace i).isCompact_range (P.continuous_exceptionalFace i)).isBounded

theorem exceptionalFace_radial (P : TrialSmoothProfiles182) (i : Fin 39)
    (Y : Fin 38 → Fin (P.m + 1) → ℝ) (hY : P.exceptionalFace i Y ≠ 0) :
    bandFaceCellSum182 Y < trialCellCount := by
  apply P.face_radial 2 Y
  intro hz
  exact hY (by simp only [exceptionalFace, bandMaskedFace, hz, zero_mul, neg_zero])

theorem bandErasure_pullback (P : TrialSmoothProfiles182) (i : Fin 39)
    (Y : Fin 38 → FiniteMeasure ℝ) :
    P.bandErasure i (fun k => fragmentBandMasses P.a (Y k)) = P.coefficientErasure i Y := by
  have hb := measurable_fragmentBandMasses P.a
  have hmap : Measure.map (fragmentBandMasses P.a) selbergPhysicalMeasure182 =
      selbergBandMeasure182 P.a := Measure.map_smul _ hb.aemeasurable
  have hslice : Measurable (fun Z : Fin (P.m + 1) → ℝ =>
      P.F (i.insertNth Z (fun k => fragmentBandMasses P.a (Y k)))) :=
    (P.F_smooth.continuous.comp (continuous_id.finInsertNth i continuous_const)).measurable
  calc
    _ = ∫ Z : FiniteMeasure ℝ, P.F (i.insertNth (fragmentBandMasses P.a Z)
        (fun k => fragmentBandMasses P.a (Y k))) ∂selbergPhysicalMeasure182 := by
      unfold bandErasure
      rw [← hmap]
      exact integral_map_of_stronglyMeasurable hb hslice.stronglyMeasurable
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun Z => by
        apply congrArg P.F
        funext k
        rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨l, rfl⟩
        · simp only [Fin.insertNth_apply_same]
        · simp only [Fin.insertNth_apply_succAbove]

theorem bandMaskedFace_pullback (P : TrialSmoothProfiles182) (b : Fin 3) (i : Fin 39)
    (Y : Fin 38 → FiniteMeasure ℝ) :
    P.bandMaskedFace b i (fun k => fragmentBandMasses P.a (Y k)) =
      P.facePhysical b Y * P.coefficientErasure i Y := by
  unfold bandMaskedFace
  rw [P.bandErasure_pullback]
  rfl

theorem physicalBandErased_eq (P : TrialSmoothProfiles182) (i : Fin 39)
    (Y : Fin 38 → FiniteMeasure ℝ) :
    physicalBandErased182 P.a i (P.exceptionalFace i) P.F Y =
      (1 - P.facePhysical 2 Y) * P.coefficientErasure i Y := by
  change -P.bandMaskedFace 2 i (fun k => fragmentBandMasses P.a (Y k)) +
    P.coefficientErasure i Y = _
  rw [P.bandMaskedFace_pullback]
  ring

theorem physicalBandKernelEnergy_eq (P : TrialSmoothProfiles182) (i : Fin 39) :
    physicalBandKernelEnergy182 P.a i (P.exceptionalFace i) P.F =
      ∫ Y, trialFaceKernel Y *
        (P.coefficientErasure i Y - P.facePhysical 2 Y * P.coefficientErasure i Y) ^ 2
        ∂trialAmbientProduct selbergFragmentCap182 38 := by
  unfold physicalBandKernelEnergy182
  apply integral_congr_ae
  exact ae_of_all _ fun Y => by
    dsimp only
    rw [P.physicalBandErased_eq]
    ring

theorem sharp_exceptional_moment_upper (P : TrialSmoothProfiles182)
    {H : Finset ℕ} (hH : H.card = 39) (i : Fin 39) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ res : ℕ,
      bandSharpMoment182 H P.a (H.orderEmbOfFin hH) i (P.exceptionalFace i) P.F x res ≤
        sieveMomentScale182 H x * ((∫ Y, trialFaceKernel Y *
          (P.coefficientErasure i Y - P.facePhysical 2 Y * P.coefficientErasure i Y) ^ 2
            ∂trialAmbientProduct selbergFragmentCap182 38) + ε) := by
  have h := physical_sharp_exceptional_moment_upper182 hH P.a P.strictMono P.zero P.last i
    (P.exceptionalFace i) P.F (P.continuous_exceptionalFace i).measurable
    P.F_smooth.continuous.measurable (P.bounded_exceptionalFace i)
    (P.F_compact.isCompact_range P.F_smooth.continuous).isBounded
    (ae_of_all _ fun _ => (P.continuous_exceptionalFace i).continuousAt)
    (ae_of_all _ fun _ => P.F_smooth.continuous.continuousAt)
    (P.exceptionalFace_radial i) (fun X hX => P.root_radial X hX i) ε hε
  simpa only [P.physicalBandKernelEnergy_eq] using h

#print axioms continuous_bandErasure
#print axioms bandErasure_pullback
#print axioms physicalBandKernelEnergy_eq
#print axioms sharp_exceptional_moment_upper

end TrialSmoothProfiles182
end PrimeGap182
