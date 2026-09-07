import SourceBandRows182

/-! Open radial cell support for finite-band smoothing.  The sum of cell
indices is retained exactly, including the erased 38-coordinate support;
a total-mass cutoff alone would not imply that floor-sum condition. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace PrimeGap182

def TrialBandCellInterior {d m : ℕ} (v : Fin d → Fin (m + 1) → ℝ) : Prop :=
  ∃ k : Fin d → ℕ, (∑ i, k i) < trialCellCount ∧
    ∀ i, (k i : ℝ) * (trialMesh : ℝ) < ∑ j, v i j ∧
      (∑ j, v i j) < ((k i : ℝ) + 1) * (trialMesh : ℝ)

theorem isOpen_trialBandCellInterior {d m : ℕ} :
    IsOpen {v : Fin d → Fin (m + 1) → ℝ | TrialBandCellInterior v} := by
  unfold TrialBandCellInterior
  rw [Set.ofPred_exists]
  apply isOpen_iUnion
  intro k
  apply isOpen_const.inter
  apply PrimeGap186.trial_isOpen_finite_forall
  intro i
  have hc : Continuous (fun v : Fin d → Fin (m + 1) → ℝ => ∑ j, v i j) := by fun_prop
  exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)

theorem trialBandCellInterior_indices {d m : ℕ}
    (v : Fin d → Fin (m + 1) → ℝ) (hv : TrialBandCellInterior v) :
    (∑ i, PrimeGap182Analytic.bandCellIndex182 (v i)) < trialCellCount := by
  obtain ⟨k, hk, hv⟩ := hv
  have hh : (0 : ℝ) < (trialMesh : ℝ) := Rat.cast_pos.mpr trialMesh_pos
  have heq (i : Fin d) : PrimeGap182Analytic.bandCellIndex182 (v i) = k i := by
    apply (Nat.floor_eq_iff (by
      apply div_nonneg _ hh.le
      exact (mul_nonneg (Nat.cast_nonneg _) hh.le).trans (hv i).1.le)).mpr
    exact ⟨(le_div_iff₀ hh).mpr (hv i).1.le, (div_lt_iff₀ hh).mpr (hv i).2⟩
  simpa only [heq] using hk

theorem trialBandCellInterior_face {m : ℕ}
    (v : Fin 38 → Fin (m + 1) → ℝ) (hv : TrialBandCellInterior v) :
    PrimeGap182Analytic.bandFaceCellSum182 v < trialCellCount :=
  trialBandCellInterior_indices v hv

theorem trialBandCellInterior_removeNth {m : ℕ}
    (v : Fin 39 → Fin (m + 1) → ℝ) (hv : TrialBandCellInterior v) (i : Fin 39) :
    PrimeGap182Analytic.bandFaceCellSum182 (i.removeNth v) < trialCellCount := by
  have hs := trialBandCellInterior_indices v hv
  have he := Fin.sum_univ_succAbove
    (fun k : Fin 39 => PrimeGap182Analytic.bandCellIndex182 (v k)) i
  change (∑ k : Fin 38, PrimeGap182Analytic.bandCellIndex182 (v (i.succAbove k))) < _
  rw [he] at hs
  exact (Nat.le_add_left _ _).trans_lt hs

theorem trialBandCellInterior_of_mass {d m : ℕ}
    (v : Fin d → Fin (m + 1) → ℝ) (X : Fin d → FiniteMeasure ℝ)
    (hmass : ∀ i, (∑ j, v i j) = ((X i).mass : ℝ))
    (hgrid : ∀ i (n : ℕ), ((X i).mass : ℝ) ≠ (n : ℝ) * (trialMesh : ℝ))
    (hcell : (∑ i, trialCellIndex (X i)) < trialCellCount) : TrialBandCellInterior v := by
  refine ⟨fun i => trialCellIndex (X i), hcell, ?_⟩
  intro i
  rw [hmass i]
  have hh : (0 : ℝ) < (trialMesh : ℝ) := Rat.cast_pos.mpr trialMesh_pos
  have hlo : (trialCellIndex (X i) : ℝ) * (trialMesh : ℝ) ≤ ((X i).mass : ℝ) :=
    (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg (by positivity) hh.le))
  refine ⟨lt_of_le_of_ne hlo (Ne.symm (hgrid i _)), ?_⟩
  exact (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (((X i).mass : ℝ) / (trialMesh : ℝ)))

theorem trialProductMeasure_ae_mass_grid (d : ℕ) :
    ∀ᵐ X ∂trialProductMeasure d, ∀ i (n : ℕ),
      ((X i).mass : ℝ) ≠ (n : ℝ) * (trialMesh : ℝ) := by
  let : IsFiniteMeasure trialPhysicalMeasure := trialPhysicalMeasure_finite
  have hm : Measurable (fun X : FiniteMeasure ℝ => (X.mass : ℝ)) :=
    ((Measure.measurable_coe MeasurableSet.univ).comp measurable_subtype_coe).ennreal_toReal
  have hsingle (c : ℝ) : ∀ᵐ X ∂trialPhysicalMeasure, (X.mass : ℝ) ≠ c := by
    apply ae_mono trialPhysicalMeasure_le_baseline
    exact ae_of_ae_map hm.aemeasurable
      ((ae_mono PrimeGap186.trialPhysicalMeasure_mass_map.2)
        (Measure.ae_ne (volume.restrict (Set.Ici (0 : ℝ))) c))
  simp only [ae_all_iff]
  intro i n
  exact (Measure.tendsto_eval_ae_ae
    (μ := fun _ : Fin d => trialPhysicalMeasure) (i := i)).eventually (hsingle _)

#print axioms trialBandCellInterior_removeNth
#print axioms trialProductMeasure_ae_mass_grid

end PrimeGap182
