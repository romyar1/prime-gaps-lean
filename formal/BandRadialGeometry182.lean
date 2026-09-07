import RadialExceptionalMoment182

/-!
Finite-band radial masks and their actual fragment-law geometry. The
grid-boundary and local-constancy arguments generalize the checked public
trial construction; source credits and pins are recorded in Selberg39.
-/

noncomputable section
open scoped BigOperators ENNReal Topology
open Filter MeasureTheory PrimeGap186

namespace PrimeGap182Analytic

def selbergPhysicalMeasure182 : Measure (FiniteMeasure ℝ) :=
  ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * selbergFragmentCap182) •
    fragmentLaw selbergFragmentCap182

def selbergBandMeasure182 {m : ℕ} (a : Fin (m + 2) → ℝ) : Measure (Fin (m + 1) → ℝ) :=
  ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * selbergFragmentCap182) •
    Measure.map (fragmentBandMasses a) (fragmentLaw selbergFragmentCap182)

instance selbergPhysicalMeasure182_finite : IsFiniteMeasure selbergPhysicalMeasure182 := by
  let : IsProbabilityMeasure (fragmentLaw selbergFragmentCap182) :=
    fragmentLaw_isProbabilityMeasure selbergFragmentCap182
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top

instance selbergBandMeasure182_finite {m : ℕ} (a : Fin (m + 2) → ℝ) :
    IsFiniteMeasure (selbergBandMeasure182 a) := by
  let : IsProbabilityMeasure (fragmentLaw selbergFragmentCap182) :=
    fragmentLaw_isProbabilityMeasure selbergFragmentCap182
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top

def bandCellIndex182 {m : ℕ} (v : Fin (m + 1) → ℝ) : ℕ :=
  ⌊(∑ j, v j) / (PrimeGap182.trialMesh : ℝ)⌋₊

def bandFaceCellSum182 {m : ℕ} (Y : Fin 38 → Fin (m + 1) → ℝ) : ℕ :=
  ∑ i, bandCellIndex182 (Y i)

def bandFaceBlockMask182 {m : ℕ} (b : Fin 512) (Y : Fin 38 → Fin (m + 1) → ℝ) : ℝ :=
  if bandFaceCellSum182 Y < PrimeGap182.trialCellCount ∧ bandFaceCellSum182 Y / 768 = b.val
    then 1 else 0

def bandBlockFace182 {m : ℕ} (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (b : Fin 512) (Y : Fin 38 → Fin (m + 1) → ℝ) : ℝ :=
  bandFaceBlockMask182 b Y * G Y

def bandBlockProfile182 {m : ℕ} (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (i : Fin 39) (b : Fin 512) (X : Fin 39 → Fin (m + 1) → ℝ) : ℝ :=
  bandFaceBlockMask182 b (i.removeNth X) * F X

theorem measurable_bandCellIndex182 {m : ℕ} : Measurable (@bandCellIndex182 m) :=
  ((Finset.measurable_sum _ fun j _ => measurable_pi_apply j).div_const _).nat_floor

theorem measurable_bandFaceBlockMask182 {m : ℕ} (b : Fin 512) :
    Measurable (@bandFaceBlockMask182 m b) := by
  have hs : Measurable (@bandFaceCellSum182 m) :=
    Finset.measurable_sum _ fun i _ => measurable_bandCellIndex182.comp (measurable_pi_apply i)
  exact Measurable.ite ((measurableSet_lt hs measurable_const).inter
    (measurableSet_eq_fun ((measurable_of_countable (fun n : ℕ => n / 768)).comp hs)
      measurable_const)) measurable_const measurable_const

theorem bandFaceBlockMask182_values {m : ℕ} (b : Fin 512) (Y : Fin 38 → Fin (m + 1) → ℝ) :
    bandFaceBlockMask182 b Y = 0 ∨ bandFaceBlockMask182 b Y = 1 := by
  unfold bandFaceBlockMask182
  split_ifs <;> simp

theorem bandFaceBlockMask182_disjoint {m : ℕ} {b c : Fin 512} (hbc : b ≠ c)
    (Y : Fin 38 → Fin (m + 1) → ℝ) :
    bandFaceBlockMask182 b Y * bandFaceBlockMask182 c Y = 0 := by
  unfold bandFaceBlockMask182
  split_ifs with hb hc
  · exact False.elim (hbc (Fin.ext (hb.2.symm.trans hc.2)))
  all_goals norm_num

theorem bandFaceBlockMask182_bounded {m : ℕ} (b : Fin 512) :
    Bornology.IsBounded (Set.range (@bandFaceBlockMask182 m b)) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1, ?_⟩
  rintro _ ⟨Y, rfl⟩
  rcases bandFaceBlockMask182_values b Y with h | h <;> simp [h]

theorem selbergBandMeasure182_total_no_atoms {m : ℕ} (a : Fin (m + 2) → ℝ)
    (ha : StrictMono a) (ha0 : a 0 = 0) (haLast : a (Fin.last (m + 1)) = selbergFragmentCap182)
    (t : ℝ) : (selbergBandMeasure182 a) {v | (∑ j, v j) = t} = 0 := by
  let total : (Fin (m + 1) → ℝ) → ℝ := fun v => ∑ j, v j
  have ht : Continuous total := continuous_finsetSum _ fun j _ => continuous_apply j
  have hb := measurable_fragmentBandMasses a
  have hmap : Measure.map (fragmentBandMasses a) selbergPhysicalMeasure182 =
      selbergBandMeasure182 a := Measure.map_smul _ hb.aemeasurable
  have hconfig : ∀ᵐ c ∂selbergPhysicalMeasure182,
      c.restrict (Set.Ioc (0 : ℝ) selbergFragmentCap182) = c :=
    Measure.ae_smul_measure (ae_restrict_Ioc_fragmentLaw selbergFragmentCap182) _
  have htotal : Measure.map total (selbergBandMeasure182 a) =
      (volume.restrict (Set.Ici (0 : ℝ))).withDensity
        (fun s => ENNReal.ofReal (dickmanRho (s / selbergFragmentCap182))) := by
    calc
      _ = Measure.map (fun c : FiniteMeasure ℝ => (c.mass : ℝ)) selbergPhysicalMeasure182 := by
        rw [← hmap, Measure.map_map ht.measurable hb]
        apply Measure.map_congr
        filter_upwards [hconfig] with c hc
        dsimp only [Function.comp_def, total]
        rw [sum_fragmentBandMasses a ha.monotone c, ha0, haLast, hc]
      _ = _ := by
        change Measure.map _ (ENNReal.ofReal _ • fragmentLaw selbergFragmentCap182) = _
        have hm : Measurable (fun c : FiniteMeasure ℝ => (c.mass : ℝ)) :=
          ((Measure.measurable_coe MeasurableSet.univ).comp measurable_subtype_coe).ennreal_toReal
        rw [Measure.map_smul _ hm.aemeasurable]
        exact normalized_fragmentLaw_mass_eq_dickman selbergFragmentCap182
          (by norm_num [selbergFragmentCap182, selbergRho182])
  change (selbergBandMeasure182 a) (total ⁻¹' {t}) = 0
  rw [← Measure.map_apply ht.measurable (measurableSet_singleton t), htotal]
  exact measure_singleton t

theorem selbergBandMeasure182_ae_off_grid {m : ℕ} (a : Fin (m + 2) → ℝ)
    (ha : StrictMono a) (ha0 : a 0 = 0) (haLast : a (Fin.last (m + 1)) = selbergFragmentCap182)
    (d : ℕ) : ∀ᵐ Y ∂Measure.pi (fun _ : Fin d => selbergBandMeasure182 a),
      ∀ i : Fin d, ∀ n : ℕ, (∑ j, Y i j) ≠ (n : ℝ) * (PrimeGap182.trialMesh : ℝ) := by
  have hz : (Measure.pi (fun _ : Fin d => selbergBandMeasure182 a))
      {Y | ∃ i : Fin d, ∃ n : ℕ, (∑ j, Y i j) = (n : ℝ) * (PrimeGap182.trialMesh : ℝ)} = 0 := by
    simp only [Set.ofPred_exists]
    exact measure_iUnion_null fun i => measure_iUnion_null fun n =>
      Measure.pi_eval_preimage_null (fun _ : Fin d => selbergBandMeasure182 a)
        (i := i) (selbergBandMeasure182_total_no_atoms a ha ha0 haLast _)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with Y hY
  intro i n he
  exact hY ⟨i, n, he⟩

theorem bandCellIndex182_locally_constant {m : ℕ} (v : Fin (m + 1) → ℝ)
    (hv : ∀ n : ℕ, (∑ j, v j) ≠ (n : ℝ) * (PrimeGap182.trialMesh : ℝ)) :
    ∀ᶠ w in nhds v, bandCellIndex182 w = bandCellIndex182 v := by
  let t : ℝ := (∑ j, v j) / (PrimeGap182.trialMesh : ℝ)
  have hh : 0 < (PrimeGap182.trialMesh : ℝ) := Rat.cast_pos.mpr PrimeGap182.trialMesh_pos
  have hc : Continuous (fun w : Fin (m + 1) → ℝ =>
      (∑ j, w j) / (PrimeGap182.trialMesh : ℝ)) :=
    (continuous_finsetSum _ fun j _ => continuous_apply j).div_const _
  by_cases ht : t < 0
  · have hlt : t < 1 := ht.trans zero_lt_one
    filter_upwards [hc.continuousAt.eventually (Iio_mem_nhds hlt)] with w hw
    exact (Nat.floor_eq_zero.mpr hw).trans (Nat.floor_eq_zero.mpr hlt).symm
  · have ht0 : 0 ≤ t := le_of_not_gt ht
    have hlo : (bandCellIndex182 v : ℝ) < t := by
      apply lt_of_le_of_ne (Nat.floor_le ht0)
      intro heq
      exact hv _ ((div_eq_iff hh.ne').mp heq.symm)
    filter_upwards [hc.continuousAt.eventually
      (Ioo_mem_nhds hlo (Nat.lt_floor_add_one t))] with w hw
    exact (Nat.floor_eq_iff ((Nat.cast_nonneg (bandCellIndex182 v)).trans hw.1.le)).mpr
      ⟨hw.1.le, hw.2⟩

theorem bandFaceBlockMask182_continuousAt {m : ℕ} (b : Fin 512)
    (Y : Fin 38 → Fin (m + 1) → ℝ)
    (hY : ∀ i : Fin 38, ∀ n : ℕ, (∑ j, Y i j) ≠ (n : ℝ) * (PrimeGap182.trialMesh : ℝ)) :
    ContinuousAt (bandFaceBlockMask182 b) Y := by
  have hi : ∀ᶠ X in nhds Y, ∀ i : Fin 38, bandCellIndex182 (X i) = bandCellIndex182 (Y i) :=
    eventually_all.mpr fun i => (continuous_apply i).continuousAt.eventually
      (bandCellIndex182_locally_constant (Y i) (hY i))
  apply (continuousAt_const : ContinuousAt
    (fun _ : Fin 38 → Fin (m + 1) → ℝ => bandFaceBlockMask182 b Y) Y).congr_of_eventuallyEq
  filter_upwards [hi] with X hX
  simp only [bandFaceBlockMask182, bandFaceCellSum182, hX]
  exact (ite_eq_ite _ _ _).mpr True.intro

theorem bandBlockFace182_regular {m : ℕ} (a : Fin (m + 2) → ℝ)
    (ha : StrictMono a) (ha0 : a 0 = 0) (haLast : a (Fin.last (m + 1)) = selbergFragmentCap182)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ) (hG : Measurable G)
    (hbG : Bornology.IsBounded (Set.range G))
    (hcG : ∀ᵐ Y ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a), ContinuousAt G Y)
    (b : Fin 512) : Measurable (bandBlockFace182 G b) ∧
      Bornology.IsBounded (Set.range (bandBlockFace182 G b)) ∧
      ∀ᵐ Y ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a),
        ContinuousAt (bandBlockFace182 G b) Y := by
  refine ⟨(measurable_bandFaceBlockMask182 b).mul hG,
    isBounded_range_mul_comp (bandFaceBlockMask182_bounded b) hbG id id, ?_⟩
  filter_upwards [selbergBandMeasure182_ae_off_grid a ha ha0 haLast 38, hcG] with Y hY hg
  exact (bandFaceBlockMask182_continuousAt b Y hY).mul hg

theorem bandBlockProfile182_regular {m : ℕ} (a : Fin (m + 2) → ℝ)
    (ha : StrictMono a) (ha0 : a 0 = 0) (haLast : a (Fin.last (m + 1)) = selbergFragmentCap182)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (hF : Measurable F)
    (hbF : Bornology.IsBounded (Set.range F))
    (hcF : ∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => selbergBandMeasure182 a), ContinuousAt F X)
    (i : Fin 39) (b : Fin 512) : Measurable (bandBlockProfile182 F i b) ∧
      Bornology.IsBounded (Set.range (bandBlockProfile182 F i b)) ∧
      ∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => selbergBandMeasure182 a),
        ContinuousAt (bandBlockProfile182 F i b) X := by
  have he : Continuous (fun X : Fin 39 → Fin (m + 1) → ℝ => i.removeNth X) := by
    change Continuous (fun X : Fin 39 → Fin (m + 1) → ℝ => fun k : Fin 38 => X (i.succAbove k))
    fun_prop
  refine ⟨?_, ?_, ?_⟩
  · change Measurable (fun X : Fin 39 → Fin (m + 1) → ℝ =>
      bandFaceBlockMask182 b (fun k : Fin 38 => X (i.succAbove k)) * F X)
    apply Measurable.mul _ hF
    apply (measurable_bandFaceBlockMask182 (m := m) b).comp
    exact measurable_pi_lambda _ fun k => measurable_pi_apply (i.succAbove k)
  · exact isBounded_range_mul_comp (bandFaceBlockMask182_bounded (m := m) b) hbF
      (fun X : Fin 39 → Fin (m + 1) → ℝ => i.removeNth X) id
  · filter_upwards [selbergBandMeasure182_ae_off_grid a ha ha0 haLast 39, hcF] with X hX hf
    have hm := ContinuousAt.comp'
      (f := fun Y : Fin 39 → Fin (m + 1) → ℝ => i.removeNth Y)
      (g := bandFaceBlockMask182 b) (x := X)
      (bandFaceBlockMask182_continuousAt b (i.removeNth X)
        (fun k => hX (i.succAbove k))) he.continuousAt
    exact hm.mul hf

theorem bandBlockProfile182_erasure {m : ℕ} (a : Fin (m + 2) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (i : Fin 39) (b : Fin 512)
    (Y : Fin 38 → Fin (m + 1) → ℝ) :
    (∫ t, bandBlockProfile182 F i b (i.insertNth t Y) ∂selbergBandMeasure182 a) =
      bandFaceBlockMask182 b Y * (∫ t, F (i.insertNth t Y) ∂selbergBandMeasure182 a) := by
  simp only [bandBlockProfile182, Fin.removeNth_insertNth, integral_const_mul]

theorem bandBlock_combined_cross_zero {m : ℕ} (a : Fin (m + 2) → ℝ)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (i : Fin 39)
    {b c : Fin 512} (hbc : b ≠ c) (Y : Fin 38 → Fin (m + 1) → ℝ) :
    (bandBlockFace182 G b Y + ∫ t, bandBlockProfile182 F i b (i.insertNth t Y)
      ∂selbergBandMeasure182 a) *
    (bandBlockFace182 G c Y + ∫ t, bandBlockProfile182 F i c (i.insertNth t Y)
      ∂selbergBandMeasure182 a) = 0 := by
  rw [bandBlockProfile182_erasure, bandBlockProfile182_erasure]
  simp only [bandBlockFace182, ← mul_add]
  calc
    _ = (bandFaceBlockMask182 b Y * bandFaceBlockMask182 c Y) *
      (G Y + ∫ t, F (i.insertNth t Y) ∂selbergBandMeasure182 a) ^ 2 := by ring
    _ = _ := by rw [bandFaceBlockMask182_disjoint hbc, zero_mul]

theorem bandFaceBlockMask182_pullback {m : ℕ} (a : Fin (m + 2) → ℝ)
    (ha : Monotone a) (Y : Fin 38 → FiniteMeasure ℝ)
    (hY : ∀ i, (Y i).restrict (Set.Ioc (a 0) (a (Fin.last (m + 1)))) = Y i)
    (b : Fin 512) : bandFaceBlockMask182 b (fun i => fragmentBandMasses a (Y i)) =
      PrimeGap182.trialFaceBlockMask b Y := by
  have hs (i : Fin 38) : (∑ j, fragmentBandMasses a (Y i) j) = ((Y i).mass : ℝ) := by
    rw [sum_fragmentBandMasses a ha, hY i]
  simp only [bandFaceBlockMask182, bandFaceCellSum182, bandCellIndex182, hs,
    PrimeGap182.trialFaceBlockMask, PrimeGap182.trialFaceCellSum, PrimeGap182.trialCellIndex]
  exact (ite_eq_ite _ _ _).mpr True.intro

#print axioms selbergBandMeasure182_total_no_atoms
#print axioms bandBlockProfile182_regular
#print axioms bandBlock_combined_cross_zero
#print axioms bandFaceBlockMask182_pullback

end PrimeGap182Analytic
