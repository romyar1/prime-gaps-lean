import SourceBandDomain182

/-! The actual source projection is exhausted in L² by open finite-band
certificates.  The proof uses finite marked tails, the proved null
boundaries, and dominated convergence under the actual physical law. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace PrimeGap182

theorem trial_source_band_exhaustion (d : ℕ)
    (outer inner : List TrialSourceRow)
    (ho : ∀ R ∈ outer, trialMesh < R.activation)
    (hi : ∀ R ∈ inner, trialMesh < R.activation)
    (radius : ℝ) (f : (Fin (d + 1) → FiniteMeasure ℝ) → ℝ)
    (hf : Measurable f) (C : ℝ) (hfb : ∀ X, ‖f X‖ ≤ C)
    (hinv : TrialMassCapInvariant trialReferenceCaps f)
    (hsupp : ∀ X, f X ≠ 0 → (∑ i, trialCellIndex (X i)) < trialCellCount ∧
      trialTotalMass X ≤ radius)
    (κ : ℝ) (hκ : (trialLargestCap : ℝ) ≤ κ)
    (m : ℕ → ℕ) (a : (N : ℕ) → Fin (m N + 2) → ℝ)
    (hgeom : ∀ N, StrictMono (a N) ∧ a N 0 = 0 ∧
      a N (0 : Fin (m N + 1)).succ = (trialMesh : ℝ) ∧
      a N (Fin.last (m N + 1)) = κ)
    (hmesh : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      ∀ j : Fin (m N + 1), j ≠ 0 → a N j.succ - a N j.castSucc < ε) :
    Tendsto (fun N => ∫ X : Fin (d + 1) → FiniteMeasure ℝ,
      ({v | TrialBandSourceDomain outer inner radius (a N) v}.indicator
        (fun v => f (fun i => PrimeGap186.trialBandRepresentative (a N) (v i)))
          (fun i => PrimeGap186.fragmentBandMasses (a N) (X i)) -
        trialRowsProjection outer inner f X) ^ 2 ∂trialProductMeasure (d + 1)) atTop (𝓝 0) := by
  classical
  let : IsFiniteMeasure trialPhysicalMeasure := trialPhysicalMeasure_finite
  let μ := trialProductMeasure (d + 1)
  let U (N : ℕ) := {v : Fin (d + 1) → Fin (m N + 1) → ℝ |
    TrialBandSourceDomain outer inner radius (a N) v}
  let B (N : ℕ) (X : Fin (d + 1) → FiniteMeasure ℝ) :=
    fun i => PrimeGap186.fragmentBandMasses (a N) (X i)
  let fN (N : ℕ) := (U N).indicator
    (fun v => f (fun i => PrimeGap186.trialBandRepresentative (a N) (v i)))
  let g := trialRowsProjection outer inner f
  have hoPos (R) (hR : R ∈ outer) : (0 : ℚ) < R.activation :=
    trialMesh_pos.trans (ho R hR)
  have hiPos (R) (hR : R ∈ inner) : (0 : ℚ) < R.activation :=
    trialMesh_pos.trans (hi R hR)
  have hgm : Measurable g := measurable_trialRowsProjection outer inner hoPos hiPos hf
  have hUopen (N : ℕ) : IsOpen (U N) := isOpen_trialBandSourceDomain outer inner radius (a N)
  have hBm (N : ℕ) : Measurable (B N) := measurable_pi_lambda _ fun i =>
    (PrimeGap186.measurable_fragmentBandMasses (a N)).comp (measurable_pi_apply i)
  have hfm (N : ℕ) : Measurable (fN N) := by
    apply Measurable.indicator _ (hUopen N).measurableSet
    exact hf.comp (measurable_pi_lambda _ fun i =>
      (PrimeGap186.trialBandRepresentative_measurable (a N)).comp (measurable_pi_apply i))
  have hP : MeasurableSet {X : Fin (d + 1) → FiniteMeasure ℝ |
      ∀ᶠ N in atTop, fN N (B N X) = g X} := by
    simp only [Filter.eventually_atTop, Set.ofPred_exists, Set.ofPred_forall]
    exact MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun M =>
      MeasurableSet.iInter fun _ => measurableSet_eq_fun ((hfm M).comp (hBm M)) hgm
  have hrowsO : ∀ᵐ X ∂μ, ∀ R ∈ outer, TrialOuterRowAllowed R X →
      trialTotalMass X < (R.outerCore : ℝ) ∨ trialSourceCountMeasure X
        {p : ℝ | (R.activation : ℝ) < p ∧
          ¬ TrialOuterRowOpen R ((trialWeightedMeasure X).real (Set.Ici p)) p} = 0 :=
    trial_eventually_list_forall outer (ae μ) _
      (fun R hR => trialOuterRowAllowed_ae_strict d R (Rat.cast_pos.mpr (hoPos R hR)))
  have hrowsI : ∀ᵐ X ∂μ, ∀ R ∈ inner, TrialInnerRowAllowed R X →
      R.order = 1 ∨ trialTotalMass X < (R.innerCore : ℝ) ∨ trialSourceCountMeasure X
        {p : ℝ | (R.activation : ℝ) < p ∧
          ¬ TrialInnerRowOpen R ((trialWeightedMeasure X).real (Set.Ici p)) p} = 0 :=
    trial_eventually_list_forall inner (ae μ) _
      (fun R hR => trialInnerRowAllowed_ae_strict d R (Rat.cast_pos.mpr (hiPos R hR)))
  have hQ : ∀ᵐ X ∂μ,
      (∀ q : ℚ, trialSourceCountMeasure X {(q : ℝ)} = 0) ∧
      (∀ i (q : ℚ), (X i : Measure ℝ) {(q : ℝ)} = 0) ∧
      (∀ i (n : ℕ), ((X i).mass : ℝ) ≠ (n : ℝ) * (trialMesh : ℝ)) ∧
      trialTotalMass X ≠ radius ∧
      (∀ R ∈ outer, TrialOuterRowAllowed R X →
        trialTotalMass X < (R.outerCore : ℝ) ∨ trialSourceCountMeasure X
          {p : ℝ | (R.activation : ℝ) < p ∧
            ¬ TrialOuterRowOpen R ((trialWeightedMeasure X).real (Set.Ici p)) p} = 0) ∧
      (∀ R ∈ inner, TrialInnerRowAllowed R X →
        R.order = 1 ∨ trialTotalMass X < (R.innerCore : ℝ) ∨ trialSourceCountMeasure X
          {p : ℝ | (R.activation : ℝ) < p ∧
            ¬ TrialInnerRowOpen R ((trialWeightedMeasure X).real (Set.Ici p)) p} = 0) := by
    filter_upwards [trialProductMeasure_ae_count_marks (d + 1),
      trialProductMeasure_ae_fixed_marks (d + 1), trialProductMeasure_ae_mass_grid (d + 1),
      trial_total_mass_ne d radius, hrowsO, hrowsI] with X hc hf hg ht ho hi
    exact ⟨hc, hf, hg, ht, ho, hi⟩
  have hevent : ∀ᵐ X ∂μ, ∀ᶠ N in atTop, fN N (B N X) = g X := by
    apply trialProductMeasure_ae_finite_tail_elim_of_ae (trialMesh : ℝ) trial_seed_cap.1
      (d + 1) (fun X => ∀ᶠ N in atTop, fN N (B N X) = g X) _ hP hQ
    intro Y n x hY hx hQX
    let X : Fin (d + 1) → FiniteMeasure ℝ :=
      fun i => Y i + PrimeGap186.weightedEmpirical (n i) (x i)
    change ∀ᶠ N in atTop, fN N (B N X) = g X
    rcases hQX with ⟨hcount, hfixed, hgrid, hradNe, hstrictO, hstrictI⟩
    have hfull := PrimeGap186.trial_finite_configuration_cap (d + 1) (trialMesh : ℝ) κ
      trial_seed_cap.1 (trial_seed_cap.2.le.trans hκ) Y n x hY
      (fun i k => ⟨(hx i k).1, (hx i k).2.trans hκ⟩)
    have hfullL := PrimeGap186.trial_finite_configuration_cap (d + 1) (trialMesh : ℝ)
      (trialLargestCap : ℝ) trial_seed_cap.1 trial_seed_cap.2.le Y n x hY hx
    have hcapL (i : Fin (d + 1)) : (X i : Measure ℝ) (Set.Ioi (trialLargestCap : ℝ)) = 0 := by
      have he := congrArg (fun Z : FiniteMeasure ℝ => (Z : Measure ℝ)) (hfullL.1 i)
      rw [FiniteMeasure.restrict_measure_eq] at he
      rw [← he, Measure.restrict_apply measurableSet_Ioi,
        Set.disjoint_iff_inter_eq_empty.mp Set.Ioc_disjoint_Ioi_same.symm, measure_empty]
    have htotal (N : ℕ) : trialBandTotal (B N X) = trialTotalMass X := by
      apply PrimeGap186.trial_band_total_sum (a N) (hgeom N).1.monotone
      simpa only [(hgeom N).2.1, (hgeom N).2.2.2] using hfull.2
    have hmassB (N : ℕ) (i : Fin (d + 1)) :
        (∑ j, B N X i j) = ((X i).mass : ℝ) := by
      dsimp only [B]
      rw [PrimeGap186.sum_fragmentBandMasses (a N) (hgeom N).1.monotone,
        (hgeom N).2.1, (hgeom N).2.2.2, hfull.1 i]
    have hfullN (N : ℕ) : (∑ i, X i).restrict
        (Set.Ioc (a N 0) (a N (Fin.last (m N + 1)))) = ∑ i, X i := by
      simpa only [(hgeom N).2.1, (hgeom N).2.2.2] using hfull.2
    have hgap (N : ℕ) := trialBand_finite_configuration_gap κ hκ (a N) (hgeom N).1
      (hgeom N).2.1 (hgeom N).2.2.1 (hgeom N).2.2.2 Y n x hY hx
    obtain ⟨hmass, hcaps⟩ := trialBand_representatives_eventually κ hκ m a hgeom hmesh
      (d + 1) Y n x hY hx hfixed trialReferenceCaps trialReferenceCaps_data.2.2.2
    have hrep : ∀ᶠ N in atTop,
        f (fun i => PrimeGap186.trialBandRepresentative (a N) (B N X i)) = f X := by
      filter_upwards [hcaps] with N hN
      exact hinv _ X (hmass N) hN
    by_cases hzero : f X = 0
    · filter_upwards [hrep] with N hN
      simp only [fN, Set.indicator_apply, hN, hzero, ite_self, g, trialRowsProjection]
    by_cases hrows : TrialRowsAllowed outer inner X
    · have hradius : trialTotalMass X < radius := lt_of_le_of_ne (hsupp X hzero).2 hradNe
      let z : ((i : Fin (d + 1)) × Fin (n i)) → ℝ := fun k => x k.1 k.2
      have htail := PrimeGap186.trial_finite_tail_mass_and_count (d + 1) (trialMesh : ℝ)
        trial_seed_cap.1 Y n x hY (fun i k => (hx i k).1)
      have hz (k) : 0 ≤ z k ∧ z k ≤ κ :=
        ⟨(trial_seed_cap.1.trans (hx k.1 k.2).1).le, (hx k.1 k.2).2.trans hκ⟩
      have hoEvent : ∀ᶠ N in atTop, ∀ R ∈ outer, TrialBandOuterRow R (a N) (B N X) := by
        apply trial_eventually_list_forall outer atTop
        intro R hR
        exact trialBandOpenRow_eventually κ (R.outerCore : ℝ) (R.activation : ℝ)
          (Rat.cast_lt.mpr (ho R hR)) m a hgeom hmesh X hfull.2 z hz
          (by simpa only [trialWeightedMeasure, FiniteMeasure.toMeasure_sum] using htail.1)
          htail.2 (hcount R.activation) (TrialOuterRowOpen R) (isOpen_trialOuterRowOpen R)
          (hstrictO R hR (hrows.1 R hR))
      have hiEvent : ∀ᶠ N in atTop, ∀ R ∈ inner, TrialBandInnerRow R (a N) (B N X) := by
        apply trial_eventually_list_forall inner atTop
        intro R hR
        rcases hstrictI R hR (hrows.2 R hR) with hOne | hrow
        · exact Filter.Eventually.of_forall fun _ => Or.inl hOne
        · have hev := trialBandOpenRow_eventually κ (R.innerCore : ℝ) (R.activation : ℝ)
            (Rat.cast_lt.mpr (hi R hR)) m a hgeom hmesh X hfull.2 z hz
            (by simpa only [trialWeightedMeasure, FiniteMeasure.toMeasure_sum] using htail.1)
            htail.2 (hcount R.activation) (TrialInnerRowOpen R) (isOpen_trialInnerRowOpen R) hrow
          filter_upwards [hev] with N hN
          exact Or.inr hN
      filter_upwards [hrep, hcaps, hoEvent, hiEvent] with N hrepN hcapsN hoN hiN
      have hU : B N X ∈ U N := by
        refine ⟨hoN, hiN, ?_, trialBandCellInterior_of_mass _ X (hmassB N) hgrid
          (hsupp X hzero).1, ?_⟩
        · intro j hj
          have hbandzero : trialBandMassSum (B N X) j = 0 := by
            apply Finset.sum_eq_zero
            intro i _
            have hcap : (PrimeGap186.trialBandRepresentative (a N) (B N X i) : Measure ℝ)
                (Set.Ioi (trialLargestCap : ℝ)) = 0 :=
              (hcapsN i trialLargestCap trialReferenceCaps_data.1).mpr (hcapL i)
            exact (PrimeGap186.trialBandRepresentative_cap_zero_iff (a N) _
              (fun _ => NNReal.coe_nonneg _) (trialLargestCap : ℝ)).mp hcap j hj
          rw [hbandzero]
          exact PrimeGap186.trial_band_positive_lower_of_seed (a N) (hgeom N).1
            (hgeom N).2.1 (by rw [(hgeom N).2.2.1]; exact trial_seed_cap.2.le) hj
        · simpa only [htotal] using hradius
      simp only [fN, Set.indicator_of_mem hU, hrepN, g, trialRowsProjection, ite_eq_left hrows]
    · exact Filter.Eventually.of_forall fun N => by
        have hnot : B N X ∉ U N := by
          intro hU
          exact hrows (trialBandSourceDomain_sound outer inner ho hi radius (a N)
            (hgeom N).1 (hgeom N).2.1 (hgeom N).2.2.1 X (hfullN N) (hgap N) hU).1
        simp only [fN, Set.indicator_of_notMem hnot, g, trialRowsProjection, ite_eq_right hrows]
  have hfNb (N : ℕ) (v : Fin (d + 1) → Fin (m N + 1) → ℝ) : ‖fN N v‖ ≤ C :=
    (norm_indicator_le_norm_self _ _).trans (hfb _)
  have hgb (X : Fin (d + 1) → FiniteMeasure ℝ) : ‖g X‖ ≤ C :=
    (trialRowsProjection_norm_le outer inner f X).trans (hfb X)
  have hconv := tendsto_integral_of_dominated_convergence
    (μ := μ) (F := fun N X => (fN N (B N X) - g X) ^ 2)
    (f := fun _ => (0 : ℝ)) (fun _ => (2 * C) ^ 2)
    (fun N => ((((hfm N).comp (hBm N)).sub hgm).pow_const 2).aestronglyMeasurable)
    (integrable_const _) (fun N => Filter.Eventually.of_forall fun X => by
      rw [norm_pow]
      apply pow_le_pow_left₀ (norm_nonneg _) _
      calc
        ‖fN N (B N X) - g X‖ ≤ ‖fN N (B N X)‖ + ‖g X‖ := norm_sub_le _ _
        _ ≤ C + C := add_le_add (hfNb N _) (hgb X)
        _ = 2 * C := by ring)
    (by filter_upwards [hevent] with X hX
        apply tendsto_const_nhds.congr'
        filter_upwards [hX] with N hN
        simp only [hN, sub_self, zero_pow (by decide : 2 ≠ 0)])
  simpa only [integral_zero] using hconv

#print axioms trial_source_band_exhaustion

end PrimeGap182
