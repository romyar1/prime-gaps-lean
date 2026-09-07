import SourceBandRows182

/-! Finite-tail and representative convergence for the actual 182 law.
The caps in the convergence statement are an arbitrary finite set of
rational thresholds strictly above the seed band. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace PrimeGap182

theorem trialProductMeasure_ae_finite_tail_elim_of_ae
    (δ : ℝ) (hδ : 0 < δ) (d : ℕ)
    (P Q : (Fin d → FiniteMeasure ℝ) → Prop)
    (hP : MeasurableSet {X | P X})
    (hQ : ∀ᵐ X ∂trialProductMeasure d, Q X)
    (hfinite : ∀ (Y : Fin d → FiniteMeasure ℝ) (n : Fin d → ℕ)
      (x : (i : Fin d) → Fin (n i) → ℝ),
      (∀ i, (Y i).restrict (Set.Ioc (0 : ℝ) δ) = Y i) →
      (∀ i k, δ < x i k ∧ x i k ≤ (trialLargestCap : ℝ)) →
      Q (fun i => Y i + PrimeGap186.weightedEmpirical (n i) (x i)) →
      P (fun i => Y i + PrimeGap186.weightedEmpirical (n i) (x i))) :
    ∀ᵐ X ∂trialProductMeasure d, P X := by
  let μ := trialProductMeasure d
  let R : Set (Fin d → FiniteMeasure ℝ) := (toMeasurable μ {X | ¬ Q X})ᶜ
  have hR : MeasurableSet R := (measurableSet_toMeasurable μ _).compl
  have hRQ : ∀ X ∈ R, Q X := by
    intro X hX
    by_contra hn
    exact hX (subset_toMeasurable μ {X | ¬ Q X} hn)
  have hRae : ∀ᵐ X ∂μ, X ∈ R := by
    apply measure_eq_zero_iff_ae_notMem.mp
    simpa only [measure_toMeasurable] using ae_iff.mp hQ
  have himp : ∀ᵐ X ∂μ, X ∈ R → P X := by
    apply trialProductMeasure_ae_finite_tail_elim δ hδ d (fun X => X ∈ R → P X)
    · convert hR.compl.union hP using 1
      ext X
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, imp_iff_not_or]
    · intro Y n x hY hx hX
      exact hfinite Y n x hY hx (hRQ _ hX)
  filter_upwards [hRae, himp] with X hX hXP
  exact hXP hX

theorem trialProductMeasure_ae_fixed_marks (d : ℕ) :
    ∀ᵐ X ∂trialProductMeasure d, ∀ i (q : ℚ), (X i : Measure ℝ) {(q : ℝ)} = 0 := by
  let : IsFiniteMeasure trialPhysicalMeasure := trialPhysicalMeasure_finite
  simp only [ae_all_iff]
  intro i q
  exact (Measure.tendsto_eval_ae_ae
    (μ := fun _ : Fin d => trialPhysicalMeasure) (i := i)).eventually
      (trial_fixed_mark_null (q : ℝ))

theorem trialProductMeasure_ae_count_marks (d : ℕ) :
    ∀ᵐ X ∂trialProductMeasure d, ∀ q : ℚ, trialSourceCountMeasure X {(q : ℝ)} = 0 := by
  simpa only [ae_all_iff] using fun q : ℚ => trial_count_fixed_mark_null d (q : ℝ)

theorem trial_seed_cap : (0 : ℝ) < (trialMesh : ℝ) ∧
    (trialMesh : ℝ) < (trialLargestCap : ℝ) := by
  norm_num [trialMesh, trialRadius, trialIntervals, trialLargestCap]

theorem trialBand_representatives_eventually
    (κ : ℝ) (hκ : (trialLargestCap : ℝ) ≤ κ)
    (m : ℕ → ℕ) (a : (N : ℕ) → Fin (m N + 2) → ℝ)
    (hgeom : ∀ N, StrictMono (a N) ∧ a N 0 = 0 ∧
      a N (0 : Fin (m N + 1)).succ = (trialMesh : ℝ) ∧
      a N (Fin.last (m N + 1)) = κ)
    (hmesh : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      ∀ j : Fin (m N + 1), j ≠ 0 → a N j.succ - a N j.castSucc < ε)
    (d : ℕ) (Y : Fin d → FiniteMeasure ℝ) (n : Fin d → ℕ)
    (x : (i : Fin d) → Fin (n i) → ℝ)
    (hY : ∀ i, (Y i).restrict (Set.Ioc (0 : ℝ) (trialMesh : ℝ)) = Y i)
    (hx : ∀ i k, (trialMesh : ℝ) < x i k ∧ x i k ≤ (trialLargestCap : ℝ))
    (hfixed : ∀ i (q : ℚ),
      ((Y i + PrimeGap186.weightedEmpirical (n i) (x i) : FiniteMeasure ℝ) :
        Measure ℝ) {(q : ℝ)} = 0)
    (C : Finset ℚ) (hC : ∀ q ∈ C, trialMesh < q) :
    let X : Fin d → FiniteMeasure ℝ :=
      fun i => Y i + PrimeGap186.weightedEmpirical (n i) (x i)
    (∀ N i, (PrimeGap186.trialBandRepresentative (a N)
      (PrimeGap186.fragmentBandMasses (a N) (X i))).mass = (X i).mass) ∧
    ∀ᶠ N in atTop, ∀ i (q : ℚ), q ∈ C →
      ((PrimeGap186.trialBandRepresentative (a N)
        (PrimeGap186.fragmentBandMasses (a N) (X i)) : Measure ℝ)
          (Set.Ioi (q : ℝ)) = 0 ↔ (X i : Measure ℝ) (Set.Ioi (q : ℝ)) = 0) := by
  classical
  intro X
  have hδ := trial_seed_cap.1
  have hfull := (PrimeGap186.trial_finite_configuration_cap d (trialMesh : ℝ) κ hδ
    (trial_seed_cap.2.le.trans hκ) Y n x hY
    (fun i k => ⟨(hx i k).1, (hx i k).2.trans hκ⟩)).1
  have htail (i : Fin d) : (X i : Measure ℝ).restrict (Set.Ioi (trialMesh : ℝ)) =
      ∑ k, ENNReal.ofReal (x i k) • Measure.dirac (x i k) :=
    PrimeGap186.trial_finite_tail_coordinate_mass (trialMesh : ℝ) (Y i) (n i) (x i)
      (hY i) (fun k => (hx i k).1)
  refine ⟨?_, ?_⟩
  · intro N i
    apply NNReal.coe_injective
    apply PrimeGap186.trialBandRepresentative_preserves_mass (a N) (hgeom N).1.monotone
    simpa only [(hgeom N).2.1, (hgeom N).2.2.2] using hfull i
  · apply Filter.eventually_all.mpr
    intro i
    apply C.eventually_all.mpr
    intro q hq
    let Ni : Measure ℝ := ((X i : Measure ℝ).restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun p : ℝ => ENNReal.ofReal p⁻¹)
    have hNi : Ni ≪ (X i : Measure ℝ) :=
      (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
    have hNtail : Ni.restrict (Set.Ioi (trialMesh : ℝ)) =
        ∑ j : Fin (n i), Measure.dirac (x i j) :=
      PrimeGap186.trial_count_tail_of_weighted_tail (X i) (trialMesh : ℝ) hδ (x i)
        (fun j => (hx i j).1) (htail i)
    obtain ⟨ε, hε, hfine⟩ := PrimeGap186.trialBandRepresentative_cap_fine (X i) Ni
      (trialMesh : ℝ) κ (q : ℝ) (Rat.cast_lt.mpr (hC q hq)) (x i)
      (fun j => ⟨(hδ.trans (hx i j).1).le, (hx i j).2.trans hκ⟩)
      (hfull i) (htail i) hNtail hNi (hNi (hfixed i q))
    filter_upwards [hmesh ε hε] with N hN
    exact hfine (m N) (a N) (hgeom N).1.monotone (hgeom N).2.1
      (hgeom N).2.2.1 (hgeom N).2.2.2 hN

theorem trialBand_finite_configuration_gap
    (κ : ℝ) (hκ : (trialLargestCap : ℝ) ≤ κ) {d m : ℕ}
    (a : Fin (m + 2) → ℝ) (ha : StrictMono a) (ha0 : a 0 = 0)
    (hseed : a (0 : Fin (m + 1)).succ = (trialMesh : ℝ))
    (hlast : a (Fin.last (m + 1)) = κ)
    (Y : Fin d → FiniteMeasure ℝ) (n : Fin d → ℕ)
    (x : (i : Fin d) → Fin (n i) → ℝ)
    (hY : ∀ i, (Y i).restrict (Set.Ioc (0 : ℝ) (trialMesh : ℝ)) = Y i)
    (hx : ∀ i k, (trialMesh : ℝ) < x i k ∧ x i k ≤ (trialLargestCap : ℝ)) :
    let X := fun i => Y i + PrimeGap186.weightedEmpirical (n i) (x i)
    ∀ j : Fin (m + 1), 0 < a j.castSucc →
      PrimeGap186.fragmentBandMasses a (∑ i, X i) j = 0 ∨
        a j.castSucc < PrimeGap186.fragmentBandMasses a (∑ i, X i) j := by
  intro X j hj
  have hj0 : j ≠ 0 := by
    rintro rfl
    simp only [Fin.castSucc_zero, ha0, lt_self_iff_false] at hj
  have hδj : (trialMesh : ℝ) ≤ a j.castSucc := by
    rw [← hseed]
    exact ha.monotone (Fin.succ_le_castSucc_iff.mpr (Fin.pos_iff_ne_zero.mpr hj0))
  let z : ((i : Fin d) × Fin (n i)) → ℝ := fun k => x k.1 k.2
  have htail := PrimeGap186.trial_finite_tail_mass_and_count d (trialMesh : ℝ)
    trial_seed_cap.1 Y n x hY (fun i k => (hx i k).1)
  apply PrimeGap186.trial_finite_tail_band_gap a ha.monotone (∑ i, X i)
    (trialMesh : ℝ) z htail.1 _ j hδj
  intro k
  exact ⟨(trial_seed_cap.1.trans (hx k.1 k.2).1).le,
    by simpa only [hlast] using (hx k.1 k.2).2.trans hκ⟩

#print axioms trialProductMeasure_ae_finite_tail_elim_of_ae
#print axioms trialBand_representatives_eventually
#print axioms trialBand_finite_configuration_gap

end PrimeGap182
