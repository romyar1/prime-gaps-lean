import SourceRowGeometry182
import SourceMarkedCover182

/-! Actual row failures produce labelled finite-atom offenders. The
weighted inclusive tail and the counting measure are linked explicitly. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace PrimeGap182

theorem source_finite_atoms_exists_of_measure_ne_zero {ι : Type*} [Fintype ι]
    (N : Measure ℝ) (δ : ℝ) (f : ι → ℝ)
    (hN : N.restrict (Set.Ioi δ) = ∑ a : ι, Measure.dirac (f a))
    (S : Set ℝ) (hS : S ⊆ Set.Ioi δ) (hne : N S ≠ 0) : ∃ a, f a ∈ S := by
  classical
  by_contra hn
  have hempty : (Finset.univ.filter (fun a : ι => f a ∈ S)) = ∅ :=
    Finset.filter_eq_empty_iff.mpr (fun a _ ha => hn ⟨a, ha⟩)
  exact hne (by rw [source_finite_atoms_count N δ f hN S hS, hempty,
    Finset.card_empty, Nat.cast_zero])

theorem source_finite_mark_le_cap {ι : Type*} [Fintype ι]
    (X : FiniteMeasure ℝ) (δ cap : ℝ) (f : ι → ℝ) (hf : ∀ a, 0 < f a)
    (htail : (X : Measure ℝ).restrict (Set.Ioi δ) =
      ∑ a : ι, ENNReal.ofReal (f a) • Measure.dirac (f a))
    (hcap : (X : Measure ℝ) (Set.Ioi cap) = 0) (a : ι) : f a ≤ cap := by
  classical
  by_contra ha
  have hfa : cap < f a := lt_of_not_ge ha
  have hz : ((X : Measure ℝ).restrict (Set.Ioi δ)) (Set.Ioi cap) = 0 := by
    rw [Measure.restrict_apply measurableSet_Ioi]
    exact measure_mono_null Set.inter_subset_left hcap
  rw [htail, Measure.finsetSum_apply, Finset.sum_eq_zero_iff] at hz
  have he := hz a (Finset.mem_univ a)
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply_of_mem (show f a ∈ Set.Ioi cap from hfa), mul_one] at he
  exact (ENNReal.ofReal_pos.mpr (hf a)).ne' he

theorem trialWeightedMeasure_real_sum {d : ℕ} (X : Fin d → FiniteMeasure ℝ)
    (S : Set ℝ) : (trialWeightedMeasure X).real S = ∑ i, (X i : Measure ℝ).real S := by
  simp only [trialWeightedMeasure, measureReal_def, Measure.finsetSum_apply]
  exact ENNReal.toReal_sum (fun i _ => measure_ne_top (X i : Measure ℝ) S)

theorem trialWeightedMeasure_real_univ {d : ℕ} (X : Fin d → FiniteMeasure ℝ) :
    (trialWeightedMeasure X).real Set.univ = trialTotalMass X := by
  rw [trialWeightedMeasure_real_sum]
  simp only [trialTotalMass, measureReal_def, ← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal]

theorem trialSource_tail_small_mass_le {d : ℕ} (c : TrialSourceCoverData)
    (X : Fin d → FiniteMeasure ℝ) (p : ℝ) (hp : (c.low : ℝ) < p) :
    (trialWeightedMeasure X).real (Set.Ici p) + trialSourceSmallMass c X ≤
      trialTotalMass X := by
  let : IsFiniteMeasure (trialWeightedMeasure X) := by
    unfold trialWeightedMeasure
    infer_instance
  have hd : Disjoint (Set.Ici p) (Set.Ioc (0 : ℝ) (c.low : ℝ)) :=
    Set.disjoint_left.mpr (fun _ ha hb => not_lt_of_ge (ha.trans hb.2) hp)
  rw [trialSourceSmallMass, ← trialWeightedMeasure_real_sum,
    ← measureReal_union hd measurableSet_Ioc, ← trialWeightedMeasure_real_univ X]
  exact measureReal_mono (Set.subset_univ _)

theorem source_weighted_inclusive_tail {d : ℕ} {ι : Type*} [Fintype ι]
    (X : Fin d → FiniteMeasure ℝ) (δ : ℝ) (f : ι → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hW : (trialWeightedMeasure X).restrict (Set.Ioi δ) =
      ∑ a : ι, ENNReal.ofReal (f a) • Measure.dirac (f a))
    (p : ℝ) (hp : δ < p) :
    (trialWeightedMeasure X).real (Set.Ici p) =
      ∑ a ∈ Finset.univ.filter (fun a : ι => p ≤ f a), f a := by
  have htail : ((∑ i, X i : FiniteMeasure ℝ) : Measure ℝ).restrict (Set.Ioi δ) =
      ∑ a : ι, ENNReal.ofReal (f a) • Measure.dirac (f a) := by
    simpa only [FiniteMeasure.toMeasure_sum, trialWeightedMeasure] using hW
  simpa only [FiniteMeasure.toMeasure_sum, trialWeightedMeasure, Set.mem_Ici,
    Finset.sum_filter] using
    PrimeGap186.trial_finite_tail_measureReal (∑ i, X i) δ f htail hf
      (Set.Ici p) measurableSet_Ici (fun _ h => hp.trans_le h)

theorem source_outer_failure_offender {d : ℕ} {ι : Type} [Fintype ι]
    (R : TrialSourceRow) (X : Fin d → FiniteMeasure ℝ) (δ : ℝ) (cap : ℚ)
    (f : ι → ℝ) (hδ : 0 < δ) (hactivation : δ ≤ (R.activation : ℝ))
    (hf : ∀ a, δ < f a) (hcap : ∀ a, f a ≤ (cap : ℝ))
    (hN : (trialSourceCountMeasure X).restrict (Set.Ioi δ) = ∑ a : ι, Measure.dirac (f a))
    (hW : (trialWeightedMeasure X).restrict (Set.Ioi δ) =
      ∑ a : ι, ENNReal.ofReal (f a) • Measure.dirac (f a))
    (hcompatible : TrialSourceCapCompatible true R cap)
    (hfailure : ¬ TrialOuterRowAllowed R X) :
    (R.outerCore : ℝ) < trialTotalMass X ∧
      ∃ a : ι, (R.activation : ℝ) < f a ∧
        2 ≤ (Finset.univ.filter (fun b : ι => f a ≤ f b)).card ∧
        (R.outerThreshold : ℝ) <
          (∑ b ∈ Finset.univ.filter (fun b : ι => f a ≤ f b), f b) +
            ((trialSourceEffectiveOrder R : ℝ) - 1) * f a := by
  have hcore : (R.outerCore : ℝ) < trialTotalMass X :=
    lt_of_not_ge (fun h => hfailure (Or.inl h))
  have hne : trialSourceCountMeasure X {p | TrialOuterViolation R X p} ≠ 0 :=
    fun h => hfailure (Or.inr h)
  obtain ⟨a, ha⟩ := source_finite_atoms_exists_of_measure_ne_zero _ δ f hN
    {p | TrialOuterViolation R X p} (fun _ h => hactivation.trans_lt h.1) hne
  have ht := source_weighted_inclusive_tail X δ f (fun a => (hδ.trans (hf a)).le) hW
    (f a) (hf a)
  have hc : 0 < (R.innerThreshold : ℝ) := Rat.cast_pos.mpr hcompatible.1
  have hL : 2 < R.order → 3 * (R.innerThreshold : ℝ) ≤ 7 * (R.plateau : ℝ) := by
    intro ho
    exact_mod_cast hcompatible.2.1 ho
  have hown :
      if R.order ≤ 2 then 2 * (cap : ℝ) ≤ (R.outerThreshold : ℝ)
      else (cap : ℝ) + min ((3 / 2) * (cap : ℝ)) (R.plateau : ℝ) ≤ (R.outerThreshold : ℝ) ∧
        3 * (cap : ℝ) - min ((3 / 2) * (cap : ℝ)) (R.plateau : ℝ) ≤ (R.innerThreshold : ℝ) := by
    have h := hcompatible.2.2
    by_cases ho : R.order ≤ 2
    · simp only [ho, ite_true] at h ⊢
      exact_mod_cast h
    · simp only [ho, ite_false, ite_true] at h ⊢
      constructor
      · have hreal := (Rat.cast_le (K := ℝ)).mpr h.1
        simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_min, Rat.cast_div,
          Rat.cast_ofNat] using hreal
      · have hreal := (Rat.cast_le (K := ℝ)).mpr h.2
        simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_min, Rat.cast_div,
          Rat.cast_ofNat] using hreal
  refine ⟨hcore, a, ha.1, ?_⟩
  apply trialSource_balanced_failure_of_offender f a 0 R cap
    (fun b => hδ.trans (hf b)) (hcap a) hc hL hown
  simpa only [TrialOuterViolation, trialOuterAllocation, trialInnerAllocation, ht,
    ite_true] using ha.2

theorem source_inner_failure_offender {d : ℕ} {ι : Type} [Fintype ι]
    (R : TrialSourceRow) (X : Fin d → FiniteMeasure ℝ) (δ : ℝ) (cap : ℚ)
    (f : ι → ℝ) (hδ : 0 < δ) (hactivation : δ ≤ (R.activation : ℝ))
    (hf : ∀ a, δ < f a) (hcap : ∀ a, f a ≤ (cap : ℝ))
    (hN : (trialSourceCountMeasure X).restrict (Set.Ioi δ) = ∑ a : ι, Measure.dirac (f a))
    (hW : (trialWeightedMeasure X).restrict (Set.Ioi δ) =
      ∑ a : ι, ENNReal.ofReal (f a) • Measure.dirac (f a))
    (hcompatible : TrialSourceCapCompatible false R cap)
    (hfailure : ¬ TrialInnerRowAllowed R X) :
    R.order ≠ 1 ∧ (R.innerCore : ℝ) < trialTotalMass X ∧
      ∃ a : ι, (R.activation : ℝ) < f a ∧
        2 ≤ (Finset.univ.filter (fun b : ι => f a ≤ f b)).card ∧
        (R.innerThreshold : ℝ) <
          (∑ b ∈ Finset.univ.filter (fun b : ι => f a ≤ f b), f b) +
            ((trialSourceEffectiveOrder R : ℝ) - 1) * f a := by
  have horder : R.order ≠ 1 := fun h => hfailure (Or.inl h)
  have hcore : (R.innerCore : ℝ) < trialTotalMass X :=
    lt_of_not_ge (fun h => hfailure (Or.inr (Or.inl h)))
  have hne : trialSourceCountMeasure X {p | TrialInnerViolation R X p} ≠ 0 :=
    fun h => hfailure (Or.inr (Or.inr h))
  obtain ⟨a, ha⟩ := source_finite_atoms_exists_of_measure_ne_zero _ δ f hN
    {p | TrialInnerViolation R X p} (fun _ h => hactivation.trans_lt h.1) hne
  have ht := source_weighted_inclusive_tail X δ f (fun a => (hδ.trans (hf a)).le) hW
    (f a) (hf a)
  have hc : 0 < (R.innerThreshold : ℝ) := Rat.cast_pos.mpr hcompatible.1
  have hL : 2 < R.order → 3 * (R.innerThreshold : ℝ) ≤ 7 * (R.plateau : ℝ) := by
    intro ho
    exact_mod_cast hcompatible.2.1 ho
  have hown :
      if R.order ≤ 2 then 2 * (cap : ℝ) ≤ (R.innerThreshold : ℝ)
      else (cap : ℝ) + (3 * (cap : ℝ) - min ((3 / 2) * (cap : ℝ)) (R.plateau : ℝ)) ≤
        (R.innerThreshold : ℝ) ∧
        min ((3 / 2) * (cap : ℝ)) (R.plateau : ℝ) ≤ (R.outerThreshold : ℝ) := by
    have h := hcompatible.2.2
    by_cases ho : R.order ≤ 2
    · simp only [ho, Bool.false_eq_true, ite_false, ite_true] at h ⊢
      exact_mod_cast h
    · simp only [ho, Bool.false_eq_true, ite_false] at h ⊢
      constructor
      · have hreal := (Rat.cast_le (K := ℝ)).mpr h.1
        simpa only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_min, Rat.cast_div,
          Rat.cast_ofNat] using hreal
      · have hreal := (Rat.cast_le (K := ℝ)).mpr h.2
        simpa only [Rat.cast_mul, Rat.cast_min, Rat.cast_div, Rat.cast_ofNat] using hreal
  refine ⟨horder, hcore, a, ha.1, ?_⟩
  apply trialSource_balanced_failure_of_offender f a 1 R cap
    (fun b => hδ.trans (hf b)) (hcap a) hc hL hown
  simpa only [TrialInnerViolation, trialOuterAllocation, trialInnerAllocation, ht,
    ite_false, show (1 : Fin 3) ≠ 0 from by decide] using ha.2

theorem trialSource_low_of_linear_offender {d : ℕ} {ι : Type*} [Fintype ι]
    (c : TrialSourceCoverData) (X : Fin d → FiniteMeasure ℝ)
    (hkind : c.kind = .low) (hm : (1 : ℝ) ≤ (c.order : ℝ))
    (hθ : (0 : ℝ) ≤ (c.slope : ℝ)) (hupper : (c.high : ℝ) ≤ (c.witnessUpper : ℝ))
    (δ : ℝ) (f : ι → ℝ)
    (hN : (trialSourceCountMeasure X).restrict (Set.Ioi δ) = ∑ a : ι, Measure.dirac (f a))
    (hlo : δ ≤ (c.low : ℝ)) (a : ι)
    (ha : f a ∈ Set.Ioc (c.low : ℝ) (c.high : ℝ))
    (hbad : (c.threshold : ℝ) < (trialWeightedMeasure X).real (Set.Ici (f a)) +
      ((c.order : ℝ) - 1) * f a) : 1 ≤ trialSourceUnmasked c X := by
  apply trialSource_low_unmasked_one_le c X hkind hθ
  · rw [source_finite_atoms_measureReal_sum _ δ f hN _ (fun _ h => hlo.trans_lt h.1)]
    have hi := Finset.single_le_sum (s := (Finset.univ : Finset ι))
      (f := fun b => Set.indicator (Set.Ioc (c.low : ℝ) (c.high : ℝ))
        (fun _ => (1 : ℝ)) (f b))
      (fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _) (Finset.mem_univ a)
    simpa only [Set.indicator_of_mem (s := Set.Ioc (c.low : ℝ) (c.high : ℝ)) ha] using hi
  · have hmass := trialSource_tail_small_mass_le c X (f a) ha.1
    have hp := mul_le_mul_of_nonneg_left (ha.2.trans hupper) (sub_nonneg.mpr hm)
    nlinarith only [hbad, hmass, hp]

theorem trialWeightedMeasure_tail_le_total {d : ℕ} (X : Fin d → FiniteMeasure ℝ) (p : ℝ) :
    (trialWeightedMeasure X).real (Set.Ici p) ≤ trialTotalMass X := by
  let : IsFiniteMeasure (trialWeightedMeasure X) := by unfold trialWeightedMeasure; infer_instance
  rw [← trialWeightedMeasure_real_univ X]
  exact measureReal_mono (Set.subset_univ _)

#print axioms source_finite_mark_le_cap
#print axioms trialSource_tail_small_mass_le
#print axioms source_weighted_inclusive_tail
#print axioms source_outer_failure_offender
#print axioms source_inner_failure_offender
#print axioms trialSource_low_of_linear_offender

end PrimeGap182
