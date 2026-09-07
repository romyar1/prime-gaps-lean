import TrialCapTransfer182

/-! Boundary nullity for the actual 182 fragment law and strictly inward
versions of its source rows. The baseline's general affine-mark null theorem
is transferred through an exact physical cap restriction. The row arguments
use each row's own plateau, including flat plateau faces. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

theorem trialPhysicalMeasure_le_baseline : trialPhysicalMeasure ≤ PrimeGap186.trialPhysicalMeasure := by
  have hc : (trialLargestCap : ℝ) ≤ (PrimeGap186.trialLargestCap : ℝ) := by
    norm_num [trialLargestCap, PrimeGap186.trialLargestCap, PrimeGap186.trialMesh]
  rw [← trialAmbient_cap_restrict _ hc]
  exact Measure.restrict_le_self

theorem trialProductMeasure_le_baseline (d : ℕ) :
    trialProductMeasure d ≤ Measure.pi (fun _ : Fin d => PrimeGap186.trialPhysicalMeasure) := by
  have hc : (trialLargestCap : ℝ) ≤ (PrimeGap186.trialLargestCap : ℝ) := by
    norm_num [trialLargestCap, PrimeGap186.trialLargestCap, PrimeGap186.trialMesh]
  rw [← (trialAmbient_pi_cap_restrict _ hc d).2]
  exact Measure.restrict_le_self

theorem trial_count_tail_affine_boundary_null (d : ℕ) (δ a b : ℝ)
    (hδ : 0 < δ) (ha : 0 ≤ a) :
    ∀ᵐ X ∂trialProductMeasure d, trialSourceCountMeasure X
      {p : ℝ | δ < p ∧ (trialWeightedMeasure X).real (Set.Ici p) + a * p = b} = 0 :=
  (ae_mono (trialProductMeasure_le_baseline d))
    (PrimeGap186.trialPhysical_count_tail_affine_boundary_null d δ a b hδ ha)

theorem trial_fixed_mark_null (b : ℝ) :
    ∀ᵐ X : FiniteMeasure ℝ ∂trialPhysicalMeasure, (X : Measure ℝ) {b} = 0 :=
  (ae_mono trialPhysicalMeasure_le_baseline) (PrimeGap186.trialPhysical_fixed_mark_null b)

theorem trial_count_fixed_mark_null (d : ℕ) (b : ℝ) :
    ∀ᵐ X ∂trialProductMeasure d, trialSourceCountMeasure X {b} = 0 :=
  (ae_mono (trialProductMeasure_le_baseline d)) (PrimeGap186.trialPhysical_count_fixed_mark_null d b)

theorem trial_total_mass_ne (d : ℕ) (b : ℝ) :
    ∀ᵐ X ∂trialProductMeasure (d + 1), trialTotalMass X ≠ b :=
  (ae_mono (trialProductMeasure_le_baseline (d + 1))) (PrimeGap186.trialPhysical_total_mass_ne d b)

def TrialOuterRowOpen (R : TrialSourceRow) (u p : ℝ) : Prop :=
  if R.order ≤ 2 then u + p < (R.outerThreshold : ℝ)
  else u + trialOuterAllocation R p < (R.outerThreshold : ℝ) ∧
    trialInnerAllocation R p < (R.innerThreshold : ℝ)

def TrialInnerRowOpen (R : TrialSourceRow) (u p : ℝ) : Prop :=
  if R.order ≤ 2 then u + p < (R.innerThreshold : ℝ)
  else u + trialInnerAllocation R p < (R.innerThreshold : ℝ) ∧
    (trialOuterAllocation R p < (R.outerThreshold : ℝ) ∨ (R.plateau : ℝ) ≤ (R.outerThreshold : ℝ))

theorem isOpen_trialOuterRowOpen (R : TrialSourceRow) (u : ℝ) :
    IsOpen {p : ℝ | TrialOuterRowOpen R u p} := by
  have hφ : Continuous (trialOuterAllocation R) := by unfold trialOuterAllocation; fun_prop
  have hψ : Continuous (trialInnerAllocation R) := by
    unfold trialInnerAllocation trialOuterAllocation
    fun_prop
  unfold TrialOuterRowOpen
  split_ifs
  · exact isOpen_lt (continuous_const.add continuous_id) continuous_const
  · exact (isOpen_lt (continuous_const.add hφ) continuous_const).inter
      (isOpen_lt hψ continuous_const)

theorem isOpen_trialInnerRowOpen (R : TrialSourceRow) (u : ℝ) :
    IsOpen {p : ℝ | TrialInnerRowOpen R u p} := by
  have hφ : Continuous (trialOuterAllocation R) := by unfold trialOuterAllocation; fun_prop
  have hψ : Continuous (trialInnerAllocation R) := by
    unfold trialInnerAllocation trialOuterAllocation
    fun_prop
  unfold TrialInnerRowOpen
  split_ifs
  · exact isOpen_lt (continuous_const.add continuous_id) continuous_const
  · exact (isOpen_lt (continuous_const.add hψ) continuous_const).inter
      ((isOpen_lt hφ continuous_const).union isOpen_const)

theorem trialOuterRowAllowed_ae_strict (d : ℕ) (R : TrialSourceRow)
    (hA : (0 : ℝ) < (R.activation : ℝ)) :
    ∀ᵐ X ∂trialProductMeasure (d + 1), TrialOuterRowAllowed R X →
      trialTotalMass X < (R.outerCore : ℝ) ∨
        trialSourceCountMeasure X {p : ℝ | (R.activation : ℝ) < p ∧
          ¬ TrialOuterRowOpen R ((trialWeightedMeasure X).real (Set.Ici p)) p} = 0 := by
  filter_upwards [trial_total_mass_ne d (R.outerCore : ℝ),
    trial_count_tail_affine_boundary_null (d + 1) (R.activation : ℝ) 1
      (R.outerThreshold : ℝ) hA (by norm_num),
    trial_count_tail_affine_boundary_null (d + 1) (R.activation : ℝ) (3 / 2)
      (R.outerThreshold : ℝ) hA (by norm_num),
    trial_count_tail_affine_boundary_null (d + 1) (R.activation : ℝ) 0
      ((R.outerThreshold : ℝ) - (R.plateau : ℝ)) hA (by norm_num),
    trial_count_fixed_mark_null (d + 1) ((R.innerThreshold : ℝ) / (3 / 2)),
    trial_count_fixed_mark_null (d + 1) (((R.innerThreshold : ℝ) + (R.plateau : ℝ)) / 3)]
      with X hcore hbase hleft hright hψleft hψright hallowed
  rcases hallowed with hcorele | hbad
  · exact Or.inl (lt_of_le_of_ne hcorele hcore)
  · right
    unfold TrialOuterRowOpen
    change trialSourceCountMeasure X {p : ℝ | (R.activation : ℝ) < p ∧
      (if R.order ≤ 2 then (R.outerThreshold : ℝ) < (trialWeightedMeasure X).real (Set.Ici p) + p
      else (R.outerThreshold : ℝ) < (trialWeightedMeasure X).real (Set.Ici p) + trialOuterAllocation R p ∨
        (R.innerThreshold : ℝ) < trialInnerAllocation R p)} = 0 at hbad
    by_cases horder : R.order ≤ 2
    · simp only [horder, ite_true] at hbad ⊢
      have heq : trialSourceCountMeasure X {p : ℝ | (R.activation : ℝ) < p ∧
          (trialWeightedMeasure X).real (Set.Ici p) + p = (R.outerThreshold : ℝ)} = 0 := by
        simpa only [one_mul] using hbase
      apply measure_mono_null _ (measure_union_null hbad heq)
      intro p hp
      by_cases hgt : (R.outerThreshold : ℝ) < (trialWeightedMeasure X).real (Set.Ici p) + p
      · exact Or.inl ⟨hp.1, hgt⟩
      · exact Or.inr ⟨hp.1, le_antisymm (le_of_not_gt hgt) (le_of_not_gt hp.2)⟩
    · simp only [horder, ite_false] at hbad ⊢
      apply measure_mono_null _
        (measure_union_null hbad (measure_union_null hleft
          (measure_union_null hright (measure_union_null hψleft hψright))))
      intro p hp
      by_cases hgt : (R.outerThreshold : ℝ) < (trialWeightedMeasure X).real (Set.Ici p) +
          trialOuterAllocation R p ∨ (R.innerThreshold : ℝ) < trialInnerAllocation R p
      · exact Or.inl ⟨hp.1, hgt⟩
      · have hle := not_or.mp hgt
        rcases not_and_or.mp hp.2 with hfirst | hsecond
        · have heq : (trialWeightedMeasure X).real (Set.Ici p) + trialOuterAllocation R p =
              (R.outerThreshold : ℝ) := le_antisymm (le_of_not_gt hle.1) (le_of_not_gt hfirst)
          by_cases hmin : (3 / 2 : ℝ) * p ≤ (R.plateau : ℝ)
          · exact Or.inr (Or.inl ⟨hp.1, by
              simpa only [trialOuterAllocation, min_eq_left hmin] using heq⟩)
          · refine Or.inr (Or.inr (Or.inl ⟨hp.1, ?_⟩))
            rw [trialOuterAllocation, min_eq_right (lt_of_not_ge hmin).le] at heq
            simp only [zero_mul, add_zero]
            linarith only [heq]
        · have heq : trialInnerAllocation R p = (R.innerThreshold : ℝ) :=
            le_antisymm (le_of_not_gt hle.2) (le_of_not_gt hsecond)
          by_cases hmin : (3 / 2 : ℝ) * p ≤ (R.plateau : ℝ)
          · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
            apply (eq_div_iff (by norm_num : (3 / 2 : ℝ) ≠ 0)).2
            rw [trialInnerAllocation, trialOuterAllocation, min_eq_left hmin] at heq
            linarith only [heq]
          · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
            apply (eq_div_iff (by norm_num : (3 : ℝ) ≠ 0)).2
            rw [trialInnerAllocation, trialOuterAllocation, min_eq_right (lt_of_not_ge hmin).le] at heq
            linarith only [heq]

theorem trialInnerRowAllowed_ae_strict (d : ℕ) (R : TrialSourceRow)
    (hA : (0 : ℝ) < (R.activation : ℝ)) :
    ∀ᵐ X ∂trialProductMeasure (d + 1), TrialInnerRowAllowed R X →
      R.order = 1 ∨ trialTotalMass X < (R.innerCore : ℝ) ∨
        trialSourceCountMeasure X {p : ℝ | (R.activation : ℝ) < p ∧
          ¬ TrialInnerRowOpen R ((trialWeightedMeasure X).real (Set.Ici p)) p} = 0 := by
  filter_upwards [trial_total_mass_ne d (R.innerCore : ℝ),
    trial_count_tail_affine_boundary_null (d + 1) (R.activation : ℝ) 1
      (R.innerThreshold : ℝ) hA (by norm_num),
    trial_count_tail_affine_boundary_null (d + 1) (R.activation : ℝ) (3 / 2)
      (R.innerThreshold : ℝ) hA (by norm_num),
    trial_count_tail_affine_boundary_null (d + 1) (R.activation : ℝ) 3
      ((R.innerThreshold : ℝ) + (R.plateau : ℝ)) hA (by norm_num),
    trial_count_fixed_mark_null (d + 1) ((R.outerThreshold : ℝ) / (3 / 2))]
      with X hcore hbase hleft hright hφ hallowed
  rcases hallowed with horderOne | hcorele | hbad
  · exact Or.inl horderOne
  · exact Or.inr (Or.inl (lt_of_le_of_ne hcorele hcore))
  · right; right
    unfold TrialInnerRowOpen
    change trialSourceCountMeasure X {p : ℝ | (R.activation : ℝ) < p ∧
      (if R.order ≤ 2 then (R.innerThreshold : ℝ) < (trialWeightedMeasure X).real (Set.Ici p) + p
      else (R.innerThreshold : ℝ) < (trialWeightedMeasure X).real (Set.Ici p) + trialInnerAllocation R p ∨
        (R.outerThreshold : ℝ) < trialOuterAllocation R p)} = 0 at hbad
    by_cases horder : R.order ≤ 2
    · simp only [horder, ite_true] at hbad ⊢
      have heq : trialSourceCountMeasure X {p : ℝ | (R.activation : ℝ) < p ∧
          (trialWeightedMeasure X).real (Set.Ici p) + p = (R.innerThreshold : ℝ)} = 0 := by
        simpa only [one_mul] using hbase
      apply measure_mono_null _ (measure_union_null hbad heq)
      intro p hp
      by_cases hgt : (R.innerThreshold : ℝ) < (trialWeightedMeasure X).real (Set.Ici p) + p
      · exact Or.inl ⟨hp.1, hgt⟩
      · exact Or.inr ⟨hp.1, le_antisymm (le_of_not_gt hgt) (le_of_not_gt hp.2)⟩
    · simp only [horder, ite_false] at hbad ⊢
      apply measure_mono_null _
        (measure_union_null hbad (measure_union_null hleft (measure_union_null hright hφ)))
      intro p hp
      by_cases hgt : (R.innerThreshold : ℝ) < (trialWeightedMeasure X).real (Set.Ici p) +
          trialInnerAllocation R p ∨ (R.outerThreshold : ℝ) < trialOuterAllocation R p
      · exact Or.inl ⟨hp.1, hgt⟩
      · have hle := not_or.mp hgt
        rcases not_and_or.mp hp.2 with hfirst | hsecond
        · have heq : (trialWeightedMeasure X).real (Set.Ici p) + trialInnerAllocation R p =
              (R.innerThreshold : ℝ) := le_antisymm (le_of_not_gt hle.1) (le_of_not_gt hfirst)
          by_cases hmin : (3 / 2 : ℝ) * p ≤ (R.plateau : ℝ)
          · refine Or.inr (Or.inl ⟨hp.1, ?_⟩)
            rw [trialInnerAllocation, trialOuterAllocation, min_eq_left hmin] at heq
            linarith only [heq]
          · refine Or.inr (Or.inr (Or.inl ⟨hp.1, ?_⟩))
            rw [trialInnerAllocation, trialOuterAllocation, min_eq_right (lt_of_not_ge hmin).le] at heq
            linarith only [heq]
        · have hnot := not_or.mp hsecond
          have heq : trialOuterAllocation R p = (R.outerThreshold : ℝ) :=
            le_antisymm (le_of_not_gt hle.2) (le_of_not_gt hnot.1)
          have hmin : (3 / 2 : ℝ) * p ≤ (R.plateau : ℝ) := by
            by_contra hmin
            rw [trialOuterAllocation, min_eq_right (lt_of_not_ge hmin).le] at heq
            exact hnot.2 heq.le
          refine Or.inr (Or.inr (Or.inr ?_))
          apply (eq_div_iff (by norm_num : (3 / 2 : ℝ) ≠ 0)).2
          rw [trialOuterAllocation, min_eq_left hmin] at heq
          linarith only [heq]

#print axioms trial_count_tail_affine_boundary_null
#print axioms trialOuterRowAllowed_ae_strict
#print axioms trialInnerRowAllowed_ae_strict

end PrimeGap182
