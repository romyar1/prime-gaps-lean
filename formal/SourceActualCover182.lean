import SourceFiniteCover182

/-! The true-event cover under the actual scaled fragment law. Every
finite-atom hypothesis is discharged by the Poisson-fragment construction. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace PrimeGap182

theorem source_finite_configuration_tails (d : ℕ)
    (Y : Fin d → FiniteMeasure ℝ) (n : Fin d → ℕ) (x : (i : Fin d) → Fin (n i) → ℝ)
    (hY : ∀ i, (Y i).restrict (Set.Ioc (0 : ℝ) (trialMesh : ℝ)) = Y i)
    (hx : ∀ i a, (trialMesh : ℝ) < x i a) :
    let X := fun i => Y i + PrimeGap186.weightedEmpirical (n i) (x i)
    (∀ i, (X i : Measure ℝ).restrict (Set.Ioi (trialMesh : ℝ)) =
      ∑ a : Fin (n i), ENNReal.ofReal (x i a) • Measure.dirac (x i a)) ∧
    (trialSourceCountMeasure X).restrict (Set.Ioi (trialMesh : ℝ)) =
      (∑ a : (i : Fin d) × Fin (n i), Measure.dirac (x a.1 a.2)) ∧
    (trialWeightedMeasure X).restrict (Set.Ioi (trialMesh : ℝ)) =
      ∑ a : (i : Fin d) × Fin (n i),
        ENNReal.ofReal (x a.1 a.2) • Measure.dirac (x a.1 a.2) := by
  intro X
  have hδ : (0 : ℝ) < (trialMesh : ℝ) := Rat.cast_pos.mpr trialMesh_pos
  have h := PrimeGap186.trial_finite_tail_mass_and_count d (trialMesh : ℝ) hδ Y n x hY hx
  refine ⟨fun i => PrimeGap186.trial_finite_tail_coordinate_mass _ _ _ _ (hY i) (hx i), h.2, ?_⟩
  simpa only [trialWeightedMeasure, FiniteMeasure.toMeasure_sum] using h.1

theorem measurableSet_trialActualOuter :
    MeasurableSet {X : Fin 39 → FiniteMeasure ℝ | TrialActualOuter X} := by
  have heq : {X : Fin 39 → FiniteMeasure ℝ | TrialActualOuter X} =
      trialActualOuterMask ⁻¹' ({1} : Set ℝ) := by
    ext X
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, trialActualOuterMask]
    split_ifs <;> simp_all
  rw [heq]
  exact (measurableSet_singleton (1 : ℝ)).preimage measurable_trialActualOuterMask

theorem measurableSet_trialOuterCover_exists :
    MeasurableSet {X : Fin 39 → FiniteMeasure ℝ | ∃ j : Fin 60, TrialOuterCoverEvent j X} := by
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion measurableSet_trialOuterCoverEvent

theorem measurableSet_trialInnerCover_role (role : Fin 5) :
    MeasurableSet {X : Fin 38 → FiniteMeasure ℝ |
      ∃ j : Fin 137, trialSourceInnerRole j = role ∧ TrialInnerCoverEvent j X} := by
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro j
  by_cases hj : trialSourceInnerRole j = role
  · simpa only [hj, true_and] using measurableSet_trialInnerCoverEvent j
  · simp only [hj, false_and, Set.ofPred_false, MeasurableSet.empty]

def TrialLadderInnerRowsAllowed (side : Fin 2) (X : Fin 38 → FiniteMeasure ℝ) : Prop :=
  ∀ R ∈ (if side = 0 then trialOldSourceRows else trialNewSourceRows), TrialInnerRowAllowed R X

theorem measurableSet_trialLadderInnerRows (side : Fin 2) :
    MeasurableSet {X : Fin 38 → FiniteMeasure ℝ | TrialLadderInnerRowsAllowed side X} := by
  apply measurableSet_trialRows
  intro R hR
  apply measurableSet_trialInnerRowAllowed
  by_cases hs : side = 0
  · exact trialSourceRows_activation_pos.1 R (by simpa only [hs, ite_true] using hR)
  · exact trialSourceRows_activation_pos.2 R (by simpa only [hs, ite_false] using hR)

theorem trialActualOuter_covered_ae :
    ∀ᵐ X ∂trialProductMeasure 39, TrialShellDomain 0 X →
      TrialActualOuter X ∨ ∃ j : Fin 60, TrialOuterCoverEvent j X := by
  apply trialProductMeasure_ae_finite_tail_elim (trialMesh : ℝ)
    (Rat.cast_pos.mpr trialMesh_pos) 39
  · simpa only [imp_iff_not_or, Set.ofPred_or, Set.compl_def, Set.mem_ofPred_eq] using
      (measurableSet_trialShellDomain 0).compl.union
        (measurableSet_trialActualOuter.union measurableSet_trialOuterCover_exists)
  · intro Y n x hY hx hShell
    let X := fun i => Y i + PrimeGap186.weightedEmpirical (n i) (x i)
    by_cases hrows : ∀ R ∈ trialOldSourceRows ++ trialNewSourceRows, TrialOuterRowAllowed R X
    · exact Or.inl ⟨hShell, (trialShellDomain_cap 0 hShell).2, hrows⟩
    · push Not at hrows
      obtain ⟨R, hR, hf⟩ := hrows
      rw [← trialRowReferences_exact] at hR
      obtain ⟨ref, href, rfl⟩ := List.mem_map.mp hR
      obtain ⟨htail, hN, hW⟩ := source_finite_configuration_tails 39 Y n x hY (fun i a => (hx i a).1)
      exact Or.inr (source_outer_row_covered_finite ref href X n x (fun i a => (hx i a).1)
        htail hN hW hShell hf)

theorem trialLadderInner_covered_ae (side : Fin 2) :
    ∀ᵐ X ∂trialProductMeasure 38, TrialShellDomain (if side = 0 then 1 else 2) X →
      TrialLadderInnerRowsAllowed side X ∨
        ∃ j : Fin 137, trialSourceInnerRole j = (if side = 0 then 1 else 2) ∧
          TrialInnerCoverEvent j X := by
  apply trialProductMeasure_ae_finite_tail_elim (trialMesh : ℝ)
    (Rat.cast_pos.mpr trialMesh_pos) 38
  · simpa only [imp_iff_not_or, Set.ofPred_or, Set.compl_def, Set.mem_ofPred_eq] using
      (measurableSet_trialShellDomain (if side = 0 then 1 else 2)).compl.union
        ((measurableSet_trialLadderInnerRows side).union
          (measurableSet_trialInnerCover_role (if side = 0 then 1 else 2)))
  · intro Y n x hY hx hShell
    let X := fun i => Y i + PrimeGap186.weightedEmpirical (n i) (x i)
    by_cases hrows : TrialLadderInnerRowsAllowed side X
    · exact Or.inl hrows
    · change ¬ ∀ R ∈ (if side = 0 then trialOldSourceRows else trialNewSourceRows),
        TrialInnerRowAllowed R X at hrows
      push Not at hrows
      obtain ⟨R, hR, hf⟩ := hrows
      rw [← trialLadderReferences_exact side] at hR
      obtain ⟨ref, href, rfl⟩ := List.mem_map.mp hR
      obtain ⟨htail, hN, hW⟩ := source_finite_configuration_tails 38 Y n x hY (fun i a => (hx i a).1)
      exact Or.inr (source_inner_row_covered_finite side ref href X n x (fun i a => (hx i a).1)
        htail hN hW hShell hf)

theorem trialSubtractionRow_covered_ae :
    ∀ᵐ X ∂trialProductMeasure 38, TrialShellDomain 3 X →
      TrialOuterRowAllowed trialSubtractionSourceRow X ∨
        ∃ j : Fin 137, trialSourceInnerRole j = 3 ∧ TrialInnerCoverEvent j X := by
  apply trialProductMeasure_ae_finite_tail_elim (trialMesh : ℝ)
    (Rat.cast_pos.mpr trialMesh_pos) 38
  · simpa only [imp_iff_not_or, Set.ofPred_or, Set.compl_def, Set.mem_ofPred_eq] using
      (measurableSet_trialShellDomain 3).compl.union
        ((measurableSet_trialOuterRowAllowed trialSubtractionSourceRow (by decide +kernel)).union
          (measurableSet_trialInnerCover_role 3))
  · intro Y n x hY hx hShell
    let X := fun i => Y i + PrimeGap186.weightedEmpirical (n i) (x i)
    by_cases hrow : TrialOuterRowAllowed trialSubtractionSourceRow X
    · exact Or.inl hrow
    · obtain ⟨htail, hN, hW⟩ := source_finite_configuration_tails 38 Y n x hY (fun i a => (hx i a).1)
      exact Or.inr (source_subtraction_row_covered_finite X n x (fun i a => (hx i a).1)
        htail hN hW hShell hrow)

#print axioms trialActualOuter_covered_ae
#print axioms trialLadderInner_covered_ae
#print axioms trialSubtractionRow_covered_ae

end PrimeGap182
