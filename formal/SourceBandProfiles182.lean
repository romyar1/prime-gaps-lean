import SourceBandFinite182
import SourceBandRadial182

/-! The literal trial and shell masks depend on finitely many atom caps and
the coordinate masses.  These are the exact reference functions used by
the band approximation, including the component caps of the 726-term trial. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace PrimeGap182

def trialReferenceCaps : Finset ℚ :=
  (trialLargestCap :: ((List.ofFn trialComponentCap) ++
    ((List.ofFn trialShells).flatten.map TrialShell.cap))).toFinset

theorem trialReferenceCaps_data :
    trialLargestCap ∈ trialReferenceCaps ∧
    (∀ c : Fin 3, trialComponentCap c ∈ trialReferenceCaps) ∧
    (∀ role : Fin 5, ∀ s ∈ trialShells role, s.cap ∈ trialReferenceCaps) ∧
    (∀ q ∈ trialReferenceCaps, trialMesh < q) := by
  decide +kernel

def TrialMassCapInvariant {d : ℕ} (C : Finset ℚ)
    (f : (Fin d → FiniteMeasure ℝ) → ℝ) : Prop :=
  ∀ X Y, (∀ i, (X i).mass = (Y i).mass) →
    (∀ i q, q ∈ C → ((X i : Measure ℝ) (Set.Ioi (q : ℝ)) = 0 ↔
      (Y i : Measure ℝ) (Set.Ioi (q : ℝ)) = 0)) → f X = f Y

theorem trialShellDomain_mass_caps {d : ℕ} (role : Fin 5)
    (X Y : Fin d → FiniteMeasure ℝ) (hmass : ∀ i, (X i).mass = (Y i).mass)
    (hcaps : ∀ i q, q ∈ trialReferenceCaps →
      ((X i : Measure ℝ) (Set.Ioi (q : ℝ)) = 0 ↔ (Y i : Measure ℝ) (Set.Ioi (q : ℝ)) = 0)) :
    TrialShellDomain role X ↔ TrialShellDomain role Y := by
  have hc (i : Fin d) : trialCellIndex (X i) = trialCellIndex (Y i) := by
    simp only [trialCellIndex, hmass]
  have hs (s : TrialShell) (hs : s ∈ trialShells role) : TrialShellAllowed s X ↔ TrialShellAllowed s Y := by
    have hh := fun i => hcaps i s.cap (trialReferenceCaps_data.2.2.1 role s hs)
    simp only [TrialShellAllowed, hc, TrialCapAllowed, hh]
  simp only [TrialShellDomain]
  exact exists_congr fun i => hs _ (List.get_mem _ i)

theorem trialMask_massCapInvariant {d : ℕ} (role : Fin 5) :
    TrialMassCapInvariant trialReferenceCaps (@trialMask d role) := by
  intro X Y hm hc
  unfold trialMask
  rw [trialShellDomain_mass_caps role X Y hm hc]

theorem trialStepFunction_massCapInvariant :
    TrialMassCapInvariant trialReferenceCaps trialStepFunction := by
  intro X Y hm hc
  have hcell (i : Fin 39) : trialCellIndex (X i) = trialCellIndex (Y i) := by
    simp only [trialCellIndex, hm]
  have hcomp (c : Fin 3) : trialComponentMask c X = trialComponentMask c Y := by
    have hh := fun i => hc i (trialComponentCap c) (trialReferenceCaps_data.2.1 c)
    simp only [trialComponentMask, TrialCapAllowed, hh]
    exact (ite_eq_ite _ _ _).mpr True.intro
  simp only [trialStepFunction, trialMask_massCapInvariant 0 X Y hm hc, hcomp, hcell]

theorem trialShellDomain_cell_support {d : ℕ} (role : Fin 5)
    (X : Fin d → FiniteMeasure ℝ) (h : TrialShellDomain role X) :
    (∑ i, trialCellIndex (X i)) < trialCellCount := by
  obtain ⟨j, hj⟩ := h
  exact hj.1

def TrialRowsAllowed {d : ℕ} (outer inner : List TrialSourceRow)
    (X : Fin d → FiniteMeasure ℝ) : Prop :=
  (∀ R ∈ outer, TrialOuterRowAllowed R X) ∧ (∀ R ∈ inner, TrialInnerRowAllowed R X)

def trialRowsProjection {d : ℕ} (outer inner : List TrialSourceRow)
    (f : (Fin d → FiniteMeasure ℝ) → ℝ) (X : Fin d → FiniteMeasure ℝ) : ℝ := by
  classical
  exact if TrialRowsAllowed outer inner X then f X else 0

theorem measurableSet_trialRowsAllowed {d : ℕ} (outer inner : List TrialSourceRow)
    (ho : ∀ R ∈ outer, (0 : ℚ) < R.activation)
    (hi : ∀ R ∈ inner, (0 : ℚ) < R.activation) :
    MeasurableSet {X : Fin d → FiniteMeasure ℝ | TrialRowsAllowed outer inner X} :=
  (measurableSet_trialRows outer _ (fun R hR => measurableSet_trialOuterRowAllowed R (ho R hR))).inter
    (measurableSet_trialRows inner _ (fun R hR => measurableSet_trialInnerRowAllowed R (hi R hR)))

theorem measurable_trialRowsProjection {d : ℕ} (outer inner : List TrialSourceRow)
    (ho : ∀ R ∈ outer, (0 : ℚ) < R.activation)
    (hi : ∀ R ∈ inner, (0 : ℚ) < R.activation)
    {f : (Fin d → FiniteMeasure ℝ) → ℝ} (hf : Measurable f) :
    Measurable (trialRowsProjection outer inner f) :=
  Measurable.ite (measurableSet_trialRowsAllowed outer inner ho hi) hf measurable_const

theorem trialRowsProjection_norm_le {d : ℕ} (outer inner : List TrialSourceRow)
    (f : (Fin d → FiniteMeasure ℝ) → ℝ) (X : Fin d → FiniteMeasure ℝ) :
    ‖trialRowsProjection outer inner f X‖ ≤ ‖f X‖ := by
  unfold trialRowsProjection
  split_ifs <;> simp

theorem trialRowsProjection_step :
    trialRowsProjection (trialOldSourceRows ++ trialNewSourceRows) [] trialStepFunction =
      trialSourceStepFunction := by
  funext X
  by_cases hF : trialStepFunction X = 0
  · simp only [trialRowsProjection, hF, ite_self, trialSourceStepFunction, mul_zero]
  · have hs := trialStepFunction_support X hF
    have he : TrialActualOuter X ↔
        TrialRowsAllowed (trialOldSourceRows ++ trialNewSourceRows) [] X := by
      simp [TrialActualOuter, TrialRowsAllowed, hs.1, hs.2.2.2]
    unfold trialRowsProjection trialSourceStepFunction trialActualOuterMask
    by_cases hr : TrialRowsAllowed (trialOldSourceRows ++ trialNewSourceRows) [] X
    · rw [ite_eq_left hr, ite_eq_left (he.mpr hr), one_mul]
    · rw [ite_eq_right hr, ite_eq_right (fun h => hr (he.mp h)), zero_mul]

theorem trialRowsProjection_base :
    trialRowsProjection [] (trialOldSourceRows ++ trialNewSourceRows) (trialMask 1) =
      trialActualBaseMask := by
  funext X
  by_cases hs : TrialShellDomain 1 X
  · have hc := (trialShellDomain_cap 1 hs).2
    have he : TrialActualBase X ↔
        TrialRowsAllowed [] (trialOldSourceRows ++ trialNewSourceRows) X := by
      simp [TrialActualBase, TrialRowsAllowed, hs, hc]
    unfold trialRowsProjection trialMask trialActualBaseMask
    by_cases hr : TrialRowsAllowed [] (trialOldSourceRows ++ trialNewSourceRows) X
    · rw [ite_eq_left hr, ite_eq_left hs, ite_eq_left (he.mpr hr)]
    · rw [ite_eq_right hr, ite_eq_right (fun h => hr (he.mp h))]
  · simp [trialRowsProjection, trialMask, hs, trialActualBaseMask, TrialActualBase]

theorem trialRowsProjection_enlarged :
    trialRowsProjection [] trialNewSourceRows (trialMask 2) = trialActualEnlargedMask := by
  funext X
  by_cases hs : TrialShellDomain 2 X
  · have hc := (trialShellDomain_cap 2 hs).2
    have he : TrialActualEnlarged X ↔ TrialRowsAllowed [] trialNewSourceRows X := by
      simp [TrialActualEnlarged, TrialRowsAllowed, hs, hc]
    unfold trialRowsProjection trialMask trialActualEnlargedMask
    by_cases hr : TrialRowsAllowed [] trialNewSourceRows X
    · rw [ite_eq_left hr, ite_eq_left hs, ite_eq_left (he.mpr hr)]
    · rw [ite_eq_right hr, ite_eq_right (fun h => hr (he.mp h))]
  · simp [trialRowsProjection, trialMask, hs, trialActualEnlargedMask, TrialActualEnlarged]

theorem trialRowsProjection_subtraction :
    trialRowsProjection [trialSubtractionSourceRow] [] (trialMask 3) = trialActualSubtractionMask := by
  funext X
  by_cases hs : TrialShellDomain 3 X
  · have hc := (trialShellDomain_cap 3 hs).2
    have ht := trialSubtraction_shell_total X hs
    have he : TrialActualSubtraction X ↔ TrialRowsAllowed [trialSubtractionSourceRow] [] X := by
      simp [TrialActualSubtraction, TrialRowsAllowed, hs, hc, ht]
    unfold trialRowsProjection trialMask trialActualSubtractionMask
    by_cases hr : TrialRowsAllowed [trialSubtractionSourceRow] [] X
    · rw [ite_eq_left hr, ite_eq_left hs, ite_eq_left (he.mpr hr)]
    · rw [ite_eq_right hr, ite_eq_right (fun h => hr (he.mp h))]
  · simp [trialRowsProjection, trialMask, hs, trialActualSubtractionMask, TrialActualSubtraction]

#print axioms trialReferenceCaps_data
#print axioms trialStepFunction_massCapInvariant
#print axioms trialRowsProjection_step
#print axioms trialRowsProjection_subtraction

end PrimeGap182
