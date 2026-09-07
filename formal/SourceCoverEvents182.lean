import SourceFiniteAtoms182

/-! Measurable source events used for restoration.

The outer event keeps the owner mass reservation on which the sharper
coordinate count is valid. Its indicator is dominated by the literal
positive count kernel. Actual source failure covering is proved separately;
it is not part of these definitions or a supplied axiom. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace PrimeGap182

def TrialOuterCoverEvent (j : Fin 60) (X : Fin 39 → FiniteMeasure ℝ) : Prop :=
  TrialSourceDomain (trialOuterCertificates j).cover X ∧
    1 ≤ trialSourceUnmasked (trialOuterCertificates j).cover X ∧
      TrialSourceOwnerEvent (trialOuterCertificates j) X

def TrialInnerCoverEvent (j : Fin 137) (Y : Fin 38 → FiniteMeasure ℝ) : Prop :=
  TrialSourceDomain (trialInnerCertificates j).cover Y ∧
    1 ≤ trialSourceUnmasked (trialInnerCertificates j).cover Y

def trialOuterCoverIndicator (j : Fin 60) (X : Fin 39 → FiniteMeasure ℝ) : ℝ :=
  Set.indicator {Z | TrialOuterCoverEvent j Z} (fun _ => 1) X

def trialInnerCoverIndicator (j : Fin 137) (Y : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  Set.indicator {Z | TrialInnerCoverEvent j Z} (fun _ => 1) Y

theorem measurableSet_trialOuterCoverEvent (j : Fin 60) :
    MeasurableSet {X : Fin 39 → FiniteMeasure ℝ | TrialOuterCoverEvent j X} := by
  exact (measurableSet_trialSourceDomain _).inter
    ((measurableSet_le measurable_const
      (trialSourceUnmasked_regular _ (trialOuterCover_regular j) 39 1 (by norm_num)).1).inter
        (measurableSet_trialSourceOwnerEvent _))

theorem measurableSet_trialInnerCoverEvent (j : Fin 137) :
    MeasurableSet {Y : Fin 38 → FiniteMeasure ℝ | TrialInnerCoverEvent j Y} := by
  exact (measurableSet_trialSourceDomain _).inter
    (measurableSet_le measurable_const
      (trialSourceUnmasked_regular _ (trialInnerCover_regular j) 38 1 (by norm_num)).1)

theorem measurable_trialOuterCoverIndicator (j : Fin 60) :
    Measurable (trialOuterCoverIndicator j) :=
  measurable_const.indicator (measurableSet_trialOuterCoverEvent j)

theorem measurable_trialInnerCoverIndicator (j : Fin 137) :
    Measurable (trialInnerCoverIndicator j) :=
  measurable_const.indicator (measurableSet_trialInnerCoverEvent j)

theorem trialOuterCoverIndicator_le_kernel (j : Fin 60)
    (X : Fin 39 → FiniteMeasure ℝ) :
    0 ≤ trialOuterCoverIndicator j X ∧
      trialOuterCoverIndicator j X ≤ trialSourceKernel (trialOuterCertificates j).cover X := by
  by_cases hX : TrialOuterCoverEvent j X
  · have hI : trialOuterCoverIndicator j X = 1 :=
      Set.indicator_of_mem (s := {Z | TrialOuterCoverEvent j Z}) hX _
    rw [hI]
    refine ⟨zero_le_one, ?_⟩
    simpa only [trialSourceKernel, hX.1, ite_true] using hX.2.1
  · have hI : trialOuterCoverIndicator j X = 0 :=
      Set.indicator_of_notMem (s := {Z | TrialOuterCoverEvent j Z}) hX _
    rw [hI]
    exact ⟨le_rfl, (trialSourceKernel_regular _ (trialOuterCover_regular j) 39).2.choose_spec.2 X |>.1⟩

theorem trialInnerCoverIndicator_le_kernel (j : Fin 137)
    (Y : Fin 38 → FiniteMeasure ℝ) :
    0 ≤ trialInnerCoverIndicator j Y ∧
      trialInnerCoverIndicator j Y ≤ trialSourceKernel (trialInnerCertificates j).cover Y := by
  by_cases hY : TrialInnerCoverEvent j Y
  · have hI : trialInnerCoverIndicator j Y = 1 :=
      Set.indicator_of_mem (s := {Z | TrialInnerCoverEvent j Z}) hY _
    rw [hI]
    refine ⟨zero_le_one, ?_⟩
    simpa only [trialSourceKernel, hY.1, ite_true] using hY.2
  · have hI : trialInnerCoverIndicator j Y = 0 :=
      Set.indicator_of_notMem (s := {Z | TrialInnerCoverEvent j Z}) hY _
    rw [hI]
    exact ⟨le_rfl, (trialSourceKernel_regular _ (trialInnerCover_regular j) 38).2.choose_spec.2 Y |>.1⟩

theorem trialCapPullback_square_on_outer_event (j : Fin 60)
    (X : Fin 39 → FiniteMeasure ℝ) (hX : TrialOuterCoverEvent j X) (V : Fin 39 → ℝ) :
    (∑ i : Fin 39, trialCapFaceMultiplier (i.removeNth X) * V i) ^ 2 ≤
      trialSourceCountMultiplier j X *
        ∑ i : Fin 39, trialSourceFaceWeight (i.removeNth X) * V i ^ 2 :=
  trialCapPullback_square_le_source_local j X hX.1 hX.2.2 V

#print axioms measurableSet_trialOuterCoverEvent
#print axioms trialOuterCoverIndicator_le_kernel
#print axioms trialInnerCoverIndicator_le_kernel
#print axioms trialCapPullback_square_on_outer_event

end PrimeGap182
