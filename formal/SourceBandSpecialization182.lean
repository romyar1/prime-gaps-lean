import SourceBandExhaustion182
import SourceHybridReference182

/-! Simultaneous band-exhaustion interfaces for the literal signed trial
and the three actual source masks. All generic hypotheses are discharged
from the data and actual fragment functions. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace PrimeGap182

def trialApproxOuterRows : List TrialSourceRow := trialOldSourceRows ++ trialNewSourceRows
def trialApproxFaceOuterRows (b : Fin 3) : List TrialSourceRow :=
  if b = 2 then [trialSubtractionSourceRow] else []
def trialApproxFaceInnerRows (b : Fin 3) : List TrialSourceRow :=
  if b = 0 then trialApproxOuterRows else if b = 1 then trialNewSourceRows else []
def trialApproxFaceRadius : Fin 3 → ℚ :=
  ![trialBaseRadius, trialEnlargedRadius, trialSubtractionRadius]
def trialApproxFaceRole : Fin 3 → Fin 5 := ![1, 2, 3]
def trialApproxFaceReference (b : Fin 3) : (Fin 38 → FiniteMeasure ℝ) → ℝ :=
  trialMask (trialApproxFaceRole b)
def trialApproxFaceActual : Fin 3 → (Fin 38 → FiniteMeasure ℝ) → ℝ :=
  ![trialActualBaseMask, trialActualEnlargedMask, trialActualSubtractionMask]

theorem trialApproxRows_seed :
    (∀ R ∈ trialApproxOuterRows, trialMesh < R.activation) ∧
    (∀ b : Fin 3, ∀ R ∈ trialApproxFaceOuterRows b, trialMesh < R.activation) ∧
    (∀ b : Fin 3, ∀ R ∈ trialApproxFaceInnerRows b, trialMesh < R.activation) := by
  decide +kernel

theorem trialApproxFaceRadius_data : ∀ b : Fin 3,
    ∀ g ∈ trialGridShells (trialApproxFaceRole b),
      (g.upper : ℚ) * trialMesh ≤ trialApproxFaceRadius b := by
  decide +kernel

theorem trialApproxFace_projection (b : Fin 3) :
    trialRowsProjection (trialApproxFaceOuterRows b) (trialApproxFaceInnerRows b)
      (trialApproxFaceReference b) = trialApproxFaceActual b := by
  fin_cases b
  · exact trialRowsProjection_base
  · exact trialRowsProjection_enlarged
  · exact trialRowsProjection_subtraction

theorem measurable_trialApproxFaceActual (b : Fin 3) : Measurable (trialApproxFaceActual b) := by
  fin_cases b
  · exact measurable_trialActualBaseMask
  · exact measurable_trialActualEnlargedMask
  · exact measurable_trialActualSubtractionMask

theorem trialApproxFaceActual_bits (b : Fin 3) (X : Fin 38 → FiniteMeasure ℝ) :
    trialApproxFaceActual b X = 0 ∨ trialApproxFaceActual b X = 1 := by
  fin_cases b
  · exact (trialActualFaceMasks_nested X).1
  · exact (trialActualFaceMasks_nested X).2.1
  · exact (trialActualFaceMasks_nested X).2.2.1

def trialSourceBandDomain {m : ℕ} (a : Fin (m + 2) → ℝ) :
    Set (Fin 39 → Fin (m + 1) → ℝ) :=
  {v | TrialBandSourceDomain trialApproxOuterRows [] (trialRadius : ℝ) a v}

def trialFaceBandDomain {m : ℕ} (b : Fin 3) (a : Fin (m + 2) → ℝ) :
    Set (Fin 38 → Fin (m + 1) → ℝ) :=
  {v | TrialBandSourceDomain (trialApproxFaceOuterRows b) (trialApproxFaceInnerRows b)
    (trialApproxFaceRadius b : ℝ) a v}

def trialFaceBandReferenceSet {m : ℕ} (b : Fin 3) (a : Fin (m + 2) → ℝ) :
    Set (Fin 38 → Fin (m + 1) → ℝ) :=
  trialFaceBandDomain b a ∩
    {v | trialApproxFaceReference b (fun i => PrimeGap186.trialBandRepresentative a (v i)) = 1}

theorem trialSourceBandDomain_open {m : ℕ} (a : Fin (m + 2) → ℝ) :
    IsOpen (trialSourceBandDomain a) := isOpen_trialBandSourceDomain _ _ _ a

theorem trialFaceBandDomain_open {m : ℕ} (b : Fin 3) (a : Fin (m + 2) → ℝ) :
    IsOpen (trialFaceBandDomain b a) := isOpen_trialBandSourceDomain _ _ _ a

theorem trialFaceBandReferenceSet_measurable {m : ℕ} (b : Fin 3) (a : Fin (m + 2) → ℝ) :
    MeasurableSet (trialFaceBandReferenceSet b a) :=
  (trialFaceBandDomain_open b a).measurableSet.inter
    (measurableSet_eq_fun ((measurable_trialMask (trialApproxFaceRole b)).comp
      (measurable_pi_lambda _ fun i =>
        (PrimeGap186.trialBandRepresentative_measurable a).comp (measurable_pi_apply i))) measurable_const)

theorem trialFaceBandReferenceSet_indicator {m : ℕ} (b : Fin 3) (a : Fin (m + 2) → ℝ)
    (v : Fin 38 → Fin (m + 1) → ℝ) :
    (trialFaceBandReferenceSet b a).indicator (fun _ => (1 : ℝ)) v =
      (trialFaceBandDomain b a).indicator
        (fun v => trialApproxFaceReference b (fun i => PrimeGap186.trialBandRepresentative a (v i))) v := by
  by_cases hU : v ∈ trialFaceBandDomain b a
  · rcases trialMask_values (trialApproxFaceRole b)
      (fun i => PrimeGap186.trialBandRepresentative a (v i)) with hm | hm
    · have hA : v ∉ trialFaceBandReferenceSet b a := by
        intro h
        change trialApproxFaceReference b _ = 0 at hm
        exact zero_ne_one (hm.symm.trans h.2)
      rw [Set.indicator_of_notMem hA, Set.indicator_of_mem hU]
      exact hm.symm
    · have hA : v ∈ trialFaceBandReferenceSet b a := ⟨hU, hm⟩
      rw [Set.indicator_of_mem hA, Set.indicator_of_mem hU]
      exact hm.symm
  · have hA : v ∉ trialFaceBandReferenceSet b a := fun h => hU h.1
    rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hU]

theorem trial_actual_source_band_exhaustion182
    (κ : ℝ) (hκ : (trialLargestCap : ℝ) ≤ κ)
    (m : ℕ → ℕ) (a : (N : ℕ) → Fin (m N + 2) → ℝ)
    (hgeom : ∀ N, StrictMono (a N) ∧ a N 0 = 0 ∧
      a N (0 : Fin (m N + 1)).succ = (trialMesh : ℝ) ∧ a N (Fin.last (m N + 1)) = κ)
    (hmesh : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      ∀ j : Fin (m N + 1), j ≠ 0 → a N j.succ - a N j.castSucc < ε) :
    Tendsto (fun N => ∫ X : Fin 39 → FiniteMeasure ℝ,
      ((trialSourceBandDomain (a N)).indicator
        (fun v => trialStepFunction (fun i => PrimeGap186.trialBandRepresentative (a N) (v i)))
          (fun i => PrimeGap186.fragmentBandMasses (a N) (X i)) - trialSourceStepFunction X) ^ 2
        ∂trialProductMeasure 39) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := trial_regular_step.bounded
  have h := trial_source_band_exhaustion 38 trialApproxOuterRows [] trialApproxRows_seed.1
    (by simp) (trialRadius : ℝ) trialStepFunction measurable_trialStepFunction C hC
    trialStepFunction_massCapInvariant
    (fun X hX => ⟨trialShellDomain_cell_support 0 X (trialStepFunction_support X hX).1,
      (trialStepFunction_support X hX).2.1⟩) κ hκ m a hgeom hmesh
  simpa only [trialSourceBandDomain, trialApproxOuterRows, trialRowsProjection_step] using h

theorem trial_actual_face_band_exhaustion182
    (κ : ℝ) (hκ : (trialLargestCap : ℝ) ≤ κ)
    (m : ℕ → ℕ) (a : (N : ℕ) → Fin (m N + 2) → ℝ)
    (hgeom : ∀ N, StrictMono (a N) ∧ a N 0 = 0 ∧
      a N (0 : Fin (m N + 1)).succ = (trialMesh : ℝ) ∧ a N (Fin.last (m N + 1)) = κ)
    (hmesh : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      ∀ j : Fin (m N + 1), j ≠ 0 → a N j.succ - a N j.castSucc < ε) (b : Fin 3) :
    Tendsto (fun N => ∫ X : Fin 38 → FiniteMeasure ℝ,
      ((trialFaceBandReferenceSet b (a N)).indicator (fun _ => (1 : ℝ))
          (fun i => PrimeGap186.fragmentBandMasses (a N) (X i)) - trialApproxFaceActual b X) ^ 2
        ∂trialProductMeasure 38) atTop (𝓝 0) := by
  have hb (X : Fin 38 → FiniteMeasure ℝ) : ‖trialApproxFaceReference b X‖ ≤ 1 := by
    rcases trialMask_values (trialApproxFaceRole b) X with h | h <;> simp only [trialApproxFaceReference, h,
      norm_zero, norm_one, zero_le_one, le_refl]
  have hs (X : Fin 38 → FiniteMeasure ℝ) (hX : trialApproxFaceReference b X ≠ 0) :
      (∑ i, trialCellIndex (X i)) < trialCellCount ∧ trialTotalMass X ≤ (trialApproxFaceRadius b : ℝ) := by
    have hShell : TrialShellDomain (trialApproxFaceRole b) X := by
      by_contra hn
      exact hX (by simp [trialApproxFaceReference, trialMask, hn])
    exact ⟨trialShellDomain_cell_support _ X hShell,
      sourceShell_total_le _ _ (trialApproxFaceRadius_data b) X hShell⟩
  have h := trial_source_band_exhaustion 37 (trialApproxFaceOuterRows b) (trialApproxFaceInnerRows b)
    (trialApproxRows_seed.2.1 b) (trialApproxRows_seed.2.2 b) (trialApproxFaceRadius b : ℝ)
    (trialApproxFaceReference b) (measurable_trialMask _) 1 hb (trialMask_massCapInvariant _) hs
    κ hκ m a hgeom hmesh
  simpa only [trialFaceBandReferenceSet_indicator, trialFaceBandDomain, trialApproxFace_projection] using h

#print axioms trial_actual_source_band_exhaustion182
#print axioms trial_actual_face_band_exhaustion182

end PrimeGap182
