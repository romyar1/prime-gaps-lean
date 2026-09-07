import SourceBandSpecialization182

/-! Arithmetic meaning of the actual source-count predicates.  Nullity of
the forbidden counting event is converted to inequalities for every
activated prime, then to owner bounds for every divisor. -/

noncomputable section
open MeasureTheory PrimeGap186
open scoped BigOperators NNReal

namespace PrimeGap182

def trialOwnerPlateau (row : TrialSourceRow) : ℝ≥0 := (row.plateau : ℝ).toNNReal

def TrialOuterOwnerBound (row : TrialSourceRow) (R : ℝ) (D : ℕ) : Prop :=
  if row.order ≤ 2 then
    logSize R D ≤ (row.outerCore : ℝ) ∨
      (primeFragmentOwner id R (row.activation : ℝ) D : ℝ) ≤ (row.outerThreshold : ℝ)
  else logSize R D ≤ (row.outerCore : ℝ) ∨
    (primeFragmentOwner (physicalOuterOwner (trialOwnerPlateau row)) R
      (row.activation : ℝ) D : ℝ) ≤ (row.outerThreshold : ℝ) ∧
    (physicalInnerOwner (trialOwnerPlateau row)
      (maxActivatedPrimeFragment R (row.activation : ℝ) D) : ℝ) ≤ (row.innerThreshold : ℝ)

def TrialInnerOwnerBound (row : TrialSourceRow) (R : ℝ) (D : ℕ) : Prop :=
  row.order = 1 ∨ if row.order ≤ 2 then
    logSize R D ≤ (row.innerCore : ℝ) ∨
      (primeFragmentOwner id R (row.activation : ℝ) D : ℝ) ≤ (row.innerThreshold : ℝ)
  else logSize R D ≤ (row.innerCore : ℝ) ∨
    (primeFragmentOwner (physicalInnerOwner (trialOwnerPlateau row)) R
      (row.activation : ℝ) D : ℝ) ≤ (row.innerThreshold : ℝ) ∧
    (physicalOuterOwner (trialOwnerPlateau row)
      (maxActivatedPrimeFragment R (row.activation : ℝ) D) : ℝ) ≤ (row.outerThreshold : ℝ)

theorem trialOuterRowAllowed_prime_arithmetic {d : ℕ} (row : TrialSourceRow)
    (R : ℝ) (hR : 1 < R) (r : Fin d → ℕ) (hr : Squarefree (∏ i, r i))
    (hrow : TrialOuterRowAllowed row (fun i => primeLogConfiguration R (r i))) :
    logSize R (∏ i, r i) ≤ (row.outerCore : ℝ) ∨
      ∀ p ∈ activatedPrimeFactors R (row.activation : ℝ) (∏ i, r i),
        if row.order ≤ 2 then
          (primeFragmentSuffix R (∏ i, r i) p : ℝ) + 2 * logSize R p ≤
            (row.outerThreshold : ℝ)
        else
          (primeFragmentSuffix R (∏ i, r i) p : ℝ) + logSize R p +
              trialOuterAllocation row (logSize R p) ≤ (row.outerThreshold : ℝ) ∧
            trialInnerAllocation row (logSize R p) ≤ (row.innerThreshold : ℝ) := by
  classical
  have hsum : trialWeightedMeasure (fun i => primeLogConfiguration R (r i)) =
      (primeLogConfiguration R (∏ i, r i) : Measure ℝ) := by
    rw [primeLogConfiguration_prod R Finset.univ r hr, FiniteMeasure.toMeasure_sum]
    rfl
  rcases hrow with hcore | hzero
  · exact Or.inl (by simpa only [trialTotalMass, primeLogConfiguration_total_mass d R hR r hr]
      using hcore)
  right
  intro p hp
  have hpD := (Finset.mem_filter.mp hp).1
  have hpact : (row.activation : ℝ) < logSize R p :=
    (Real.lt_logb_iff_rpow_lt hR
      (by exact_mod_cast Nat.pos_of_mem_primeFactors hpD)).mpr (Finset.mem_filter.mp hp).2
  have hnot := physicalSourceCountMeasure_notMem_of_zero d R hR r hr _ hzero p hpD
  change ¬ TrialOuterViolation row (fun i => primeLogConfiguration R (r i)) (logSize R p) at hnot
  unfold TrialOuterViolation at hnot
  rw [hsum, primeLogConfiguration_Ici_prime R hR _ p hpD] at hnot
  by_cases ho : row.order ≤ 2
  · rw [ite_eq_left ho] at hnot ⊢
    simp only [not_and, hpact, true_implies, not_lt] at hnot
    linarith
  · rw [ite_eq_right ho] at hnot ⊢
    simpa only [not_and, hpact, true_implies, not_or, not_lt] using hnot

theorem trialInnerRowAllowed_prime_arithmetic {d : ℕ} (row : TrialSourceRow)
    (R : ℝ) (hR : 1 < R) (r : Fin d → ℕ) (hr : Squarefree (∏ i, r i))
    (hrow : TrialInnerRowAllowed row (fun i => primeLogConfiguration R (r i))) :
    row.order = 1 ∨ logSize R (∏ i, r i) ≤ (row.innerCore : ℝ) ∨
      ∀ p ∈ activatedPrimeFactors R (row.activation : ℝ) (∏ i, r i),
        if row.order ≤ 2 then
          (primeFragmentSuffix R (∏ i, r i) p : ℝ) + 2 * logSize R p ≤
            (row.innerThreshold : ℝ)
        else
          (primeFragmentSuffix R (∏ i, r i) p : ℝ) + logSize R p +
              trialInnerAllocation row (logSize R p) ≤ (row.innerThreshold : ℝ) ∧
            trialOuterAllocation row (logSize R p) ≤ (row.outerThreshold : ℝ) := by
  classical
  have hsum : trialWeightedMeasure (fun i => primeLogConfiguration R (r i)) =
      (primeLogConfiguration R (∏ i, r i) : Measure ℝ) := by
    rw [primeLogConfiguration_prod R Finset.univ r hr, FiniteMeasure.toMeasure_sum]
    rfl
  rcases hrow with hone | hcore | hzero
  · exact Or.inl hone
  · exact Or.inr (Or.inl (by
      simpa only [trialTotalMass, primeLogConfiguration_total_mass d R hR r hr] using hcore))
  right; right
  intro p hp
  have hpD := (Finset.mem_filter.mp hp).1
  have hpact : (row.activation : ℝ) < logSize R p :=
    (Real.lt_logb_iff_rpow_lt hR
      (by exact_mod_cast Nat.pos_of_mem_primeFactors hpD)).mpr (Finset.mem_filter.mp hp).2
  have hnot := physicalSourceCountMeasure_notMem_of_zero d R hR r hr _ hzero p hpD
  change ¬ TrialInnerViolation row (fun i => primeLogConfiguration R (r i)) (logSize R p) at hnot
  unfold TrialInnerViolation at hnot
  rw [hsum, primeLogConfiguration_Ici_prime R hR _ p hpD] at hnot
  by_cases ho : row.order ≤ 2
  · rw [ite_eq_left ho] at hnot ⊢
    simp only [not_and, hpact, true_implies, not_lt] at hnot
    linarith
  · rw [ite_eq_right ho] at hnot ⊢
    simpa only [not_and, hpact, true_implies, not_or, not_lt] using hnot

theorem trialOuterRowAllowed_divisor_owner {d : ℕ} (row : TrialSourceRow)
    (hA : 0 ≤ row.outerThreshold) (hC : 0 ≤ row.innerThreshold) (hL : 0 ≤ row.plateau)
    (R : ℝ) (hR : 1 < R) (r : Fin d → ℕ) (hr : Squarefree (∏ i, r i))
    (hrow : TrialOuterRowAllowed row (fun i => primeLogConfiguration R (r i)))
    (D : ℕ) (hD : D ∣ ∏ i, r i) : TrialOuterOwnerBound row R D := by
  classical
  have hDs : Squarefree D := hr.squarefree_of_dvd hD
  have hDpos := Nat.pos_of_ne_zero hDs.ne_zero
  have hprodpos := Nat.pos_of_ne_zero hr.ne_zero
  have hraw := trialOuterRowAllowed_prime_arithmetic row R hR r hr hrow
  have hAr : 0 ≤ (row.outerThreshold : ℝ) := by exact_mod_cast hA
  have hCr : 0 ≤ (row.innerThreshold : ℝ) := by exact_mod_cast hC
  have hLr : (trialOwnerPlateau row : ℝ) = (row.plateau : ℝ) :=
    Real.coe_toNNReal _ (by exact_mod_cast hL)
  unfold TrialOuterOwnerBound
  by_cases hord : row.order ≤ 2
  · rw [ite_eq_left hord]
    have hsrc : logSize R (∏ i, r i) ≤ (row.outerCore : ℝ) ∨
        (primeFragmentOwner id R (row.activation : ℝ) (∏ i, r i) : ℝ) ≤
            (row.outerThreshold : ℝ) ∧
          (((fun _ : ℝ≥0 => (0 : ℝ≥0))
            (maxActivatedPrimeFragment R (row.activation : ℝ) (∏ i, r i))) : ℝ) ≤ 0 := by
      rcases hraw with hcore | hpoint
      · exact Or.inl hcore
      right
      apply physicalSource_owner_sup_bounds R _ _ id (fun _ => 0) rfl _ 0 hAr le_rfl
      intro p hp
      have h := hpoint p hp
      rw [ite_eq_left hord] at h
      have hu := coe_logFragment R hR (Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      refine ⟨?_, le_rfl⟩
      simp only [id_eq, NNReal.coe_add, hu]
      linarith
    exact (sourceSupport_dvd hR hD hDpos hprodpos id (fun _ => 0) monotone_const hsrc).imp_right And.left
  · rw [ite_eq_right hord]
    have hsrc : logSize R (∏ i, r i) ≤ (row.outerCore : ℝ) ∨
        (primeFragmentOwner (physicalOuterOwner (trialOwnerPlateau row)) R
          (row.activation : ℝ) (∏ i, r i) : ℝ) ≤ (row.outerThreshold : ℝ) ∧
        (physicalInnerOwner (trialOwnerPlateau row)
          (maxActivatedPrimeFragment R (row.activation : ℝ) (∏ i, r i)) : ℝ) ≤
            (row.innerThreshold : ℝ) := by
      rcases hraw with hcore | hpoint
      · exact Or.inl hcore
      right
      apply physicalSource_owner_sup_bounds R _ _ (physicalOuterOwner (trialOwnerPlateau row))
        (physicalInnerOwner (trialOwnerPlateau row)) (by simp [physicalInnerOwner]) _ _ hAr hCr
      intro p hp
      have h := hpoint p hp
      rw [ite_eq_right hord] at h
      have hu := coe_logFragment R hR (Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      have hf := physicalSource_owner_real (trialOwnerPlateau row) (logFragment R p)
      simpa only [NNReal.coe_add, hf.1, hf.2, hu, hLr, trialOuterAllocation,
        trialInnerAllocation] using h
    exact sourceSupport_dvd hR hD hDpos hprodpos (physicalOuterOwner (trialOwnerPlateau row))
      (physicalInnerOwner (trialOwnerPlateau row)) (physicalInner_mono _) hsrc

theorem trialInnerRowAllowed_divisor_owner {d : ℕ} (row : TrialSourceRow)
    (hA : 0 ≤ row.outerThreshold) (hC : 0 ≤ row.innerThreshold) (hL : 0 ≤ row.plateau)
    (R : ℝ) (hR : 1 < R) (r : Fin d → ℕ) (hr : Squarefree (∏ i, r i))
    (hrow : TrialInnerRowAllowed row (fun i => primeLogConfiguration R (r i)))
    (D : ℕ) (hD : D ∣ ∏ i, r i) : TrialInnerOwnerBound row R D := by
  classical
  have hDs : Squarefree D := hr.squarefree_of_dvd hD
  have hDpos := Nat.pos_of_ne_zero hDs.ne_zero
  have hprodpos := Nat.pos_of_ne_zero hr.ne_zero
  have hraw := trialInnerRowAllowed_prime_arithmetic row R hR r hr hrow
  have hAr : 0 ≤ (row.outerThreshold : ℝ) := by exact_mod_cast hA
  have hCr : 0 ≤ (row.innerThreshold : ℝ) := by exact_mod_cast hC
  have hLr : (trialOwnerPlateau row : ℝ) = (row.plateau : ℝ) :=
    Real.coe_toNNReal _ (by exact_mod_cast hL)
  unfold TrialInnerOwnerBound
  rcases hraw with hone | hraw
  · exact Or.inl hone
  right
  by_cases hord : row.order ≤ 2
  · rw [ite_eq_left hord]
    have hsrc : logSize R (∏ i, r i) ≤ (row.innerCore : ℝ) ∨
        (primeFragmentOwner id R (row.activation : ℝ) (∏ i, r i) : ℝ) ≤
            (row.innerThreshold : ℝ) ∧
          (((fun _ : ℝ≥0 => (0 : ℝ≥0))
            (maxActivatedPrimeFragment R (row.activation : ℝ) (∏ i, r i))) : ℝ) ≤ 0 := by
      rcases hraw with hcore | hpoint
      · exact Or.inl hcore
      right
      apply physicalSource_owner_sup_bounds R _ _ id (fun _ => 0) rfl _ 0 hCr le_rfl
      intro p hp
      have h := hpoint p hp
      rw [ite_eq_left hord] at h
      have hu := coe_logFragment R hR (Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      refine ⟨?_, le_rfl⟩
      simp only [id_eq, NNReal.coe_add, hu]
      linarith
    exact (sourceSupport_dvd hR hD hDpos hprodpos id (fun _ => 0) monotone_const hsrc).imp_right And.left
  · rw [ite_eq_right hord]
    have hsrc : logSize R (∏ i, r i) ≤ (row.innerCore : ℝ) ∨
        (primeFragmentOwner (physicalInnerOwner (trialOwnerPlateau row)) R
          (row.activation : ℝ) (∏ i, r i) : ℝ) ≤ (row.innerThreshold : ℝ) ∧
        (physicalOuterOwner (trialOwnerPlateau row)
          (maxActivatedPrimeFragment R (row.activation : ℝ) (∏ i, r i)) : ℝ) ≤
            (row.outerThreshold : ℝ) := by
      rcases hraw with hcore | hpoint
      · exact Or.inl hcore
      right
      apply physicalSource_owner_sup_bounds R _ _ (physicalInnerOwner (trialOwnerPlateau row))
        (physicalOuterOwner (trialOwnerPlateau row)) (by simp [physicalOuterOwner]) _ _ hCr hAr
      intro p hp
      have h := hpoint p hp
      rw [ite_eq_right hord] at h
      have hu := coe_logFragment R hR (Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      have hf := physicalSource_owner_real (trialOwnerPlateau row) (logFragment R p)
      simpa only [NNReal.coe_add, hf.1, hf.2, hu, hLr, trialOuterAllocation,
        trialInnerAllocation] using h
    exact sourceSupport_dvd hR hD hDpos hprodpos (physicalInnerOwner (trialOwnerPlateau row))
      (physicalOuterOwner (trialOwnerPlateau row)) (physicalOuter_mono _) hsrc

#print axioms trialOuterRowAllowed_prime_arithmetic
#print axioms trialInnerRowAllowed_prime_arithmetic
#print axioms trialOuterRowAllowed_divisor_owner
#print axioms trialInnerRowAllowed_divisor_owner

end PrimeGap182
