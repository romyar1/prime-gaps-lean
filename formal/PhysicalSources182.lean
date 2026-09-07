import PhysicalTrial182

/-!
Actual source predicates for the fixed 39-coordinate trial. These are
conditions on the weighted fragment measures and their inclusive tails.
In particular, order-three rows use their own recorded owner plateau.
The subtraction core is B₀−T₁; B₀−S_C belongs to the complementary source.

This module does not assume a dense-divisibility transfer or a source cover.
Those arithmetic/cover theorems are separate obligations.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace PrimeGap182

def trialWeightedMeasure {d : ℕ} (X : Fin d → FiniteMeasure ℝ) : Measure ℝ :=
  ∑ i, (X i : Measure ℝ)

def trialTotalMass {d : ℕ} (X : Fin d → FiniteMeasure ℝ) : ℝ :=
  ∑ i, ((X i).mass : ℝ)

/-- Division by the positive atom location recovers the fragment counting measure. -/
def trialSourceCountMeasure {d : ℕ} (X : Fin d → FiniteMeasure ℝ) : Measure ℝ :=
  PrimeGap186.physicalSourceCountMeasure X

def trialOuterAllocation (R : TrialSourceRow) (p : ℝ) : ℝ :=
  min ((3 / 2) * p) (R.plateau : ℝ)

def trialInnerAllocation (R : TrialSourceRow) (p : ℝ) : ℝ :=
  3 * p - trialOuterAllocation R p

def TrialOuterViolation {d : ℕ} (R : TrialSourceRow)
    (X : Fin d → FiniteMeasure ℝ) (p : ℝ) : Prop :=
  (R.activation : ℝ) < p ∧
    if R.order ≤ 2 then
      (R.outerThreshold : ℝ) < (trialWeightedMeasure X).real (Set.Ici p) + p
    else
      (R.outerThreshold : ℝ) < (trialWeightedMeasure X).real (Set.Ici p) +
        trialOuterAllocation R p ∨
      (R.innerThreshold : ℝ) < trialInnerAllocation R p

def TrialInnerViolation {d : ℕ} (R : TrialSourceRow)
    (X : Fin d → FiniteMeasure ℝ) (p : ℝ) : Prop :=
  (R.activation : ℝ) < p ∧
    if R.order ≤ 2 then
      (R.innerThreshold : ℝ) < (trialWeightedMeasure X).real (Set.Ici p) + p
    else
      (R.innerThreshold : ℝ) < (trialWeightedMeasure X).real (Set.Ici p) +
        trialInnerAllocation R p ∨
      (R.outerThreshold : ℝ) < trialOuterAllocation R p

def TrialOuterRowAllowed {d : ℕ} (R : TrialSourceRow)
    (X : Fin d → FiniteMeasure ℝ) : Prop :=
  trialTotalMass X ≤ (R.outerCore : ℝ) ∨
    trialSourceCountMeasure X {p | TrialOuterViolation R X p} = 0

def TrialInnerRowAllowed {d : ℕ} (R : TrialSourceRow)
    (X : Fin d → FiniteMeasure ℝ) : Prop :=
  R.order = 1 ∨ trialTotalMass X ≤ (R.innerCore : ℝ) ∨
    trialSourceCountMeasure X {p | TrialInnerViolation R X p} = 0

def TrialActualOuter (X : Fin 39 → FiniteMeasure ℝ) : Prop :=
  TrialShellDomain 0 X ∧ TrialCapAllowed trialPrimeCap X ∧
    ∀ R ∈ trialOldSourceRows ++ trialNewSourceRows, TrialOuterRowAllowed R X

def TrialActualBase (Y : Fin 38 → FiniteMeasure ℝ) : Prop :=
  TrialShellDomain 1 Y ∧ TrialCapAllowed trialPrimeCap Y ∧
    ∀ R ∈ trialOldSourceRows ++ trialNewSourceRows, TrialInnerRowAllowed R Y

def TrialActualEnlarged (Y : Fin 38 → FiniteMeasure ℝ) : Prop :=
  TrialShellDomain 2 Y ∧ TrialCapAllowed trialPrimeCap Y ∧
    ∀ R ∈ trialNewSourceRows, TrialInnerRowAllowed R Y

def trialSubtractionSourceRow : TrialSourceRow where
  order := 2
  omega := 14506963516466639465886413077 / 2179640814020907704460000000000
  delta := trialSubtractionActivation * trialRho
  lowerBand := (1 / 2) / trialRho
  upperBand := ((1 / 2) + 2 *
    (14506963516466639465886413077 / 2179640814020907704460000000000)) / trialRho
  activation := trialSubtractionActivation
  outerCore := trialSubtractionCore
  innerCore := (1 / 2) / trialRho - trialSubtractionRadius
  outerThreshold := trialSubtractionCore + trialSubtractionActivation
  innerThreshold := (1 / 2) / trialRho - trialSubtractionRadius + trialSubtractionActivation
  plateau := 0

/-- Only the order-two outer predicate is used; the companion pairing is with L₁. -/
def TrialActualSubtraction (Y : Fin 38 → FiniteMeasure ℝ) : Prop :=
  TrialShellDomain 3 Y ∧ TrialCapAllowed trialPrimeCap Y ∧
    trialTotalMass Y ≤ (trialSubtractionRadius : ℝ) ∧
      TrialOuterRowAllowed trialSubtractionSourceRow Y

def trialActualOuterMask (X : Fin 39 → FiniteMeasure ℝ) : ℝ := by
  classical
  exact if TrialActualOuter X then 1 else 0

def trialActualBaseMask (Y : Fin 38 → FiniteMeasure ℝ) : ℝ := by
  classical
  exact if TrialActualBase Y then 1 else 0

def trialActualEnlargedMask (Y : Fin 38 → FiniteMeasure ℝ) : ℝ := by
  classical
  exact if TrialActualEnlarged Y then 1 else 0

def trialActualSubtractionMask (Y : Fin 38 → FiniteMeasure ℝ) : ℝ := by
  classical
  exact if TrialActualSubtraction Y then 1 else 0

def trialSourceStepFunction (X : Fin 39 → FiniteMeasure ℝ) : ℝ :=
  trialActualOuterMask X * trialStepFunction X

def trialActualFaceMultiplier (Y : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  (trialLambda : ℝ) * trialActualBaseMask Y +
    (1 - (trialLambda : ℝ)) * trialActualEnlargedMask Y +
    trialHybridLoss * trialFaceKernel Y * trialActualSubtractionMask Y -
      trialHybridLoss * trialFaceKernel Y

theorem trialSourceRows_activation_pos :
    (∀ R ∈ trialOldSourceRows, (0 : ℚ) < R.activation) ∧
      (∀ R ∈ trialNewSourceRows, (0 : ℚ) < R.activation) := by
  decide +kernel

theorem measurable_trialWeightedMeasure (d : ℕ) :
    Measurable (trialWeightedMeasure (d := d)) :=
  Finset.measurable_fun_sum _ fun i _ =>
    measurable_subtype_coe.comp (measurable_pi_apply i)

theorem measurable_trialTotalMass (d : ℕ) : Measurable (trialTotalMass (d := d)) :=
  Finset.measurable_sum _ fun i _ =>
    ((Measure.measurable_coe MeasurableSet.univ).comp
      (measurable_subtype_coe.comp (measurable_pi_apply i))).ennreal_toReal

theorem measurable_trialSourceCountMeasure (d : ℕ) :
    Measurable (trialSourceCountMeasure (d := d)) :=
  (PrimeGap186.physicalSourceCountMeasure_regular d).1

theorem measurable_trialInclusiveTail (d : ℕ) :
    Measurable (fun z : (Fin d → FiniteMeasure ℝ) × ℝ =>
      (trialWeightedMeasure z.1).real (Set.Ici z.2)) := by
  let K : ProbabilityTheory.Kernel ((Fin d → FiniteMeasure ℝ) × ℝ) ℝ :=
    ⟨fun z => trialWeightedMeasure z.1, (measurable_trialWeightedMeasure d).comp measurable_fst⟩
  have hK (z : (Fin d → FiniteMeasure ℝ) × ℝ) : IsFiniteMeasure (K z) := by
    change IsFiniteMeasure (∑ i, (z.1 i : Measure ℝ))
    infer_instance
  exact (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left_of_finite
    (κ := K) (measurableSet_le measurable_fst.snd measurable_snd) hK).ennreal_toReal

theorem measurable_trialCountEvaluation (d : ℕ) (a : ℝ) (ha : 0 < a)
    (E : Set ((Fin d → FiniteMeasure ℝ) × ℝ)) (hE : MeasurableSet E)
    (hsub : ∀ X, Prod.mk X ⁻¹' E ⊆ Set.Ioi a) :
    Measurable (fun X => trialSourceCountMeasure X (Prod.mk X ⁻¹' E)) := by
  let N : ProbabilityTheory.Kernel (Fin d → FiniteMeasure ℝ) ℝ :=
    ⟨trialSourceCountMeasure, measurable_trialSourceCountMeasure d⟩
  let K : ProbabilityTheory.Kernel (Fin d → FiniteMeasure ℝ) ℝ :=
    N.restrict (s := Set.Ioi a) measurableSet_Ioi
  have hK (X : Fin d → FiniteMeasure ℝ) : IsFiniteMeasure (K X) :=
    ((PrimeGap186.physicalSourceCountMeasure_regular d).2 a ha X).1
  have hm := ProbabilityTheory.Kernel.measurable_kernel_prodMk_left_of_finite (κ := K) hE hK
  have heq (X : Fin d → FiniteMeasure ℝ) :
      K X (Prod.mk X ⁻¹' E) = trialSourceCountMeasure X (Prod.mk X ⁻¹' E) :=
    Measure.restrict_eq_self _ (hsub X)
  exact (funext heq) ▸ hm

theorem measurable_trialOuterViolationCount {d : ℕ} (R : TrialSourceRow)
    (hR : (0 : ℚ) < R.activation) :
    Measurable (fun X : Fin d → FiniteMeasure ℝ =>
      trialSourceCountMeasure X {p | TrialOuterViolation R X p}) := by
  apply measurable_trialCountEvaluation d (R.activation : ℝ) (Rat.cast_pos.mpr hR)
    {z | TrialOuterViolation R z.1 z.2}
  · have hD : Measurable (fun z : (Fin d → FiniteMeasure ℝ) × ℝ =>
        trialOuterAllocation R z.2) := by unfold trialOuterAllocation; fun_prop
    have hE : Measurable (fun z : (Fin d → FiniteMeasure ℝ) × ℝ =>
        trialInnerAllocation R z.2) := by unfold trialInnerAllocation trialOuterAllocation; fun_prop
    by_cases ho : R.order ≤ 2
    · simp only [TrialOuterViolation, ho, ite_true, Set.ofPred_and]
      exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_const ((measurable_trialInclusiveTail d).add measurable_snd))
    · simp only [TrialOuterViolation, ho, ite_false, Set.ofPred_and, Set.ofPred_or]
      exact (measurableSet_lt measurable_const measurable_snd).inter
        ((measurableSet_lt measurable_const ((measurable_trialInclusiveTail d).add hD)).union
          (measurableSet_lt measurable_const hE))
  · intro X p hp
    exact hp.1

theorem measurable_trialInnerViolationCount {d : ℕ} (R : TrialSourceRow)
    (hR : (0 : ℚ) < R.activation) :
    Measurable (fun X : Fin d → FiniteMeasure ℝ =>
      trialSourceCountMeasure X {p | TrialInnerViolation R X p}) := by
  apply measurable_trialCountEvaluation d (R.activation : ℝ) (Rat.cast_pos.mpr hR)
    {z | TrialInnerViolation R z.1 z.2}
  · have hD : Measurable (fun z : (Fin d → FiniteMeasure ℝ) × ℝ =>
        trialOuterAllocation R z.2) := by unfold trialOuterAllocation; fun_prop
    have hE : Measurable (fun z : (Fin d → FiniteMeasure ℝ) × ℝ =>
        trialInnerAllocation R z.2) := by unfold trialInnerAllocation trialOuterAllocation; fun_prop
    by_cases ho : R.order ≤ 2
    · simp only [TrialInnerViolation, ho, ite_true, Set.ofPred_and]
      exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_const ((measurable_trialInclusiveTail d).add measurable_snd))
    · simp only [TrialInnerViolation, ho, ite_false, Set.ofPred_and, Set.ofPred_or]
      exact (measurableSet_lt measurable_const measurable_snd).inter
        ((measurableSet_lt measurable_const ((measurable_trialInclusiveTail d).add hE)).union
          (measurableSet_lt measurable_const hD))
  · intro X p hp
    exact hp.1

theorem measurableSet_trialOuterRowAllowed {d : ℕ} (R : TrialSourceRow)
    (hR : (0 : ℚ) < R.activation) :
    MeasurableSet {X : Fin d → FiniteMeasure ℝ | TrialOuterRowAllowed R X} :=
  (measurableSet_le (measurable_trialTotalMass d) measurable_const).union
    ((measurableSet_singleton (0 : ℝ≥0∞)).preimage (measurable_trialOuterViolationCount R hR))

theorem measurableSet_trialInnerRowAllowed {d : ℕ} (R : TrialSourceRow)
    (hR : (0 : ℚ) < R.activation) :
    MeasurableSet {X : Fin d → FiniteMeasure ℝ | TrialInnerRowAllowed R X} := by
  classical
  by_cases ho : R.order = 1
  · simpa only [TrialInnerRowAllowed, ho, true_or, Set.ofPred_true] using MeasurableSet.univ
  · simp only [TrialInnerRowAllowed, ho, false_or, Set.ofPred_or]
    exact (measurableSet_le (measurable_trialTotalMass d) measurable_const).union
      ((measurableSet_singleton (0 : ℝ≥0∞)).preimage (measurable_trialInnerViolationCount R hR))

theorem measurableSet_trialRows {d : ℕ} (rows : List TrialSourceRow)
    (P : TrialSourceRow → (Fin d → FiniteMeasure ℝ) → Prop)
    (hP : ∀ R ∈ rows, MeasurableSet {X | P R X}) :
    MeasurableSet {X | ∀ R ∈ rows, P R X} := by
  induction rows with
  | nil => simp
  | cons R rows ih =>
    simpa only [List.forall_mem_cons, Set.ofPred_and] using
      (hP R (by simp)).inter (ih (fun T hT => hP T (by simp [hT])))

theorem measurableSet_trialShellDomain {d : ℕ} (role : Fin 5) :
    MeasurableSet {X : Fin d → FiniteMeasure ℝ | TrialShellDomain role X} := by
  simp only [TrialShellDomain, Set.ofPred_exists]
  exact MeasurableSet.iUnion fun i => measurableSet_trialShellAllowed _

theorem measurable_trialActualOuterMask : Measurable trialActualOuterMask := by
  apply Measurable.ite _ measurable_const measurable_const
  apply (measurableSet_trialShellDomain 0).inter
  apply (measurableSet_trialCapAllowed _).inter
  apply measurableSet_trialRows
  intro R hR
  apply measurableSet_trialOuterRowAllowed R
  rcases List.mem_append.mp hR with hR | hR
  · exact trialSourceRows_activation_pos.1 R hR
  · exact trialSourceRows_activation_pos.2 R hR

theorem measurable_trialActualBaseMask : Measurable trialActualBaseMask := by
  apply Measurable.ite _ measurable_const measurable_const
  apply (measurableSet_trialShellDomain 1).inter
  apply (measurableSet_trialCapAllowed _).inter
  apply measurableSet_trialRows
  intro R hR
  apply measurableSet_trialInnerRowAllowed R
  rcases List.mem_append.mp hR with hR | hR
  · exact trialSourceRows_activation_pos.1 R hR
  · exact trialSourceRows_activation_pos.2 R hR

theorem measurable_trialActualEnlargedMask : Measurable trialActualEnlargedMask := by
  apply Measurable.ite _ measurable_const measurable_const
  apply (measurableSet_trialShellDomain 2).inter
  apply (measurableSet_trialCapAllowed _).inter
  exact measurableSet_trialRows _ _ fun R hR =>
    measurableSet_trialInnerRowAllowed R (trialSourceRows_activation_pos.2 R hR)

theorem measurable_trialActualSubtractionMask : Measurable trialActualSubtractionMask := by
  apply Measurable.ite _ measurable_const measurable_const
  apply (measurableSet_trialShellDomain 3).inter
  apply (measurableSet_trialCapAllowed _).inter
  apply (measurableSet_le (measurable_trialTotalMass 38) measurable_const).inter
  exact measurableSet_trialOuterRowAllowed _ (by
    norm_num [trialSubtractionSourceRow, trialSubtractionActivation])

theorem measurable_trialSourceStepFunction : Measurable trialSourceStepFunction :=
  measurable_trialActualOuterMask.mul measurable_trialStepFunction

theorem integrable_trialSourceStepFunction_sq :
    Integrable (fun X => trialSourceStepFunction X ^ 2) (trialProductMeasure 39) := by
  have hmask : ∀ X, ‖trialActualOuterMask X ^ 2‖ ≤ (1 : ℝ) := by
    intro X
    dsimp only [trialActualOuterMask]
    split_ifs <;> norm_num
  simpa only [trialSourceStepFunction, mul_pow] using
    integrable_trialStepFunction_sq.bdd_mul
      (measurable_trialActualOuterMask.pow_const 2).aestronglyMeasurable (ae_of_all _ hmask)

/-- Exact correspondence with the prime-factor counting measure for sampled arrays. -/
theorem trialSourceCountMeasure_primeLogConfiguration (d : ℕ) (R : ℝ) (hR : 1 < R)
    (r : Fin d → ℕ) (hr : Squarefree (∏ i, r i)) :
    trialSourceCountMeasure (fun i => PrimeGap186.primeLogConfiguration R (r i)) =
      ∑ p ∈ (∏ i, r i).primeFactors, Measure.dirac (PrimeGap186.logSize R p) :=
  PrimeGap186.physicalSourceCountMeasure_primeLogConfiguration d R hR r hr

#print axioms trialSourceRows_activation_pos
#print axioms measurable_trialActualOuterMask
#print axioms measurable_trialActualBaseMask
#print axioms measurable_trialActualEnlargedMask
#print axioms measurable_trialActualSubtractionMask
#print axioms integrable_trialSourceStepFunction_sq
#print axioms trialSourceCountMeasure_primeLogConfiguration

end PrimeGap182
