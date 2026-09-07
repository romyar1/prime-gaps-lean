import PrimeGaps186
import TrialData182
import SharpMinorant

/-!
The literal signed 39-coordinate trial and its actual fragment-law integrals.

The coefficients, knots, component caps, shell caps, and both source ladders
are copied from the hash-bound JSON by `scripts/export_trial_data.py`.
The B-spline uses the total coordinate midpoint sum (no 9/10 shift).
Independent cap components are added before the square or erasure is taken.
The numerical cap bounds below are explicit premises about these integrals.
No interval integration or distribution estimate is postulated as an axiom.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PrimeGap182

def trialCellIndex (X : FiniteMeasure ℝ) : ℕ :=
  ⌊(X.mass : ℝ) / (trialMesh : ℝ)⌋₊

def trialCellMidpoint (j : ℕ) : ℚ := ((j : ℚ) + 1 / 2) * trialMesh

def trialProfileValue (j : ℕ) : ℚ :=
  (21 / 200) / (1 + trialCellMidpoint j / 100) +
    (179 / 200) / (1 + (907 / 5) * trialCellMidpoint j)

def trialProfileNormalizer : ℚ :=
  ∑ j ∈ Finset.range trialCellCount, trialProfileValue j ^ 2

def trialPhysicalNormalizer : ℝ :=
  ((trialMesh : ℝ) * (trialProfileNormalizer : ℝ)) ^ 39

def trialKnot (i : ℕ) : ℚ :=
  if h : i < 26 then trialKnots ⟨i, h⟩ else trialRadius

/-- Cox--de Boor recursion. Zero denominators contribute zero; an interior
repeated knot uses the right-hand span. The last endpoint uses the left value. -/
def trialBSpline : ℕ → ℕ → ℚ → ℚ
  | 0, i, x => if (trialKnot i ≤ x ∧ x < trialKnot (i + 1)) ∨
      (trialKnot i < trialKnot (i + 1) ∧ x = trialKnot (i + 1) ∧ x = trialRadius)
      then 1 else 0
  | d + 1, i, x =>
      (x - trialKnot i) / (trialKnot (i + d + 1) - trialKnot i) * trialBSpline d i x +
      (trialKnot (i + d + 2) - x) / (trialKnot (i + d + 2) - trialKnot (i + 1)) *
        trialBSpline d (i + 1) x

def trialRadialValue (c : Fin 3) (s : Fin 11) (x : ℚ) : ℚ :=
  ∑ j : Fin 22, trialDataCoefficient c s j * trialBSpline 3 j.val x

def trialAngularValue {d : ℕ} (s : Fin 11) (t : Fin d → ℚ) : ℚ :=
  ((trialAngularSignature s).map (fun p => ∑ i, t i ^ p)).prod

def trialCellValue (c : Fin 3) (j : Fin 39 → ℕ) : ℝ :=
  (((∏ i, trialProfileValue (j i)) *
    ∑ s : Fin 11, trialRadialValue c s (∑ i, trialCellMidpoint (j i)) *
      trialAngularValue s (fun i => trialCellMidpoint (j i)) : ℚ) : ℝ)

/-- Every cap concerns fragment locations, not the total mass of a coordinate. -/
def TrialCapAllowed {d : ℕ} (cap : ℚ) (X : Fin d → FiniteMeasure ℝ) : Prop :=
  ∀ i, (X i : Measure ℝ) (Set.Ioi (cap : ℝ)) = 0

/-- Whole-cell upper totals implement the original inward support convention. -/
def TrialShellAllowed {d : ℕ} (shell : TrialShell)
    (X : Fin d → FiniteMeasure ℝ) : Prop :=
  let r : ℕ := ∑ i, trialCellIndex (X i)
  r < trialCellCount ∧ shell.lower < ((r + d : ℕ) : ℚ) * trialMesh ∧
    ((r + d : ℕ) : ℚ) * trialMesh ≤ shell.upper ∧ TrialCapAllowed shell.cap X

def TrialShellDomain {d : ℕ} (role : Fin 5) (X : Fin d → FiniteMeasure ℝ) : Prop :=
  ∃ i : Fin (trialShells role).length, TrialShellAllowed ((trialShells role).get i) X

def trialMask {d : ℕ} (role : Fin 5) (X : Fin d → FiniteMeasure ℝ) : ℝ := by
  classical
  exact if TrialShellDomain role X then 1 else 0

def trialComponentMask (c : Fin 3) (X : Fin 39 → FiniteMeasure ℝ) : ℝ := by
  classical
  exact if TrialCapAllowed (trialComponentCap c) X then 1 else 0

def trialStepFunction (X : Fin 39 → FiniteMeasure ℝ) : ℝ :=
  trialMask 0 X * ∑ c : Fin 3,
    trialComponentMask c X * trialCellValue c (fun i => trialCellIndex (X i))

/-- The actual Poisson fragment law from the baseline, with its physical scaling. -/
def trialPhysicalMeasure : Measure (FiniteMeasure ℝ) :=
  ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * (trialLargestCap : ℝ)) •
    PrimeGap186.fragmentLaw (trialLargestCap : ℝ)

def trialProductMeasure (d : ℕ) : Measure (Fin d → FiniteMeasure ℝ) :=
  Measure.pi (fun _ : Fin d => trialPhysicalMeasure)

def trialMarginal (i : Fin 39) (Y : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  ∫ X : FiniteMeasure ℝ, trialStepFunction (i.insertNth X Y) ∂trialPhysicalMeasure

/-- The degree-21 alternating upper polynomial for log(1+x), kept rational. -/
def trialLogUpper (x : ℚ) : ℚ :=
  ∑ i : Fin 21, (-1 : ℚ) ^ i.val * x ^ (i.val + 1) / (i.val + 1 : ℕ)

def trialPairBinSize : ℚ := (trialMinorantA - 2 * trialRoughness) / trialPairBins

def trialPairBinUpper (i : Fin 1024) : ℚ :=
  2 * trialRoughness + ((i.val + 1 : ℕ) : ℚ) * trialPairBinSize

def trialPairRawWeight (i : Fin 1024) : ℚ :=
  let s := trialPairBinUpper i
  (12 / 5) * max (s - trialHingeThreshold) 0 / (2 / 5 - trialHingeThreshold) *
    trialPairBinSize * trialLogUpper ((s - 2 * trialRoughness) / trialRoughness) / s

def trialPairWeight (i : Fin 1024) : ℚ :=
  ((⌈trialPairRawWeight i * 10 ^ 25⌉ : ℤ) : ℚ) / 10 ^ 25

/-- The engine has `n=N-k=393177` cells; its radial block width is 768. -/
def trialKernelBlock : ℕ := (trialCellCount + trialRadialBlocks - 1) / trialRadialBlocks

def trialKernelStop (j : ℕ) : ℕ :=
  min trialCellCount ((j / trialKernelBlock + 1) * trialKernelBlock)

def trialKernelRadius (j : ℕ) : ℚ :=
  trialRhoStar * ((trialKernelStop j - 1 + 38 : ℕ) : ℚ) * trialMesh

def trialPairKernelRat (j : ℕ) : ℚ :=
  if j < trialCellCount then
    ∑ i : Fin 1024, trialPairWeight i /
      min (trialRoughness - trialAuxiliaryRetreat)
        ((1 - trialPairBinUpper i) / 2 - trialKernelRadius j - trialAuxiliaryRetreat)
  else 0

/-- The literal finite step kernel, extended by zero outside its recorded cells. -/
def trialPairKernel (j : ℕ) : ℝ := (trialPairKernelRat j : ℝ)

def trialFaceKernel (Y : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  trialPairKernel (∑ i, trialCellIndex (Y i))

def trialHybridLoss : ℝ := (trialKappa : ℝ) * ((trialLambda : ℝ)⁻¹ - 1)

def trialCapFaceMultiplier (Y : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  (trialLambda : ℝ) * trialMask 1 Y + (1 - (trialLambda : ℝ)) * trialMask 2 Y +
    trialHybridLoss * trialFaceKernel Y * trialMask 3 Y - trialHybridLoss * trialFaceKernel Y

def trialSquareIntegral : ℝ :=
  (∫ X, trialStepFunction X ^ 2 ∂trialProductMeasure 39) / trialPhysicalNormalizer

def trialFaceIntegral (w : (Fin 38 → FiniteMeasure ℝ) → ℝ) : ℝ :=
  (∑ i : Fin 39, ∫ Y, w Y * trialMarginal i Y ^ 2 ∂trialProductMeasure 38) /
    trialPhysicalNormalizer

def trialBaseIntegral : ℝ := trialFaceIntegral (trialMask 1)

def trialEnlargementIntegral : ℝ :=
  trialFaceIntegral (fun Y => trialMask 2 Y * (1 - trialMask 1 Y))

def trialTailIntegral : ℝ :=
  trialFaceIntegral (fun Y => trialMask 4 Y * (1 - trialMask 3 Y) * trialFaceKernel Y)

def trialCapQuotient : ℝ :=
  (trialRhoStar : ℝ) * (trialBaseIntegral + (1 - (trialLambda : ℝ)) *
    trialEnlargementIntegral - trialHybridLoss * trialTailIntegral) / trialSquareIntegral

/-- These are actual integral inequalities; no equality to a free scalar is assumed. -/
structure PhysicalCapBounds182 : Prop where
  denominator_lower : (trialDenominatorLower : ℝ) ≤ trialSquareIntegral
  denominator_upper : trialSquareIntegral ≤ (trialDenominatorUpper : ℝ)
  base_lower : (trialJ0Lower : ℝ) ≤ trialBaseIntegral
  enlargement_lower : (trialJPlusLower : ℝ) ≤ trialEnlargementIntegral
  tail_upper : trialTailIntegral ≤ (trialTailUpper : ℝ)

theorem trialCellCount_eq : trialCellCount = 393177 := by rfl

theorem trialKernelBlock_eq : trialKernelBlock = 768 := by rfl

theorem trialMesh_pos : (0 : ℚ) < trialMesh := by
  norm_num [trialMesh, trialRadius, trialIntervals]

theorem trialProfileValue_pos (j : ℕ) : 0 < trialProfileValue j := by
  have hmid : 0 ≤ trialCellMidpoint j := by
    dsimp only [trialCellMidpoint]
    exact mul_nonneg (by positivity) trialMesh_pos.le
  unfold trialProfileValue
  positivity

theorem trialProfileNormalizer_pos : 0 < trialProfileNormalizer := by
  apply Finset.sum_pos'
  · intro j _
    exact sq_nonneg _
  · exact ⟨0, by norm_num [trialCellCount, trialIntervals, trialDimension],
      sq_pos_of_pos (trialProfileValue_pos 0)⟩

theorem trialPhysicalNormalizer_pos : 0 < trialPhysicalNormalizer := by
  unfold trialPhysicalNormalizer
  exact pow_pos (mul_pos (Rat.cast_pos.mpr trialMesh_pos)
    (Rat.cast_pos.mpr trialProfileNormalizer_pos)) _

theorem trialPhysicalMeasure_finite : IsFiniteMeasure trialPhysicalMeasure := by
  let : IsProbabilityMeasure (PrimeGap186.fragmentLaw (trialLargestCap : ℝ)) :=
    PrimeGap186.fragmentLaw_isProbabilityMeasure _
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top

instance (d : ℕ) : IsFiniteMeasure (trialProductMeasure d) := by
  let : IsFiniteMeasure trialPhysicalMeasure := trialPhysicalMeasure_finite
  dsimp only [trialProductMeasure]
  infer_instance

theorem measurable_trialCellIndex : Measurable trialCellIndex :=
  (((Measure.measurable_coe MeasurableSet.univ).comp
    measurable_subtype_coe).ennreal_toReal.div_const (trialMesh : ℝ)).nat_floor

theorem measurableSet_trialCapAllowed {d : ℕ} (cap : ℚ) :
    MeasurableSet {X : Fin d → FiniteMeasure ℝ | TrialCapAllowed cap X} := by
  simp only [TrialCapAllowed, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_singleton (0 : ℝ≥0∞)).preimage
    (((Measure.measurable_coe measurableSet_Ioi).comp measurable_subtype_coe).comp
      (measurable_pi_apply i))

theorem measurableSet_trialShellAllowed {d : ℕ} (shell : TrialShell) :
    MeasurableSet {X : Fin d → FiniteMeasure ℝ | TrialShellAllowed shell X} := by
  let r : (Fin d → FiniteMeasure ℝ) → ℕ := fun X => ∑ i, trialCellIndex (X i)
  have hr : Measurable r := Finset.measurable_sum _ fun i _ =>
    measurable_trialCellIndex.comp (measurable_pi_apply i)
  have ht : Measurable (fun X => ((r X + d : ℕ) : ℚ) * trialMesh) :=
    (measurable_of_countable (fun n : ℕ => ((n + d : ℕ) : ℚ) * trialMesh)).comp hr
  exact (measurableSet_lt hr measurable_const).inter
    ((measurableSet_lt measurable_const ht).inter
      ((measurableSet_le ht measurable_const).inter (measurableSet_trialCapAllowed _)))

theorem measurable_trialMask {d : ℕ} (role : Fin 5) :
    Measurable (trialMask (d := d) role) := by
  apply Measurable.ite _ measurable_const measurable_const
  simp only [TrialShellDomain, Set.ofPred_exists]
  exact MeasurableSet.iUnion fun i => measurableSet_trialShellAllowed _

theorem measurable_trialComponentMask (c : Fin 3) : Measurable (trialComponentMask c) :=
  Measurable.ite (measurableSet_trialCapAllowed _) measurable_const measurable_const

theorem measurable_trialStepFunction : Measurable trialStepFunction := by
  have hi : Measurable (fun X : Fin 39 → FiniteMeasure ℝ =>
      fun i => trialCellIndex (X i)) := measurable_pi_lambda _ fun i =>
    measurable_trialCellIndex.comp (measurable_pi_apply i)
  apply (measurable_trialMask 0).mul
  apply Finset.measurable_sum
  intro c _
  exact (measurable_trialComponentMask c).mul
    ((measurable_of_countable (trialCellValue c)).comp hi)

theorem trialStepFunction_finite_range : (Set.range trialStepFunction).Finite := by
  classical
  let V : ((Fin 39 → Fin trialCellCount) × (Fin 3 → Bool)) → ℝ := fun z =>
    ∑ c : Fin 3, if z.2 c then trialCellValue c (fun i => (z.1 i).val) else 0
  apply ((Set.finite_range V).insert 0).subset
  rintro _ ⟨X, rfl⟩
  by_cases hX : TrialShellDomain 0 X
  · obtain ⟨i, hi⟩ := hX
    have hsum : (∑ j : Fin 39, trialCellIndex (X j)) < trialCellCount := hi.1
    have hj (j : Fin 39) : trialCellIndex (X j) < trialCellCount :=
      (Finset.single_le_sum (fun k _ => Nat.zero_le (trialCellIndex (X k)))
        (Finset.mem_univ j)).trans_lt hsum
    let z : (Fin 39 → Fin trialCellCount) × (Fin 3 → Bool) :=
      (fun j => ⟨trialCellIndex (X j), hj j⟩,
       fun c => decide (TrialCapAllowed (trialComponentCap c) X))
    apply Set.mem_insert_of_mem
    refine ⟨z, ?_⟩
    rw [trialStepFunction, trialMask, ite_eq_left ⟨i, hi⟩, one_mul]
    dsimp only [V, z]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : TrialCapAllowed (trialComponentCap c) X <;>
      simp [trialComponentMask, hc]
  · simp [trialStepFunction, trialMask, hX]

theorem integrable_trialStepFunction :
    Integrable trialStepFunction (trialProductMeasure 39) := by
  obtain ⟨C, _, hC⟩ := trialStepFunction_finite_range.isBounded.exists_pos_norm_le
  exact Integrable.of_bound measurable_trialStepFunction.aestronglyMeasurable C
    (ae_of_all _ fun X => hC _ ⟨X, rfl⟩)

theorem integrable_trialStepFunction_sq :
    Integrable (fun X => trialStepFunction X ^ 2) (trialProductMeasure 39) := by
  obtain ⟨C, _, hC⟩ := trialStepFunction_finite_range.isBounded.exists_pos_norm_le
  simpa only [pow_two] using integrable_trialStepFunction.mul_bdd
    measurable_trialStepFunction.aestronglyMeasurable (ae_of_all _ fun X => hC _ ⟨X, rfl⟩)

theorem measurable_trialMarginal (i : Fin 39) : Measurable (trialMarginal i) := by
  let : IsFiniteMeasure trialPhysicalMeasure := trialPhysicalMeasure_finite
  have hins : Measurable
      (fun Z : FiniteMeasure ℝ × (Fin 38 → FiniteMeasure ℝ) =>
        trialStepFunction (i.insertNth Z.1 Z.2)) := by
    change Measurable (trialStepFunction ∘
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 39 => FiniteMeasure ℝ) i).symm)
    exact measurable_trialStepFunction.comp
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 39 => FiniteMeasure ℝ) i).symm.measurable
  exact (hins.stronglyMeasurable.integral_prod_left'
    (μ := trialPhysicalMeasure)).measurable

theorem bounded_trialMarginal (i : Fin 39) :
    ∃ C : ℝ, ∀ Y : Fin 38 → FiniteMeasure ℝ, ‖trialMarginal i Y‖ ≤ C := by
  let : IsFiniteMeasure trialPhysicalMeasure := trialPhysicalMeasure_finite
  obtain ⟨C, _, hC⟩ := trialStepFunction_finite_range.isBounded.exists_pos_norm_le
  refine ⟨C * trialPhysicalMeasure.real Set.univ, ?_⟩
  intro Y
  exact norm_integral_le_of_norm_le_const (ae_of_all _ fun X => hC _ ⟨i.insertNth X Y, rfl⟩)

theorem integrable_trialMarginal (i : Fin 39) :
    Integrable (trialMarginal i) (trialProductMeasure 38) := by
  obtain ⟨C, hC⟩ := bounded_trialMarginal i
  exact Integrable.of_bound (measurable_trialMarginal i).aestronglyMeasurable C (ae_of_all _ hC)

theorem integrable_trialMarginal_sq (i : Fin 39) :
    Integrable (fun Y => trialMarginal i Y ^ 2) (trialProductMeasure 38) := by
  obtain ⟨C, hC⟩ := bounded_trialMarginal i
  simpa only [pow_two] using (integrable_trialMarginal i).mul_bdd
    (measurable_trialMarginal i).aestronglyMeasurable (ae_of_all _ hC)

theorem trialMarginal_sq_eq_integral_prod (i : Fin 39) (Y : Fin 38 → FiniteMeasure ℝ) :
    trialMarginal i Y ^ 2 =
      ∫ X : FiniteMeasure ℝ × FiniteMeasure ℝ,
        trialStepFunction (i.insertNth X.1 Y) * trialStepFunction (i.insertNth X.2 Y)
          ∂(trialPhysicalMeasure.prod trialPhysicalMeasure) := by
  let : IsFiniteMeasure trialPhysicalMeasure := trialPhysicalMeasure_finite
  simpa only [trialMarginal, pow_two] using
    (integral_prod_mul (μ := trialPhysicalMeasure) (ν := trialPhysicalMeasure)
      (fun X : FiniteMeasure ℝ => trialStepFunction (i.insertNth X Y))
      (fun X : FiniteMeasure ℝ => trialStepFunction (i.insertNth X Y))).symm

theorem trialPairKernel_finite_range : (Set.range trialPairKernel).Finite := by
  classical
  apply ((Set.finite_range (fun j : Fin trialCellCount => trialPairKernel j.val)).insert 0).subset
  rintro _ ⟨j, rfl⟩
  by_cases hj : j < trialCellCount
  · exact Set.mem_insert_of_mem 0 ⟨⟨j, hj⟩, rfl⟩
  · simp [trialPairKernel, trialPairKernelRat, hj]

theorem measurable_trialFaceKernel : Measurable trialFaceKernel := by
  exact (measurable_of_countable trialPairKernel).comp
    (Finset.measurable_sum _ fun i _ =>
      measurable_trialCellIndex.comp (measurable_pi_apply i))

theorem trialMask_bounds {d : ℕ} (role : Fin 5) (X : Fin d → FiniteMeasure ℝ) :
    ‖trialMask role X‖ ≤ 1 ∧ ‖1 - trialMask role X‖ ≤ 1 := by
  classical
  dsimp only [trialMask]
  split_ifs <;> norm_num

theorem integrable_trial_base_term (i : Fin 39) :
    Integrable (fun Y => trialMask 1 Y * trialMarginal i Y ^ 2) (trialProductMeasure 38) :=
  (integrable_trialMarginal_sq i).bdd_mul
    (measurable_trialMask 1).aestronglyMeasurable (ae_of_all _ fun Y => (trialMask_bounds 1 Y).1)

theorem integrable_trial_enlargement_term (i : Fin 39) :
    Integrable (fun Y => trialMask 2 Y * (1 - trialMask 1 Y) * trialMarginal i Y ^ 2)
      (trialProductMeasure 38) := by
  apply (integrable_trialMarginal_sq i).bdd_mul (c := 1)
    ((measurable_trialMask 2).mul (measurable_const.sub
      (measurable_trialMask 1))).aestronglyMeasurable
  apply ae_of_all
  intro Y
  change ‖trialMask 2 Y * (1 - trialMask 1 Y)‖ ≤ 1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (trialMask_bounds 2 Y).1).trans
    (trialMask_bounds 1 Y).2

theorem integrable_trial_tail_term (i : Fin 39) :
    Integrable (fun Y => trialMask 4 Y * (1 - trialMask 3 Y) * trialFaceKernel Y *
      trialMarginal i Y ^ 2) (trialProductMeasure 38) := by
  obtain ⟨C, _, hC⟩ := trialPairKernel_finite_range.isBounded.exists_pos_norm_le
  apply (integrable_trialMarginal_sq i).bdd_mul (c := C)
    (((measurable_trialMask 4).mul (measurable_const.sub
      (measurable_trialMask 3))).mul measurable_trialFaceKernel).aestronglyMeasurable
  apply ae_of_all
  intro Y
  change ‖trialMask 4 Y * (1 - trialMask 3 Y) * trialFaceKernel Y‖ ≤ C
  rw [norm_mul, norm_mul]
  have hm : ‖trialMask 4 Y‖ * ‖1 - trialMask 3 Y‖ ≤ 1 :=
    (mul_le_of_le_one_left (norm_nonneg _) (trialMask_bounds 4 Y).1).trans
      (trialMask_bounds 3 Y).2
  exact (mul_le_of_le_one_left (norm_nonneg _) hm).trans
    (hC _ ⟨∑ j, trialCellIndex (Y j), rfl⟩)

theorem trialSquareIntegral_nonneg : 0 ≤ trialSquareIntegral :=
  div_nonneg (integral_nonneg fun _ => sq_nonneg _) trialPhysicalNormalizer_pos.le

theorem trialSquareIntegral_pos (h : PhysicalCapBounds182) : 0 < trialSquareIntegral := by
  exact lt_of_lt_of_le (by norm_num [trialDenominatorLower]) h.denominator_lower

theorem trialCapQuotient_lower (h : PhysicalCapBounds182) :
    (36038765896603259 / 36028797018963968 : ℝ) ≤ trialCapQuotient := by
  have hlam : 0 ≤ 1 - (trialLambda : ℝ) := by norm_num [trialLambda]
  have hd : 0 ≤ trialHybridLoss := by norm_num [trialHybridLoss, trialLambda, trialKappa]
  have hρ : 0 ≤ (trialRhoStar : ℝ) := by norm_num [trialRhoStar]
  have hnum := mul_le_mul_of_nonneg_left
    (sub_le_sub (add_le_add h.base_lower
      (mul_le_mul_of_nonneg_left h.enlargement_lower hlam))
      (mul_le_mul_of_nonneg_left h.tail_upper hd)) hρ
  unfold trialCapQuotient
  apply (le_div_iff₀ (trialSquareIntegral_pos h)).mpr
  calc
    _ ≤ (36038765896603259 / 36028797018963968 : ℝ) *
        (trialDenominatorUpper : ℝ) :=
      mul_le_mul_of_nonneg_left h.denominator_upper (by norm_num)
    _ ≤ (trialRhoStar : ℝ) * ((trialJ0Lower : ℝ) + (1 - (trialLambda : ℝ)) *
        (trialJPlusLower : ℝ) - trialHybridLoss * (trialTailUpper : ℝ)) := by
      norm_num [trialRhoStar, trialJ0Lower, trialLambda, trialJPlusLower,
        trialHybridLoss, trialKappa, trialTailUpper, trialDenominatorUpper]
    _ ≤ _ := hnum

theorem trialCapQuotient_surplus (h : PhysicalCapBounds182) :
    (9968877639291 / 36028797018963968 : ℝ) ≤ trialCapQuotient - 1 := by
  linarith [trialCapQuotient_lower h]

#print axioms trialPhysicalNormalizer_pos
#print axioms trialPhysicalMeasure_finite
#print axioms measurable_trialStepFunction
#print axioms trialStepFunction_finite_range
#print axioms integrable_trialStepFunction_sq
#print axioms integrable_trialMarginal_sq
#print axioms trialMarginal_sq_eq_integral_prod
#print axioms integrable_trial_tail_term
#print axioms trialCapQuotient_lower
#print axioms trialCapQuotient_surplus

end PrimeGap182
