import SourceDataChecks182
import TrialMaskGeometry182

/-! Actual source-count kernels on the fixed fragment law.

Low witnesses use the literal bins and upward-rounded witness endpoint.
Rank kernels retain the largest-fragment condition and the second mark;
high kernels count triples, including marks in the same coordinate.
The local count multiplier is evaluated on the full configuration before
erasure. Its coarse index is the sum of the individual quotients by 48.
All kernels are proved measurable and bounded; integral inequalities are
introduced only as explicit premises in the subsequent module.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

def trialSourceCellSum {d : ℕ} (X : Fin d → FiniteMeasure ℝ) : ℕ :=
  ∑ i, trialCellIndex (X i)

def TrialSourceDomain {d : ℕ} (c : TrialSourceCoverData)
    (X : Fin d → FiniteMeasure ℝ) : Prop :=
  d = c.dimension ∧ ∃ j : Fin c.pieces.length,
    let p := c.pieces.get j
    p.first ≤ trialSourceCellSum X ∧ trialSourceCellSum X ≤ p.last ∧
      TrialCapAllowed p.cap X

def trialSourceSmallMass {d : ℕ} (c : TrialSourceCoverData)
    (X : Fin d → FiniteMeasure ℝ) : ℝ :=
  ∑ i, (X i : Measure ℝ).real (Set.Ioc 0 (c.low : ℝ))

def trialSourceUnmasked {d : ℕ} (c : TrialSourceCoverData)
    (X : Fin d → FiniteMeasure ℝ) : ℝ := by
  classical
  exact match c.kind with
  | .low => (trialSourceCountMeasure X).real (Set.Ioc (c.low : ℝ) (c.high : ℝ)) *
      Real.exp ((c.slope : ℝ) * (trialTotalMass X +
        ((c.order : ℝ) - 1) * (c.witnessUpper : ℝ) - (c.threshold : ℝ) -
          trialSourceSmallMass c X))
  | .rankTwo => ∫ q : ℝ in Set.Ioc (c.low : ℝ) (c.high : ℝ),
      (if trialSourceCountMeasure X (Set.Ioi q) = 0 ∧
          (2 : ℝ) ≤ (trialSourceCountMeasure X).real
            (Set.Ioc (((c.threshold : ℝ) - q) / (c.order : ℝ)) q)
        then (1 : ℝ) else 0) ∂trialSourceCountMeasure X
  | .high => (Nat.choose ⌊(trialSourceCountMeasure X).real (Set.Ioi (c.split : ℝ))⌋₊ 3 : ℝ)

def trialSourceKernel {d : ℕ} (c : TrialSourceCoverData)
    (X : Fin d → FiniteMeasure ℝ) : ℝ := by
  classical
  exact if TrialSourceDomain c X then trialSourceUnmasked c X else 0

/-- The radial absolute face envelope used by the frozen contractions. -/
def trialSourceFaceWeight (Y : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  if trialSourceCellSum Y ≤ 355047 then 1
  else if trialSourceCellSum Y ≤ 359896 then (trialSourceEnlargementWeight : ℝ)
  else (trialSourceEpsilonUpper : ℝ)

def trialSourceCountIndex (r : TrialOuterCertificateData)
    (X : Fin 39 → FiniteMeasure ℝ) : ℕ :=
  if r.countCoarse then ∑ i, trialCellIndex (X i) / 48 else trialSourceCellSum X

def trialSourceCountAt (r : TrialOuterCertificateData) (n : ℕ) : ℝ :=
  ∑ b : Fin r.counts.length,
    let c := r.counts.get b
    if c.first ≤ n ∧ n ≤ c.last then (c.factor : ℝ) else 0

def trialSourceCountMultiplier (j : Fin 60) (X : Fin 39 → FiniteMeasure ℝ) : ℝ :=
  trialSourceCountAt (trialOuterCertificates j)
    (trialSourceCountIndex (trialOuterCertificates j) X)

theorem measurable_trialSourceCellSum (d : ℕ) :
    Measurable (trialSourceCellSum (d := d)) :=
  Finset.measurable_sum _ fun i _ =>
    measurable_trialCellIndex.comp (measurable_pi_apply i)

theorem measurableSet_trialSourceDomain {d : ℕ} (c : TrialSourceCoverData) :
    MeasurableSet {X : Fin d → FiniteMeasure ℝ | TrialSourceDomain c X} := by
  by_cases hd : d = c.dimension
  · simp only [TrialSourceDomain, hd, true_and, Set.ofPred_exists]
    apply MeasurableSet.iUnion fun j => ?_
    exact (measurableSet_le measurable_const (measurable_trialSourceCellSum d)).inter
      ((measurableSet_le (measurable_trialSourceCellSum d) measurable_const).inter
        (measurableSet_trialCapAllowed _))
  · simp [TrialSourceDomain, hd]

theorem measurable_trialSourceSmallMass {d : ℕ} (c : TrialSourceCoverData) :
    Measurable (trialSourceSmallMass (d := d) c) :=
  Finset.measurable_sum _ fun i _ =>
    ((Measure.measurable_coe measurableSet_Ioc).comp
      (measurable_subtype_coe.comp (measurable_pi_apply i))).ennreal_toReal

theorem trialSourceUnmasked_regular (c : TrialSourceCoverData)
    (hc : TrialSourceCoverRegular c) (d : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    Measurable (trialSourceUnmasked (d := d) c) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ X : Fin d → FiniteMeasure ℝ, trialTotalMass X ≤ M →
        0 ≤ trialSourceUnmasked c X ∧ trialSourceUnmasked c X ≤ B := by
  change Measurable (fun X : Fin d → FiniteMeasure ℝ => trialSourceUnmasked c X) ∧ _
  have hm : (0 : ℝ) < (c.order : ℝ) := Rat.cast_pos.mpr hc.1
  have hlo : (0 : ℝ) < (c.low : ℝ) := Rat.cast_pos.mpr hc.2.1
  have hhi : (c.high : ℝ) < (c.threshold : ℝ) := Rat.cast_lt.mpr hc.2.2.1
  have hθ : (0 : ℝ) ≤ (c.slope : ℝ) := Rat.cast_nonneg.mpr hc.2.2.2.1
  have hsplit : (0 : ℝ) < (c.split : ℝ) := Rat.cast_pos.mpr hc.2.2.2.2.1
  have hN := measurable_trialSourceCountMeasure d
  cases hk : c.kind with
  | low =>
    simp only [trialSourceUnmasked, hk]
    refine ⟨?_, (M / (c.low : ℝ)) * Real.exp ((c.slope : ℝ) *
      (M + ((c.order : ℝ) - 1) * (c.witnessUpper : ℝ) - (c.threshold : ℝ))),
      mul_nonneg (div_nonneg hM hlo.le) (Real.exp_pos _).le, ?_⟩
    · exact (((Measure.measurable_coe measurableSet_Ioc).comp hN).ennreal_toReal).mul
        (measurable_const.mul (((measurable_trialTotalMass d).add_const _).sub_const _ |>.sub
          (measurable_trialSourceSmallMass c))).exp
    · intro X hX
      refine ⟨mul_nonneg measureReal_nonneg (Real.exp_pos _).le, ?_⟩
      obtain ⟨hfinite, hcount⟩ :=
        (PrimeGap186.physicalSourceCountMeasure_regular d).2 (c.low : ℝ) hlo X
      have hcount' : (trialSourceCountMeasure X).real (Set.Ioc (c.low : ℝ) (c.high : ℝ)) ≤
          M / (c.low : ℝ) :=
        (measureReal_mono (fun _ hx => hx.1) (isFiniteMeasure_restrict.mp hfinite)).trans
          (hcount.trans (div_le_div_of_nonneg_right hX hlo.le))
      have hsmall : 0 ≤ trialSourceSmallMass c X :=
        Finset.sum_nonneg fun _ _ => measureReal_nonneg
      apply mul_le_mul hcount' _ (Real.exp_pos _).le (div_nonneg hM hlo.le)
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hθ
      linarith
  | rankTwo =>
    simp only [trialSourceUnmasked, hk, trialSourceCountMeasure]
    obtain ⟨h, hb⟩ := PrimeGap186.physicalSource_rank_cover_regular d
      (c.order : ℝ) (c.threshold : ℝ) (c.low : ℝ) (c.high : ℝ) hm hlo hhi
    exact ⟨h, M / (c.low : ℝ), div_nonneg hM hlo.le, fun X hX =>
      ⟨(hb X).1, (hb X).2.trans (div_le_div_of_nonneg_right hX hlo.le)⟩⟩
  | high =>
    simp only [trialSourceUnmasked, hk]
    refine ⟨(measurable_of_countable (fun n : ℕ => (Nat.choose n 3 : ℝ))).comp
      (((Measure.measurable_coe measurableSet_Ioi).comp hN).ennreal_toReal.nat_floor),
      (⌊M / (c.split : ℝ)⌋₊ ^ 3 : ℝ), by positivity, ?_⟩
    intro X hX
    refine ⟨Nat.cast_nonneg _, ?_⟩
    have hcount := ((PrimeGap186.physicalSourceCountMeasure_regular d).2
      (c.split : ℝ) hsplit X).2
    have hfloor := Nat.floor_mono (hcount.trans
      (div_le_div_of_nonneg_right hX hsplit.le))
    exact_mod_cast (Nat.choose_le_pow
      ⌊(trialSourceCountMeasure X).real (Set.Ioi (c.split : ℝ))⌋₊ 3).trans
        (Nat.pow_le_pow_left hfloor 3)

theorem trialSourceKernel_regular (c : TrialSourceCoverData)
    (hc : TrialSourceCoverRegular c) (d : ℕ) :
    Measurable (trialSourceKernel (d := d) c) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ X : Fin d → FiniteMeasure ℝ,
        0 ≤ trialSourceKernel c X ∧ trialSourceKernel c X ≤ B := by
  let M : ℝ := ((trialCellCount + d : ℕ) : ℝ) * (trialMesh : ℝ)
  have hM : 0 ≤ M := mul_nonneg (Nat.cast_nonneg _) (Rat.cast_nonneg.mpr trialMesh_pos.le)
  obtain ⟨hU, B, hB, hb⟩ := trialSourceUnmasked_regular c hc d M hM
  refine ⟨Measurable.ite (measurableSet_trialSourceDomain c) hU measurable_const, B, hB, ?_⟩
  intro X
  by_cases hX : TrialSourceDomain c X
  · simp only [trialSourceKernel, hX, ite_true]
    apply hb
    obtain ⟨_, j, hj⟩ := hX
    have hindex : trialSourceCellSum X < trialCellCount :=
      hj.2.1.trans_lt (hc.2.2.2.2.2 j)
    exact (trialTotalMass_cell_bound X).trans
      (mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (Nat.add_le_add_right hindex.le d))
        (Rat.cast_nonneg.mpr trialMesh_pos.le))
  · simp only [trialSourceKernel, hX, ite_false, le_refl, true_and]
    exact hB

theorem measurable_trialSourceFaceWeight : Measurable trialSourceFaceWeight := by
  unfold trialSourceFaceWeight
  exact Measurable.ite
    (measurableSet_le (measurable_trialSourceCellSum 38) measurable_const) measurable_const
    (Measurable.ite (measurableSet_le (measurable_trialSourceCellSum 38) measurable_const)
      measurable_const measurable_const)

theorem trialSourceFaceWeight_bounds (Y : Fin 38 → FiniteMeasure ℝ) :
    0 ≤ trialSourceFaceWeight Y ∧ trialSourceFaceWeight Y ≤ 1 := by
  unfold trialSourceFaceWeight
  split_ifs <;> norm_num [trialSourceEnlargementWeight, trialSourceEpsilonUpper]

theorem measurable_trialSourceCountMultiplier (j : Fin 60) :
    Measurable (trialSourceCountMultiplier j) := by
  apply (measurable_of_countable (trialSourceCountAt (trialOuterCertificates j))).comp
  unfold trialSourceCountIndex
  split_ifs
  · exact Finset.measurable_sum _ fun i _ =>
      ((measurable_of_countable (fun n : ℕ => n / 48)).comp measurable_trialCellIndex).comp
        (measurable_pi_apply i)
  · exact measurable_trialSourceCellSum 39

theorem trialSourceCountMultiplier_bounds (j : Fin 60) (X : Fin 39 → FiniteMeasure ℝ) :
    0 ≤ trialSourceCountMultiplier j X ∧
      trialSourceCountMultiplier j X ≤ 39 * (trialOuterCertificates j).counts.length := by
  unfold trialSourceCountMultiplier trialSourceCountAt
  constructor
  · apply Finset.sum_nonneg
    intro b _
    dsimp only
    split_ifs
    · exact Rat.cast_nonneg.mpr (trialOuterCountBand_bounds j b).1
    · rfl
  · calc
      _ ≤ ∑ _b : Fin (trialOuterCertificates j).counts.length, (39 : ℝ) := by
        apply Finset.sum_le_sum
        intro b _
        dsimp only
        split_ifs
        · exact_mod_cast (trialOuterCountBand_bounds j b).2.1
        · norm_num
      _ = _ := by simp [mul_comm]

#print axioms trialSourceUnmasked_regular
#print axioms trialSourceKernel_regular
#print axioms trialSourceCountMultiplier_bounds

end PrimeGap182
