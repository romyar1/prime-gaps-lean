import SourceBoundary182

/-! Open finite-band certificates for the literal source rows.  They use
upper band endpoints and the actual no-small-positive-band-mass property.
Soundness yields the actual counting-measure row predicate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

theorem trialOuterRowOpen_mono (R : TrialSourceRow) {u v p q : ℝ}
    (huv : u ≤ v) (hpq : p ≤ q) (h : TrialOuterRowOpen R v q) : TrialOuterRowOpen R u p := by
  have hφ : trialOuterAllocation R p ≤ trialOuterAllocation R q :=
    min_le_min (mul_le_mul_of_nonneg_left hpq (by norm_num)) le_rfl
  have hψ : trialInnerAllocation R p ≤ trialInnerAllocation R q :=
    PrimeGap186.trial_three_owner_mono hpq (R.plateau : ℝ)
  unfold TrialOuterRowOpen at h ⊢
  split_ifs at h ⊢
  · exact (add_le_add huv hpq).trans_lt h
  · exact ⟨(add_le_add huv hφ).trans_lt h.1, hψ.trans_lt h.2⟩

theorem trialInnerRowOpen_mono (R : TrialSourceRow) {u v p q : ℝ}
    (huv : u ≤ v) (hpq : p ≤ q) (h : TrialInnerRowOpen R v q) : TrialInnerRowOpen R u p := by
  have hφ : trialOuterAllocation R p ≤ trialOuterAllocation R q :=
    min_le_min (mul_le_mul_of_nonneg_left hpq (by norm_num)) le_rfl
  have hψ : trialInnerAllocation R p ≤ trialInnerAllocation R q :=
    PrimeGap186.trial_three_owner_mono hpq (R.plateau : ℝ)
  unfold TrialInnerRowOpen at h ⊢
  split_ifs at h ⊢
  · exact (add_le_add huv hpq).trans_lt h
  · exact ⟨(add_le_add huv hψ).trans_lt h.1,
      h.2.elim (fun hq => Or.inl (hφ.trans_lt hq)) Or.inr⟩

theorem trialOuterViolation_not_open {d : ℕ} (R : TrialSourceRow)
    (X : Fin d → FiniteMeasure ℝ) (p : ℝ) (hp : TrialOuterViolation R X p) :
    ¬ TrialOuterRowOpen R ((trialWeightedMeasure X).real (Set.Ici p)) p := by
  intro hg
  unfold TrialOuterViolation at hp
  unfold TrialOuterRowOpen at hg
  split_ifs at hp hg
  · linarith only [hp.2, hg]
  · rcases hp.2 with ht | ht <;> linarith only [ht, hg.1, hg.2]

theorem trialInnerViolation_not_open {d : ℕ} (R : TrialSourceRow)
    (X : Fin d → FiniteMeasure ℝ) (p : ℝ) (hp : TrialInnerViolation R X p) :
    ¬ TrialInnerRowOpen R ((trialWeightedMeasure X).real (Set.Ici p)) p := by
  intro hg
  unfold TrialInnerViolation at hp
  unfold TrialInnerRowOpen at hg
  split_ifs at hp hg
  · linarith only [hp.2, hg]
  · rcases hp.2 with ht | ht
    · linarith only [ht, hg.1]
    · rcases hg.2 with hφ | hplateau
      · linarith only [ht, hφ]
      · exact (not_lt_of_ge ((min_le_right _ _).trans hplateau)) ht

theorem trialOuterRowAllowed_of_band {d m : ℕ} (R : TrialSourceRow)
    (a : Fin (m + 2) → ℝ) (ha : Monotone a) (X : Fin d → FiniteMeasure ℝ)
    (hcap : (∑ i, X i).restrict (Set.Ioc (a 0) (a (Fin.last (m + 1)))) = ∑ i, X i)
    (hband : ∀ j : Fin (m + 1), a j.succ ≤ (R.activation : ℝ) ∨
      PrimeGap186.fragmentBandMasses a (∑ i, X i) j = 0 ∨
        TrialOuterRowOpen R
          (∑ k ∈ (Finset.univ : Finset (Fin (m + 1))).filter (fun k => j ≤ k),
            PrimeGap186.fragmentBandMasses a (∑ i, X i) k) (a j.succ)) :
    TrialOuterRowAllowed R X := by
  right
  have hz := PrimeGap186.trial_band_count_bad_zero a ha (∑ i, X i) hcap
    (R.activation : ℝ) (TrialOuterRowOpen R) (trialOuterRowOpen_mono R) hband
  have hz' : trialSourceCountMeasure X {p : ℝ | (R.activation : ℝ) < p ∧
      ¬ TrialOuterRowOpen R ((trialWeightedMeasure X).real (Set.Ici p)) p} = 0 := by
    simpa only [FiniteMeasure.toMeasure_sum, trialSourceCountMeasure,
      PrimeGap186.physicalSourceCountMeasure, trialWeightedMeasure] using hz
  apply measure_mono_null _ hz'
  intro p hp
  exact ⟨hp.1, trialOuterViolation_not_open R X p hp⟩

theorem trialInnerRowAllowed_of_band {d m : ℕ} (R : TrialSourceRow)
    (a : Fin (m + 2) → ℝ) (ha : Monotone a) (X : Fin d → FiniteMeasure ℝ)
    (hcap : (∑ i, X i).restrict (Set.Ioc (a 0) (a (Fin.last (m + 1)))) = ∑ i, X i)
    (hband : ∀ j : Fin (m + 1), a j.succ ≤ (R.activation : ℝ) ∨
      PrimeGap186.fragmentBandMasses a (∑ i, X i) j = 0 ∨
        TrialInnerRowOpen R
          (∑ k ∈ (Finset.univ : Finset (Fin (m + 1))).filter (fun k => j ≤ k),
            PrimeGap186.fragmentBandMasses a (∑ i, X i) k) (a j.succ)) :
    TrialInnerRowAllowed R X := by
  right; right
  have hz := PrimeGap186.trial_band_count_bad_zero a ha (∑ i, X i) hcap
    (R.activation : ℝ) (TrialInnerRowOpen R) (trialInnerRowOpen_mono R) hband
  have hz' : trialSourceCountMeasure X {p : ℝ | (R.activation : ℝ) < p ∧
      ¬ TrialInnerRowOpen R ((trialWeightedMeasure X).real (Set.Ici p)) p} = 0 := by
    simpa only [FiniteMeasure.toMeasure_sum, trialSourceCountMeasure,
      PrimeGap186.physicalSourceCountMeasure, trialWeightedMeasure] using hz
  apply measure_mono_null _ hz'
  intro p hp
  exact ⟨hp.1, trialInnerViolation_not_open R X p hp⟩

def trialBandMassSum {d m : ℕ} (v : Fin d → Fin (m + 1) → ℝ) (j : Fin (m + 1)) : ℝ := ∑ i, v i j

def trialBandTotal {d m : ℕ} (v : Fin d → Fin (m + 1) → ℝ) : ℝ := ∑ i, ∑ j, v i j

def trialBandTail {d m : ℕ} (v : Fin d → Fin (m + 1) → ℝ) (j : Fin (m + 1)) : ℝ :=
  ∑ k ∈ (Finset.univ : Finset (Fin (m + 1))).filter (fun k => j ≤ k), trialBandMassSum v k

def TrialBandOuterRow {d m : ℕ} (R : TrialSourceRow) (a : Fin (m + 2) → ℝ)
    (v : Fin d → Fin (m + 1) → ℝ) : Prop :=
  trialBandTotal v < (R.outerCore : ℝ) ∨ ∀ j : Fin (m + 1),
    a j.succ ≤ (R.activation : ℝ) ∨ trialBandMassSum v j < a j.castSucc ∨
      TrialOuterRowOpen R (trialBandTail v j) (a j.succ)

def TrialBandInnerRow {d m : ℕ} (R : TrialSourceRow) (a : Fin (m + 2) → ℝ)
    (v : Fin d → Fin (m + 1) → ℝ) : Prop :=
  R.order = 1 ∨ trialBandTotal v < (R.innerCore : ℝ) ∨ ∀ j : Fin (m + 1),
    a j.succ ≤ (R.activation : ℝ) ∨ trialBandMassSum v j < a j.castSucc ∨
      TrialInnerRowOpen R (trialBandTail v j) (a j.succ)

theorem continuous_trialBandMassSum {d m : ℕ} (j : Fin (m + 1)) :
    Continuous (fun v : Fin d → Fin (m + 1) → ℝ => trialBandMassSum v j) := by
  unfold trialBandMassSum
  fun_prop

theorem continuous_trialBandTotal {d m : ℕ} :
    Continuous (@trialBandTotal d m) := by unfold trialBandTotal; fun_prop

theorem continuous_trialBandTail {d m : ℕ} (j : Fin (m + 1)) :
    Continuous (fun v : Fin d → Fin (m + 1) → ℝ => trialBandTail v j) := by
  unfold trialBandTail trialBandMassSum
  fun_prop

theorem isOpen_trialBandOuterRow {d m : ℕ} (R : TrialSourceRow) (a : Fin (m + 2) → ℝ) :
    IsOpen {v : Fin d → Fin (m + 1) → ℝ | TrialBandOuterRow R a v} := by
  apply (isOpen_lt continuous_trialBandTotal continuous_const).union
  apply PrimeGap186.trial_isOpen_finite_forall
  intro j
  apply isOpen_const.union
  apply (isOpen_lt (continuous_trialBandMassSum j) continuous_const).union
  change IsOpen {v : Fin d → Fin (m + 1) → ℝ |
    TrialOuterRowOpen R (trialBandTail v j) (a j.succ)}
  by_cases hR : R.order ≤ 2
  · simp only [TrialOuterRowOpen, hR, reduceIte]
    exact isOpen_lt (show Continuous (fun v => trialBandTail v j + a j.succ) from
      (continuous_trialBandTail j).add continuous_const) continuous_const
  · simp only [TrialOuterRowOpen, hR, reduceIte]
    exact (isOpen_lt (show Continuous (fun v =>
      trialBandTail v j + trialOuterAllocation R (a j.succ)) from
      (continuous_trialBandTail j).add continuous_const) continuous_const).inter isOpen_const

theorem isOpen_trialBandInnerRow {d m : ℕ} (R : TrialSourceRow) (a : Fin (m + 2) → ℝ) :
    IsOpen {v : Fin d → Fin (m + 1) → ℝ | TrialBandInnerRow R a v} := by
  apply isOpen_const.union
  apply (isOpen_lt continuous_trialBandTotal continuous_const).union
  apply PrimeGap186.trial_isOpen_finite_forall
  intro j
  apply isOpen_const.union
  apply (isOpen_lt (continuous_trialBandMassSum j) continuous_const).union
  change IsOpen {v : Fin d → Fin (m + 1) → ℝ |
    TrialInnerRowOpen R (trialBandTail v j) (a j.succ)}
  by_cases hR : R.order ≤ 2
  · simp only [TrialInnerRowOpen, hR, reduceIte]
    exact isOpen_lt (show Continuous (fun v => trialBandTail v j + a j.succ) from
      (continuous_trialBandTail j).add continuous_const) continuous_const
  · simp only [TrialInnerRowOpen, hR, reduceIte]
    exact (isOpen_lt (show Continuous (fun v =>
      trialBandTail v j + trialInnerAllocation R (a j.succ)) from
      (continuous_trialBandTail j).add continuous_const) continuous_const).inter isOpen_const

theorem trialBandMassSum_configuration {d m : ℕ} (a : Fin (m + 2) → ℝ)
    (X : Fin d → FiniteMeasure ℝ) (j : Fin (m + 1)) :
    trialBandMassSum (fun i => PrimeGap186.fragmentBandMasses a (X i)) j =
      PrimeGap186.fragmentBandMasses a (∑ i, X i) j :=
  (PrimeGap186.trial_fragmentBandMasses_sum a X j).symm

theorem trialBandOuterRow_sound {d m : ℕ} (R : TrialSourceRow)
    (a : Fin (m + 2) → ℝ) (ha : StrictMono a) (ha0 : a 0 = 0)
    (hseed : a (0 : Fin (m + 1)).succ ≤ (R.activation : ℝ))
    (X : Fin d → FiniteMeasure ℝ)
    (hcap : (∑ i, X i).restrict (Set.Ioc (a 0) (a (Fin.last (m + 1)))) = ∑ i, X i)
    (hgap : ∀ j : Fin (m + 1), 0 < a j.castSucc →
      PrimeGap186.fragmentBandMasses a (∑ i, X i) j = 0 ∨
        a j.castSucc < PrimeGap186.fragmentBandMasses a (∑ i, X i) j)
    (hrow : TrialBandOuterRow R a (fun i => PrimeGap186.fragmentBandMasses a (X i))) :
    TrialOuterRowAllowed R X := by
  rcases hrow with hcore | hband
  · left
    rw [trialBandTotal, PrimeGap186.trial_band_total_sum a ha.monotone X hcap] at hcore
    exact hcore.le
  · apply trialOuterRowAllowed_of_band R a ha.monotone X hcap
    intro j
    rcases hband j with hs | he | hg
    · exact Or.inl hs
    · by_cases hs : a j.succ ≤ (R.activation : ℝ)
      · exact Or.inl hs
      · right; left
        have hjpos := PrimeGap186.trial_band_positive_lower_of_seed a ha ha0 hseed (lt_of_not_ge hs)
        rcases hgap j hjpos with hz | hp
        · exact hz
        · rw [trialBandMassSum_configuration] at he
          exact False.elim ((not_lt_of_ge hp.le) he)
    · right; right
      simpa only [trialBandTail, trialBandMassSum_configuration] using hg

theorem trialBandInnerRow_sound {d m : ℕ} (R : TrialSourceRow)
    (a : Fin (m + 2) → ℝ) (ha : StrictMono a) (ha0 : a 0 = 0)
    (hseed : a (0 : Fin (m + 1)).succ ≤ (R.activation : ℝ))
    (X : Fin d → FiniteMeasure ℝ)
    (hcap : (∑ i, X i).restrict (Set.Ioc (a 0) (a (Fin.last (m + 1)))) = ∑ i, X i)
    (hgap : ∀ j : Fin (m + 1), 0 < a j.castSucc →
      PrimeGap186.fragmentBandMasses a (∑ i, X i) j = 0 ∨
        a j.castSucc < PrimeGap186.fragmentBandMasses a (∑ i, X i) j)
    (hrow : TrialBandInnerRow R a (fun i => PrimeGap186.fragmentBandMasses a (X i))) :
    TrialInnerRowAllowed R X := by
  rcases hrow with hOne | hcore | hband
  · exact Or.inl hOne
  · right; left
    rw [trialBandTotal, PrimeGap186.trial_band_total_sum a ha.monotone X hcap] at hcore
    exact hcore.le
  · apply trialInnerRowAllowed_of_band R a ha.monotone X hcap
    intro j
    rcases hband j with hs | he | hg
    · exact Or.inl hs
    · by_cases hs : a j.succ ≤ (R.activation : ℝ)
      · exact Or.inl hs
      · right; left
        have hjpos := PrimeGap186.trial_band_positive_lower_of_seed a ha ha0 hseed (lt_of_not_ge hs)
        rcases hgap j hjpos with hz | hp
        · exact hz
        · rw [trialBandMassSum_configuration] at he
          exact False.elim ((not_lt_of_ge hp.le) he)
    · right; right
      simpa only [trialBandTail, trialBandMassSum_configuration] using hg

#print axioms trialBandOuterRow_sound
#print axioms trialBandInnerRow_sound

end PrimeGap182
