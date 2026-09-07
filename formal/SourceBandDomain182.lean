import SourceBandProfiles182

/-! Open source domains and their eventual validity on finite fragment
configurations.  They retain the exact cell-index support separately from
the total-mass and atom-cap conditions. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace PrimeGap182

theorem trial_eventually_list_forall {α β : Type*} (l : List α) (F : Filter β)
    (P : α → β → Prop) (h : ∀ a ∈ l, ∀ᶠ b in F, P a b) :
    ∀ᶠ b in F, ∀ a ∈ l, P a b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have hl := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    filter_upwards [ha, hl] with b hab hlb
    simpa only [List.forall_mem_cons] using And.intro hab hlb

theorem isOpen_trialRowList {α : Type*} [TopologicalSpace α]
    (rows : List TrialSourceRow) (P : TrialSourceRow → α → Prop)
    (hP : ∀ R ∈ rows, IsOpen {x | P R x}) : IsOpen {x | ∀ R ∈ rows, P R x} := by
  induction rows with
  | nil => simp
  | cons R rows ih =>
    simpa only [List.forall_mem_cons, Set.ofPred_and] using
      (hP R (by simp)).inter (ih (fun T hT => hP T (List.mem_cons_of_mem R hT)))

def TrialBandSourceDomain {d m : ℕ} (outer inner : List TrialSourceRow)
    (radius : ℝ) (a : Fin (m + 2) → ℝ) (v : Fin d → Fin (m + 1) → ℝ) : Prop :=
  (∀ R ∈ outer, TrialBandOuterRow R a v) ∧
    (∀ R ∈ inner, TrialBandInnerRow R a v) ∧
    (∀ j : Fin (m + 1), (trialLargestCap : ℝ) < a j.succ →
      trialBandMassSum v j < a j.castSucc) ∧
    TrialBandCellInterior v ∧ trialBandTotal v < radius

theorem isOpen_trialBandSourceDomain {d m : ℕ} (outer inner : List TrialSourceRow)
    (radius : ℝ) (a : Fin (m + 2) → ℝ) :
    IsOpen {v : Fin d → Fin (m + 1) → ℝ | TrialBandSourceDomain outer inner radius a v} := by
  have ho := isOpen_trialRowList outer (fun R => @TrialBandOuterRow d m R a)
    (fun R _ => isOpen_trialBandOuterRow R a)
  have hi := isOpen_trialRowList inner (fun R => @TrialBandInnerRow d m R a)
    (fun R _ => isOpen_trialBandInnerRow R a)
  have hc : IsOpen {v : Fin d → Fin (m + 1) → ℝ |
      ∀ j : Fin (m + 1), (trialLargestCap : ℝ) < a j.succ →
        trialBandMassSum v j < a j.castSucc} := by
    apply PrimeGap186.trial_isOpen_finite_forall
    intro j
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun _ =>
      isOpen_lt (continuous_trialBandMassSum j) continuous_const
  exact ho.inter (hi.inter (hc.inter
    (isOpen_trialBandCellInterior.inter (isOpen_lt continuous_trialBandTotal continuous_const))))

theorem trialBandSourceDomain_sound {d m : ℕ} (outer inner : List TrialSourceRow)
    (ho : ∀ R ∈ outer, trialMesh < R.activation)
    (hi : ∀ R ∈ inner, trialMesh < R.activation)
    (radius : ℝ) (a : Fin (m + 2) → ℝ) (ha : StrictMono a) (ha0 : a 0 = 0)
    (hseed : a (0 : Fin (m + 1)).succ = (trialMesh : ℝ))
    (X : Fin d → FiniteMeasure ℝ)
    (hfull : (∑ i, X i).restrict (Set.Ioc (a 0) (a (Fin.last (m + 1)))) = ∑ i, X i)
    (hgap : ∀ j : Fin (m + 1), 0 < a j.castSucc →
      PrimeGap186.fragmentBandMasses a (∑ i, X i) j = 0 ∨
        a j.castSucc < PrimeGap186.fragmentBandMasses a (∑ i, X i) j)
    (hU : TrialBandSourceDomain outer inner radius a
      (fun i => PrimeGap186.fragmentBandMasses a (X i))) :
    TrialRowsAllowed outer inner X ∧ TrialCapAllowed trialLargestCap X ∧
      trialTotalMass X < radius ∧
      TrialBandCellInterior (fun i => PrimeGap186.fragmentBandMasses a (X i)) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, hU.2.2.2.1⟩
  · intro R hR
    apply trialBandOuterRow_sound R a ha ha0 _ X hfull hgap (hU.1 R hR)
    rw [hseed]
    exact (Rat.cast_lt.mpr (ho R hR)).le
  · intro R hR
    apply trialBandInnerRow_sound R a ha ha0 _ X hfull hgap (hU.2.1 R hR)
    rw [hseed]
    exact (Rat.cast_lt.mpr (hi R hR)).le
  · exact (PrimeGap186.trial_inward_band_cap_domain a ha ha0 (trialLargestCap : ℝ)
      (by rw [hseed]; exact trial_seed_cap.2.le)).2 X hfull hgap hU.2.2.1
  · simpa only [trialBandTotal, trialTotalMass,
      PrimeGap186.trial_band_total_sum a ha.monotone X hfull] using hU.2.2.2.2

def TrialBandOpenRow {d m : ℕ} (core activation : ℝ) (G : ℝ → ℝ → Prop)
    (a : Fin (m + 2) → ℝ) (v : Fin d → Fin (m + 1) → ℝ) : Prop :=
  trialBandTotal v < core ∨ ∀ j : Fin (m + 1),
    a j.succ ≤ activation ∨ trialBandMassSum v j < a j.castSucc ∨
      G (trialBandTail v j) (a j.succ)

theorem trialBandOpenRow_eventually {d : ℕ} {ι : Type*} [Fintype ι]
    (κ core activation : ℝ) (hA : (trialMesh : ℝ) < activation)
    (m : ℕ → ℕ) (a : (N : ℕ) → Fin (m N + 2) → ℝ)
    (hgeom : ∀ N, StrictMono (a N) ∧ a N 0 = 0 ∧
      a N (0 : Fin (m N + 1)).succ = (trialMesh : ℝ) ∧
      a N (Fin.last (m N + 1)) = κ)
    (hmesh : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      ∀ j : Fin (m N + 1), j ≠ 0 → a N j.succ - a N j.castSucc < ε)
    (X : Fin d → FiniteMeasure ℝ)
    (hfull : (∑ i, X i).restrict (Set.Ioc (0 : ℝ) κ) = ∑ i, X i)
    (z : ι → ℝ) (hz : ∀ k, 0 ≤ z k ∧ z k ≤ κ)
    (htail : (trialWeightedMeasure X).restrict (Set.Ioi (trialMesh : ℝ)) =
      ∑ k, ENNReal.ofReal (z k) • Measure.dirac (z k))
    (hNtail : (trialSourceCountMeasure X).restrict (Set.Ioi (trialMesh : ℝ)) =
      ∑ k, Measure.dirac (z k))
    (hfixed : trialSourceCountMeasure X {activation} = 0)
    (G : ℝ → ℝ → Prop) (hG : ∀ u, IsOpen {p | G u p})
    (hrow : trialTotalMass X < core ∨ trialSourceCountMeasure X
      {p : ℝ | activation < p ∧ ¬ G ((trialWeightedMeasure X).real (Set.Ici p)) p} = 0) :
    ∀ᶠ N in atTop, TrialBandOpenRow core activation G (a N)
      (fun i => PrimeGap186.fragmentBandMasses (a N) (X i)) := by
  classical
  rcases hrow with hcore | hbad
  · exact Filter.Eventually.of_forall fun N => Or.inl (by
      simpa only [trialBandTotal, trialTotalMass,
        PrimeGap186.trial_band_total_sum (a N) (hgeom N).1.monotone X
          (by simpa only [(hgeom N).2.1, (hgeom N).2.2.2] using hfull)] using hcore)
  have htail' : ((∑ i, X i : FiniteMeasure ℝ) : Measure ℝ).restrict
      (Set.Ioi (trialMesh : ℝ)) = ∑ k, ENNReal.ofReal (z k) • Measure.dirac (z k) := by
    simpa only [trialWeightedMeasure, FiniteMeasure.toMeasure_sum] using htail
  have hgood := PrimeGap186.trial_finite_count_strict_row (∑ i, X i)
    (trialSourceCountMeasure X) (trialMesh : ℝ) activation hA z hNtail G hfixed
    (by simpa only [FiniteMeasure.toMeasure_sum, trialWeightedMeasure] using hbad)
  obtain ⟨ε, hε, hfine⟩ := PrimeGap186.trial_finite_band_inward_row (∑ i, X i)
    (trialMesh : ℝ) κ activation hA.le z hz htail' G hG hgood
  filter_upwards [hmesh ε hε] with N hN
  right
  intro j
  rcases hfine (m N) (a N) (hgeom N).1.monotone (hgeom N).2.2.1
      (hgeom N).2.2.2 hN j with hlow | hempty | hgood
  · exact Or.inl hlow
  · by_cases hs : a N j.succ ≤ activation
    · exact Or.inl hs
    · right; left
      have hj := PrimeGap186.trial_band_positive_lower_of_seed (a N) (hgeom N).1
        (hgeom N).2.1 (by rw [(hgeom N).2.2.1]; exact hA.le) (lt_of_not_ge hs)
      rw [trialBandMassSum_configuration, hempty]
      exact hj
  · right; right
    simpa only [trialBandTail, trialBandMassSum_configuration] using hgood

#print axioms trialBandSourceDomain_sound
#print axioms trialBandOpenRow_eventually

end PrimeGap182
