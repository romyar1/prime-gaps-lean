import SourceOffender182
import SourceGroupSelection182

/-! Finite group cover with the literal bin inventory. The reusable lemma
is instantiated by the actual outer and inner data below. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace PrimeGap182

structure SourceCoverInventory (J : Type) where
  cover : J → TrialSourceCoverData
  high : J
  lowBins : List J
  rankBins : List J
  parameters : ∀ j, TrialSourceMarkParameters (cover j)
  highKind : (cover high).kind = .high
  lowPartition : SourceBinPartition (lowBins.map (fun j => trialSourceEndpoints (cover j)))
    (cover high).activation (cover high).split
  rankPartition : SourceBinPartition (rankBins.map (fun j => trialSourceEndpoints (cover j)))
    ((cover high).threshold / ((cover high).order + 1)) (cover high).hardCap
  lowMatch : ∀ j ∈ lowBins, (cover j).kind = .low ∧
    TrialSourceMatchesGroup (cover j) (cover high)
  rankMatch : ∀ j ∈ rankBins, (cover j).kind = .rankTwo ∧
    TrialSourceMatchesGroup (cover j) (cover high) ∧
    (cover j).lowerRadius = (cover high).lowerRadius

def trialOuterInventory (g : Fin 2) : SourceCoverInventory (Fin 60) where
  cover j := (trialOuterCertificates j).cover
  high := trialOuterHighBin g
  lowBins := trialOuterLowBins g
  rankBins := trialOuterRankBins g
  parameters := trialOuterMark_parameters
  highKind := (trialOuterBins_match_group g).2.2
  lowPartition := trialOuterLow_partition g
  rankPartition := trialOuterRank_partition g
  lowMatch := (trialOuterBins_match_group g).1
  rankMatch j hj := ⟨((trialOuterBins_match_group g).2.1 j hj).1,
    ((trialOuterBins_match_group g).2.1 j hj).2, trialOuterRank_radius g j hj⟩

def trialInnerInventory (g : Fin 5) : SourceCoverInventory (Fin 137) where
  cover j := (trialInnerCertificates j).cover
  high := trialInnerHighBin g
  lowBins := trialInnerLowBins g
  rankBins := trialInnerRankBins g
  parameters := trialInnerMark_parameters
  highKind := (trialInnerBins_match_group g).2.2
  lowPartition := trialInnerLow_partition g
  rankPartition := trialInnerRank_partition g
  lowMatch := (trialInnerBins_match_group g).1
  rankMatch j hj := ⟨((trialInnerBins_match_group g).2.1 j hj).1,
    ((trialInnerBins_match_group g).2.1 j hj).2, trialInnerRank_radius g j hj⟩

theorem trialInnerInventory_domain (g : Fin 5) (X : Fin 38 → FiniteMeasure ℝ)
    (hShell : TrialShellDomain (trialInnerGroupRole g) X) (j : Fin 137)
    (hj : j = (trialInnerInventory g).high ∨ j ∈ (trialInnerInventory g).lowBins ∨
      j ∈ (trialInnerInventory g).rankBins)
    (hl : ((trialInnerCertificates j).cover.lowerRadius : ℝ) < trialTotalMass X)
    (hu : trialTotalMass X ≤ ((trialInnerCertificates j).cover.upperRadius : ℝ)) :
    TrialSourceDomain (trialInnerCertificates j).cover X := by
  have hrole : trialSourceInnerRole j = trialInnerGroupRole g := by
    rcases hj with rfl | hj | hj
    · exact (trialInnerBins_role g).1
    · exact (trialInnerBins_role g).2.1 j hj
    · exact (trialInnerBins_role g).2.2 j hj
  exact trialSourceDomain_inner_of_shell j X (hrole.symm ▸ hShell) hl hu

def TrialMarkedOwnerWitness {ι : Type} [Fintype ι]
    (c : TrialSourceCoverData) (f : ι → ℝ) : Prop :=
  c.kind = .low ∨
    (c.kind = .rankTwo ∧ ∃ a b, a ≠ b ∧ (c.low : ℝ) ≤ f a ∧
      (c.threshold : ℝ) ≤ f a + (c.order : ℝ) * f b) ∨
    (c.kind = .high ∧ 3 ≤ (Finset.univ.filter (fun a : ι => (c.split : ℝ) < f a)).card)

theorem source_group_cover {J ι : Type} [Fintype ι] {d : ℕ}
    (I : SourceCoverInventory J) (X : Fin d → FiniteMeasure ℝ) (f : ι → ℝ)
    (hN : (trialSourceCountMeasure X).restrict (Set.Ioi (trialMesh : ℝ)) =
      ∑ a : ι, Measure.dirac (f a))
    (hW : (trialWeightedMeasure X).restrict (Set.Ioi (trialMesh : ℝ)) =
      ∑ a : ι, ENNReal.ofReal (f a) • Measure.dirac (f a))
    (hf : ∀ a, (trialMesh : ℝ) < f a)
    (hcap : ∀ a, f a ≤ ((I.cover I.high).hardCap : ℝ))
    (hlower : ((I.cover I.high).lowerRadius : ℝ) < trialTotalMass X)
    (hupper : trialTotalMass X ≤ ((I.cover I.high).upperRadius : ℝ))
    (hDomain : ∀ j, (j = I.high ∨ j ∈ I.lowBins ∨ j ∈ I.rankBins) →
      ((I.cover j).lowerRadius : ℝ) < trialTotalMass X →
      trialTotalMass X ≤ ((I.cover j).upperRadius : ℝ) → TrialSourceDomain (I.cover j) X)
    (a : ι) (hactivation : ((I.cover I.high).activation : ℝ) < f a)
    (htwo : 2 ≤ (Finset.univ.filter (fun b : ι => f a ≤ f b)).card)
    (hbad : ((I.cover I.high).threshold : ℝ) <
      (∑ b ∈ Finset.univ.filter (fun b : ι => f a ≤ f b), f b) +
        (((I.cover I.high).order : ℝ) - 1) * f a)
    (hLowRadius : ∀ j ∈ I.lowBins,
      f a ∈ Set.Ioc ((I.cover j).low : ℝ) ((I.cover j).high : ℝ) →
        ((I.cover j).lowerRadius : ℝ) < trialTotalMass X) :
    ∃ j, (j = I.high ∨ j ∈ I.lowBins ∨ j ∈ I.rankBins) ∧
      TrialSourceDomain (I.cover j) X ∧ 1 ≤ trialSourceUnmasked (I.cover j) X ∧
      TrialMarkedOwnerWitness (I.cover j) f := by
  let G := I.cover I.high
  have hG := I.parameters I.high
  have hm : (1 : ℝ) ≤ (G.order : ℝ) := by exact_mod_cast hG.2.1
  have hmpos : (0 : ℝ) < (G.order : ℝ) := lt_of_lt_of_le zero_lt_one hm
  have hδ : (0 : ℝ) < (trialMesh : ℝ) := Rat.cast_pos.mpr trialMesh_pos
  have hhigh := hG.2.2.2.2.2
  have hhighEq : G.low = G.split ∧ G.high = G.hardCap := by
    simpa only [I.highKind, reduceCtorEq, ite_false, G] using hhigh
  have hsplit : (trialMesh : ℝ) ≤ (G.split : ℝ) := by
    exact Rat.cast_le.mpr (hhighEq.1 ▸ hG.1.le)
  by_cases haLow : f a ≤ (G.split : ℝ)
  · obtain ⟨j, hj, hjlo, hjhi⟩ := sourceBinPartition_image_mem _ _ _ _ I.lowPartition (f a)
      ⟨hactivation, haLow⟩
    have hjbin : f a ∈ Set.Ioc ((I.cover j).low : ℝ) ((I.cover j).high : ℝ) := ⟨hjlo, hjhi⟩
    obtain ⟨hkind, hfamily, hdim, horder, hact, hthreshold, hlo, hhi, hcapEq, hsplitEq⟩ :=
      I.lowMatch j hj
    have hc := I.parameters j
    have hlow : (I.cover j).low < (I.cover j).high ∧
        (I.cover j).high ≤ (I.cover j).witnessUpper ∧ 0 ≤ (I.cover j).slope ∧
        (I.cover j).high ≤ (I.cover j).split := by
      simpa only [hkind, ite_true] using hc.2.2.2.2.2
    refine ⟨j, Or.inr (Or.inl hj), hDomain j (Or.inr (Or.inl hj)) (hLowRadius j hj hjbin) (by
      simpa only [hhi] using hupper), ?_, Or.inl hkind⟩
    apply trialSource_low_of_linear_offender (I.cover j) X hkind
      (by exact_mod_cast hc.2.1) (by exact_mod_cast hlow.2.2.1) (Rat.cast_le.mpr hlow.2.1)
      (trialMesh : ℝ) f hN (Rat.cast_le.mpr hc.1.le) a hjbin
    rw [source_weighted_inclusive_tail X _ f (fun b => (hδ.trans (hf b)).le) hW (f a) (hf a),
      horder, hthreshold]
    exact hbad
  · have hp : (G.split : ℝ) < f a := lt_of_not_ge haLow
    have hguard : (G.hardCap : ℝ) + (G.order : ℝ) * (G.split : ℝ) ≤ (G.threshold : ℝ) := by
      exact_mod_cast hG.2.2.2.1
    rcases source_two_high_or_balanced_pair f (G.order : ℝ) (G.threshold : ℝ)
      (G.split : ℝ) (G.hardCap : ℝ) hmpos hcap hguard a hp htwo hbad with hthree | hpair
    · refine ⟨I.high, Or.inl rfl, hDomain I.high (Or.inl rfl) hlower hupper,
        trialSource_high_unmasked_one_le G X I.highKind _ f hN hsplit hthree,
        Or.inr (Or.inr ⟨I.highKind, hthree⟩)⟩
    · obtain ⟨b, c, hne, hmax, hcb, _hcSplit, hpair, hq, hcut⟩ := hpair
      have hq' : (((G.threshold / (G.order + 1) : ℚ) : ℝ)) < f b := by
        simpa only [Rat.cast_div, Rat.cast_add, Rat.cast_one] using hq
      obtain ⟨j, hj, hjlo, hjhi⟩ := sourceBinPartition_image_mem _ _ _ _ I.rankPartition (f b)
        ⟨hq', hcap b⟩
      obtain ⟨hkind, hmatch, hradius⟩ := I.rankMatch j hj
      obtain ⟨hfamily, hdim, horder, hact, hthreshold, hlo, hhi, hcapEq, hsplitEq⟩ := hmatch
      have hc := I.parameters j
      have hjpair : (((I.cover j).threshold : ℝ) - f b) / ((I.cover j).order : ℝ) < f c := by
        rw [hthreshold, horder]
        exact (div_lt_iff₀ hmpos).mpr (by linarith only [hpair])
      have hjcut : (trialMesh : ℝ) ≤
          (((I.cover j).threshold : ℝ) - f b) / ((I.cover j).order : ℝ) := by
        rw [hthreshold, horder]
        exact hsplit.trans hcut
      refine ⟨j, Or.inr (Or.inr hj), hDomain j (Or.inr (Or.inr hj)) (by simpa only [hradius] using hlower)
        (by simpa only [hhi] using hupper), ?_, Or.inr (Or.inl ⟨hkind, b, c, hne, hjlo.le, ?_⟩)⟩
      · exact trialSource_rank_unmasked_one_le (I.cover j) X hkind _ f hN
          (Rat.cast_le.mpr hc.1.le) b c hne ⟨hjlo, hjhi⟩ hmax hcb hjcut hjpair
      · simpa only [horder, hthreshold] using hpair.le

theorem trialSourceOwnerEvent_of_marked_witness (j : Fin 60)
    (X : Fin 39 → FiniteMeasure ℝ) (n : Fin 39 → ℕ)
    (x : (i : Fin 39) → Fin (n i) → ℝ)
    (hx : ∀ i a, (trialMesh : ℝ) < x i a)
    (htail : ∀ i, (X i : Measure ℝ).restrict (Set.Ioi (trialMesh : ℝ)) =
      ∑ a : Fin (n i), ENNReal.ofReal (x i a) • Measure.dirac (x i a))
    (h : TrialMarkedOwnerWitness (trialOuterCertificates j).cover
      (fun a : (i : Fin 39) × Fin (n i) => x a.1 a.2)) :
    TrialSourceOwnerEvent (trialOuterCertificates j) X := by
  have hδ : (0 : ℝ) < (trialMesh : ℝ) := Rat.cast_pos.mpr trialMesh_pos
  rcases h with hlow | ⟨hrank, a, b, hne, hlo, hpair⟩ | ⟨hhigh, hthree⟩
  · exact trialSourceOwnerEvent_low _ (trialOuterOwner_formula j) hlow X
  · exact trialSourceOwnerEvent_rank_pair _ (trialOuterOwner_formula j) hrank
      (by exact_mod_cast (trialOuterMark_parameters j).2.1) X _ hδ n x hx htail a b hne hlo hpair
  · exact trialSourceOwnerEvent_high _ (trialOuterOwner_formula j) hhigh X _ hδ n x hx htail hthree

#print axioms source_group_cover
#print axioms trialSourceOwnerEvent_of_marked_witness

end PrimeGap182
