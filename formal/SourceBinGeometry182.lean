import SourceCoverEvents182
import SourceEventData182

/-! Complete real-interval coverage by the literal low and largest-mark
bins. The indices refer to the original 60/137 source integral records. -/

namespace PrimeGap182

def trialOuterHighBin (g : Fin 2) : Fin 60 := ![28, 29] g
def trialInnerHighBin (g : Fin 5) : Fin 137 := ![78, 91, 106, 120, 136] g

def trialOuterGroup (g : Fin 2) : TrialSourceCoverData :=
  (trialOuterCertificates (trialOuterHighBin g)).cover

def trialInnerGroup (g : Fin 5) : TrialSourceCoverData :=
  (trialInnerCertificates (trialInnerHighBin g)).cover

def trialOuterLowBins (g : Fin 2) : List (Fin 60) :=
  ![[30, 31, 32, 33, 34, 35, 36, 37],
    [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59]] g

def trialOuterRankBins (g : Fin 2) : List (Fin 60) :=
  ![[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13],
    [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]] g

def trialInnerLowBins (g : Fin 5) : List (Fin 137) :=
  ![[0, 1, 2, 3, 4, 5, 6, 7],
    [36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56],
    [8, 9, 10, 11, 12, 13, 14, 15],
    [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35],
    [57, 58, 59, 60, 61, 62, 63]] g

def trialInnerRankBins (g : Fin 5) : List (Fin 137) :=
  ![[64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77],
    [79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90],
    [92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105],
    [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119],
    [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]] g

def SourceBinPartition (L : List (ℚ × ℚ)) (a b : ℚ) : Prop :=
  L ≠ [] ∧ L.IsChain (fun x y => x.2 = y.1) ∧
    (L.headD (0, 0)).1 ≤ a ∧ b ≤ (L.getLastD (0, 0)).2

def trialSourceEndpoints (c : TrialSourceCoverData) : ℚ × ℚ := (c.low, c.high)

set_option maxRecDepth 4096 in
theorem trialOuterLow_partition : ∀ g : Fin 2,
    SourceBinPartition ((trialOuterLowBins g).map
      (fun j => trialSourceEndpoints (trialOuterCertificates j).cover))
      (trialOuterGroup g).activation (trialOuterGroup g).split := by
  unfold SourceBinPartition
  decide +kernel

set_option maxRecDepth 4096 in
theorem trialOuterRank_partition : ∀ g : Fin 2,
    SourceBinPartition ((trialOuterRankBins g).map
      (fun j => trialSourceEndpoints (trialOuterCertificates j).cover))
      ((trialOuterGroup g).threshold / ((trialOuterGroup g).order + 1))
      (trialOuterGroup g).hardCap := by
  unfold SourceBinPartition
  decide +kernel

set_option maxRecDepth 10000 in
theorem trialInnerLow_partition : ∀ g : Fin 5,
    SourceBinPartition ((trialInnerLowBins g).map
      (fun j => trialSourceEndpoints (trialInnerCertificates j).cover))
      (trialInnerGroup g).activation (trialInnerGroup g).split := by
  unfold SourceBinPartition
  intro g
  fin_cases g <;> decide +kernel

set_option maxRecDepth 4096 in
theorem trialInnerRank_partition : ∀ g : Fin 5,
    SourceBinPartition ((trialInnerRankBins g).map
      (fun j => trialSourceEndpoints (trialInnerCertificates j).cover))
      ((trialInnerGroup g).threshold / ((trialInnerGroup g).order + 1))
      (trialInnerGroup g).hardCap := by
  unfold SourceBinPartition
  decide +kernel

def TrialSourceMatchesGroup (c G : TrialSourceCoverData) : Prop :=
  c.family = G.family ∧ c.dimension = G.dimension ∧ c.order = G.order ∧
    c.activation = G.activation ∧ c.threshold = G.threshold ∧
    G.lowerRadius ≤ c.lowerRadius ∧ c.upperRadius = G.upperRadius ∧
    c.hardCap = G.hardCap ∧ c.split = G.split

set_option maxRecDepth 4096 in
theorem trialOuterBins_match_group : ∀ g : Fin 2,
    (∀ j ∈ trialOuterLowBins g,
      (trialOuterCertificates j).cover.kind = .low ∧
        TrialSourceMatchesGroup (trialOuterCertificates j).cover (trialOuterGroup g)) ∧
    (∀ j ∈ trialOuterRankBins g,
      (trialOuterCertificates j).cover.kind = .rankTwo ∧
        TrialSourceMatchesGroup (trialOuterCertificates j).cover (trialOuterGroup g)) ∧
      (trialOuterGroup g).kind = .high := by
  unfold TrialSourceMatchesGroup
  decide +kernel

set_option maxRecDepth 4096 in
theorem trialInnerBins_match_group : ∀ g : Fin 5,
    (∀ j ∈ trialInnerLowBins g,
      (trialInnerCertificates j).cover.kind = .low ∧
        TrialSourceMatchesGroup (trialInnerCertificates j).cover (trialInnerGroup g)) ∧
    (∀ j ∈ trialInnerRankBins g,
      (trialInnerCertificates j).cover.kind = .rankTwo ∧
        TrialSourceMatchesGroup (trialInnerCertificates j).cover (trialInnerGroup g)) ∧
      (trialInnerGroup g).kind = .high := by
  unfold TrialSourceMatchesGroup
  decide +kernel

theorem sourceBinChain_mem (L : List (ℚ × ℚ)) :
    L.IsChain (fun x y => x.2 = y.1) → L ≠ [] →
      ∀ p : ℝ, ((L.headD (0, 0)).1 : ℝ) < p → p ≤ ((L.getLastD (0, 0)).2 : ℝ) →
        ∃ v ∈ L, (v.1 : ℝ) < p ∧ p ≤ (v.2 : ℝ) := by
  induction L with
  | nil => intro _ h; exact (h rfl).elim
  | cons a L ih =>
    intro hchain _ p hlo hhi
    cases L with
    | nil => exact ⟨a, by simp, by simpa using hlo, by simpa using hhi⟩
    | cons b L =>
      by_cases ha : p ≤ (a.2 : ℝ)
      · exact ⟨a, by simp, by simpa using hlo, ha⟩
      · have hab := (List.isChain_cons_cons.mp hchain).1
        obtain ⟨v, hv, hp⟩ := ih (List.isChain_cons_cons.mp hchain).2 (by simp) p
          (by simpa only [List.headD_cons, ← hab] using lt_of_not_ge ha)
          (by simpa using hhi)
        exact ⟨v, List.mem_cons_of_mem a hv, hp⟩

theorem sourceBinPartition_image_mem {ι : Type*} (L : List ι)
    (f : ι → ℚ × ℚ) (a b : ℚ) (h : SourceBinPartition (L.map f) a b)
    (p : ℝ) (hp : (a : ℝ) < p ∧ p ≤ (b : ℝ)) :
    ∃ j ∈ L, ((f j).1 : ℝ) < p ∧ p ≤ ((f j).2 : ℝ) := by
  obtain ⟨v, hv, hvl, hvu⟩ := sourceBinChain_mem (L.map f) h.2.1 h.1 p
    ((Rat.cast_le.mpr h.2.2.1).trans_lt hp.1) (hp.2.trans (Rat.cast_le.mpr h.2.2.2))
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
  exact ⟨j, hj, hvl, hvu⟩

theorem trialOuterLow_bin_exists (g : Fin 2) (p : ℝ)
    (hp : ((trialOuterGroup g).activation : ℝ) < p ∧ p ≤ ((trialOuterGroup g).split : ℝ)) :
    ∃ j ∈ trialOuterLowBins g,
      p ∈ Set.Ioc ((trialOuterCertificates j).cover.low : ℝ)
        ((trialOuterCertificates j).cover.high : ℝ) :=
  sourceBinPartition_image_mem _ _ _ _ (trialOuterLow_partition g) p hp

theorem trialOuterRank_bin_exists (g : Fin 2) (p : ℝ)
    (hp : (((trialOuterGroup g).threshold / ((trialOuterGroup g).order + 1) : ℚ) : ℝ) < p ∧
      p ≤ ((trialOuterGroup g).hardCap : ℝ)) :
    ∃ j ∈ trialOuterRankBins g,
      p ∈ Set.Ioc ((trialOuterCertificates j).cover.low : ℝ)
        ((trialOuterCertificates j).cover.high : ℝ) :=
  sourceBinPartition_image_mem _ _ _ _ (trialOuterRank_partition g) p hp

theorem trialInnerLow_bin_exists (g : Fin 5) (p : ℝ)
    (hp : ((trialInnerGroup g).activation : ℝ) < p ∧ p ≤ ((trialInnerGroup g).split : ℝ)) :
    ∃ j ∈ trialInnerLowBins g,
      p ∈ Set.Ioc ((trialInnerCertificates j).cover.low : ℝ)
        ((trialInnerCertificates j).cover.high : ℝ) :=
  sourceBinPartition_image_mem _ _ _ _ (trialInnerLow_partition g) p hp

theorem trialInnerRank_bin_exists (g : Fin 5) (p : ℝ)
    (hp : (((trialInnerGroup g).threshold / ((trialInnerGroup g).order + 1) : ℚ) : ℝ) < p ∧
      p ≤ ((trialInnerGroup g).hardCap : ℝ)) :
    ∃ j ∈ trialInnerRankBins g,
      p ∈ Set.Ioc ((trialInnerCertificates j).cover.low : ℝ)
        ((trialInnerCertificates j).cover.high : ℝ) :=
  sourceBinPartition_image_mem _ _ _ _ (trialInnerRank_partition g) p hp

#print axioms trialOuterLow_bin_exists
#print axioms trialOuterRank_bin_exists
#print axioms trialInnerLow_bin_exists
#print axioms trialInnerRank_bin_exists
#print axioms trialOuterBins_match_group
#print axioms trialInnerBins_match_group

end PrimeGap182
