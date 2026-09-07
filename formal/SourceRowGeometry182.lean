import SourceDomainGeometry182
import SourceEventGeometry182

/-! Exact row-to-group geometry for the actual source inventory. The low
sources have clipped radial lower endpoints; these are checked against
the offending row, not replaced by the group's un-clipped endpoint. -/

namespace PrimeGap182

def trialSourceEffectiveOrder (R : TrialSourceRow) : ℚ :=
  if R.order ≤ 2 then 2 else 5 / 2

def trialSourceRowCore (outer : Bool) (R : TrialSourceRow) : ℚ :=
  if outer then R.outerCore else R.innerCore

def trialSourceRowThreshold (outer : Bool) (R : TrialSourceRow) : ℚ :=
  if outer then R.outerThreshold else R.innerThreshold

def trialLadderRowReferences (side : Fin 2) : List (Fin 2 × ℕ) :=
  (List.range (if side = 0 then trialOldSourceRows.length else trialNewSourceRows.length)).map
    (fun i => (side, i))

def trialAllRowReferences : List (Fin 2 × ℕ) :=
  trialLadderRowReferences 0 ++ trialLadderRowReferences 1

set_option maxRecDepth 10000 in
theorem trialRowReferences_exact :
    trialAllRowReferences.map trialRowByReference = trialOldSourceRows ++ trialNewSourceRows := by
  rfl

set_option maxRecDepth 10000 in
theorem trialLadderReferences_exact (side : Fin 2) :
    (trialLadderRowReferences side).map trialRowByReference =
      if side = 0 then trialOldSourceRows else trialNewSourceRows := by
  fin_cases side <;> rfl

def trialInnerFirstGroup (side : Fin 2) : Fin 5 := if side = 0 then 0 else 2
def trialInnerSecondGroup (side : Fin 2) : Fin 5 := if side = 0 then 1 else 3
def trialInnerGroupRole (g : Fin 5) : Fin 5 :=
  if g.val < 2 then 1 else if g.val < 4 then 2 else 3

def TrialSourceCapCompatible (outer : Bool) (R : TrialSourceRow) (cap : ℚ) : Prop :=
  0 < R.innerThreshold ∧
    (2 < R.order → 3 * R.innerThreshold ≤ 7 * R.plateau) ∧
    if outer then
      if R.order ≤ 2 then 2 * cap ≤ R.outerThreshold
      else cap + min ((3 / 2) * cap) R.plateau ≤ R.outerThreshold ∧
        3 * cap - min ((3 / 2) * cap) R.plateau ≤ R.innerThreshold
    else
      if R.order ≤ 2 then 2 * cap ≤ R.innerThreshold
      else cap + (3 * cap - min ((3 / 2) * cap) R.plateau) ≤ R.innerThreshold ∧
        min ((3 / 2) * cap) R.plateau ≤ R.outerThreshold

set_option maxRecDepth 10000 in
theorem trialOuterGroup_caps : ∀ g : Fin 2, ∀ ref ∈ (trialOuterGroup g).sourceRows,
    TrialSourceCapCompatible true (trialRowByReference ref) (trialOuterGroup g).hardCap := by
  unfold TrialSourceCapCompatible
  decide +kernel

set_option maxRecDepth 10000 in
theorem trialInnerGroup_caps : ∀ g : Fin 5, ∀ ref ∈ (trialInnerGroup g).sourceRows,
    TrialSourceCapCompatible false (trialRowByReference ref) (trialInnerGroup g).hardCap := by
  unfold TrialSourceCapCompatible
  decide +kernel

set_option maxRecDepth 10000 in
theorem trialOuterGroup_row_ranges :
    (trialOuterGroup 1).lowerRadius = (trialOuterGroup 0).upperRadius ∧
    (∀ ref ∈ trialAllRowReferences,
      (trialOuterGroup 0).lowerRadius ≤ (trialRowByReference ref).outerCore ∧
      (ref ∈ (trialOuterGroup 0).sourceRows ∨
        (trialOuterGroup 0).upperRadius ≤ (trialRowByReference ref).outerCore) ∧
      ref ∈ (trialOuterGroup 1).sourceRows) := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem trialInnerGroup_row_ranges : ∀ side : Fin 2,
    let G₀ := trialInnerGroup (trialInnerFirstGroup side)
    let G₁ := trialInnerGroup (trialInnerSecondGroup side)
    G₁.lowerRadius = G₀.upperRadius ∧
    (∀ ref ∈ trialLadderRowReferences side,
      (trialRowByReference ref).order ≠ 1 →
      G₀.lowerRadius ≤ (trialRowByReference ref).innerCore ∧
      (ref ∈ G₀.sourceRows ∨ G₀.upperRadius ≤ (trialRowByReference ref).innerCore) ∧
      ref ∈ G₁.sourceRows) := by
  decide +kernel

/-- The radius lost by clipping is already excluded by the actual core
or by the offending row's own threshold. -/
def TrialSourceLowClip (outer : Bool) (c G : TrialSourceCoverData) : Prop :=
  ∀ ref ∈ G.sourceRows, (trialRowByReference ref).activation < c.high →
    ref ∈ c.sourceRows ∧
      c.lowerRadius ≤ max G.lowerRadius
        (max (trialSourceRowCore outer (trialRowByReference ref))
          (trialSourceRowThreshold outer (trialRowByReference ref) -
            (trialSourceEffectiveOrder (trialRowByReference ref) - 1) * c.high))

set_option maxRecDepth 10000 in
theorem trialOuterLow_clipping : ∀ g : Fin 2, ∀ j ∈ trialOuterLowBins g,
    TrialSourceLowClip true (trialOuterCertificates j).cover (trialOuterGroup g) := by
  unfold TrialSourceLowClip
  decide +kernel

set_option maxRecDepth 10000 in
theorem trialInnerLow_clipping : ∀ g : Fin 5, ∀ j ∈ trialInnerLowBins g,
    TrialSourceLowClip false (trialInnerCertificates j).cover (trialInnerGroup g) := by
  unfold TrialSourceLowClip
  decide +kernel

set_option maxRecDepth 10000 in
theorem trialOuterRank_radius : ∀ g : Fin 2, ∀ j ∈ trialOuterRankBins g,
    (trialOuterCertificates j).cover.lowerRadius = (trialOuterGroup g).lowerRadius := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem trialInnerRank_radius : ∀ g : Fin 5, ∀ j ∈ trialInnerRankBins g,
    (trialInnerCertificates j).cover.lowerRadius = (trialInnerGroup g).lowerRadius := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem trialSourceGroups_piece_caps :
    (∀ g : Fin 2, ∀ p ∈ (trialOuterGroup g).pieces, p.cap ≤ (trialOuterGroup g).hardCap) ∧
    (∀ g : Fin 5, ∀ p ∈ (trialInnerGroup g).pieces, p.cap ≤ (trialInnerGroup g).hardCap) := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem trialSourceGroups_shell_upper :
    (∀ g ∈ trialGridShells 0, (g.upper : ℚ) * trialMesh ≤ (trialOuterGroup 1).upperRadius) ∧
    (∀ side : Fin 2, ∀ g ∈ trialGridShells (trialInnerGroupRole (trialInnerSecondGroup side)),
      (g.upper : ℚ) * trialMesh ≤ (trialInnerGroup (trialInnerSecondGroup side)).upperRadius) ∧
    (∀ g ∈ trialGridShells 3, (g.upper : ℚ) * trialMesh ≤ (trialInnerGroup 4).upperRadius) := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem trialInnerBins_role : ∀ g : Fin 5,
    trialSourceInnerRole (trialInnerHighBin g) = trialInnerGroupRole g ∧
    (∀ j ∈ trialInnerLowBins g, trialSourceInnerRole j = trialInnerGroupRole g) ∧
    (∀ j ∈ trialInnerRankBins g, trialSourceInnerRole j = trialInnerGroupRole g) := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem trialSubtractionGroup_geometry :
    (trialInnerGroup 4).lowerRadius = trialSubtractionSourceRow.outerCore ∧
    (trialInnerGroup 4).activation = trialSubtractionSourceRow.activation ∧
    (trialInnerGroup 4).threshold = trialSubtractionSourceRow.outerThreshold ∧
    (trialInnerGroup 4).order = trialSourceEffectiveOrder trialSubtractionSourceRow ∧
    TrialSourceCapCompatible true trialSubtractionSourceRow (trialInnerGroup 4).hardCap ∧
    (∀ j ∈ trialInnerLowBins 4,
      (trialInnerCertificates j).cover.lowerRadius = (trialInnerGroup 4).lowerRadius) := by
  unfold TrialSourceCapCompatible
  decide +kernel

theorem sourceLow_clipped_radius_lt (outer : Bool) (c G : TrialSourceCoverData)
    (hclip : TrialSourceLowClip outer c G) (ref : Fin 2 × ℕ) (href : ref ∈ G.sourceRows)
    (s p : ℝ) (hactivation : ((trialRowByReference ref).activation : ℝ) < p)
    (hhigh : p ≤ (c.high : ℝ))
    (hgroup : (G.lowerRadius : ℝ) < s)
    (hcore : (trialSourceRowCore outer (trialRowByReference ref) : ℝ) < s)
    (hbad : (trialSourceRowThreshold outer (trialRowByReference ref) : ℝ) <
      s + ((trialSourceEffectiveOrder (trialRowByReference ref) : ℝ) - 1) * p) :
    (c.lowerRadius : ℝ) < s := by
  have ha : (trialRowByReference ref).activation < c.high :=
    Rat.cast_lt.mp (hactivation.trans_le hhigh)
  have hm : (0 : ℝ) ≤ (trialSourceEffectiveOrder (trialRowByReference ref) : ℝ) - 1 := by
    unfold trialSourceEffectiveOrder
    split_ifs <;> norm_num
  have hlast : (trialSourceRowThreshold outer (trialRowByReference ref) : ℝ) -
      ((trialSourceEffectiveOrder (trialRowByReference ref) : ℝ) - 1) * (c.high : ℝ) < s := by
    nlinarith only [hbad, mul_le_mul_of_nonneg_left hhigh hm]
  have h := Rat.cast_le (K := ℝ).mpr (hclip ref href ha).2
  push_cast at h
  exact h.trans_lt (max_lt hgroup (max_lt hcore hlast))

#print axioms trialOuterGroup_row_ranges
#print axioms trialInnerGroup_row_ranges
#print axioms trialOuterLow_clipping
#print axioms trialInnerLow_clipping
#print axioms trialSubtractionGroup_geometry
#print axioms sourceLow_clipped_radius_lt

end PrimeGap182
