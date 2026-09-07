import SourceDataChecks182
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Data.List.Chain

/-! Rational certification of all 812 local-count bands.
The formula is derived geometrically in SourceCountGeometry182; it is not
the Python count algorithm imported as a premise. -/

namespace PrimeGap182

def trialSourceCountOffset : ℚ := 19 * trialMesh - trialEnlargedRadius

def trialSourceFirstIndex (c : TrialSourceCoverData) : ℕ :=
  (c.pieces.headD ⟨0, 0, 0⟩).first

def trialSourceCountFirst (r : TrialOuterCertificateData) : ℕ :=
  (r.counts.headD ⟨0, 0, 0, 0⟩).first

def trialSourceCountLast (r : TrialOuterCertificateData) : ℕ :=
  (r.counts.getLastD ⟨0, 0, 0, 0⟩).last

def trialSourceBandLower (r : TrialOuterCertificateData) (b : TrialSourceCountBand) : ℚ :=
  let n := if r.countCoarse then max (trialSourceFirstIndex r.cover) (48 * b.first) else b.first
  ((n : ℚ) + 39 / 2) * trialMesh

def trialSourceReservedMass (r : TrialOuterCertificateData) (k : ℕ) : ℚ :=
  max 0 (r.ownerMass - k * trialMesh / 2)

def trialSourceCountFloorBound (r : TrialOuterCertificateData)
    (b : TrialSourceCountBand) (k : ℕ) : ℕ :=
  let s := max (trialSourceBandLower r b) (trialSourceReservedMass r k)
  min 39 (min ⌊s / (s + trialSourceCountOffset)⌋₊
    (k + ⌊(s - trialSourceReservedMass r k) / (s + trialSourceCountOffset)⌋₊))

def TrialSourceCountBandCertified (r : TrialOuterCertificateData)
    (b : TrialSourceCountBand) : Prop :=
  if trialSourceBandLower r b + trialSourceCountOffset ≤ 0 then 39 ≤ b.count
  else ∀ k : Fin (r.maxOwners + 1),
    (r.maxOwners = 0 ∨ 0 < k.val) → trialSourceCountFloorBound r b k.val ≤ b.count

def TrialSourceCountTableShape (r : TrialOuterCertificateData) : Prop :=
  0 < r.counts.length ∧
  r.counts.IsChain (fun a b => a.last + 1 = b.first) ∧
  (∀ b : Fin r.counts.length, (r.counts.get b).first ≤ (r.counts.get b).last) ∧
  (∀ p : Fin r.cover.pieces.length,
    let c := r.cover.pieces.get p
    trialSourceFirstIndex r.cover ≤ c.first ∧
    if r.countCoarse then
      (trialSourceCountFirst r = 0 ∨ 48 * (trialSourceCountFirst r - 1) + 39 * 47 < c.first) ∧
        c.last < 48 * (trialSourceCountLast r + 1)
    else trialSourceCountFirst r ≤ c.first ∧ c.last ≤ trialSourceCountLast r)

set_option maxRecDepth 4096 in
theorem trialSourceCountBand_certified : ∀ j : Fin 60,
    ∀ b : Fin (trialOuterCertificates j).counts.length,
      TrialSourceCountBandCertified (trialOuterCertificates j)
        ((trialOuterCertificates j).counts.get b) := by
  unfold TrialSourceCountBandCertified
  decide +kernel

set_option maxRecDepth 4096 in
theorem trialSourceCountTable_shape : ∀ j : Fin 60,
    TrialSourceCountTableShape (trialOuterCertificates j) := by
  unfold TrialSourceCountTableShape
  decide +kernel

set_option maxRecDepth 4096 in
theorem trialSourceOwnerMass_bounds : ∀ j : Fin 60,
    let r := trialOuterCertificates j
    0 ≤ r.ownerMass ∧ r.ownerMass + trialSourceCountOffset ≤ 0 ∧
      r.maxOwners ≤ 39 ∧ (r.maxOwners = 0 → r.ownerMass = 0) := by
  decide +kernel

#print axioms trialSourceCountBand_certified
#print axioms trialSourceCountTable_shape
#print axioms trialSourceOwnerMass_bounds

end PrimeGap182
