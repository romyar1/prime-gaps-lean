import BandWeightedMoments182
import BandArrayAlgebra182

/-! The six actual source pairings needed by the smooth hybrid argument.
The base, enlarged, and subtraction faces are canonical 38-coordinate
arrays sampled from the masked marginal. The root is the weighted erasure
of the canonical 39-coordinate array. -/

noncomputable section
open MeasureTheory Filter PrimeGap186 PrimeGap182Analytic
open scoped BigOperators Topology

namespace PrimeGap182

inductive SieveFaceRole182
  | root | base | correction | rootMinusBase | subtractionMinusBase | rootMinusSubtraction
  deriving DecidableEq

open SieveFaceRole182

namespace TrialSmoothProfiles182

def sieveFacePart (P : TrialSmoothProfiles182) (i : Fin 39) (r : SieveFaceRole182) :
    (Fin 38 → Fin (P.m + 1) → ℝ) → ℝ :=
  match r with
  | root => fun _ => 0
  | base => P.bandMaskedFace 0 i
  | correction => fun Y => P.bandMaskedFace 1 i Y - P.bandMaskedFace 0 i Y
  | rootMinusBase => fun Y => -P.bandMaskedFace 0 i Y
  | subtractionMinusBase => fun Y => P.bandMaskedFace 2 i Y - P.bandMaskedFace 0 i Y
  | rootMinusSubtraction => fun Y => -P.bandMaskedFace 2 i Y

def sieveRootPart (P : TrialSmoothProfiles182) (r : SieveFaceRole182) :
    (Fin 39 → Fin (P.m + 1) → ℝ) → ℝ :=
  match r with
  | root | rootMinusBase | rootMinusSubtraction => P.F
  | base | correction | subtractionMinusBase => fun _ => 0

def sieveFaceProfile (P : TrialSmoothProfiles182) (i : Fin 39) (r : SieveFaceRole182)
    (Y : Fin 38 → Fin (P.m + 1) → ℝ) : ℝ :=
  match r with
  | root => P.bandErasure i Y
  | base => P.bandMaskedFace 0 i Y
  | correction => P.bandMaskedFace 1 i Y - P.bandMaskedFace 0 i Y
  | rootMinusBase => P.bandErasure i Y - P.bandMaskedFace 0 i Y
  | subtractionMinusBase => P.bandMaskedFace 2 i Y - P.bandMaskedFace 0 i Y
  | rootMinusSubtraction => P.bandErasure i Y - P.bandMaskedFace 2 i Y

def sieveFaceArray (P : TrialSmoothProfiles182) (H : Finset ℕ) (i : Fin 39)
    (r : SieveFaceRole182) (x : ℝ) : (Fin 38 → ℕ) →₀ ℝ :=
  erasedBandArray182 H P.a i (P.sieveFacePart i r) (P.sieveRootPart r) x

theorem continuous_sieveFacePart (P : TrialSmoothProfiles182) (i : Fin 39) (r : SieveFaceRole182) :
    Continuous (P.sieveFacePart i r) := by
  cases r
  · exact continuous_const
  · exact P.continuous_bandMaskedFace 0 i
  · exact (P.continuous_bandMaskedFace 1 i).sub (P.continuous_bandMaskedFace 0 i)
  · exact (P.continuous_bandMaskedFace 0 i).neg
  · exact (P.continuous_bandMaskedFace 2 i).sub (P.continuous_bandMaskedFace 0 i)
  · exact (P.continuous_bandMaskedFace 2 i).neg

theorem compact_sieveFacePart (P : TrialSmoothProfiles182) (i : Fin 39) (r : SieveFaceRole182) :
    HasCompactSupport (P.sieveFacePart i r) := by
  cases r
  · exact HasCompactSupport.zero
  · exact P.compact_bandMaskedFace 0 i
  · exact (P.compact_bandMaskedFace 1 i).sub (P.compact_bandMaskedFace 0 i)
  · exact (P.compact_bandMaskedFace 0 i).neg
  · exact (P.compact_bandMaskedFace 2 i).sub (P.compact_bandMaskedFace 0 i)
  · exact (P.compact_bandMaskedFace 2 i).neg

theorem continuous_sieveRootPart (P : TrialSmoothProfiles182) (r : SieveFaceRole182) :
    Continuous (P.sieveRootPart r) := by
  cases r <;> first | exact P.F_smooth.continuous | exact continuous_const

theorem compact_sieveRootPart (P : TrialSmoothProfiles182) (r : SieveFaceRole182) :
    HasCompactSupport (P.sieveRootPart r) := by
  cases r <;> first | exact P.F_compact | exact HasCompactSupport.zero

theorem sieveFaceProfile_eq_combined (P : TrialSmoothProfiles182) (i : Fin 39)
    (r : SieveFaceRole182) (Y : Fin 38 → Fin (P.m + 1) → ℝ) :
    P.sieveFaceProfile i r Y = bandCombinedFace182 P.a i (P.sieveFacePart i r) (P.sieveRootPart r) Y := by
  cases r <;> simp only [sieveFaceProfile, sieveFacePart, sieveRootPart,
    bandCombinedFace182, bandErasure, integral_zero, add_zero, zero_add] <;> ring

def sievePairWeight (k : Fin 6) : Fin 3 := ![0, 0, 1, 2, 0, 2] k
def sievePairLeft (k : Fin 6) : SieveFaceRole182 :=
  ![root, base, rootMinusBase, subtractionMinusBase, correction, correction] k
def sievePairRight (k : Fin 6) : SieveFaceRole182 :=
  ![base, base, correction, correction, correction, correction] k

def sievePairIntegral (P : TrialSmoothProfiles182) (i : Fin 39) (k : Fin 6) : ℝ :=
  ∫ Y, P.sieveFaceProfile i (sievePairLeft k) Y * P.sieveFaceProfile i (sievePairRight k) Y
    ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 P.a)

def sievePairMoment (P : TrialSmoothProfiles182) (H : Finset ℕ) (h : Fin 39 → ℕ)
    (i : Fin 39) (k : Fin 6) (x : ℝ) (res : ℕ) : ℝ :=
  bandWeightedBilinear182 H h i (sievePairWeight k)
    (P.sieveFaceArray H i (sievePairLeft k) x)
    (P.sieveFaceArray H i (sievePairRight k) x) x res

/-- Exactly six pairings per detected coordinate; no C-by-C distribution
estimate is added. The defect square with A-C is controlled separately. -/
def CoherentSources (P : TrialSmoothProfiles182) (H : Finset ℕ) (hH : H.card = 39) : Prop :=
  ∀ (i : Fin 39) (k : Fin 6),
    BandCoherentDiscrepancy182 H (H.orderEmbOfFin hH) i (sievePairWeight k)
      (P.sieveFaceArray H i (sievePairLeft k)) (P.sieveFaceArray H i (sievePairRight k))

theorem sieve_pair_moment (P : TrialSmoothProfiles182) {H : Finset ℕ} (hH : H.card = 39)
    (hs : P.CoherentSources H hH) (i : Fin 39) (k : Fin 6) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
      ∀ res : ℕ, Nat.Coprime (res + H.orderEmbOfFin hH i) (presievingModulus H x) →
        |P.sievePairMoment H (H.orderEmbOfFin hH) i k x res -
          (selbergWeightMean182 (sievePairWeight k) * P.sievePairIntegral i k) *
            sieveMomentScale182 H x| ≤ ε * sieveMomentScale182 H x := by
  have hm := erasedBandArray182_weighted_moment hH P.a P.strictMono P.zero P.last i
    (sievePairWeight k) (P.sieveFacePart i (sievePairLeft k)) (P.sieveFacePart i (sievePairRight k))
    (P.sieveRootPart (sievePairLeft k)) (P.sieveRootPart (sievePairRight k))
    (P.continuous_sieveFacePart i _).measurable (P.continuous_sieveFacePart i _).measurable
    (P.continuous_sieveRootPart _).measurable (P.continuous_sieveRootPart _).measurable
    ((P.compact_sieveFacePart i _).isCompact_range (P.continuous_sieveFacePart i _)).isBounded
    ((P.compact_sieveFacePart i _).isCompact_range (P.continuous_sieveFacePart i _)).isBounded
    ((P.compact_sieveRootPart _).isCompact_range (P.continuous_sieveRootPart _)).isBounded
    ((P.compact_sieveRootPart _).isCompact_range (P.continuous_sieveRootPart _)).isBounded
    (ae_of_all _ fun _ => (P.continuous_sieveFacePart i _).continuousAt)
    (ae_of_all _ fun _ => (P.continuous_sieveFacePart i _).continuousAt)
    (ae_of_all _ fun _ => (P.continuous_sieveRootPart _).continuousAt)
    (ae_of_all _ fun _ => (P.continuous_sieveRootPart _).continuousAt) (hs i k)
  simpa only [sievePairMoment, sieveFaceArray, sievePairIntegral,
    ← P.sieveFaceProfile_eq_combined] using hm

#print axioms sieveFaceProfile_eq_combined
#print axioms sieve_pair_moment

end TrialSmoothProfiles182
end PrimeGap182
