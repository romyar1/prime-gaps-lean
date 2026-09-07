import SourcePairingMoments182
import PrimeTranslate182

/-! Exact arithmetic identification of the six bilinear source pairings
and the exceptional square with the seven terms of the hybrid lower bound. -/

noncomputable section
open MeasureTheory Filter PrimeGap186 PrimeGap182Analytic
open scoped BigOperators Topology

namespace PrimeGap182.TrialSmoothProfiles182
open SieveFaceRole182

def bandRoot (P : TrialSmoothProfiles182) (H : Finset ℕ) (h : Fin 39 → ℕ)
    (x : ℝ) (n : ℕ) : ℝ :=
  sampledSelbergRoot (canonicalBandArray182 H P.a P.F x) (fun j => n + h j)

def bandMask (P : TrialSmoothProfiles182) (H : Finset ℕ) (h : Fin 39 → ℕ)
    (i : Fin 39) (b : Fin 3) (x : ℝ) (n : ℕ) : ℝ :=
  sampledSelbergRoot (canonicalBandArray182 H P.a (P.bandMaskedFace b i) x)
    (fun j => n + h (i.succAbove j))

def originalFaceValue (P : TrialSmoothProfiles182) (H : Finset ℕ) (h : Fin 39 → ℕ)
    (i : Fin 39) (r : SieveFaceRole182) (x : ℝ) (n : ℕ) : ℝ :=
  match r with
  | root => P.bandRoot H h x n
  | base => P.bandMask H h i 0 x n
  | correction => P.bandMask H h i 1 x n - P.bandMask H h i 0 x n
  | rootMinusBase => P.bandRoot H h x n - P.bandMask H h i 0 x n
  | subtractionMinusBase => P.bandMask H h i 2 x n - P.bandMask H h i 0 x n
  | rootMinusSubtraction => P.bandRoot H h x n - P.bandMask H h i 2 x n

def erasedFaceValue (P : TrialSmoothProfiles182) (H : Finset ℕ) (h : Fin 39 → ℕ)
    (i : Fin 39) (r : SieveFaceRole182) (x : ℝ) (n : ℕ) : ℝ :=
  sampledSelbergRoot (P.sieveFaceArray H i r x) (fun j => n + h (i.succAbove j))

theorem weighted_erasedFaceValue (P : TrialSmoothProfiles182) (H : Finset ℕ)
    (h : Fin 39 → ℕ) (i : Fin 39) (r : SieveFaceRole182) (w : Fin 3)
    (x : ℝ) (hx : 1 < x) (n : ℕ) (hxn : x ≤ ((n + h i : ℕ) : ℝ)) :
    selbergWeight182 w x (n + h i) * P.erasedFaceValue H h i r x n =
      selbergWeight182 w x (n + h i) * P.originalFaceValue H h i r x n := by
  have hA := canonicalBandArray182_weighted_erasure H P.a P.F i h w x hx n hxn
  cases r <;> simp only [erasedFaceValue, sieveFaceArray, sieveFacePart, sieveRootPart,
    originalFaceValue, bandRoot, bandMask, erasedBandArray182, canonicalBandArray182_zero,
    canonicalBandArray182_sub, canonicalBandArray182_neg, selbergErasedArray39_zero,
    zero_add, add_zero, sampledSelbergRoot_add, sampledSelbergRoot_sub,
    sampledSelbergRoot_neg] <;> nlinarith only [hA]

theorem weighted_erasedFaceValue_mul (P : TrialSmoothProfiles182) (H : Finset ℕ)
    (h : Fin 39 → ℕ) (i : Fin 39) (r s : SieveFaceRole182) (w : Fin 3)
    (x : ℝ) (hx : 1 < x) (n : ℕ) (hxn : x ≤ ((n + h i : ℕ) : ℝ)) :
    selbergWeight182 w x (n + h i) * P.erasedFaceValue H h i r x n * P.erasedFaceValue H h i s x n =
      selbergWeight182 w x (n + h i) * P.originalFaceValue H h i r x n * P.originalFaceValue H h i s x n := by
  by_cases hw : selbergWeight182 w x (n + h i) = 0
  · simp only [hw, zero_mul]
  · rw [mul_left_cancel₀ hw (P.weighted_erasedFaceValue H h i r w x hx n hxn),
      mul_left_cancel₀ hw (P.weighted_erasedFaceValue H h i s w x hx n hxn)]

def sievePairValue (P : TrialSmoothProfiles182) (H : Finset ℕ) (h : Fin 39 → ℕ)
    (i : Fin 39) (k : Fin 6) (x : ℝ) (n : ℕ) : ℝ :=
  selbergWeight182 (sievePairWeight k) x (n + h i) *
    P.erasedFaceValue H h i (sievePairLeft k) x n * P.erasedFaceValue H h i (sievePairRight k) x n

theorem sievePairValue_eq_original (P : TrialSmoothProfiles182) (H : Finset ℕ)
    (h : Fin 39 → ℕ) (i : Fin 39) (k : Fin 6)
    (x : ℝ) (hx : 1 < x) (n : ℕ) (hxn : x ≤ ((n + h i : ℕ) : ℝ)) :
    P.sievePairValue H h i k x n =
      selbergWeight182 (sievePairWeight k) x (n + h i) *
        P.originalFaceValue H h i (sievePairLeft k) x n *
        P.originalFaceValue H h i (sievePairRight k) x n :=
  P.weighted_erasedFaceValue_mul H h i (sievePairLeft k) (sievePairRight k)
    (sievePairWeight k) x hx n hxn

def sieveExceptionalValue (P : TrialSmoothProfiles182) (H : Finset ℕ) (h : Fin 39 → ℕ)
    (i : Fin 39) (x : ℝ) (n : ℕ) : ℝ :=
  sharpDefect x (41361 / 100000) (n + h i) * P.erasedFaceValue H h i rootMinusSubtraction x n ^ 2

theorem sieveExceptionalValue_eq_original (P : TrialSmoothProfiles182) (H : Finset ℕ)
    (h : Fin 39 → ℕ) (i : Fin 39) (x : ℝ) (hx : 1 < x) (n : ℕ)
    (hxn : x ≤ ((n + h i : ℕ) : ℝ)) :
    P.sieveExceptionalValue H h i x n = sharpDefect x (41361 / 100000) (n + h i) *
      (P.bandRoot H h x n - P.bandMask H h i 2 x n) ^ 2 := by
  have hh := P.weighted_erasedFaceValue_mul H h i rootMinusSubtraction rootMinusSubtraction
    2 x hx n hxn
  change sharpDefect x (41361 / 100000) (n + h i) * _ * _ =
    sharpDefect x (41361 / 100000) (n + h i) * _ * _ at hh
  simpa only [sieveExceptionalValue, originalFaceValue, pow_two, mul_assoc] using hh

theorem tailCompletion_eq_source_pairings (P : TrialSmoothProfiles182) (H : Finset ℕ)
    (h : Fin 39 → ℕ) (i : Fin 39) (x : ℝ) (hx : 1 < x) (n : ℕ)
    (hxn : x ≤ ((n + h i : ℕ) : ℝ)) (t η : ℝ) :
    tailCompletion (primeIndicator (n + h i)) (sharpDefect x (41361 / 100000) (n + h i))
      (P.bandRoot H h x n) (P.bandMask H h i 0 x n) (P.bandMask H h i 2 x n)
      (t * (P.bandMask H h i 1 x n - P.bandMask H h i 0 x n)) η =
        2 * P.sievePairValue H h i 0 x n - P.sievePairValue H h i 1 x n +
        2 * t * P.sievePairValue H h i 2 x n + 2 * t * P.sievePairValue H h i 3 x n -
        t ^ 2 * P.sievePairValue H h i 4 x n - η⁻¹ * t ^ 2 * P.sievePairValue H h i 5 x n -
        η * P.sieveExceptionalValue H h i x n := by
  simp_rw [P.sievePairValue_eq_original H h i _ x hx n hxn,
    P.sieveExceptionalValue_eq_original H h i x hx n hxn]
  let A := P.bandRoot H h x n
  let B := P.bandMask H h i 0 x n
  let C := P.bandMask H h i 2 x n
  let D := P.bandMask H h i 1 x n - P.bandMask H h i 0 x n
  let p := primeIndicator (n + h i)
  let b := sharpDefect x (41361 / 100000) (n + h i)
  change tailCompletion p b A B C (t * D) η =
    2 * (p * A * B) - p * B * B + 2 * t * ((p - b) * (A - B) * D) +
      2 * t * (b * (C - B) * D) - t ^ 2 * (p * D * D) -
      η⁻¹ * t ^ 2 * (b * D * D) - η * (b * (A - C) ^ 2)
  unfold tailCompletion
  ring

#print axioms weighted_erasedFaceValue
#print axioms tailCompletion_eq_source_pairings

end PrimeGap182.TrialSmoothProfiles182
