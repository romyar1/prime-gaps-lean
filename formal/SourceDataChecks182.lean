import SourceData182
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin

/-! Kernel checks of the literal source parameters and their normalization.
These are rational identities, not numerical integral inequalities. -/

open scoped BigOperators
namespace PrimeGap182

def TrialSourceCoverRegular (c : TrialSourceCoverData) : Prop :=
  0 < c.order ∧ 0 < c.low ∧ c.high < c.threshold ∧ 0 ≤ c.slope ∧ 0 < c.split ∧
    ∀ j : Fin c.pieces.length, (c.pieces.get j).last < trialCellCount

set_option maxRecDepth 4096 in
theorem trialOuterCover_regular : ∀ j : Fin 60,
    TrialSourceCoverRegular (trialOuterCertificates j).cover := by
  unfold TrialSourceCoverRegular
  decide +kernel

set_option maxRecDepth 4096 in
theorem trialInnerCover_regular : ∀ j : Fin 137,
    TrialSourceCoverRegular (trialInnerCertificates j).cover := by
  unfold TrialSourceCoverRegular
  decide +kernel

set_option maxRecDepth 4096 in
theorem trialOuterData_normalization : ∀ j : Fin 60,
    let r := trialOuterCertificates j
    0 ≤ r.rootUpper ∧ 0 ≤ r.faceUpper ∧ 0 ≤ r.sqrtUpper ∧
    r.rootUpper = 39 * trialDenominatorLower * r.normalizedA ∧
    trialRhoStar ^ 2 * r.faceUpper = trialDenominatorLower * r.normalizedM ∧
    r.normalizedA * r.normalizedM ≤ r.sqrtUpper ^ 2 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem trialInnerData_normalization : ∀ j : Fin 137,
    let r := trialInnerCertificates j
    0 ≤ r.faceUpper ∧ 0 ≤ r.coefficientUpper ∧
    trialRhoStar * r.coefficientUpper * r.faceUpper =
      trialDenominatorLower * r.normalizedB := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem trialOuterCountBand_bounds : ∀ j : Fin 60,
    ∀ b : Fin (trialOuterCertificates j).counts.length,
      let r := (trialOuterCertificates j).counts.get b
      0 ≤ r.factor ∧ r.factor ≤ 39 ∧ r.count ≤ 39 ∧
      r.factor = 39 * trialSourceEpsilonUpper +
        (1 - trialSourceEpsilonUpper) * r.count := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem trialInnerData_total :
    (∑ j : Fin 137, (trialInnerCertificates j).normalizedB) = trialSourceInnerTotalUpper := by
  decide +kernel

#print axioms trialOuterCover_regular
#print axioms trialInnerCover_regular
#print axioms trialOuterData_normalization
#print axioms trialInnerData_normalization
#print axioms trialOuterCountBand_bounds
#print axioms trialInnerData_total

end PrimeGap182
