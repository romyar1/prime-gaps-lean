import SourceDataChecks182
import Mathlib.Data.Real.Basic

/-! Rational loss arithmetic for the literal 60 outer and 137 inner source
certificates. This computes only the penalty, not the physical integral leaves. -/

open scoped BigOperators
namespace PrimeGap182

def trialRestorationPenalty : ℚ :=
  trialSourceInnerTotalUpper + trialSourceGammaUpper * trialSourceInnerTotalUpper / trialSourceCommonT +
    2 * ∑ j : Fin 60, (trialOuterCertificates j).sqrtUpper +
    (trialSourceCommonT - trialSourceGammaLower) * ∑ j : Fin 60, (trialOuterCertificates j).normalizedA

set_option maxRecDepth 10000 in
theorem trialRestoration_margin_rat :
    (65213759 / 10 ^ 12 : ℚ) <
      9968877639291 / 36028797018963968 - trialRestorationPenalty := by
  decide +kernel

theorem trialRestoration_margin_real :
    (65213759 / 10 ^ 12 : ℝ) <
      9968877639291 / 36028797018963968 - (trialRestorationPenalty : ℝ) := by
  have h := (Rat.cast_lt (K := ℝ)).mpr trialRestoration_margin_rat
  norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat] at h ⊢
  exact h

#print axioms trialRestoration_margin_rat
#print axioms trialRestoration_margin_real

end PrimeGap182
