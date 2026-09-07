import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Harman-loss enlargement and the hybrid quadratic lower bound

This file verifies the universal scalar inequalities used in lines 239--296
of the frozen `prime_gaps_182.tex`. The hypothesis `κ ≤ harmanKappaUpper`
remains explicit. No theorem here asserts the value or bound of an analytic
integral, validity of the Harman minorant, a distribution estimate, or a
prime-gap theorem. The separate exact Python integration certificate is not
imported as an axiom.

The parameter enlargement holds for every κ, ℓ, K in their specified
intervals. The square-root hinge inequality holds for every nonnegative u,v.
All decimal constants below are written as exact rational expressions.
-/

noncomputable section

namespace PrimeGap182Audit

def harmanKappaUpper : ℝ := 46653544162031 / 500000000000000000
def harmanEll : ℝ := 6308693370963335 / 576460752303423488
def harmanEllLower : ℝ := 27 / 2500
def harmanEllUpper : ℝ := 7 / 625
def harmanKernelUpper : ℝ := 1097 / 500
def harmanRhoStar : ℝ := 2624989 / 10000000

def harmanEpsilon : ℝ :=
  harmanKappaUpper * (1 / harmanEllLower - 1) * harmanKernelUpper

def harmanDelta : ℝ := 4 * harmanRhoStar * harmanEpsilon
def harmanGamma : ℝ := 1 - harmanDelta
def harmanCapitalGamma : ℝ := 4 * harmanRhoStar * (1 + harmanEpsilon)

theorem harman_constants_positive :
    0 < harmanKappaUpper ∧ 0 < harmanEllLower ∧
    harmanEllUpper < 1 ∧ 0 < harmanKernelUpper ∧ 0 < harmanRhoStar := by
  norm_num [harmanKappaUpper, harmanEllLower, harmanEllUpper,
    harmanKernelUpper, harmanRhoStar]

theorem harmanEll_mem_interval :
    harmanEllLower ≤ harmanEll ∧ harmanEll ≤ harmanEllUpper := by
  norm_num [harmanEll, harmanEllLower, harmanEllUpper]

/-- The error multiplier is uniformly dominated throughout all three
parameter intervals. The actual analytic κ bound is an explicit premise. -/
theorem harman_error_multiplier_enlargement
    (κ ℓ K : ℝ) (hκ0 : 0 ≤ κ) (hκ : κ ≤ harmanKappaUpper)
    (hℓ0 : harmanEllLower ≤ ℓ) (hℓ1 : ℓ ≤ harmanEllUpper)
    (hK0 : 0 ≤ K) (hK : K ≤ harmanKernelUpper) :
    0 ≤ κ * (1 / ℓ - 1) * K ∧
      κ * (1 / ℓ - 1) * K ≤ harmanEpsilon := by
  have hℓpos : 0 < ℓ := harman_constants_positive.2.1.trans_le hℓ0
  have hℓone : ℓ ≤ 1 := hℓ1.trans harman_constants_positive.2.2.1.le
  have hrec0 : 0 ≤ 1 / ℓ - 1 := by
    apply sub_nonneg.mpr
    apply (le_div_iff₀ hℓpos).mpr
    simpa only [one_mul] using hℓone
  have hrec : 1 / ℓ - 1 ≤ 1 / harmanEllLower - 1 :=
    sub_le_sub_right (one_div_le_one_div_of_le
      harman_constants_positive.2.1 hℓ0) 1
  have hprod : κ * (1 / ℓ - 1) ≤
      harmanKappaUpper * (1 / harmanEllLower - 1) :=
    mul_le_mul hκ hrec hrec0 harman_constants_positive.1.le
  have hupper0 : 0 ≤ harmanKappaUpper * (1 / harmanEllLower - 1) :=
    (mul_nonneg hκ0 hrec0).trans hprod
  exact ⟨mul_nonneg (mul_nonneg hκ0 hrec0) hK0,
    mul_le_mul hprod hK hK0 hupper0⟩

theorem harmanEpsilon_exact :
    harmanEpsilon = 126565513539834821311 / 6750000000000000000000 := by
  norm_num [harmanEpsilon, harmanKappaUpper, harmanEllLower, harmanKernelUpper]

theorem harman_restoration_constants_exact :
    harmanDelta = 332233080821417467758340579 / 16875000000000000000000000000 ∧
    harmanGamma = 16542766919178582532241659421 / 16875000000000000000000000000 ∧
    harmanCapitalGamma =
      18050908830821417467758340579 / 16875000000000000000000000000 := by
  norm_num [harmanDelta, harmanGamma, harmanCapitalGamma,
    harmanRhoStar, harmanEpsilon_exact]

theorem harman_restoration_constants_valid :
    0 < harmanDelta ∧ harmanDelta < 1 ∧ 0 < harmanGamma ∧
      0 < harmanCapitalGamma ∧ harmanGamma < 11 / 10 := by
  rcases harman_restoration_constants_exact with ⟨hδ, hγ, hΓ⟩
  rw [hδ, hγ, hΓ]
  norm_num

/-- The unnormalized error bound propagates to the lower-operator and
difference-operator constants by their actual affine formulas. -/
theorem harman_operator_parameter_enlargement
    (κ ℓ K : ℝ) (hκ0 : 0 ≤ κ) (hκ : κ ≤ harmanKappaUpper)
    (hℓ0 : harmanEllLower ≤ ℓ) (hℓ1 : ℓ ≤ harmanEllUpper)
    (hK0 : 0 ≤ K) (hK : K ≤ harmanKernelUpper) :
    4 * harmanRhoStar * (κ * (1 / ℓ - 1) * K) ≤ harmanDelta ∧
      harmanGamma ≤ 1 - 4 * harmanRhoStar * (κ * (1 / ℓ - 1) * K) ∧
      4 * harmanRhoStar * (1 + κ * (1 / ℓ - 1) * K) ≤ harmanCapitalGamma := by
  have h := (harman_error_multiplier_enlargement κ ℓ K hκ0 hκ hℓ0 hℓ1 hK0 hK).2
  have hr : 0 ≤ 4 * harmanRhoStar := by
    exact mul_nonneg (by norm_num) harman_constants_positive.2.2.2.2.le
  have hδ := mul_le_mul_of_nonneg_left h hr
  refine ⟨hδ, sub_le_sub_left hδ 1, ?_⟩
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl h) hr

/-- Algebraic hinge linearization, proved without any analytic hypotheses. -/
theorem nonnegative_hinge_square_lower_bound (a b ℓ : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) :
    (1 - ℓ) * a ^ 2 - (1 / ℓ - 1) * b ^ 2 ≤ (max (a - b) 0) ^ 2 := by
  by_cases hab : a - b ≤ 0
  · rw [max_eq_right hab]
    have hsquares : a ^ 2 ≤ b ^ 2 := by nlinarith only [ha, hb, hab]
    have hscaled : ℓ * a ^ 2 ≤ b ^ 2 :=
      (mul_le_of_le_one_left (sq_nonneg a) hℓ1).trans hsquares
    have hid : (1 - ℓ) * a ^ 2 - (1 / ℓ - 1) * b ^ 2 =
        ((1 - ℓ) * (ℓ * a ^ 2 - b ^ 2)) / ℓ := by
      field_simp
    rw [hid]
    have hnonpos : (1 - ℓ) * (ℓ * a ^ 2 - b ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hℓ1) (sub_nonpos.mpr hscaled)
    simpa only [zero_pow (by decide : 2 ≠ 0)] using
      div_nonpos_of_nonpos_of_nonneg hnonpos hℓ.le
  · rw [max_eq_left (le_of_lt (lt_of_not_ge hab))]
    have hsq : 0 ≤ (ℓ * a - b) ^ 2 / ℓ := div_nonneg (sq_nonneg _) hℓ.le
    have hid : (a - b) ^ 2 - ((1 - ℓ) * a ^ 2 - (1 / ℓ - 1) * b ^ 2) =
        (ℓ * a - b) ^ 2 / ℓ := by
      field_simp
      ring
    rw [← hid] at hsq
    exact sub_nonneg.mp hsq

/-- The main paper's universal square-root hinge inequality. -/
theorem sqrt_hinge_linearization (u v ℓ : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) :
    (1 - ℓ) * u - (1 / ℓ - 1) * v ≤
      (max (Real.sqrt u - Real.sqrt v) 0) ^ 2 := by
  simpa only [Real.sq_sqrt hu, Real.sq_sqrt hv] using
    nonnegative_hinge_square_lower_bound (Real.sqrt u) (Real.sqrt v) ℓ
      (Real.sqrt_nonneg u) (Real.sqrt_nonneg v) hℓ hℓ1

/-- Substituting any true loss below the explicit upper bound yields the
quadratic lower form with the fixed coefficient used in the cap quotient. -/
theorem harman_hybrid_quadratic_lower_bound (u E κ : ℝ)
    (hu : 0 ≤ u) (hE : 0 ≤ E) (hκ0 : 0 ≤ κ) (hκ : κ ≤ harmanKappaUpper) :
    (1 - harmanEll) * u - harmanKappaUpper * (1 / harmanEll - 1) * E ≤
      (max (Real.sqrt u - Real.sqrt (κ * E)) 0) ^ 2 := by
  have hℓpos : 0 < harmanEll :=
    harman_constants_positive.2.1.trans_le harmanEll_mem_interval.1
  have hℓone : harmanEll ≤ 1 :=
    harmanEll_mem_interval.2.trans harman_constants_positive.2.2.1.le
  have hrec : 0 ≤ 1 / harmanEll - 1 := by
    apply sub_nonneg.mpr
    apply (le_div_iff₀ hℓpos).mpr
    simpa only [one_mul] using hℓone
  have herr := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hκ hrec) hE
  have hmain := sqrt_hinge_linearization u (κ * E) harmanEll hu
    (mul_nonneg hκ0 hE) hℓpos hℓone
  calc
    (1 - harmanEll) * u - harmanKappaUpper * (1 / harmanEll - 1) * E ≤
        (1 - harmanEll) * u - κ * (1 / harmanEll - 1) * E := sub_le_sub_left herr _
    _ = (1 - harmanEll) * u - (1 / harmanEll - 1) * (κ * E) := by ring
    _ ≤ (max (Real.sqrt u - Real.sqrt (κ * E)) 0) ^ 2 := hmain

#print axioms harman_constants_positive
#print axioms harmanEll_mem_interval
#print axioms harman_error_multiplier_enlargement
#print axioms harmanEpsilon_exact
#print axioms harman_restoration_constants_exact
#print axioms harman_restoration_constants_valid
#print axioms harman_operator_parameter_enlargement
#print axioms nonnegative_hinge_square_lower_bound
#print axioms sqrt_hinge_linearization
#print axioms harman_hybrid_quadratic_lower_bound

end PrimeGap182Audit
