import PhysicalTrial182

/-!
Analytic domination for the new roughness and hinge.  The baseline logarithm
lemma is generic; its old-parameter density monotonicity is not used here.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

theorem pairLogDensity_monotone (r a : ℝ) (hr : 0 < r) (ha : a < 3 * r) :
    MonotoneOn (fun s : ℝ => Real.log ((s - r) / r) / s) (Set.Icc (2 * r) a) := by
  let f : ℝ → ℝ := fun s => Real.log ((s - r) / r) / s
  have hpos (s : ℝ) (hs : s ∈ Set.Icc (2 * r) a) : 0 < s ∧ 0 < s - r := by
    constructor <;> linarith [hs.1]
  have hderiv (s : ℝ) (hs : s ∈ Set.Icc (2 * r) a) :
      HasDerivAt f ((s / (s - r) - Real.log ((s - r) / r)) / s ^ 2) s := by
    obtain ⟨hspos, hsub⟩ := hpos s hs
    have hlog := (((hasDerivAt_id' s).sub_const r).div_const r).log
      (ne_of_gt (div_pos hsub hr))
    rw [div_div_div_cancel_right₀ hr.ne', one_div] at hlog
    simpa only [f, inv_mul_eq_div, mul_one] using
      hlog.fun_div (hasDerivAt_id' s) hspos.ne'
  change MonotoneOn f (Set.Icc (2 * r) a)
  refine (strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_).monotoneOn
  · intro s hs
    exact (hderiv s hs).continuousAt.continuousWithinAt
  · intro s hs
    have hs' : s ∈ Set.Icc (2 * r) a := interior_subset hs
    obtain ⟨hspos, hsub⟩ := hpos s hs'
    have hqlt : (s - r) / r < 2 := (div_lt_iff₀ hr).2 (by linarith [hs'.2])
    have hloglt : Real.log ((s - r) / r) < 1 :=
      (Real.log_le_sub_one_of_pos (div_pos hsub hr)).trans_lt (by linarith)
    have hratio : 1 < s / (s - r) := (one_lt_div hsub).2 (sub_lt_self s hr)
    rw [(hderiv s hs').deriv]
    exact div_pos (sub_pos.mpr (hloglt.trans hratio)) (pow_pos hspos 2)

theorem pairHinge_monotone (t : ℝ) (ht : t < 2 / 5) :
    Monotone (PrimeGap182Analytic.pairHinge t) := by
  intro x y hxy
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr ht.le)
  exact mul_le_mul_of_nonneg_left
    (max_le_max (sub_le_sub_right hxy t) le_rfl) (by norm_num)

theorem pairLogDensity_nonneg (r s : ℝ) (hr : 0 < r) (hs : 2 * r ≤ s) :
    0 ≤ Real.log ((s - r) / r) / s := by
  have hratio : 1 ≤ (s - r) / r := (le_div_iff₀ hr).2 (by linarith)
  exact div_nonneg (Real.log_nonneg hratio) (by linarith)

def trialPairDensity (s : ℝ) : ℝ :=
  PrimeGap182Analytic.pairHinge (trialHingeThreshold : ℝ) s *
    (Real.log ((s - (trialRoughness : ℝ)) / (trialRoughness : ℝ)) / s)

theorem trialPairDensity_nonneg {s : ℝ} (hs : 2 * (trialRoughness : ℝ) ≤ s) :
    0 ≤ trialPairDensity s :=
  mul_nonneg
    (PrimeGap182Analytic.pairHinge_nonneg _ _ (by norm_num [trialHingeThreshold]))
    (pairLogDensity_nonneg _ _ (by norm_num [trialRoughness]) hs)

theorem trialPairDensity_monotone :
    MonotoneOn trialPairDensity
      (Set.Icc (2 * (trialRoughness : ℝ)) (trialMinorantA : ℝ)) := by
  intro x hx y hy hxy
  apply mul_le_mul
    (pairHinge_monotone _ (by norm_num [trialHingeThreshold]) hxy)
    (pairLogDensity_monotone _ _ (by norm_num [trialRoughness])
      (by norm_num [trialMinorantA, trialRoughness]) hx hy hxy)
  · exact pairLogDensity_nonneg _ _ (by norm_num [trialRoughness]) hx.1
  · exact PrimeGap182Analytic.pairHinge_nonneg _ _ (by norm_num [trialHingeThreshold])

theorem trialLogUpper_eq (x : ℚ) :
    trialLogUpper x = PrimeGap186.exceptionalLogUpper21 x := by
  unfold trialLogUpper PrimeGap186.exceptionalLogUpper21
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => (-1 : ℚ) ^ n * x ^ (n + 1) / (n + 1 : ℕ)),
    ← Finset.Ico_succ_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Nat.add_comm 1 n, Nat.cast_add, Nat.cast_one, pow_succ]
  ring

theorem trialLogUpper_dominates (x : ℚ) (hx : 0 ≤ x) (hx1 : x < 1) :
    Real.log (1 + (x : ℝ)) ≤ (trialLogUpper x : ℝ) := by
  rw [trialLogUpper_eq]
  simpa only [PrimeGap186.exceptionalLogUpper21, Rat.cast_sum, Rat.cast_div,
    Rat.cast_mul, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast] using
    PrimeGap186.exceptional_log_upper21 (x : ℝ) (Rat.cast_nonneg.mpr hx)
      (by exact_mod_cast hx1)

theorem trialLogUpper_nonneg (x : ℚ) (hx : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ trialLogUpper x := by
  apply (Rat.cast_nonneg (K := ℝ)).mp
  exact (Real.log_nonneg (by exact le_add_of_nonneg_right (Rat.cast_nonneg.mpr hx))).trans
    (trialLogUpper_dominates x hx hx1)

#print axioms pairLogDensity_monotone
#print axioms trialPairDensity_monotone
#print axioms trialLogUpper_dominates

end PrimeGap182
