import PrimeGaps186

/-! Explicit absorption of monomial boundary errors with the new roughness
exponent .17278. Adapted from Apache-2.0 PrimeGaps186 at the pinned source hash. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

theorem minorant_boundary_log_arithmetic (A x m z : ℝ)
    (hA : 0 < A) (hx : Real.exp 1 ≤ x) (hm : 0 ≤ m) (hz : 0 ≤ z)
    (hmass : m ≤ 17 * 64 *
      (1023 * (Real.log x) ^ (-(A + 20)) * x +
        x ^ (1 - (8639 : ℝ) / 50000)) * (1 + Real.log (64 * x)) ^ 16)
    (hzbound : z ≤ 4 * (Real.log x) ^ 2)
    (hsmall : (Real.log x) ^ (A + 18) ≤ x ^ ((8639 : ℝ) / 50000)) :
    2 * m * z ≤
      (8 * (17 * 64) * (1023 + 1) * (2 + Real.log 64) ^ 16) *
        x / (Real.log x) ^ A := by
  let D : ℝ := A + 20
  let l : ℝ := Real.log x
  let h : ℝ := l ^ (-D)
  let C0 : ℝ := 2 + Real.log 64
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
  have hx1 : 1 ≤ x := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hx
  have hlog1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hlog0 : 0 < Real.log x := zero_lt_one.trans_le hlog1
  have hLA : 0 < l ^ A := zero_lt_one.trans_le (Real.one_le_rpow hlog1 hA.le)
  have hh : 0 < h := Real.rpow_pos_of_pos hlog0 _
  have hC0 : 0 < C0 := by
    have hlog64 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 64)
    dsimp [C0]
    linarith
  have hlog64 : 1 + Real.log (64 * x) ≤ C0 * l := by
    rw [Real.log_mul (by norm_num : (64 : ℝ) ≠ 0) hx0.ne']
    dsimp only [C0, l]
    nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 64)]
  have hH0 : 0 ≤ 1 + Real.log (64 * x) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 64 * x by nlinarith)
    linarith
  have hlog64pow : (1 + Real.log (64 * x)) ^ 16 ≤ C0 ^ 16 * l ^ 16 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hH0 hlog64 16
  have hmeshdecay : h * l ^ 18 ≤ 1 / l ^ A := by
    have heq : h * l ^ 18 = l ^ (18 - D) := by
      dsimp only [h, l]
      rw [show (l ^ 18 : ℝ) = l ^ (18 : ℝ) from (Real.rpow_natCast l 18).symm,
        ← Real.rpow_add hlog0]
      congr 1
      ring
    rw [heq, one_div, ← Real.rpow_neg hlog0.le]
    exact Real.rpow_le_rpow_of_exponent_le hlog1 (by dsimp [D]; linarith)
  have hpowerdecay : x ^ (1 - (8639 : ℝ) / 50000) * l ^ 18 ≤ x / l ^ A := by
    apply (le_div_iff₀ hLA).mpr
    calc
      _ = x ^ (1 - (8639 : ℝ) / 50000) * l ^ (A + 18) := by
        dsimp only [l]
        rw [Real.rpow_add hlog0,
          show (Real.log x) ^ (18 : ℝ) = (Real.log x) ^ (18 : ℕ) from Real.rpow_natCast _ 18]
        ring
      _ ≤ x ^ (1 - (8639 : ℝ) / 50000) * x ^ ((8639 : ℝ) / 50000) :=
        mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hx0.le _)
      _ = x := by rw [← Real.rpow_add hx0]; norm_num
  have hmass' : m ≤
      17 * 64 * (1023 * h * x + x ^ (1 - (8639 : ℝ) / 50000)) *
        (C0 ^ 16 * l ^ 16) :=
    hmass.trans (mul_le_mul_of_nonneg_left hlog64pow (by positivity))
  calc
    2 * m * z ≤ 2 *
        (17 * 64 * (1023 * h * x + x ^ (1 - (8639 : ℝ) / 50000)) *
          (C0 ^ 16 * l ^ 16)) * (4 * l ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hmass' (by norm_num)) hzbound hz
        (mul_nonneg (by norm_num) (hm.trans hmass'))
    _ = (8 * (17 * 64) * C0 ^ 16) *
        (1023 * x * (h * l ^ 18) + x ^ (1 - (8639 : ℝ) / 50000) * l ^ 18) := by ring
    _ ≤ (8 * (17 * 64) * C0 ^ 16) *
        (1023 * x * (1 / l ^ A) + x / l ^ A) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hmeshdecay (by positivity)) hpowerdecay)
        (by positivity)
    _ = _ := by dsimp only [C0, l]; ring

#print axioms minorant_boundary_log_arithmetic

end PrimeGap182Analytic.Harman
