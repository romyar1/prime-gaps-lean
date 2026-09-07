import TypeIIIFiveScaleBound

/-!
# Taking square roots without losing the bad-prime weights

All five terms share the majorant 1/(b sqrt(B)), since B ≥ b ≥ 1. This is
precisely the weight required by the already proved convergent bad-prime sum.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

def linearFiveScale (M Q S Y H : ℝ) : ℝ :=
  H * M ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ) +
  H * M * Q ^ (1 / 2 : ℝ) +
  H ^ (1 / 2 : ℝ) * M ^ (7 / 8 : ℝ) * Q ^ (3 / 2 : ℝ) *
    S ^ (-(1 / 4 : ℝ)) * Y ^ (1 / 4 : ℝ) +
  H ^ (1 / 2 : ℝ) * M * Q ^ (5 / 4 : ℝ) * S ^ (1 / 8 : ℝ) +
  H ^ (1 / 2 : ℝ) * M * Q ^ (3 / 2 : ℝ) *
    S ^ (-(5 / 16 : ℝ)) * Y ^ (5 / 16 : ℝ)

theorem linearFiveScale_nonneg {M Q S Y H : ℝ}
    (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hY : 0 ≤ Y) (hH : 0 ≤ H) :
    0 ≤ linearFiveScale M Q S Y H := by
  unfold linearFiveScale
  positivity

theorem kernelSquare_normalize {x ε κ M Q S Y H Hb b B A E W J : ℝ}
    (hx : 1 ≤ x) (hε : 0 ≤ ε) (hM : 0 < M) (hQ : 0 < Q) (hS : 0 < S)
    (hY : 0 < Y) (hH : 0 < H) (hb : 1 ≤ b) (hbB : b ≤ B)
    (hHb : Hb = x ^ (3 * ε / 2) * H / B)
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hW : 0 ≤ W)
    (hbound : J ^ 2 ≤ A * (E * W) ^ 2 * x ^ κ * Hb * fiveScale M (Q / b) S (b * Y) Hb) :
    J ≤ Real.sqrt A * E * W * x ^ (κ / 2 + 3 * ε / 2) / (b * Real.sqrt B) *
      linearFiveScale M Q S Y H := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hB0 : 0 < B := hb0.trans_le hbB
  have hHb0 : 0 < Hb := by rw [hHb]; positivity
  have hεlogx : 0 ≤ ε * Real.log x := mul_nonneg hε (Real.log_nonneg hx)
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg hb
  have hlogbB : Real.log b ≤ Real.log B := Real.log_le_log hb0 hbB
  let k : ℝ := x ^ (3 * ε / 2) / (b * Real.sqrt B)
  let d : ℝ := H * M ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ)
  let j : ℝ := H * M * Q ^ (1 / 2 : ℝ)
  let u : ℝ := H ^ (1 / 2 : ℝ) * M ^ (7 / 8 : ℝ) * Q ^ (3 / 2 : ℝ) *
    S ^ (-(1 / 4 : ℝ)) * Y ^ (1 / 4 : ℝ)
  let v : ℝ := H ^ (1 / 2 : ℝ) * M * Q ^ (5 / 4 : ℝ) * S ^ (1 / 8 : ℝ)
  let w : ℝ := H ^ (1 / 2 : ℝ) * M * Q ^ (3 / 2 : ℝ) *
    S ^ (-(5 / 16 : ℝ)) * Y ^ (5 / 16 : ℝ)
  let z₁ : ℝ := M ^ (7 / 4 : ℝ) * (Q / b) ^ 3 * S ^ (-(1 / 2 : ℝ)) * (b * Y) ^ (1 / 2 : ℝ)
  let z₂ : ℝ := M ^ 2 * (Q / b) ^ (5 / 2 : ℝ) * S ^ (1 / 4 : ℝ)
  let z₃ : ℝ := M ^ 2 * (Q / b) ^ 3 * S ^ (-(5 / 8 : ℝ)) * (b * Y) ^ (5 / 8 : ℝ)
  let zd : ℝ := Hb * (M * (Q / b) * S)
  let zj : ℝ := Hb * (M ^ 2 * (Q / b))
  have hk : 0 < k := by dsimp only [k]; positivity
  have hd : 0 < d := by dsimp only [d]; positivity
  have hj : 0 < j := by dsimp only [j]; positivity
  have hu : 0 < u := by dsimp only [u]; positivity
  have hv : 0 < v := by dsimp only [v]; positivity
  have hw : 0 < w := by dsimp only [w]; positivity
  have h₁ : Hb * z₁ ≤ (k * u) ^ 2 := by
    apply (Real.log_le_log_iff (by dsimp only [z₁]; positivity) (by positivity)).mp
    dsimp only [z₁, k, u]
    rw [hHb]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow,
      Real.log_pow, Real.log_sqrt, Nat.cast_ofNat]
    nlinarith only [hεlogx, hlogb]
  have h₂ : Hb * z₂ ≤ (k * v) ^ 2 := by
    apply (Real.log_le_log_iff (by dsimp only [z₂]; positivity) (by positivity)).mp
    dsimp only [z₂, k, v]
    rw [hHb]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow,
      Real.log_pow, Real.log_sqrt, Nat.cast_ofNat]
    nlinarith only [hεlogx, hlogb]
  have h₃ : Hb * z₃ ≤ (k * w) ^ 2 := by
    apply (Real.log_le_log_iff (by dsimp only [z₃]; positivity) (by positivity)).mp
    dsimp only [z₃, k, w]
    rw [hHb]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow,
      Real.log_pow, Real.log_sqrt, Nat.cast_ofNat]
    nlinarith only [hεlogx, hlogb]
  have h₄ : Hb * zd ≤ (k * d) ^ 2 := by
    apply (Real.log_le_log_iff (by dsimp only [zd]; positivity) (by positivity)).mp
    dsimp only [zd, k, d]
    rw [hHb]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow,
      Real.log_pow, Real.log_sqrt, Nat.cast_ofNat]
    linarith only [hlogbB]
  have h₅ : Hb * zj ≤ (k * j) ^ 2 := by
    apply (Real.log_le_log_iff (by dsimp only [zj]; positivity) (by positivity)).mp
    dsimp only [zj, k, j]
    rw [hHb]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow,
      Real.log_pow, Real.log_sqrt, Nat.cast_ofNat]
    linarith only [hlogbB]
  have hsquares : (k * d) ^ 2 + (k * j) ^ 2 + (k * u) ^ 2 + (k * v) ^ 2 + (k * w) ^ 2 ≤
      (k * (d + j + u + v + w)) ^ 2 := by
    have hh := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (f := ![k * d, k * j, k * u, k * v, k * w])
      (by intro i _; fin_cases i <;> dsimp <;> positivity)
    norm_num [Fin.sum_univ_succ] at hh
    nlinarith only [hh]
  have hmass : Hb * fiveScale M (Q / b) S (b * Y) Hb ≤
      (k * linearFiveScale M Q S Y H) ^ 2 := by
    change Hb * (z₁ + z₂ + z₃ + Hb * (M * (Q / b) * S + M ^ 2 * (Q / b))) ≤
      (k * (d + j + u + v + w)) ^ 2
    dsimp only [zd, zj] at h₄ h₅
    nlinarith only [h₁, h₂, h₃, h₄, h₅, hsquares]
  let P : ℝ := Real.sqrt A * E * W * x ^ (κ / 2)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hp : (x ^ (κ / 2)) ^ 2 = x ^ κ := by
    rw [← Real.rpow_mul_natCast hx0.le]
    congr 1
    norm_num
  have hP₂ : P ^ 2 = A * (E * W) ^ 2 * x ^ κ := by
    simp only [P, mul_pow, Real.sq_sqrt hA, hp]
    ring
  have hJ₂ : J ^ 2 ≤ (P * k * linearFiveScale M Q S Y H) ^ 2 := by
    calc
      _ ≤ P ^ 2 * (Hb * fiveScale M (Q / b) S (b * Y) Hb) := by
        rw [hP₂]
        simpa only [mul_assoc] using hbound
      _ ≤ P ^ 2 * (k * linearFiveScale M Q S Y H) ^ 2 :=
        mul_le_mul_of_nonneg_left hmass (sq_nonneg P)
      _ = _ := by ring
  have hJ := le_of_sq_le_sq hJ₂ (mul_nonneg (mul_nonneg hP hk.le)
    (linearFiveScale_nonneg hM.le hQ.le hS.le hY.le hH.le))
  apply hJ.trans_eq
  dsimp only [P, k]
  rw [Real.rpow_add hx0]
  ring

#print axioms kernelSquare_normalize

end

end PrimeGap182.TypeIII
