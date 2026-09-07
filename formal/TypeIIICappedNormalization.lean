import TypeIIIFineBandKernel
import TypeIIICriteria

/-!
# Actual five-term normalization, including the capped small-modulus branch

The cap introduces no new analytic input. Its two formerly negative powers of S
give exponents bounded above by -1/32 before the small epsilon losses.
-/

open scoped BigOperators Classical
open PrimeGap182Audit

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

def typeIIIEpsilonCap (μ θ δ : ℝ) : ℝ :=
  min (1 / 1000) (typeIIIMarginA μ θ δ / 1000)

theorem typeIIIEpsilonCap_pos {μ θ δ : ℝ} (hA : 0 < typeIIIMarginA μ θ δ) :
    0 < typeIIIEpsilonCap μ θ δ := by
  unfold typeIIIEpsilonCap
  positivity

theorem capped_exponent_bounds {μ θ δ ε : ℝ} (hμ : 0 ≤ μ) (hμupper : μ < 1 / 4)
    (hδ : 0 < δ) (hA : 0 < typeIIIMarginA μ θ δ) (hB : 0 < typeIIIMarginB θ δ)
    (hεcap : ε ≤ typeIIIEpsilonCap μ θ δ) :
    let s := typeIIIExtraction μ θ δ
    μ / 2 + 3 * θ / 2 + s / 2 - 1 + 8 * ε ≤ 0 ∧
    μ + 3 * θ / 2 - 1 + 8 * ε ≤ 0 ∧
    3 * μ / 8 + θ - s / 4 - 1 / 2 + δ / 4 + 8 * ε ≤ 0 ∧
    μ / 2 + 3 * θ / 4 + s / 8 - 1 / 2 + 8 * ε ≤ 0 ∧
    μ / 2 + θ - 5 * s / 16 - 1 / 2 + 5 * δ / 16 + 8 * ε ≤ 0 ∧
    3 * μ / 8 + 3 * (s - δ) / 4 - 1 / 2 + 6 * ε ≤ 0 ∧
    μ / 2 + 11 * (s - δ) / 16 - 1 / 2 + 6 * ε ≤ 0 := by
  intro s
  have hεA : ε ≤ typeIIIMarginA μ θ δ / 1000 := hεcap.trans (min_le_right _ _)
  have hεone : ε ≤ 1 / 1000 := hεcap.trans (min_le_left _ _)
  have hs := (typeIII_extraction_bounds hμ hδ hA hB).2.2.2
  obtain ⟨hd, hj, h₁, h₂, h₃⟩ := typeIII_errors_le_negative_margin hδ hA hB
    (show (0 : ℝ) ≤ typeIIIMarginA μ θ δ / 100 by positivity)
  dsimp only [typeIIIDiagonalExponent, typeIIICentralExponent, typeIIIFirstExponent,
    typeIIISecondExponent, typeIIIFourthExponent] at hd hj h₁ h₂ h₃
  dsimp only [s]
  refine ⟨by linarith only [hd, hεA, hA], by linarith only [hj, hεA, hA],
    by linarith only [h₁, hεA, hA], by linarith only [h₂, hεA, hA], by linarith only [h₃, hεA, hA],
    ?_, ?_⟩
  · linarith only [hμupper, hs, hδ, hεone]
  · linarith only [hμupper, hs, hδ, hεone]

theorem normalized_cappedFiveScale_le {μ θ δ ε C x M N Q : ℝ}
    (hμ : 0 ≤ μ) (hμupper : μ < 1 / 4) (hδ : 0 < δ)
    (hA : 0 < typeIIIMarginA μ θ δ) (hB : 0 < typeIIIMarginB θ δ)
    (hε : 0 < ε) (hεcap : ε ≤ typeIIIEpsilonCap μ θ δ)
    (hC : 1 ≤ C) (hx : 1 ≤ x) (hM : 0 < M) (hN : 0 < N) (hQ : 0 < Q)
    (hMNlo : x / C ≤ M * N) (hMNhi : M * N ≤ C * x)
    (hNlo : x ^ (1 - μ - ε) / C ≤ N) (hQup : Q ≤ C * x ^ (θ + ε)) :
    let s := typeIIIExtraction μ θ δ
    (N / Q ^ 2) * x ^ (5 * ε / 2) *
      linearFiveScale M Q (cappedExtractionScale x s (x ^ δ) Q) (x ^ δ) (Q ^ 3 / N) ≤
        10 * C ^ 8 * (M * N) * x ^ (-3 * ε) := by
  intro s
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlogtwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hεlogx : 0 ≤ ε * Real.log x := mul_nonneg hε.le hlogx
  obtain ⟨hed, hej, he₁, he₂, he₃, hecap₁, hecap₃⟩ :=
    capped_exponent_bounds hμ hμupper hδ hA hB hεcap
  have hgd := mul_le_mul_of_nonneg_right hed hlogx
  have hgj := mul_le_mul_of_nonneg_right hej hlogx
  have hg₁ := mul_le_mul_of_nonneg_right he₁ hlogx
  have hg₂ := mul_le_mul_of_nonneg_right he₂ hlogx
  have hg₃ := mul_le_mul_of_nonneg_right he₃ hlogx
  have hgc₁ := mul_le_mul_of_nonneg_right hecap₁ hlogx
  have hgc₃ := mul_le_mul_of_nonneg_right hecap₃ hlogx
  have hlogMNlo := Real.log_le_log (div_pos hx0 hC0) hMNlo
  have hlogMNhi := Real.log_le_log (mul_pos hM hN) hMNhi
  have hlogN := Real.log_le_log (by positivity : 0 < x ^ (1 - μ - ε) / C) hNlo
  have hlogQ := Real.log_le_log hQ hQup
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
    at hlogMNlo hlogMNhi hlogN hlogQ
  have hlogM : Real.log M ≤ 2 * Real.log C + (μ + ε) * Real.log x := by
    nlinarith only [hlogMNhi, hlogN]
  let S : ℝ := cappedExtractionScale x s (x ^ δ) Q
  have hS : 0 < S := lt_min (by positivity) (by positivity)
  have hSlog : Real.log S ≤ s * Real.log x := by
    have hh := Real.log_le_log hS (min_le_left (x ^ s) (x ^ δ * Q / 2))
    simpa only [Real.log_rpow hx0] using hh
  let H : ℝ := Q ^ 3 / N
  let k : ℝ := (N / Q ^ 2) * x ^ (5 * ε / 2)
  let d : ℝ := H * M ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ)
  let j : ℝ := H * M * Q ^ (1 / 2 : ℝ)
  let u : ℝ := H ^ (1 / 2 : ℝ) * M ^ (7 / 8 : ℝ) * Q ^ (3 / 2 : ℝ) *
    S ^ (-(1 / 4 : ℝ)) * (x ^ δ) ^ (1 / 4 : ℝ)
  let v : ℝ := H ^ (1 / 2 : ℝ) * M * Q ^ (5 / 4 : ℝ) * S ^ (1 / 8 : ℝ)
  let w : ℝ := H ^ (1 / 2 : ℝ) * M * Q ^ (3 / 2 : ℝ) *
    S ^ (-(5 / 16 : ℝ)) * (x ^ δ) ^ (5 / 16 : ℝ)
  let R : ℝ := 2 * C ^ 8 * (M * N) * x ^ (-3 * ε)
  have hk : 0 < k := by dsimp only [k]; positivity
  have hd : 0 < d := by dsimp only [d, H]; positivity
  have hj : 0 < j := by dsimp only [j, H]; positivity
  have hu : 0 < u := by dsimp only [u, H]; positivity
  have hv : 0 < v := by dsimp only [v, H]; positivity
  have hw : 0 < w := by dsimp only [w, H]; positivity
  have hR : 0 < R := by dsimp only [R]; positivity
  have hdB : k * d ≤ R := by
    apply (Real.log_le_log_iff (mul_pos hk hd) hR).mp
    dsimp only [k, d, H, R]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow, Nat.cast_ofNat]
    dsimp only [s] at hSlog
    nlinarith only [hlogM, hlogQ, hlogMNlo, hSlog, hgd, hεlogx, hlogC, hlogtwo]
  have hjB : k * j ≤ R := by
    apply (Real.log_le_log_iff (mul_pos hk hj) hR).mp
    dsimp only [k, j, H, R]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow, Nat.cast_ofNat]
    nlinarith only [hlogM, hlogQ, hlogMNlo, hgj, hεlogx, hlogC, hlogtwo]
  have hvB : k * v ≤ R := by
    apply (Real.log_le_log_iff (mul_pos hk hv) hR).mp
    dsimp only [k, v, H, R]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow, Nat.cast_ofNat]
    dsimp only [s] at hSlog
    nlinarith only [hlogM, hlogQ, hlogMNlo, hSlog, hg₂, hεlogx, hlogC, hlogtwo]
  have hnegative : k * u ≤ R ∧ k * w ≤ R := by
    by_cases hfull : x ^ s ≤ x ^ δ * Q / 2
    · have hSeq : S = x ^ s := min_eq_left hfull
      have huB : k * u ≤ R := by
        apply (Real.log_le_log_iff (mul_pos hk hu) hR).mp
        dsimp only [k, u, H, R]
        rw [hSeq]
        simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow, Nat.cast_ofNat]
        dsimp only [s]
        nlinarith only [hlogM, hlogQ, hlogMNlo, hg₁, hεlogx, hlogC, hlogtwo]
      have hwB : k * w ≤ R := by
        apply (Real.log_le_log_iff (mul_pos hk hw) hR).mp
        dsimp only [k, w, H, R]
        rw [hSeq]
        simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow, Nat.cast_ofNat]
        dsimp only [s]
        nlinarith only [hlogM, hlogQ, hlogMNlo, hg₃, hεlogx, hlogC, hlogtwo]
      exact ⟨huB, hwB⟩
    · have hcap : x ^ δ * Q / 2 ≤ x ^ s := (lt_of_not_ge hfull).le
      have hSeq : S = x ^ δ * Q / 2 := min_eq_right hcap
      have hlogQsmall : Real.log Q ≤ Real.log 2 + (s - δ) * Real.log x := by
        have hh := Real.log_le_log (by positivity : 0 < x ^ δ * Q / 2) hcap
        simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_rpow] at hh
        nlinarith only [hh]
      have huB : k * u ≤ R := by
        apply (Real.log_le_log_iff (mul_pos hk hu) hR).mp
        dsimp only [k, u, H, R]
        rw [hSeq]
        simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow, Nat.cast_ofNat]
        dsimp only [s] at hlogQsmall
        nlinarith only [hlogM, hlogQsmall, hlogMNlo, hgc₁, hεlogx, hlogC, hlogtwo]
      have hwB : k * w ≤ R := by
        apply (Real.log_le_log_iff (mul_pos hk hw) hR).mp
        dsimp only [k, w, H, R]
        rw [hSeq]
        simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow, Nat.cast_ofNat]
        dsimp only [s] at hlogQsmall
        nlinarith only [hlogM, hlogQsmall, hlogMNlo, hgc₃, hεlogx, hlogC, hlogtwo]
      exact ⟨huB, hwB⟩
  change k * (d + j + u + v + w) ≤ _
  calc
    _ = k * d + k * j + k * u + k * v + k * w := by ring
    _ ≤ R + R + R + R + R := add_le_add
      (add_le_add (add_le_add (add_le_add hdB hjB) hnegative.1) hvB) hnegative.2
    _ = _ := by dsimp only [R]; ring

#print axioms capped_exponent_bounds
#print axioms normalized_cappedFiveScale_le

end

end PrimeGap182.TypeIII
