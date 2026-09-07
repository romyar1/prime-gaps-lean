import IncidenceSourceGeometry

/-! The incidence normalization packet for the literal source scales.
`Δ` is the selected original divisor scale and `x^(-5ε) Δ` is its short
window. The lower modulus bound retains the required factor `q₀`.
All losses follow from actual scale inequalities by logarithms. -/

noncomputable section
namespace PrimeGap182Audit
open Real

set_option maxHeartbeats 800000 in
theorem sourceIncidence_envelope_of_actual_scales
    (C x «ω» δ ε γ M N R Q V H q₀ v₀ w₁ Δ m : ℝ)
    (hC : 1 ≤ C) (hx : 1 ≤ x) (hCx : C ≤ x ^ ε)
    (hω : 0 ≤ «ω») (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hM : 0 < M) (hR : 0 < R) (hQ : 0 < Q) (hV : 0 < V)
    (hH : 1 ≤ H) (hq : 1 ≤ q₀) (hv : 1 ≤ v₀) (hw : 1 ≤ w₁)
    (hΔ : 0 < Δ) (hm : 0 < m) (hN : N = x ^ γ)
    (hMNlo : x / C ≤ M * N) (hMNhi : M * N ≤ C * x)
    (hNR : N ≤ C * x ^ (δ + 4 * ε) * R)
    (hRQ : R * Q ≤ C * x ^ (1 / 2 + 2 * «ω» + ε))
    (hHdef : H = x ^ ε * R * Q ^ 2 / (q₀ * M))
    (hVlo : x ^ (5 * ε) * H / q₀ ≤ C * V)
    (hVhi : V ≤ C * x ^ (δ + 5 * ε) * H)
    (hDlo : N ≤ C * q₀ ^ 2 * x ^ (δ + 50 * ε) * H ^ 2 * Δ)
    (hDhi : Δ ≤ C * N / (q₀ ^ 2 * x ^ (50 * ε) * H ^ 2))
    (hmlo : R * Q ^ 2 * V / (C ^ 6 * q₀ * Δ * v₀) ≤ m)
    (hmhi : m ≤ C ^ 6 * R * Q ^ 2 * V / (q₀ * Δ * v₀)) :
    IncidenceSourceEnvelope x «ω» δ γ (C ^ 10 * x ^ (8 * ε))
      (x ^ (54 * ε)) (x ^ (5 * ε)) M N H q₀ v₀ w₁
      (x ^ (-5 * ε) * Δ) Δ m := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hq0 : 0 < q₀ := zero_lt_one.trans_le hq
  have hv0 : 0 < v₀ := zero_lt_one.trans_le hv
  have hN0 : 0 < N := by rw [hN]; positivity
  have hlogx : 0 ≤ log x := log_nonneg hx
  have hlogC : 0 ≤ log C := log_nonneg hC
  have hlogq : 0 ≤ log q₀ := log_nonneg hq
  have hεx : 0 ≤ ε * log x := mul_nonneg hε.le hlogx
  have hCeps : log C ≤ ε * log x := by
    have hh := Real.log_le_log hC0 hCx
    simpa only [Real.log_rpow hx0] using hh
  have hMNloLog := Real.log_le_log (by positivity : 0 < x / C) hMNlo
  have hMNhiLog := Real.log_le_log (by positivity : 0 < M * N) hMNhi
  have hNRLog := Real.log_le_log hN0 hNR
  have hRQLog := Real.log_le_log (mul_pos hR hQ) hRQ
  have hHLog := congrArg Real.log hHdef
  have hVloLog := Real.log_le_log (by positivity : 0 < x ^ (5 * ε) * H / q₀) hVlo
  have hVhiLog := Real.log_le_log hV hVhi
  have hDloLog := Real.log_le_log hN0 hDlo
  have hDhiLog := Real.log_le_log hΔ hDhi
  have hmloLog := Real.log_le_log
    (by positivity : 0 < R * Q ^ 2 * V / (C ^ 6 * q₀ * Δ * v₀)) hmlo
  have hmhiLog := Real.log_le_log hm hmhi
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
    Real.log_rpow, Nat.cast_ofNat] at hMNloLog hMNhiLog hNRLog hRQLog hHLog hVloLog hVhiLog hDloLog hDhiLog hmloLog hmhiLog
  have hHupper : log H ≤ 4 * log C + (4 * «ω» + δ + 7 * ε) * log x - log q₀ := by
    nlinarith only [hMNloLog, hNRLog, hRQLog, hHLog]
  have hL : 1 ≤ C ^ 10 * x ^ (8 * ε) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC) (Real.one_le_rpow hx (by positivity))
  refine {
    hx := hx, hω := hω, hδ := hδ, hL := hL
    hZ := Real.one_le_rpow hx (by positivity)
    hA := ⟨Real.one_le_rpow hx (by positivity),
      Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hε])⟩
    hM := hM, hN := hN, hH := hH, hq₀ := hq, hv₀ := hv, hw₁ := hw
    hΔ₁ := by positivity
    hm := hm
    hMNlo := ?_
    hMNhi := ?_
    hHhi := ?_
    hΔlo := ?_
    hΔhi := ?_
    hΔ := ?_
    hmlo := ?_
    hmhi := ?_ }
  · apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
      Real.log_rpow, Nat.cast_ofNat]
    nlinarith only [hMNloLog, hlogC, hεx]
  · apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simp (disch := positivity) only [Real.log_mul, Real.log_pow, Real.log_rpow, Nat.cast_ofNat]
    nlinarith only [hMNhiLog, hlogC, hεx]
  · apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
      Real.log_rpow, Nat.cast_ofNat]
    nlinarith only [hHupper, hlogC, hεx]
  · apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
      Real.log_rpow, Nat.cast_ofNat]
    nlinarith only [hDloLog, hlogC, hεx]
  · apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
      Real.log_rpow, Nat.cast_ofNat]
    nlinarith only [hDhiLog, hCeps]
  · rw [← mul_assoc, ← Real.rpow_add hx0]
    simp only [show 5 * ε + -5 * ε = 0 by ring, Real.rpow_zero, one_mul]
  · apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
      Real.log_rpow, Nat.cast_ofNat]
    nlinarith only [hmloLog, hHLog, hVloLog, hlogC, hεx]
  · apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
      Real.log_rpow, Nat.cast_ofNat]
    nlinarith only [hmhiLog, hHLog, hVhiLog, hlogC, hεx, hlogq]

#print axioms sourceIncidence_envelope_of_actual_scales

end PrimeGap182Audit
