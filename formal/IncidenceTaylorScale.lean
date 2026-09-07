import IncidenceSourceModulusScale

/-!
# Smallness of the actual source Fourier Taylor parameter

The period estimates follow from the literal source size intervals.
The short window is x^(-5ε) times the selected divisor scale, with no
old Type II exponent restriction used here.
-/

noncomputable section
namespace PrimeGap182Audit

theorem incidenceSourcePeriod_lower
    (C R₀ Q U V Δ q₀ r u v q₂ d₀ : ℝ)
    (hC : 0 < C) (hR₀ : 0 < R₀) (hQ : 0 < Q) (hU : 0 < U) (hV : 0 < V)
    (hΔ : 0 < Δ) (hq₀ : 0 < q₀) (hr : 0 < r) (hu : 0 < u) (hv : 0 < v)
    (hq₂ : 0 < q₂) (hd₀ : 0 < d₀)
    (hrlo : R₀ / C ≤ r * Δ) (hulo : U / C ≤ u) (hvlo : V / C ≤ v)
    (hqlo : Q / (C * q₀) ≤ q₂) (hUVlo : Q / q₀ ≤ C * U * V)
    (hdlo : Δ / C ≤ d₀) :
    R₀ * Q ^ 2 / (C ^ 6 * q₀) ≤ (r * q₀ * u * v * q₂) * d₀ := by
  have hlr := Real.log_le_log (by positivity : 0 < R₀ / C) hrlo
  have hlu := Real.log_le_log (by positivity : 0 < U / C) hulo
  have hlv := Real.log_le_log (by positivity : 0 < V / C) hvlo
  have hlq := Real.log_le_log (by positivity : 0 < Q / (C * q₀)) hqlo
  have hlUV := Real.log_le_log (by positivity : 0 < Q / q₀) hUVlo
  have hld := Real.log_le_log (by positivity : 0 < Δ / C) hdlo
  simp (disch := positivity) only [Real.log_mul, Real.log_div] at hlr hlu hlv hlq hlUV hld
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow, Nat.cast_ofNat]
  linarith only [hlr, hlu, hlv, hlq, hlUV, hld]

theorem incidenceSourcePeriod_ratio (C x ε R₀ Q q₀ M H R d₀ : ℝ)
    (hC : 0 < C) (hx : 0 < x) (hR₀ : 0 < R₀) (hQ : 0 < Q) (hq₀ : 0 < q₀)
    (hM : 0 < M) (hH : 0 < H) (hR : 0 < R) (hd₀ : 0 < d₀)
    (hHdef : H = x ^ ε * R₀ * Q ^ 2 / (q₀ * M))
    (hperiod : R₀ * Q ^ 2 / (C ^ 6 * q₀) ≤ R * d₀) :
    M * H / (d₀ * R) ≤ C ^ 6 * x ^ ε := by
  have hlH := congrArg Real.log hHdef
  have hlP := Real.log_le_log (by positivity : 0 < R₀ * Q ^ 2 / (C ^ 6 * q₀)) hperiod
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow,
    Real.log_rpow, Nat.cast_ofNat] at hlH hlP
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow,
    Real.log_rpow, Nat.cast_ofNat]
  linarith only [hlH, hlP]

theorem incidenceSourceTaylorScale_bound
    (C x ε Δ d₀ M H TM R₁ R₂ : ℝ)
    (hC : 1 ≤ C) (hx : 1 ≤ x) (hε : 0 < ε)
    (_hΔ : 0 < Δ) (hd₀ : 0 < d₀) (hM : 0 ≤ M) (hH : 0 ≤ H) (hTM : 0 ≤ TM)
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hcenter : Δ / C ≤ d₀)
    (h₁ : M * H / (d₀ * R₁) ≤ C ^ 6 * x ^ ε)
    (h₂ : M * H / (d₀ * R₂) ≤ C ^ 6 * x ^ ε) :
    (x ^ (-5 * ε) * Δ) / d₀ *
      (1 + TM * M * (2 * C * H) / d₀ * (R₁⁻¹ + R₂⁻¹)) ≤
        (C + 4 * TM * C ^ 8) * x ^ (-4 * ε) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hpower : 1 ≤ x ^ ε := Real.one_le_rpow hx hε.le
  have hratio : Δ / d₀ ≤ C :=
    (div_le_iff₀ hd₀).mpr (by
      have ht := (div_le_iff₀ hCpos).mp hcenter
      nlinarith)
  have hsum : TM * M * (2 * C * H) / d₀ * (R₁⁻¹ + R₂⁻¹) ≤
      4 * TM * C ^ 7 * x ^ ε := by
    calc
      _ = 2 * C * TM * (M * H / (d₀ * R₁) + M * H / (d₀ * R₂)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ 2 * C * TM * (C ^ 6 * x ^ ε + C ^ 6 * x ^ ε) :=
        mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by positivity)
      _ = _ := by ring
  have hG : 1 + TM * M * (2 * C * H) / d₀ * (R₁⁻¹ + R₂⁻¹) ≤
      (1 + 4 * TM * C ^ 7) * x ^ ε := by nlinarith
  have hSratio : (x ^ (-5 * ε) * Δ) / d₀ ≤ C * x ^ (-5 * ε) := by
    rw [mul_div_assoc]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hxpos.le _)
  calc
    _ ≤ (C * x ^ (-5 * ε)) * ((1 + 4 * TM * C ^ 7) * x ^ ε) :=
      mul_le_mul hSratio hG (by positivity) (by positivity)
    _ = (C + 4 * TM * C ^ 8) * (x ^ (-5 * ε) * x ^ ε) := by ring
    _ = _ := by rw [← Real.rpow_add hxpos]; congr 2; ring

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceSourcePeriod_lower
#print axioms PrimeGap182Audit.incidenceSourcePeriod_ratio
#print axioms PrimeGap182Audit.incidenceSourceTaylorScale_bound
