import IncidenceSourceNormalization

/-! Real geometry of the actual incidence row and column scales, with
the same separate loss and extraction factors as the source normalization. -/

noncomputable section

namespace PrimeGap182Audit.IncidenceSourceEnvelope

open Real

variable {x «ω» δ γ L Z A M N H q₀ v₀ w₁ Δ₁ Δ m : ℝ}
variable (h : IncidenceSourceEnvelope x «ω» δ γ L Z A M N H q₀ v₀ w₁ Δ₁ Δ m)

include h

theorem source_row_scale_lower {c : ℝ} (hc : 1 ≤ c) (hcw : c ≤ w₁) :
    H ^ 2 ≤ N * w₁ / (c * q₀ * Δ) := by
  obtain ⟨hx, hL, hZ, hA, hM, hN, hH, hq₀, hv₀, hw₁, hΔ₁, hΔ, hm⟩ := h.positive
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hac : log A ≤ log Z := (Real.log_le_log_iff hA hZ).mpr h.hA.2
  have hcw' : log c ≤ log w₁ := (Real.log_le_log_iff hc0 hw₁).mpr hcw
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
    Nat.cast_ofNat]
  linarith only [h.log_expansion, h.log_delta_upper, hac, hcw', Real.log_nonneg h.hq₀]

theorem source_angular_ratio {Y c : ℝ} (hY0 : 0 < Y) (hc : 1 ≤ c) (hcw : c ≤ w₁)
    (hY : Y ≤ L * q₀ * x ^ δ * H ^ 2 / v₀) :
    (Y / w₁) / (N * w₁ / (c * q₀ * Δ)) ≤ L * x ^ δ := by
  obtain ⟨hx, hL, hZ, hA, hM, hN, hH, hq₀, hv₀, hw₁, hΔ₁, hΔ, hm⟩ := h.positive
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hac : log A ≤ log Z := (Real.log_le_log_iff hA hZ).mpr h.hA.2
  have hcw' : log c ≤ log w₁ := (Real.log_le_log_iff hc0 hw₁).mpr hcw
  have hYlog := (Real.log_le_log_iff hY0 (by positivity)).mpr hY
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
    Real.log_rpow, Nat.cast_ofNat] at hYlog
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_rpow]
  nlinarith only [hYlog, h.log_expansion, h.log_delta_upper, hac, hcw',
    Real.log_nonneg h.hv₀, Real.log_nonneg h.hw₁]

theorem source_angular_count {Y c : ℝ} (hY0 : 0 < Y) (hc : 1 ≤ c) (hcw : c ≤ w₁)
    (hY : Y ≤ L * q₀ * x ^ δ * H ^ 2 / v₀) :
    ((max 1 ⌈(Y / w₁) / (N * w₁ / (c * q₀ * Δ))⌉₊ : ℕ) : ℝ) ≤
      2 * L * x ^ δ := by
  have hb := h.source_angular_ratio hY0 hc hcw hY
  obtain ⟨hx, hL, hZ, hA, hM, hN, hH, hq₀, hv₀, hw₁, hΔ₁, hΔ, hm⟩ := h.positive
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hratio : 0 ≤ (Y / w₁) / (N * w₁ / (c * q₀ * Δ)) := by positivity
  have hceil := (Nat.ceil_lt_add_one hratio).le
  have hbase : 1 ≤ L * x ^ δ := by
    nlinarith only [h.hL, Real.one_le_rpow h.hx h.hδ]
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le (by nlinarith only [hbase]) (by nlinarith only [hbase, hb, hceil])

theorem source_incidence_density {Y c w₂ t g : ℝ}
    (hY0 : 0 < Y) (hc : 1 ≤ c) (hw₂ : 1 ≤ w₂) (ht : 1 ≤ t)
    (hg : 0 < g) (hgw : g ≤ w₂)
    (hY : Y ≤ L * q₀ * x ^ δ * H ^ 2 / v₀) :
    (Y / (w₁ * w₂ * t)) * (N * w₁ / (c * q₀ * Δ)) / (m / (q₀ * g)) ≤
      q₀ * L ^ 4 * x ^ (2 * γ + 4 * «ω» + 2 * δ - 1) := by
  obtain ⟨hx, hL, hZ, hA, hM, hN, hH, hq₀, hv₀, hw₁, hΔ₁, hΔ, hm⟩ := h.positive
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hw₂0 : 0 < w₂ := lt_of_lt_of_le zero_lt_one hw₂
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hgw' : log g ≤ log w₂ := (Real.log_le_log_iff hg hw₂0).mpr hgw
  have hYlog := (Real.log_le_log_iff hY0 (by positivity)).mpr hY
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
    Real.log_rpow, Nat.cast_ofNat] at hYlog
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
    Real.log_rpow, Nat.cast_ofNat]
  nlinarith only [hYlog, h.log_m_lower, h.log_expansion, h.log_MN_lower,
    h.log_H_upper, h.log_N, hgw', Real.log_nonneg hc, Real.log_nonneg ht,
    Real.log_nonneg h.hA.1, Real.log_nonneg h.hH]

end PrimeGap182Audit.IncidenceSourceEnvelope

#print axioms PrimeGap182Audit.IncidenceSourceEnvelope.source_row_scale_lower
#print axioms PrimeGap182Audit.IncidenceSourceEnvelope.source_angular_ratio
#print axioms PrimeGap182Audit.IncidenceSourceEnvelope.source_angular_count
#print axioms PrimeGap182Audit.IncidenceSourceEnvelope.source_incidence_density
