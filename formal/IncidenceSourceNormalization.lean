import PrimeGaps186

/-!
# Explicit real normalization of the incidence source terms

The small multiplicative loss `L`, extraction retreat `Z`, and expansion `A`
are kept separate. Every bound below follows from the displayed raw scale
envelopes; none assumes a source-energy or distribution estimate.
-/

noncomputable section

namespace PrimeGap182Audit

open Real

structure IncidenceSourceEnvelope
    (x «ω» δ γ L Z A M N H q₀ v₀ w₁ Δ₁ Δ m : ℝ) : Prop where
  hx : 1 ≤ x
  hω : 0 ≤ «ω»
  hδ : 0 ≤ δ
  hL : 1 ≤ L
  hZ : 1 ≤ Z
  hA : 1 ≤ A ∧ A ≤ Z
  hM : 0 < M
  hN : N = x ^ γ
  hH : 1 ≤ H
  hq₀ : 1 ≤ q₀
  hv₀ : 1 ≤ v₀
  hw₁ : 1 ≤ w₁
  hΔ₁ : 0 < Δ₁
  hm : 0 < m
  hMNlo : x / L ≤ M * N
  hMNhi : M * N ≤ L * x
  hHhi : H ≤ L * x ^ (4 * «ω» + δ) / q₀
  hΔlo : N / (L * q₀ ^ 2 * x ^ δ * H ^ 2 * Z) ≤ Δ₁
  hΔhi : Δ₁ ≤ N / (q₀ ^ 2 * H ^ 2 * Z)
  hΔ : Δ = A * Δ₁
  hmlo : M * H ^ 2 / (L * q₀ * v₀ * Δ₁) ≤ m
  hmhi : m ≤ L * q₀ * x ^ δ * M * H ^ 2 / (v₀ * Δ₁)

namespace IncidenceSourceEnvelope

variable {x «ω» δ γ L Z A M N H q₀ v₀ w₁ Δ₁ Δ m : ℝ}
variable (h : IncidenceSourceEnvelope x «ω» δ γ L Z A M N H q₀ v₀ w₁ Δ₁ Δ m)

include h

theorem positive : 0 < x ∧ 0 < L ∧ 0 < Z ∧ 0 < A ∧ 0 < M ∧
    0 < N ∧ 0 < H ∧ 0 < q₀ ∧ 0 < v₀ ∧ 0 < w₁ ∧ 0 < Δ₁ ∧ 0 < Δ ∧ 0 < m := by
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one h.hx
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one h.hA.1
  have hN : 0 < N := by rw [h.hN]; exact Real.rpow_pos_of_pos hx _
  have hΔ : 0 < Δ := by rw [h.hΔ]; exact mul_pos hA h.hΔ₁
  exact ⟨hx, lt_of_lt_of_le zero_lt_one h.hL,
    lt_of_lt_of_le zero_lt_one h.hZ, hA, h.hM, hN,
    lt_of_lt_of_le zero_lt_one h.hH, lt_of_lt_of_le zero_lt_one h.hq₀,
    lt_of_lt_of_le zero_lt_one h.hv₀, lt_of_lt_of_le zero_lt_one h.hw₁,
    h.hΔ₁, hΔ, h.hm⟩

theorem log_N : log N = γ * log x := by
  rw [h.hN, Real.log_rpow h.positive.1]

theorem log_MN_lower : log x - log L ≤ log M + log N := by
  obtain ⟨hx, hL, _, _, hM, hN, _⟩ := h.positive
  have hh := (Real.log_le_log_iff (by positivity) (by positivity)).mpr h.hMNlo
  simpa only [Real.log_div (ne_of_gt hx) (ne_of_gt hL),
    Real.log_mul (ne_of_gt hM) (ne_of_gt hN)] using hh

theorem log_MN_upper : log M + log N ≤ log L + log x := by
  obtain ⟨hx, hL, _, _, hM, hN, _⟩ := h.positive
  have hh := (Real.log_le_log_iff (by positivity) (by positivity)).mpr h.hMNhi
  simpa only [Real.log_mul (ne_of_gt hM) (ne_of_gt hN),
    Real.log_mul (ne_of_gt hL) (ne_of_gt hx)] using hh

theorem log_H_upper : log H ≤ log L + (4 * «ω» + δ) * log x - log q₀ := by
  obtain ⟨hx, hL, hZ, hA, hM, hN, hH, hq₀, hv₀, hw₁, hΔ₁, hΔ, hm⟩ := h.positive
  have hh := (Real.log_le_log_iff (by positivity) (by positivity)).mpr h.hHhi
  simpa (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_rpow] using hh

theorem log_delta_lower :
    log N - (log L + 2 * log q₀ + δ * log x + 2 * log H + log Z) ≤ log Δ₁ := by
  obtain ⟨hx, hL, hZ, hA, hM, hN, hH, hq₀, hv₀, hw₁, hΔ₁, hΔ, hm⟩ := h.positive
  have hh := (Real.log_le_log_iff (by positivity) (by positivity)).mpr h.hΔlo
  simpa (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
    Real.log_rpow, Nat.cast_ofNat] using hh

theorem log_delta_upper :
    log Δ₁ ≤ log N - (2 * log q₀ + 2 * log H + log Z) := by
  obtain ⟨hx, hL, hZ, hA, hM, hN, hH, hq₀, hv₀, hw₁, hΔ₁, hΔ, hm⟩ := h.positive
  have hh := (Real.log_le_log_iff (by positivity) (by positivity)).mpr h.hΔhi
  simpa (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
    Nat.cast_ofNat] using hh

theorem log_expansion : log Δ = log A + log Δ₁ := by
  obtain ⟨hx, hL, hZ, hA, hM, hN, hH, hq₀, hv₀, hw₁, hΔ₁, hΔ, hm⟩ := h.positive
  rw [h.hΔ, Real.log_mul (ne_of_gt hA) (ne_of_gt hΔ₁)]

theorem log_m_lower :
    log M + 2 * log H - (log L + log q₀ + log v₀ + log Δ₁) ≤ log m := by
  obtain ⟨hx, hL, hZ, hA, hM, hN, hH, hq₀, hv₀, hw₁, hΔ₁, hΔ, hm⟩ := h.positive
  have hh := (Real.log_le_log_iff (by positivity) (by positivity)).mpr h.hmlo
  simpa (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
    Nat.cast_ofNat] using hh

theorem log_m_upper : log m ≤
    log L + log q₀ + δ * log x + log M + 2 * log H - (log v₀ + log Δ₁) := by
  obtain ⟨hx, hL, hZ, hA, hM, hN, hH, hq₀, hv₀, hw₁, hΔ₁, hΔ, hm⟩ := h.positive
  have hh := (Real.log_le_log_iff (by positivity) (by positivity)).mpr h.hmhi
  simpa (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
    Real.log_rpow, Nat.cast_ofNat] using hh

theorem log_m_envelope : log m ≤
    2 * log L + 3 * log q₀ + 2 * δ * log x + log Z + log M +
      4 * log H - log v₀ - log N := by
  nlinarith only [h.log_m_upper, h.log_delta_lower]

theorem log_m_scale : log m ≤
    7 * log L + log Z + (1 + 16 * «ω» + 6 * δ) * log x -
      log q₀ - log v₀ - 2 * log N := by
  nlinarith only [h.log_m_envelope, h.log_MN_upper, h.log_H_upper]

/-- The mean retains the extraction retreat, before dropping harmless denominators. -/
theorem mean_bound :
    Δ₁ * H ^ 2 / (q₀ ^ 3 * w₁ * v₀ * N) ≤
      1 / (q₀ ^ 5 * w₁ * v₀ * Z) := by
  obtain ⟨hx, hL, hZ, hA, hM, hN, hH, hq₀, hv₀, hw₁, hΔ₁, hΔ, hm⟩ := h.positive
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
    Real.log_one, Nat.cast_ofNat]
  linarith only [h.log_delta_upper]

theorem mean_bound_retreat :
    Δ₁ * H ^ 2 / (q₀ ^ 3 * w₁ * v₀ * N) ≤ 1 / Z := by
  apply h.mean_bound.trans
  obtain ⟨hx, hL, hZ, hA, hM, hN, hH, hq₀, hv₀, hw₁, hΔ₁, hΔ, hm⟩ := h.positive
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
    Real.log_one, Nat.cast_ofNat]
  linarith only [Real.log_nonneg h.hq₀, Real.log_nonneg h.hv₀,
    Real.log_nonneg h.hw₁]

theorem m_envelope :
    m ≤ L ^ 2 * q₀ ^ 3 * x ^ (2 * δ) * Z * M * H ^ 4 / (v₀ * N) := by
  obtain ⟨hx, hL, hZ, hA, hM, hN, hH, hq₀, hv₀, hw₁, hΔ₁, hΔ, hm⟩ := h.positive
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
    Real.log_rpow, Nat.cast_ofNat]
  linarith only [h.log_m_envelope]

/-- The literal normalized oscillatory source term. -/
theorem oscillatory_bound :
    x ^ (2 * δ) * m ^ (3 / 2 : ℝ) * H ^ 2 /
        (q₀ ^ (5 / 2 : ℝ) * v₀ * N * Δ) ≤
      L ^ 16 * Z ^ (5 / 2 : ℝ) *
        x ^ (3 / 2 + 40 * «ω» + 16 * δ - 5 * γ) /
        (q₀ ^ 6 * v₀ ^ (5 / 2 : ℝ)) := by
  obtain ⟨hx, hL, hZ, hA, hM, hN, hH, hq₀, hv₀, hw₁, hΔ₁, hΔ, hm⟩ := h.positive
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
    Real.log_rpow, Nat.cast_ofNat]
  nlinarith only [h.log_m_scale, h.log_delta_lower, h.log_H_upper,
    h.log_expansion, h.log_N, Real.log_nonneg h.hA.1, Real.log_nonneg h.hL]

/-- The literal normalized second exceptional-row term. -/
theorem row_two_bound :
    Real.sqrt m * H ^ 2 / (q₀ ^ (5 / 2 : ℝ) * v₀ * N) ≤
      L ^ 6 * Real.sqrt Z * x ^ (1 / 2 + 16 * «ω» + 5 * δ - 2 * γ) /
        (q₀ ^ 5 * v₀ ^ (3 / 2 : ℝ)) := by
  obtain ⟨hx, hL, hZ, hA, hM, hN, hH, hq₀, hv₀, hw₁, hΔ₁, hΔ, hm⟩ := h.positive
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
    Real.log_rpow, Real.log_sqrt, Nat.cast_ofNat]
  nlinarith only [h.log_m_scale, h.log_H_upper, h.log_N, Real.log_nonneg h.hL]

/-- The literal normalized first exceptional-row term. -/
theorem row_one_bound :
    x ^ δ * Real.sqrt m * H ^ 2 / (q₀ ^ (7 / 2 : ℝ) * v₀ * N) ≤
      L ^ 6 * Real.sqrt Z * x ^ (1 / 2 + 16 * «ω» + 6 * δ - 2 * γ) /
        (q₀ ^ 6 * v₀ ^ (3 / 2 : ℝ)) := by
  obtain ⟨hx, hL, hZ, hA, hM, hN, hH, hq₀, hv₀, hw₁, hΔ₁, hΔ, hm⟩ := h.positive
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
    Real.log_rpow, Real.log_sqrt, Nat.cast_ofNat]
  nlinarith only [h.log_m_scale, h.log_H_upper, h.log_N, Real.log_nonneg h.hL]

end IncidenceSourceEnvelope

end PrimeGap182Audit

#print axioms PrimeGap182Audit.IncidenceSourceEnvelope.mean_bound
#print axioms PrimeGap182Audit.IncidenceSourceEnvelope.mean_bound_retreat
#print axioms PrimeGap182Audit.IncidenceSourceEnvelope.m_envelope
#print axioms PrimeGap182Audit.IncidenceSourceEnvelope.oscillatory_bound
#print axioms PrimeGap182Audit.IncidenceSourceEnvelope.row_two_bound
#print axioms PrimeGap182Audit.IncidenceSourceEnvelope.row_one_bound
