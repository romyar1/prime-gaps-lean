import IncidenceSectorNormalization

/-!
# Uniform numerical margins for the normalized source terms

The small coefficient/window loss is P≤x^(ε/100). The coarser source
and angular envelopes have separate x^(20ε), x^(25ε) budgets. Thus the
mean retains the extraction retreat even after the other terms are
normalized. These are explicit scale implications, not distribution
assumptions.
-/

noncomputable section
namespace PrimeGap182Audit

set_option maxHeartbeats 1600000

theorem incidenceCorrectedContributions_saving
    {x «ω» δ γ L Z A M N H q₀ v₀ w Δ₁ Δ m : ℝ}
    (h : IncidenceSourceEnvelope x «ω» δ γ L Z A M N H q₀ v₀ w Δ₁ Δ m)
    (ε P Ly Lj : ℝ) (hε : 0 < ε) (hP : 1 ≤ P) (hLy : 0 < Ly) (hLj : 0 < Lj)
    (hPs : P ≤ x ^ (ε / 100)) (hLs : L ≤ x ^ (20 * ε))
    (hLys : Ly ≤ x ^ (25 * ε)) (hLjs : Lj ≤ x ^ (25 * ε))
    (hZ : Z = x ^ (54 * ε))
    (hgap : 600 * ε ≤ 5 * γ - 3 / 2 - 40 * «ω» - 16 * δ)
    (hrowgap : 250 * ε ≤ 2 * γ - 1 / 2 - 16 * «ω» - 6 * δ)
    (hxlarge : 11 ≤ x ^ ε) :
    P ^ 5 *
      (2 * (q₀ ^ 3 * (Δ₁ * H ^ 2 / (q₀ ^ 3 * w * v₀ * N))) +
        Lj * (q₀ ^ 3 * (x ^ δ * Real.sqrt m * H ^ 2 /
          (q₀ ^ (7 / 2 : ℝ) * v₀ * N))) +
        2 * (q₀ ^ 3 * (Real.sqrt m * H ^ 2 / (q₀ ^ (5 / 2 : ℝ) * v₀ * N)))) +
      6 * P ^ 4 * Ly * Lj *
        (q₀ ^ 3 * (x ^ (2 * δ) * m ^ (3 / 2 : ℝ) * H ^ 2 /
          (q₀ ^ (5 / 2 : ℝ) * v₀ * N * Δ))) ≤ x ^ (-49 * ε) := by
  obtain ⟨hx, hL, hZpos, hA, hM, hN, hH, hq₀, hv₀, hw, hΔ₁, hΔ, hm⟩ := h.positive
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg h.hx
  have hlogP : Real.log P ≤ (ε / 100) * Real.log x := by
    simpa only [Real.log_rpow hx] using Real.log_le_log hP0 hPs
  have hlogL : Real.log L ≤ (20 * ε) * Real.log x := by
    simpa only [Real.log_rpow hx] using Real.log_le_log hL hLs
  have hlogLy : Real.log Ly ≤ (25 * ε) * Real.log x := by
    simpa only [Real.log_rpow hx] using Real.log_le_log hLy hLys
  have hlogLj : Real.log Lj ≤ (25 * ε) * Real.log x := by
    simpa only [Real.log_rpow hx] using Real.log_le_log hLj hLjs
  have hlogZ : Real.log Z = (54 * ε) * Real.log x := by rw [hZ, Real.log_rpow hx]
  have hlogq₀ : 0 ≤ Real.log q₀ := Real.log_nonneg h.hq₀
  have hlogv₀ : 0 ≤ Real.log v₀ := Real.log_nonneg h.hv₀
  have hlogw : 0 ≤ Real.log w := Real.log_nonneg h.hw₁
  have hepslog : 0 ≤ ε * Real.log x := mul_nonneg hε.le hlogx
  have hgaplog := mul_le_mul_of_nonneg_right hgap hlogx
  have hrowgaplog := mul_le_mul_of_nonneg_right hrowgap hlogx
  have hδlog : 0 ≤ δ * Real.log x := mul_nonneg h.hδ hlogx
  have hmean : P ^ 5 * (q₀ ^ 3 * (Δ₁ * H ^ 2 / (q₀ ^ 3 * w * v₀ * N))) ≤
      x ^ (-50 * ε) := by
    apply (mul_le_mul_of_nonneg_left h.fully_corrected_mean_bound (by positivity)).trans
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow,
      Real.log_one, Real.log_rpow, Nat.cast_ofNat]
    nlinarith only [hlogP, hlogZ, hlogq₀, hlogw, hlogv₀, hepslog]
  have hrowtwo : P ^ 5 * (q₀ ^ 3 *
      (Real.sqrt m * H ^ 2 / (q₀ ^ (5 / 2 : ℝ) * v₀ * N))) ≤ x ^ (-50 * ε) := by
    apply (mul_le_mul_of_nonneg_left h.fully_corrected_row_two_bound (by positivity)).trans
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow,
      Real.log_sqrt, Real.log_rpow, Nat.cast_ofNat]
    nlinarith only [hlogP, hlogL, hlogZ, hlogq₀, hlogv₀, hepslog, hrowgaplog, hδlog]
  have hrowone : P ^ 5 * Lj * (q₀ ^ 3 *
      (x ^ δ * Real.sqrt m * H ^ 2 / (q₀ ^ (7 / 2 : ℝ) * v₀ * N))) ≤ x ^ (-50 * ε) := by
    apply (mul_le_mul_of_nonneg_left h.fully_corrected_row_one_bound (by positivity)).trans
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow,
      Real.log_sqrt, Real.log_rpow, Nat.cast_ofNat]
    nlinarith only [hlogP, hlogL, hlogLj, hlogZ, hlogq₀, hlogv₀, hepslog, hrowgaplog]
  have hosc : P ^ 4 * Ly * Lj * (q₀ ^ 3 *
      (x ^ (2 * δ) * m ^ (3 / 2 : ℝ) * H ^ 2 /
        (q₀ ^ (5 / 2 : ℝ) * v₀ * N * Δ))) ≤ x ^ (-50 * ε) := by
    apply (mul_le_mul_of_nonneg_left h.fully_corrected_oscillatory_bound (by positivity)).trans
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow,
      Real.log_rpow, Nat.cast_ofNat]
    nlinarith only [hlogP, hlogL, hlogLy, hlogLj, hlogZ, hlogq₀, hlogv₀, hepslog, hgaplog]
  calc
    _ ≤ 11 * x ^ (-50 * ε) := by linarith only [hmean, hrowone, hrowtwo, hosc]
    _ ≤ x ^ ε * x ^ (-50 * ε) := mul_le_mul_of_nonneg_right hxlarge (by positivity)
    _ = _ := by rw [← Real.rpow_add hx]; congr 1; ring

theorem incidenceStrictGuards_arbitrarily_small_epsilon
    («ω» δ γlo γhi : ℝ) (hω : 0 < «ω») (hδ : 0 < δ)
    (_hlo : 12 * «ω» + 6 * δ < γlo) (hhi : γhi < 1 / 2 - 2 * «ω»)
    (hdensity : 2 * γhi + 4 * «ω» + 2 * δ < 1)
    (hfour : 16 * «ω» + 7 * δ < γlo)
    (hfive : 3 / 2 + 40 * «ω» + 16 * δ < 5 * γlo) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      600 * ε ≤ 5 * γlo - 3 / 2 - 40 * «ω» - 16 * δ ∧
      250 * ε ≤ 2 * γlo - 1 / 2 - 16 * «ω» - 6 * δ ∧
      100 * ε ≤ γlo - 12 * «ω» - 6 * δ ∧
      100 * ε ≤ 1 / 2 - 2 * «ω» - γhi ∧
      100 * ε ≤ 1 - 2 * γhi - 4 * «ω» - 2 * δ ∧
      100 * ε ≤ γlo - 16 * «ω» - 7 * δ ∧ ε ≤ «ω» ∧ ε ≤ δ := by
  let a := (5 * γlo - 3 / 2 - 40 * «ω» - 16 * δ) / 1000
  let b := (2 * γlo - 1 / 2 - 16 * «ω» - 6 * δ) / 1000
  let c := (γlo - 12 * «ω» - 6 * δ) / 1000
  let d := (1 / 2 - 2 * «ω» - γhi) / 1000
  let e := (1 - 2 * γhi - 4 * «ω» - 2 * δ) / 1000
  let f := (γlo - 16 * «ω» - 7 * δ) / 1000
  have ha : 0 < a := by dsimp only [a]; linarith
  have hb : 0 < b := by dsimp only [b]; linarith
  have hc : 0 < c := by dsimp only [c]; linarith
  have hd : 0 < d := by dsimp only [d]; linarith
  have he : 0 < e := by dsimp only [e]; linarith
  have hf : 0 < f := by dsimp only [f]; linarith
  refine ⟨min a (min b (min c (min d (min e (min f (min «ω» δ)))))), by positivity, ?_⟩
  intro ε hε hsmall
  simp only [lt_min_iff] at hsmall
  dsimp only [a, b, c, d, e, f] at hsmall
  rcases hsmall with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h7.le, h8.le⟩ <;> linarith

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceCorrectedContributions_saving
#print axioms PrimeGap182Audit.incidenceStrictGuards_arbitrarily_small_epsilon
