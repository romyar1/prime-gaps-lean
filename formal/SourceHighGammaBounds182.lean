import PrimeGaps186

/-! The actual high-gamma discrepancy argument, reproved under
`68 * ω + 20 * δ < 1` instead of the public theorem's `72 * ω + 24 * δ < 1`.
The source and exact transformations are recorded in
`audits/source_high_gamma_generation.json`. These adapted proof fragments
retain the upstream credits and notices in the pinned public baseline.
No finite-field estimate or discrepancy conclusion is assumed here. -/

noncomputable section
open scoped BigOperators Topology ContDiff
open Filter Asymptotics PrimeGap186
namespace PrimeGap182Audit
set_option maxHeartbeats 2000000

/-- The selected incidence window supplies the sufficient near-range guard. -/
theorem highGamma_guard_of_incidence_window («ω» δ γlo : ℝ)
    (hω : «ω» < 3 / 200) (hγ : γlo ≤ 41361 / 100000)
    (hfive : 3 / 2 + 40 * «ω» + 16 * δ < 5 * γlo) :
    68 * «ω» + 20 * δ < 1 := by
  linarith only [hω, hγ, hfive]

open Classical in
theorem sourceHighGamma_scale_envelopes
    («ω» δ ε C x M N R Q H q γ : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ) (hε : 0 < ε)
    (hworking : 68 * «ω» + 20 * δ < 1)
    (hsmall : ε < δ / 10 ^ 100) (hC : 1 ≤ C) (hx : 1 ≤ x)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hQ : 0 < Q)
    (hq : 1 ≤ q) (hMN : x / C ≤ M * N) (hNγ : N = x ^ γ)
    (hNR : N ≤ C * x ^ (δ + 4 * ε) * R)
    (hRN : R ≤ C * x ^ (-2 * ε) * N)
    (hRQ : R * Q ≤ C * x ^ (1 / 2 + 2 * «ω» + ε))
    (hH : H = x ^ ε * R * Q ^ 2 / (q * M)) (hγhi : γ ≤ 1 / 2) :
    (1 / 2 - 2 * «ω» - δ / 2 ≤ γ →
      H ^ 2 * Q ^ 2 * R ^ (1 / 2 : ℝ) / N ≤ C ^ 12 * x ^ (-ε) ∧
      H ^ 2 / R ≤ C ^ 12 * x ^ (-ε) ∧
      H / Q ^ 2 ≤ C ^ 12 * x ^ (-ε)) ∧
    (1 / 4 + 14 * «ω» + 4 * δ + 100 * ε ≤ γ →
      γ ≤ 1 / 2 - 2 * «ω» - δ / 2 →
      C ^ (-2 : ℝ) * x ^ (δ / 2 - 7 * ε) ≤ x ^ (-5 * ε) * Q / H ∧
      ∀ V : ℝ, 0 < V → x ^ (5 * ε) * H / q ≤ C * V →
        H ^ (13 / 6 : ℝ) * Q ^ (1 / 3 : ℝ) * R ^ (1 / 6 : ℝ) *
            x ^ (δ / 3 + 5 * ε / 6) / N ^ (1 / 2 : ℝ) ≤
          C ^ 12 * x ^ (-5 * ε) ∧
        H ^ 2 / R ≤ C ^ 12 * x ^ (-5 * ε) ∧
        H / (V * q) ≤ C ^ 12 * x ^ (-5 * ε)) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hHpos : 0 < H := by rw [hH]; positivity
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hεδ : 1000 * ε ≤ δ := by
    have hpow : (1000 : ℝ) ≤ 10 ^ 100 := by norm_num
    have hs := (lt_div_iff₀ (by positivity : (0 : ℝ) < 10 ^ 100)).mp hsmall
    nlinarith only [hpow, hs, hε]
  have hlogMN : Real.log x - Real.log C ≤ Real.log M + Real.log N := by
    have hh := Real.log_le_log (by positivity : 0 < x / C) hMN
    simpa (disch := positivity) only [Real.log_div, Real.log_mul] using hh
  have hlogN : Real.log N = γ * Real.log x := by
    rw [hNγ, Real.log_rpow hxpos]
  have hlogNR : Real.log N ≤
      Real.log C + (δ + 4 * ε) * Real.log x + Real.log R := by
    have hh := Real.log_le_log hN hNR
    simpa (disch := positivity) only [Real.log_mul, Real.log_rpow] using hh
  have hlogRN : Real.log R ≤
      Real.log C + (-2 * ε) * Real.log x + Real.log N := by
    have hh := Real.log_le_log hR hRN
    simpa (disch := positivity) only [Real.log_mul, Real.log_rpow] using hh
  have hlogRQ : Real.log R + Real.log Q ≤
      Real.log C + (1 / 2 + 2 * «ω» + ε) * Real.log x := by
    have hh := Real.log_le_log (mul_pos hR hQ) hRQ
    simpa (disch := positivity) only [Real.log_mul, Real.log_rpow] using hh
  have hlogH : Real.log H = ε * Real.log x + Real.log R +
      2 * Real.log Q - Real.log q - Real.log M := by
    rw [hH]
    simp (disch := positivity) only [Real.log_div, Real.log_mul,
      Real.log_rpow, Real.log_pow]
    ring
  have hbound {z p : ℝ} (hz : 0 < z)
      (hlog : Real.log z ≤ 12 * Real.log C + p * Real.log x) :
      z ≤ C ^ 12 * x ^ p := by
    apply (Real.log_le_log_iff hz (by positivity)).mp
    simpa (disch := positivity) only [Real.log_mul, Real.log_pow,
      Real.log_rpow, Nat.cast_ofNat] using hlog
  have htwo : Real.log (H ^ 2 / R) ≤ 9 * Real.log C +
      (8 * «ω» + 3 * δ + 18 * ε - γ) * Real.log x := by
    simp (disch := positivity) only [Real.log_div, Real.log_pow, Nat.cast_ofNat]
    nlinarith only [hlogMN, hlogNR, hlogRQ, hlogH, hlogN, hlogq]
  constructor
  · intro hγlo
    have he₁ : 1 + 12 * «ω» + 7 * δ / 2 + 22 * ε - 5 * γ / 2 ≤ -ε := by
      linarith only [hworking, hγlo, hεδ, hω, hε]
    have he₂ : 8 * «ω» + 3 * δ + 18 * ε - γ ≤ -ε := by
      linarith only [hworking, hγlo, hεδ, hω, hδ]
    have he₃ : 2 * γ - 1 - ε ≤ -ε := by linarith only [hγhi]
    refine ⟨hbound (by positivity) ?_, hbound (by positivity) ?_,
      hbound (by positivity) ?_⟩
    · have hfirst : Real.log (H ^ 2 * Q ^ 2 * R ^ (1 / 2 : ℝ) / N) ≤
          (23 / 2 : ℝ) * Real.log C +
            (1 + 12 * «ω» + 7 * δ / 2 + 22 * ε - 5 * γ / 2) * Real.log x := by
        simp (disch := positivity) only [Real.log_div, Real.log_mul,
          Real.log_pow, Real.log_rpow, Nat.cast_ofNat]
        nlinarith only [hlogMN, hlogNR, hlogRQ, hlogH, hlogN, hlogq]
      nlinarith only [hfirst, mul_le_mul_of_nonneg_right he₁ hlogx, hlogC]
    · nlinarith only [htwo, mul_le_mul_of_nonneg_right he₂ hlogx, hlogC]
    · have hthird : Real.log (H / Q ^ 2) ≤
          2 * Real.log C + (2 * γ - 1 - ε) * Real.log x := by
        simp (disch := positivity) only [Real.log_div, Real.log_pow, Nat.cast_ofNat]
        nlinarith only [hlogMN, hlogRN, hlogH, hlogN, hlogq]
      nlinarith only [hthird, mul_le_mul_of_nonneg_right he₃ hlogx, hlogC]
  · intro hγlo hγcut
    constructor
    · apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
      simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
      have hcut := mul_le_mul_of_nonneg_right hγcut hlogx
      nlinarith only [hlogMN, hlogRQ, hlogH, hlogN, hlogq, hcut]
    · intro V hV hVlo
      have he₁ : 1 / 6 + 28 * «ω» / 3 + 8 * δ / 3 + 17 * ε -
          2 * γ / 3 ≤ -5 * ε := by linarith only [hγlo, hε]
      have he₂ : 8 * «ω» + 3 * δ + 18 * ε - γ ≤ -5 * ε := by
        linarith only [hγlo, hε, hω, hδ]
      have hlogV : 5 * ε * Real.log x + Real.log H - Real.log q ≤
          Real.log C + Real.log V := by
        have hh := Real.log_le_log (by positivity : 0 < x ^ (5 * ε) * H / q) hVlo
        simpa (disch := positivity) only [Real.log_div, Real.log_mul,
          Real.log_rpow] using hh
      refine ⟨hbound (by positivity) ?_, hbound (by positivity) ?_,
        hbound (by positivity) ?_⟩
      · have hfirst :
            Real.log (H ^ (13 / 6 : ℝ) * Q ^ (1 / 3 : ℝ) * R ^ (1 / 6 : ℝ) *
              x ^ (δ / 3 + 5 * ε / 6) / N ^ (1 / 2 : ℝ)) ≤
            (55 / 6 : ℝ) * Real.log C +
              (1 / 6 + 28 * «ω» / 3 + 8 * δ / 3 + 17 * ε - 2 * γ / 3) *
                Real.log x := by
          simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_rpow]
          nlinarith only [hlogMN, hlogNR, hlogRQ, hlogH, hlogN, hlogq]
        nlinarith only [hfirst, mul_le_mul_of_nonneg_right he₁ hlogx, hlogC]
      · nlinarith only [htwo, mul_le_mul_of_nonneg_right he₂ hlogx, hlogC]
      · simp (disch := positivity) only [Real.log_div, Real.log_mul]
        nlinarith only [hlogV, hlogC]

open Classical in
theorem opening_high_scale_resources (C «ω» δ ε : ℝ)
    (hC : 1 ≤ C) (hω : 0 < «ω») (hδ : 0 < δ) (hε : 0 < ε)
    (hworking : 68 * «ω» + 20 * δ < 1) (hsmall : ε < δ / 10 ^ 100) :
    ∀ᶠ x : ℝ in Filter.atTop,
      Real.exp 1 ≤ x ∧ 2 ≤ x ∧ C ^ 2 ≤ x ^ (δ / 2 - 7 * ε) ∧
      ∀ M N R Q γ : ℝ,
        0 < M → 0 < N → 0 < R → 0 < Q →
        x / C ≤ M * N → M * N ≤ C * x → N = x ^ γ →
        1 / 4 + 14 * «ω» + 4 * δ + 100 * ε ≤ γ →
        γ ≤ 1 / 2 →
        N ≤ C * x ^ (δ + 4 * ε) * R →
        R ≤ C * x ^ (-2 * ε) * N →
        R * Q ≤ C * x ^ (1 / 2 + 2 * «ω» + ε) →
        1 ≤ N ∧ N ≤ x ∧ 1 ≤ M ∧ M ≤ x ^ 2 ∧ R ≤ x ∧ Q ≤ x ∧
          4 * x ^ ε < M := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hεδ : ε < δ :=
    hsmall.trans_le (div_le_self hδ.le (by norm_num))
  have hεhalf : ε < 1 / 2 := by
    linarith only [hεδ, hworking, hω]
  have hmargin : 0 < δ / 2 - 7 * ε := by
    have hs := (lt_div_iff₀ (by positivity : (0 : ℝ) < 10 ^ 100)).mp hsmall
    have hn : (100 : ℝ) ≤ 10 ^ 100 := by norm_num
    nlinarith only [hs, hn, hε]
  have hCmargin : ∀ᶠ x : ℝ in Filter.atTop,
      C ^ 2 ≤ x ^ (δ / 2 - 7 * ε) :=
    (tendsto_rpow_atTop hmargin).eventually_ge_atTop (C ^ 2)
  have hCquarter : ∀ᶠ x : ℝ in Filter.atTop, C ^ 2 ≤ x ^ (1 / 4 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_ge_atTop
      (C ^ 2)
  have hCutoff := eventually_scale_dominates_cutoff_of_product_lower
    (1 / C) 1 (1 / 2) ε 4 (by positivity) (by norm_num) (by norm_num)
    (by linarith only [hεhalf])
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1),
    Filter.eventually_ge_atTop (2 : ℝ), hCmargin, hCquarter, hCutoff]
    with x hxe hx2 hCmarginAt hCquarterAt hCutoffAt
  refine ⟨hxe, hx2, hCmarginAt, ?_⟩
  intro M N R Q γ hM hN _hR hQ hMNlo hMNhi hNγ hγlo hγhi hNR hRupper hRQ
  have hxone : 1 ≤ x := (by norm_num : (1 : ℝ) ≤ 2).trans hx2
  have hxpos : 0 < x := zero_lt_one.trans_le hxone
  have hγlower : 1 / 4 + 14 * «ω» + 4 * δ + 100 * ε ≤ γ := hγlo
  have hγnonneg : 0 ≤ γ := by linarith only [hγlower, hω, hδ, hε]
  have hγhalf : γ ≤ 1 / 2 := by linarith only [hγhi, hω, hδ, hε]
  have hNhalf : N ≤ x ^ (1 / 2 : ℝ) := by
    rw [hNγ]
    exact Real.rpow_le_rpow_of_exponent_le hxone hγhalf
  have hhalf : x ^ (1 / 2 : ℝ) ≤ x := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hxone (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hNone : 1 ≤ N := by
    rw [hNγ]
    exact Real.one_le_rpow hxone hγnonneg
  have hCpow : C ≤ C ^ 2 := by
    simpa only [mul_one, pow_two] using mul_le_mul_of_nonneg_left hC hCpos.le
  have hCquarterBound : C ≤ x ^ (1 / 4 : ℝ) := hCpow.trans hCquarterAt
  have hChalf : C ≤ x ^ (1 / 2 : ℝ) := hCquarterBound.trans
    (Real.rpow_le_rpow_of_exponent_le hxone (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2))
  have hCx : C ≤ x := hChalf.trans hhalf
  have hMcut : 4 * x ^ ε < M := hCutoffAt M N hN
    (by simpa only [one_mul] using hNhalf)
    (by simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hMNlo)
  have hMone : 1 ≤ M := by
    have hxeone : 1 ≤ x ^ ε := Real.one_le_rpow hxone hε.le
    linarith only [hMcut, hxeone]
  have hMupper : M ≤ x ^ 2 := by
    calc
      M ≤ M * N := le_mul_of_one_le_right hM.le hNone
      _ ≤ C * x := hMNhi
      _ ≤ x * x := mul_le_mul_of_nonneg_right hCx hxpos.le
      _ = x ^ 2 := (pow_two x).symm
  have hRsmall : R ≤ x := by
    have hxnegative : x ^ (-2 * ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hxone (by linarith only [hε])
    calc
      R ≤ C * x ^ (-2 * ε) * N := hRupper
      _ ≤ C * 1 * N := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hxnegative hCpos.le) hN.le
      _ = C * N := by ring
      _ ≤ x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) :=
        mul_le_mul hChalf hNhalf hN.le (Real.rpow_nonneg hxpos.le _)
      _ = x := by rw [← Real.rpow_add hxpos]; norm_num
  have hQN : Q * N ≤ C ^ 2 * x ^ (1 / 2 + 2 * «ω» + δ + 5 * ε) := by
    calc
      Q * N ≤ Q * (C * x ^ (δ + 4 * ε) * R) :=
        mul_le_mul_of_nonneg_left hNR hQ.le
      _ = (C * x ^ (δ + 4 * ε)) * (R * Q) := by ring
      _ ≤ (C * x ^ (δ + 4 * ε)) * (C * x ^ (1 / 2 + 2 * «ω» + ε)) :=
        mul_le_mul_of_nonneg_left hRQ (by positivity)
      _ = C ^ 2 * (x ^ (δ + 4 * ε) * x ^ (1 / 2 + 2 * «ω» + ε)) := by ring
      _ = C ^ 2 * x ^ (1 / 2 + 2 * «ω» + δ + 5 * ε) := by
        rw [← Real.rpow_add hxpos,
          show δ + 4 * ε + (1 / 2 + 2 * «ω» + ε) =
            1 / 2 + 2 * «ω» + δ + 5 * ε by ring]
  have hQsmall : Q ≤ x := by
    have hpower : 1 / 2 + 2 * «ω» + δ + 5 * ε - γ ≤ 1 / 4 := by
      linarith only [hγlower, hω, hδ, hε]
    calc
      Q ≤ (C ^ 2 * x ^ (1 / 2 + 2 * «ω» + δ + 5 * ε)) / N :=
        (le_div_iff₀ hN).mpr hQN
      _ = C ^ 2 * x ^ (1 / 2 + 2 * «ω» + δ + 5 * ε - γ) := by
        rw [hNγ, mul_div_assoc, ← Real.rpow_sub hxpos]
      _ ≤ C ^ 2 * x ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hxone hpower) (sq_nonneg C)
      _ ≤ x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hCquarterAt (Real.rpow_nonneg hxpos.le _)
      _ = x ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hxpos]; norm_num
      _ ≤ x := hhalf
  exact ⟨hNone, hNhalf.trans hhalf, hMone, hMupper, hRsmall, hQsmall, hMcut⟩

#print axioms highGamma_guard_of_incidence_window
#print axioms sourceHighGamma_scale_envelopes
#print axioms opening_high_scale_resources

end PrimeGap182Audit
