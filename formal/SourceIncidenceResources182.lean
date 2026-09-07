import IncidenceSecondaryInterface

/-! Source selection resources with the common modulus retained in the
selected divisor target. These are consequences of the actual scale
equalities and inequalities, independent of a secondary estimate. -/

noncomputable section
open Filter PrimeGap186 Real

namespace PrimeGap182Audit

theorem sourceIncidence_divisor_target_resources
    (C «ω» δ ε : ℝ) (hC : 1 ≤ C) (hω : 0 < «ω») (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ X₀ : ℝ, Real.exp 1 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ q₀ : ℕ, 0 < q₀ →
      ∀ M N R₀ Q H γ : ℝ, 0 < M → 0 < N → 0 < R₀ → 0 < Q → 1 ≤ H →
      N = x ^ γ → 8 * «ω» + 2 * δ + 100 * ε ≤ γ → γ ≤ 1 →
      x / C ≤ M * N → N ≤ C * x ^ (δ + 4 * ε) * R₀ →
      R₀ * Q ≤ C * x ^ (1 / 2 + 2 * «ω» + ε) →
      H = x ^ ε * R₀ * Q ^ 2 / ((q₀ : ℝ) * M) →
      let Dtarget := N / (x ^ (50 * ε) * ((q₀ : ℝ) * H) ^ 2)
      H ≤ C ^ 4 * x ^ (4 * «ω» + δ + 7 * ε) / (q₀ : ℝ) ∧
        1 ≤ N ∧ N ≤ x ∧ 0 < Dtarget ∧ 1 ≤ Dtarget ∧ Dtarget ≤ N ∧
        1 ≤ x ^ δ ∧
        ∀ r : ℕ, R₀ / C ≤ (r : ℝ) → Dtarget ≤ x ^ δ * (r : ℝ) := by
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hε).eventually_ge_atTop (C ^ 8))
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by positivity : 0 < 46 * ε)).eventually_ge_atTop (C ^ 2))
  refine ⟨max (Real.exp 1) (max X₁ X₂), le_max_left _ _, ?_⟩
  intro x hxX q₀ hq₀Nat M N R₀ Q H γ hM hN hR₀ hQ hH hNγ hγlo hγhi hMNlo hNR hRQ hHdef Dtarget
  have hxe : Real.exp 1 ≤ x := (le_max_left _ _).trans hxX
  have hx : 1 ≤ x := (Real.one_le_exp zero_le_one).trans hxe
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hq₀0 : 0 < (q₀ : ℝ) := by exact_mod_cast hq₀Nat
  have hq₀1 : (1 : ℝ) ≤ q₀ := by exact_mod_cast hq₀Nat
  have hpow (a : ℝ) : 0 < x ^ a := Real.rpow_pos_of_pos hx0 a
  have hCX₈ : C ^ 8 ≤ x ^ ε :=
    hX₁ x ((le_max_left _ _).trans ((le_max_right _ _).trans hxX))
  have hCX₂ : C ^ 2 ≤ x ^ (46 * ε) :=
    hX₂ x ((le_max_right _ _).trans ((le_max_right _ _).trans hxX))
  have hNlog : log N = γ * log x := by rw [hNγ, Real.log_rpow hx0]
  have hMNlog := (Real.log_le_log_iff (by positivity) (by positivity)).mpr hMNlo
  have hNRlog := (Real.log_le_log_iff hN (by positivity)).mpr hNR
  have hRQlog := (Real.log_le_log_iff (by positivity) (by positivity)).mpr hRQ
  have hHlog := congrArg Real.log hHdef
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
    Real.log_rpow, Nat.cast_ofNat] at hMNlog hNRlog hRQlog hHlog
  have hHbound : H ≤ C ^ 4 * x ^ (4 * «ω» + δ + 7 * ε) / (q₀ : ℝ) := by
    apply (Real.log_le_log_iff hH0 (by positivity)).mp
    simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
      Real.log_rpow, Nat.cast_ofNat]
    nlinarith only [hMNlog, hNRlog, hRQlog, hHlog]
  have hHboundlog := (Real.log_le_log_iff hH0 (by positivity)).mpr hHbound
  have hC8log := (Real.log_le_log_iff (by positivity) (hpow ε)).mpr hCX₈
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
    Real.log_rpow, Nat.cast_ofNat] at hHboundlog hC8log
  have hdenN : x ^ (50 * ε) * ((q₀ : ℝ) * H) ^ 2 ≤ N := by
    apply (Real.log_le_log_iff (by positivity) hN).mp
    simp (disch := positivity) only [Real.log_mul, Real.log_pow, Real.log_rpow, Nat.cast_ofNat]
    nlinarith only [hHboundlog, hC8log, hNlog,
      mul_nonneg (sub_nonneg.mpr hγlo) (Real.log_nonneg hx),
      mul_nonneg hε.le (Real.log_nonneg hx)]
  have hNlower : 1 ≤ N := by
    rw [hNγ]
    exact Real.one_le_rpow hx (by linarith only [hγlo, hω, hδ, hε])
  have hNupper : N ≤ x := by
    rw [hNγ]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx hγhi
  have hdenPos : 0 < x ^ (50 * ε) * ((q₀ : ℝ) * H) ^ 2 := by positivity
  have hqHone : 1 ≤ ((q₀ : ℝ) * H) ^ 2 :=
    one_le_pow₀ (one_le_mul_of_one_le_of_one_le hq₀1 hH)
  have hdenOne : 1 ≤ x ^ (50 * ε) * ((q₀ : ℝ) * H) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hx (by positivity)) hqHone
  refine ⟨hHbound, hNlower, hNupper, div_pos hN hdenPos,
    (one_le_div hdenPos).mpr hdenN, div_le_self hN.le hdenOne, Real.one_le_rpow hx hδ.le, ?_⟩
  intro r hr
  have hr0 : 0 < (r : ℝ) := (div_pos hR₀ hC0).trans_le hr
  have hRr : R₀ ≤ C * (r : ℝ) := (div_le_iff₀' hC0).mp hr
  have hNtarget : N ≤ (x ^ δ * (r : ℝ)) * x ^ (50 * ε) := by
    calc
      N ≤ C * x ^ (δ + 4 * ε) * R₀ := hNR
      _ ≤ C * x ^ (δ + 4 * ε) * (C * (r : ℝ)) :=
        mul_le_mul_of_nonneg_left hRr (by positivity)
      _ = C ^ 2 * (x ^ (δ + 4 * ε) * (r : ℝ)) := by ring
      _ ≤ x ^ (46 * ε) * (x ^ (δ + 4 * ε) * (r : ℝ)) :=
        mul_le_mul_of_nonneg_right hCX₂ (by positivity)
      _ = (x ^ δ * (r : ℝ)) * x ^ (50 * ε) := by
        rw [← mul_assoc, ← Real.rpow_add hx0, show 46 * ε + (δ + 4 * ε) = δ + 50 * ε by ring,
          Real.rpow_add hx0]
        ring
  apply (div_le_iff₀ hdenPos).mpr
  calc
    N ≤ (x ^ δ * (r : ℝ)) * x ^ (50 * ε) := hNtarget
    _ ≤ ((x ^ δ * (r : ℝ)) * x ^ (50 * ε)) * ((q₀ : ℝ) * H) ^ 2 :=
      le_mul_of_one_le_right (by positivity) hqHone
    _ = _ := by ring

theorem sourceIncidence_coarse_heights
    («ω» δ ε C x M N R Q U V H q₀ : ℝ)
    (hω : «ω» < 1 / 16) (hδ : δ < 1 / 8) (hε : ε < 1 / 1000)
    (hC : 1 ≤ C) (hx : 1 ≤ x) (hCx : C ≤ x)
    (hM : 0 < M) (hN : 1 ≤ N) (hNx : N ≤ x) (hR : 0 < R) (hQ : 0 < Q)
    (hU : 0 < U) (_hV : 0 < V) (hH : 1 ≤ H) (hq₀ : 1 ≤ q₀)
    (hMN : M * N ≤ C * x) (hNR : N ≤ C * x ^ (δ + 4 * ε) * R)
    (hRC : R ≤ C * N) (hRQ : R * Q ≤ C * x ^ (1 / 2 + 2 * «ω» + ε))
    (hHbound : H ≤ C ^ 4 * x ^ (4 * «ω» + δ + 7 * ε) / q₀)
    (hUH : U * H ≤ C * Q) (hVC : V ≤ C * x ^ (δ + 5 * ε) * H) :
    M ≤ x ^ (2 : ℕ) ∧ R ≤ x ^ (2 : ℕ) ∧ Q ≤ x ^ (4 : ℕ) ∧
      H ≤ x ^ (12 : ℕ) ∧ U ≤ x ^ (5 : ℕ) ∧ V ≤ x ^ (14 : ℕ) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hMx : M ≤ x ^ (2 : ℕ) := by
    calc
      M ≤ M * N := le_mul_of_one_le_right hM.le hN
      _ ≤ C * x := hMN
      _ ≤ x * x := mul_le_mul_of_nonneg_right hCx hx0.le
      _ = _ := by ring
  have hRx : R ≤ x ^ (2 : ℕ) := by
    calc
      R ≤ C * N := hRC
      _ ≤ x * x := mul_le_mul hCx hNx hN0.le hx0.le
      _ = _ := by ring
  have hQx : Q ≤ x ^ (4 : ℕ) := by
    have hnr := (Real.log_le_log_iff hN0 (by positivity)).mpr hNR
    have hrq := (Real.log_le_log_iff (by positivity) (by positivity)).mpr hRQ
    have hcl := Real.log_le_log hC0 hCx
    apply (Real.log_le_log_iff hQ (by positivity)).mp
    simp (disch := positivity) only [Real.log_mul, Real.log_rpow] at hnr hrq
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have hexp : 1 / 2 + 2 * «ω» + δ + 5 * ε ≤ 2 := by linarith only [hω, hδ, hε]
    nlinarith only [hnr, hrq, hcl, Real.log_nonneg hN,
      mul_nonneg (sub_nonneg.mpr hexp) (Real.log_nonneg hx)]
  have hHx : H ≤ x ^ (12 : ℕ) := by
    have he : 4 * «ω» + δ + 7 * ε ≤ 1 := by linarith only [hω, hδ, hε]
    have hp : x ^ (4 * «ω» + δ + 7 * ε) ≤ x := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx he
    calc
      H ≤ C ^ 4 * x ^ (4 * «ω» + δ + 7 * ε) :=
        hHbound.trans (div_le_self (by positivity) hq₀)
      _ ≤ x ^ (4 : ℕ) * x := by gcongr
      _ = x ^ (5 : ℕ) := by ring
      _ ≤ x ^ (12 : ℕ) := pow_le_pow_right₀ hx (by omega)
  have hUx : U ≤ x ^ (5 : ℕ) := by
    calc
      U ≤ U * H := le_mul_of_one_le_right hU.le hH
      _ ≤ C * Q := hUH
      _ ≤ x * x ^ (4 : ℕ) := mul_le_mul hCx hQx hQ.le hx0.le
      _ = _ := by ring
  have hVx : V ≤ x ^ (14 : ℕ) := by
    have he : δ + 5 * ε ≤ 1 := by linarith only [hδ, hε]
    have hp : x ^ (δ + 5 * ε) ≤ x := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx he
    calc
      V ≤ C * x ^ (δ + 5 * ε) * H := hVC
      _ ≤ x * x * x ^ (12 : ℕ) := by gcongr
      _ = _ := by ring
  exact ⟨hMx, hRx, hQx, hHx, hUx, hVx⟩

#print axioms sourceIncidence_divisor_target_resources
#print axioms sourceIncidence_coarse_heights

end PrimeGap182Audit
