import SourceIncidenceResources182

/-! Elementary source reductions with the new exponent band. These
statements use actual coefficient sums and scale relations; no analytic
estimate is postulated. Adapted from Apache-2.0 PrimeGaps186 at the
source hash recorded by the generator. -/

noncomputable section
open scoped BigOperators Topology ContDiff
open Filter Asymptotics PrimeGap186

namespace PrimeGap182Audit

open Classical in
theorem opening_incidence_selector_target_lower (C x «ω» ε γhi M N R Q H γ : ℝ) (g : ℕ)
    (hC : 1 ≤ C) (hx : 1 ≤ x) (hM : 0 < M) (hN : 0 < N)
    (hR : 0 < R) (hQ : 0 < Q) (hg : 0 < g)
    (hMN : x / C ≤ M * N) (hNγ : N = x ^ γ)
    (hγ : γ ≤ γhi)
    (hRQ : R * Q ≤ C * x ^ (1 / 2 + 2 * «ω» + ε))
    (hH : H = x ^ ε * R * Q ^ 2 / ((g : ℝ) * M)) :
    (g : ℝ) / C ^ 2 * x ^ (1 / 2 - 2 * «ω» - γhi - 7 * ε) ≤
      x ^ (-5 * ε) * Q / H := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hgpos : 0 < (g : ℝ) := by exact_mod_cast hg
  have hp (a : ℝ) : 0 < x ^ a := Real.rpow_pos_of_pos hxpos a
  let X : ℝ := x ^ (-5 * ε) * Q / H
  let k : ℝ := 1 / 2 - 2 * «ω» - γhi - 7 * ε
  let t : ℝ := γhi
  let s : ℝ := 1 / 2 + 2 * «ω» + 7 * ε
  have hHpos : 0 < H := by rw [hH]; positivity
  have hXpos : 0 < X := by dsimp only [X]; positivity
  have hNupper : N ≤ x ^ t := by
    rw [hNγ]
    exact Real.rpow_le_rpow_of_exponent_le hx hγ
  have hXidentity : X * (R * Q) * x ^ (6 * ε) = (g : ℝ) * M := by
    have hpow6 : x ^ (6 * ε) = x ^ (5 * ε) * x ^ ε := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring
    dsimp only [X]
    rw [hH, show -5 * ε = -(5 * ε) by ring,
      Real.rpow_neg hxpos.le, hpow6]
    field_simp [hM.ne', hR.ne', hQ.ne', hgpos.ne', (hp ε).ne', (hp (5 * ε)).ne']
  have hDen : (R * Q) * x ^ (6 * ε) ≤ C * x ^ s := by
    calc
      (R * Q) * x ^ (6 * ε) ≤
          (C * x ^ (1 / 2 + 2 * «ω» + ε)) * x ^ (6 * ε) :=
        mul_le_mul_of_nonneg_right hRQ (hp (6 * ε)).le
      _ = C * x ^ s := by
        rw [mul_assoc, ← Real.rpow_add hxpos]
        congr 2
        dsimp only [s]
        ring
  have hMain : (g : ℝ) * x ≤ C ^ 2 * X * x ^ t * x ^ s := by
    calc
      (g : ℝ) * x ≤ (g : ℝ) * (C * (M * N)) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [mul_comm] using (div_le_iff₀ hCpos).1 hMN) hgpos.le
      _ = C * X * ((R * Q) * x ^ (6 * ε)) * N := by
        rw [show C * X * ((R * Q) * x ^ (6 * ε)) * N =
            C * (X * (R * Q) * x ^ (6 * ε)) * N by ring,
          hXidentity]
        ring
      _ ≤ C * X * (C * x ^ s) * N :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hDen (mul_pos hCpos hXpos).le) hN.le
      _ ≤ C * X * (C * x ^ s) * x ^ t :=
        mul_le_mul_of_nonneg_left hNupper (by positivity)
      _ = C ^ 2 * X * x ^ t * x ^ s := by ring
  have hPowers : x ^ k * (x ^ t * x ^ s) = x := by
    rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
    convert Real.rpow_one x using 1
    dsimp only [k, t, s]
    ring_nf
  have hLower : (g : ℝ) * x ^ k ≤ C ^ 2 * X := by
    refine le_of_mul_le_mul_right ?_ (mul_pos (hp t) (hp s))
    calc
      ((g : ℝ) * x ^ k) * (x ^ t * x ^ s) = (g : ℝ) * x := by
        rw [mul_assoc, hPowers]
      _ ≤ C ^ 2 * X * x ^ t * x ^ s := hMain
      _ = (C ^ 2 * X) * (x ^ t * x ^ s) := by ring
  have hdiv : ((g : ℝ) * x ^ k) / C ^ 2 ≤ X :=
    (div_le_iff₀ (pow_pos hCpos 2)).2 (by simpa only [mul_comm] using hLower)
  simpa only [X, k, div_mul_eq_mul_div] using hdiv

open Classical in
theorem opening_incidence_scale_resources (C «ω» δ ε γlo γhi : ℝ)
    (hC : 1 ≤ C) (hω : 0 < «ω») (hδ : 0 < δ) (hε : 0 < ε)
    (hεsmall : ε < 1 / 1000)
    (hγmin : 1 / 4 + 4 * «ω» + δ + 100 * ε ≤ γlo)
    (hγmax : γhi ≤ 1 / 2 - 2 * «ω» - 50 * ε) :
    ∀ᶠ x : ℝ in Filter.atTop,
      Real.exp 1 ≤ x ∧ 2 ≤ x ∧ C ^ 2 ≤ x ^ (1 / 2 - 2 * «ω» - γhi - 7 * ε) ∧
      ∀ M N R Q γ : ℝ,
        0 < M → 0 < N → 0 < R → 0 < Q →
        x / C ≤ M * N → M * N ≤ C * x → N = x ^ γ →
        γlo ≤ γ →
        γ ≤ γhi →
        N ≤ C * x ^ (δ + 4 * ε) * R →
        R ≤ C * x ^ (-2 * ε) * N →
        R * Q ≤ C * x ^ (1 / 2 + 2 * «ω» + ε) →
        1 ≤ N ∧ N ≤ x ∧ 1 ≤ M ∧ M ≤ x ^ 2 ∧ R ≤ x ∧ Q ≤ x ∧
          4 * x ^ ε < M := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hεhalf : ε < 1 / 2 := by linarith only [hεsmall]
  have hmargin : 0 < 1 / 2 - 2 * «ω» - γhi - 7 * ε := by
    linarith only [hγmax, hε]
  have hCmargin : ∀ᶠ x : ℝ in Filter.atTop,
      C ^ 2 ≤ x ^ (1 / 2 - 2 * «ω» - γhi - 7 * ε) :=
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
  have hγlower : 1 / 4 + 4 * «ω» + δ + 100 * ε ≤ γ := hγmin.trans hγlo
  have hγnonneg : 0 ≤ γ := by linarith only [hγlower, hω, hδ, hε]
  have hγhalf : γ ≤ 1 / 2 := by linarith only [hγhi, hγmax, hω, hε]
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

#print axioms opening_incidence_selector_target_lower
#print axioms opening_incidence_scale_resources
end PrimeGap182Audit
