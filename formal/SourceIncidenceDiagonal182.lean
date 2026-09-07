import SourceIncidenceResources182

/-! Reproved reductions for the new incidence band. These statements
retain the actual coefficient families, finite Fourier opening, and
uniform logarithmic error. The only new analytic input is the explicit
secondary incidence estimate. Adapted from the Apache-2.0 source at the
pinned hash recorded by the generator. -/

noncomputable section
open scoped BigOperators Topology ContDiff
open Filter Asymptotics PrimeGap186
namespace PrimeGap182Audit
set_option maxHeartbeats 2000000

open Classical in
theorem mixedCorrelation_diagonal_incidence_scale_uniform
    (d : ℕ) («ω» δ ε K T Bβ L Eβ Eψ A : ℝ)
    (hω : 0 < «ω») (_hδ : 0 < δ) (hε : 0 < ε)
    (hK : 1 ≤ K) (hT : 0 < T) (hBβ : 0 ≤ Bβ) (hL : 0 ≤ L)
    (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in Filter.atTop,
      ∀ (γ M Q R : ℝ) (N : ℕ),
        4 * «ω» + δ + 10 * ε ≤ γ →
        γ ≤ 1 / 2 →
        0 < M → 0 < Q → 0 < R →
        x / K ≤ M * x ^ γ → M * x ^ γ ≤ K * x →
        x ^ (-δ - 4 * ε) * x ^ γ / K ≤ R →
        R ≤ K * x ^ (-2 * ε) * x ^ γ →
        R * Q ≤ K * x ^ (1 / 2 + 2 * «ω» + ε) →
        (N : ℝ) ≤ K * x ^ γ →
        ∀ (S : Finset (ℕ × ℕ)) (β : ℕ →₀ ℂ) (c : ℕ × ℕ → ℂ),
          β.support ⊆ Finset.Icc 1 N →
          (∀ n ∈ β.support,
            ‖β n‖ ≤ Bβ * (n.divisors.card : ℝ) ^ d * (Real.log x) ^ Eβ) →
          (∀ p ∈ S, ‖c p‖ ≤ 1) →
          (∀ p ∈ S, 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
            Q ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * Q ∧
            R ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * R) →
          ∀ (a b₁ b₂ : ℕ) (ψ : ℝ → ℝ),
            (∀ t : ℝ, |ψ t| ≤ L * (Real.log x) ^ Eψ) →
            let sm : Finset ℕ := Finset.Icc 1 ⌊T * M⌋₊
            let w : ℕ → ℝ := fun n => ψ ((n : ℝ) / M)
            (∑ r ∈ S.image Prod.snd,
              ∑ p₁ ∈ S.filter (fun p => p.2 = r),
                ∑ p₂ ∈ S.filter (fun p => p.2 = r),
                  ‖c p₁ * star (c p₂) *
                    (∑ n ∈ β.support, β n * star (β n) *
                      (mixedFiberMass sm w p₁.1 p₂.1 r a b₁ b₂ n n : ℂ))‖) ≤
              M * (x ^ γ) ^ 2 / R * (Real.log x) ^ (-A) := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  obtain ⟨C, hC, hfinite⟩ := mixedFiberMass_diagonal_family_subpower_majorant d ε hε
  let F : ℝ := T * K ^ 2
  let H : ℝ := 24 * F + 8 * K ^ 3
  let D : ℝ := C * Bβ ^ 2 * L * F ^ ε * H
  let E : ℝ := 2 * Eβ + Eψ + 4
  have hF : 0 < F := by dsimp [F]; positivity
  have hsmall : ∀ᶠ x : ℝ in Filter.atTop,
      ‖D * K ^ 2 * (Real.log x) ^ (E + A)‖ ≤ ‖x ^ ε‖ :=
    ((isLittleO_log_rpow_rpow_atTop (E + A) hε).const_mul_left
      (D * K ^ 2)).eventuallyLE
  have hlarge : ∀ᶠ x : ℝ in Filter.atTop, 2 * K ^ 2 ≤ x ^ ((1 : ℝ) / 2) :=
    (tendsto_rpow_atTop one_half_pos).eventually_ge_atTop _
  filter_upwards [hsmall, hlarge, Filter.eventually_ge_atTop (Real.exp 1)]
    with x hxsmall hxlarge hx
  intro γ M Q R N hγlower hγupper hM hQ hR hMNlower hMNupper hRlower hRupper hRQ hN
    S β c hsupport hβ hc hS a b₁ b₂ ψ hψ sm w
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hxone : 1 ≤ x := (Real.one_le_exp zero_le_one).trans hx
  have hlogone : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hx
  have hlog : 0 ≤ Real.log x := zero_le_one.trans hlogone
  have hlogpos : 0 < Real.log x := zero_lt_one.trans_le hlogone
  have hdecay : 0 ≤ (Real.log x) ^ (-A) := by
    rw [Real.rpow_neg hlog]
    exact inv_nonneg.mpr (zero_le_one.trans (Real.one_le_rpow hlogone hA))
  have hxγ : 0 < x ^ γ := Real.rpow_pos_of_pos hxpos γ
  let U : ℕ := ⌊2 * Q⌋₊
  let V : ℕ := ⌊2 * R⌋₊
  let X : ℕ := ⌊T * M⌋₊ * N
  have hUcap : (U : ℝ) ≤ 2 * Q := Nat.floor_le (by positivity)
  have hVcap : (V : ℝ) ≤ 2 * R := Nat.floor_le (by positivity)
  have hX : (X : ℝ) ≤ F * x := by
    calc
      _ = (⌊T * M⌋₊ : ℝ) * (N : ℝ) := Nat.cast_mul _ _
      _ ≤ (T * M) * (K * x ^ γ) :=
        mul_le_mul (Nat.floor_le (by positivity)) hN
          (Nat.cast_nonneg N) (mul_nonneg hT.le hM.le)
      _ = T * K * (M * x ^ γ) := by ring
      _ ≤ T * K * (K * x) :=
        mul_le_mul_of_nonneg_left hMNupper (mul_nonneg hT.le hKpos.le)
      _ = F * x := by dsimp [F]; ring
  have hQbound : Q ≤ K ^ 2 * x ^ (1 / 2 + 2 * «ω» + δ + 5 * ε - γ) := by
    calc
      _ ≤ (K * x ^ (1 / 2 + 2 * «ω» + ε)) /
          (x ^ (-δ - 4 * ε) * x ^ γ / K) := by
        apply (le_div_iff₀ (by positivity)).mpr
        simpa only [mul_comm] using
          (mul_le_mul_of_nonneg_right hRlower hQ.le).trans hRQ
      _ = K ^ 2 *
          (x ^ (1 / 2 + 2 * «ω» + ε) / (x ^ (-δ - 4 * ε) * x ^ γ)) := by
        rw [div_div_eq_mul_div]
        ring
      _ = K ^ 2 * x ^ (1 / 2 + 2 * «ω» + δ + 5 * ε - γ) := by
        rw [← Real.rpow_add hxpos, ← Real.rpow_sub hxpos]
        congr 2
        ring
  have hQhalf : Q ≤ K ^ 2 * x ^ ((1 : ℝ) / 2) :=
    hQbound.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hxone (by linarith)) (sq_nonneg K))
  have hRhalf : R ≤ K ^ 2 * x ^ ((1 : ℝ) / 2) := by
    calc
      _ ≤ K * x ^ (-2 * ε) * x ^ γ := hRupper
      _ = K * x ^ (γ - 2 * ε) := by
        rw [mul_assoc, ← Real.rpow_add hxpos]
        congr 2
        ring
      _ ≤ K * x ^ ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hxone (by linarith)) hKpos.le
      _ ≤ K ^ 2 * x ^ ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right (le_self_pow₀ hK two_ne_zero)
          (Real.rpow_nonneg hxpos.le _)
  have hcap (u : ℝ) (hu : u ≤ K ^ 2 * x ^ ((1 : ℝ) / 2)) : 2 * u ≤ x := by
    calc
      _ ≤ 2 * (K ^ 2 * x ^ ((1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hu zero_le_two
      _ = (2 * K ^ 2) * x ^ ((1 : ℝ) / 2) := by ring
      _ ≤ x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hxlarge (Real.rpow_nonneg hxpos.le _)
      _ = x := by rw [← Real.rpow_add hxpos]; norm_num
  have hU : (U : ℝ) ≤ x := hUcap.trans (hcap Q hQhalf)
  have hV : (V : ℝ) ≤ x := hVcap.trans (hcap R hRhalf)
  have hlogcap (n : ℕ) (hn : (n : ℝ) ≤ x) : Real.log (n : ℝ) ≤ Real.log x := by
    by_cases hn0 : n = 0
    · simpa only [hn0, Nat.cast_zero, Real.log_zero] using hlog
    · exact Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)) hn
  have hu : 1 + Real.log (U : ℝ) ≤ 2 * Real.log x := by
    linarith [hlogcap U hU]
  have hv : 1 + Real.log (V : ℝ) ≤ 2 * Real.log x := by
    linarith [hlogcap V hV]
  have hu₃ : 2 + Real.log (U : ℝ) ≤ 3 * Real.log x := by
    linarith [hlogcap U hU]
  have hlogs :
      (1 + Real.log (V : ℝ)) * (1 + Real.log (U : ℝ)) ^ 2 *
        (2 + Real.log (U : ℝ)) ≤ 24 * (Real.log x) ^ 4 := by
    calc
      _ ≤ (2 * Real.log x) * (2 * Real.log x) ^ 2 * (3 * Real.log x) :=
        mul_le_mul
          (mul_le_mul hv (pow_le_pow_left₀ (by positivity) hu 2)
            (sq_nonneg _) (by positivity))
          hu₃ (by positivity) (by positivity)
      _ = _ := by ring
  have hendpoint : (V : ℝ) * (U : ℝ) ^ 2 ≤ 8 * K ^ 3 * x := by
    calc
      _ ≤ (2 * R) * (2 * Q) ^ 2 :=
        mul_le_mul hVcap (pow_le_pow_left₀ (Nat.cast_nonneg U) hUcap 2)
          (sq_nonneg _) (by positivity)
      _ = 8 * (R * Q) * Q := by ring
      _ ≤ 8 * (K * x ^ (1 / 2 + 2 * «ω» + ε)) *
          (K ^ 2 * x ^ (1 / 2 + 2 * «ω» + δ + 5 * ε - γ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hRQ (by norm_num)) hQbound
          hQ.le (by positivity)
      _ = 8 * K ^ 3 *
          (x ^ (1 / 2 + 2 * «ω» + ε) * x ^ (1 / 2 + 2 * «ω» + δ + 5 * ε - γ)) := by
        ring
      _ = 8 * K ^ 3 * x ^ (1 + 4 * «ω» + δ + 6 * ε - γ) := by
        rw [← Real.rpow_add hxpos]
        congr 2
        ring
      _ ≤ 8 * K ^ 3 * x := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hxone
            (show 1 + 4 * «ω» + δ + 6 * ε - γ ≤ 1 by linarith)
  have hcount :
      (X : ℝ) * (1 + Real.log (V : ℝ)) * (1 + Real.log (U : ℝ)) ^ 2 *
        (2 + Real.log (U : ℝ)) + (V : ℝ) * (U : ℝ) ^ 2 ≤
          H * x * (Real.log x) ^ 4 := by
    calc
      _ = (X : ℝ) * ((1 + Real.log (V : ℝ)) * (1 + Real.log (U : ℝ)) ^ 2 *
          (2 + Real.log (U : ℝ))) + (V : ℝ) * (U : ℝ) ^ 2 := by ring
      _ ≤ (F * x) * (24 * (Real.log x) ^ 4) + 8 * K ^ 3 * x :=
        add_le_add (mul_le_mul hX hlogs (by positivity) (by positivity)) hendpoint
      _ ≤ (F * x) * (24 * (Real.log x) ^ 4) +
          (8 * K ^ 3 * x) * (Real.log x) ^ 4 :=
        add_le_add le_rfl (le_mul_of_one_le_right (by positivity : 0 ≤ 8 * K ^ 3 * x)
          (one_le_pow₀ hlogone))
      _ = H * x * (Real.log x) ^ 4 := by dsimp [H]; ring
  have hXp : (X : ℝ) ^ ε ≤ F ^ ε * x ^ ε :=
    (Real.rpow_le_rpow (Nat.cast_nonneg X) hX hε.le).trans_eq
      (Real.mul_rpow hF.le hxpos.le)
  have hscale :
      x ^ (1 + 2 * ε) / K ^ 2 ≤ M * (x ^ γ) ^ 2 / R := by
    calc
      _ = (x / K * x ^ γ) / (K * x ^ (-2 * ε) * x ^ γ) := by
        calc
          _ = (1 / K ^ 2) * (x ^ ((1 : ℝ) - (-2 * ε))) := by
            rw [neg_mul, sub_neg_eq_add]
            ring
          _ = (x / K) / (K * x ^ (-2 * ε)) := by
            rw [Real.rpow_sub hxpos, Real.rpow_one]
            ring
          _ = _ := (mul_div_mul_right _ _ hxγ.ne').symm
      _ ≤ (M * x ^ γ * x ^ γ) / R :=
        div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_right hMNlower hxγ.le) hR hRupper
      _ = _ := by ring
  have hfinite' := hfinite S sm w β c ⌊T * M⌋₊ N U V
    (Bβ * (Real.log x) ^ Eβ) (L * (Real.log x) ^ Eψ)
    (by positivity) (by positivity) Finset.Subset.rfl hsupport
    (fun n hn => by simpa only [mul_right_comm] using hβ n hn)
    (fun n _ => hψ ((n : ℝ) / M)) hc
    (fun p hp => by
      rcases hS p hp with ⟨hp₁, hp₂, _, _, hpQ, _, hpR⟩
      exact ⟨hp₁, Nat.le_floor hpQ, hp₂, Nat.le_floor hpR⟩)
    (fun p hp => (hS p hp).2.2.1) a b₁ b₂
  have hlogpower :
      ((Real.log x) ^ Eβ) ^ 2 * (Real.log x) ^ Eψ * (Real.log x) ^ 4 =
        (Real.log x) ^ E := by
    rw [← Real.rpow_mul_natCast hlog, ← Real.rpow_natCast,
      ← Real.rpow_add hlogpos, ← Real.rpow_add hlogpos]
    congr 1
    norm_num [E, mul_comm]
  have henvelope :
      C * (Bβ * (Real.log x) ^ Eβ) ^ 2 * (L * (Real.log x) ^ Eψ) *
        (X : ℝ) ^ ε *
        ((X : ℝ) * (1 + Real.log (V : ℝ)) * (1 + Real.log (U : ℝ)) ^ 2 *
          (2 + Real.log (U : ℝ)) + (V : ℝ) * (U : ℝ) ^ 2) ≤
        D * x ^ (1 + ε) * (Real.log x) ^ E := by
    calc
      _ ≤ C * (Bβ * (Real.log x) ^ Eβ) ^ 2 * (L * (Real.log x) ^ Eψ) *
          (F ^ ε * x ^ ε) * (H * x * (Real.log x) ^ 4) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hXp (by positivity)) hcount
          (by positivity) (by positivity)
      _ = (C * Bβ ^ 2 * L * F ^ ε * H) * (x * x ^ ε) *
          (((Real.log x) ^ Eβ) ^ 2 * (Real.log x) ^ Eψ * (Real.log x) ^ 4) := by
        ring
      _ = D * x ^ (1 + ε) * (Real.log x) ^ E := by
        rw [hlogpower, Real.rpow_add hxpos, Real.rpow_one]
  have hsmall' : D * K ^ 2 * (Real.log x) ^ (E + A) ≤ x ^ ε :=
    (Real.le_norm_self _).trans
      (hxsmall.trans_eq (Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le ε)))
  have hlogcancel : (Real.log x) ^ (E + A) * (Real.log x) ^ (-A) =
      (Real.log x) ^ E := by
    rw [← Real.rpow_add hlogpos, add_neg_cancel_right]
  have hscalar : D * (Real.log x) ^ E ≤
      (x ^ ε / K ^ 2) * (Real.log x) ^ (-A) := by
    calc
      _ = (D * K ^ 2 * (Real.log x) ^ (E + A)) / K ^ 2 *
          (Real.log x) ^ (-A) := by
        rw [mul_right_comm D (K ^ 2), mul_div_cancel_right₀ _ (pow_ne_zero 2 hKpos.ne'),
          mul_assoc D ((Real.log x) ^ (E + A)), hlogcancel]
      _ ≤ _ :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hsmall' (sq_nonneg K))
          hdecay
  calc
    _ ≤ C * (Bβ * (Real.log x) ^ Eβ) ^ 2 * (L * (Real.log x) ^ Eψ) *
        (X : ℝ) ^ ε *
        ((X : ℝ) * (1 + Real.log (V : ℝ)) * (1 + Real.log (U : ℝ)) ^ 2 *
          (2 + Real.log (U : ℝ)) + (V : ℝ) * (U : ℝ) ^ 2) := hfinite'
    _ ≤ D * x ^ (1 + ε) * (Real.log x) ^ E := henvelope
    _ = x ^ (1 + ε) * (D * (Real.log x) ^ E) := by ring
    _ ≤ x ^ (1 + ε) * ((x ^ ε / K ^ 2) * (Real.log x) ^ (-A)) :=
      mul_le_mul_of_nonneg_left hscalar (Real.rpow_nonneg hxpos.le _)
    _ = (x ^ (1 + 2 * ε) / K ^ 2) * (Real.log x) ^ (-A) := by
      calc
        _ = (x ^ (1 + ε) * x ^ ε) / K ^ 2 * (Real.log x) ^ (-A) := by ring
        _ = _ := by
          rw [← Real.rpow_add hxpos, two_mul, add_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale hdecay

#print axioms mixedCorrelation_diagonal_incidence_scale_uniform
end PrimeGap182Audit
