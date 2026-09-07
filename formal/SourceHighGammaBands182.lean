import SourceHighGammaBounds182

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

open Classical in
theorem sourceTheta_near_typeII_uniform_power_saving
    («ω» δ ε C T TN A₀ A₁ L : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ) (hε : 0 < ε)
    (hworking : 68 * «ω» + 20 * δ < 1)
    (hsmall : ε < δ / 10 ^ 100)
    (hC : 1 ≤ C) (hT : 1 ≤ T) (hTN : 1 ≤ TN)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hL : 0 ≤ L) :
    ∃ K X : ℝ, 0 < K ∧ 1 ≤ X ∧
      ∀ x : ℝ, X ≤ x →
      ∀ M N R Q H γ : ℝ,
        0 < M → 0 < N → 0 < R → 0 < Q →
        x / C ≤ M * N → N = x ^ γ →
        N ≤ C * x ^ (δ + 4 * ε) * R →
        R ≤ C * x ^ (-2 * ε) * N →
        R * Q ≤ C * x ^ (1 / 2 + 2 * «ω» + ε) →
        1 / 2 - 2 * «ω» - δ / 2 ≤ γ → γ ≤ 1 / 2 →
      ∀ r q₀ a b₁ b₂ : ℕ,
        R ≤ (r : ℝ) → (r : ℝ) ≤ 2 * R →
        H = x ^ ε * R * Q ^ 2 / ((q₀ : ℝ) * M) → 1 ≤ H →
      ∀ (F : Finset (ℕ × ℕ)) (J : Finset ℤ),
        (∀ q ∈ F,
          Squarefree (r * q₀ * q.1 * q.2) ∧
          Q ≤ (q₀ * q.1 : ℕ) ∧ (q₀ * q.1 : ℕ) ≤ 2 * Q ∧
          Q ≤ (q₀ * q.2 : ℕ) ∧ (q₀ * q.2 : ℕ) ≤ 2 * Q) →
        (∀ h ∈ J, h ≠ 0 ∧ |(h : ℝ)| ≤ 2 * H) →
        Nat.Coprime a r → Nat.Coprime b₁ q₀ →
      ∀ (ℓ : ℤ) (t₀ : ℝ) (ψ : ℝ → ℝ),
        ContDiff ℝ 1 ψ → Function.support ψ ⊆ Set.Icc (-T) T →
        (∀ t : ℝ, 0 ≤ ψ t) →
        (∀ t : ℝ, |ψ t| ≤ A₀ ∧ |deriv ψ t| ≤ A₁) →
      ∀ (β : ℕ →₀ ℂ), β.support ⊆ Finset.Icc 1 ⌊TN * N⌋₊ →
        (∀ n ∈ β.support, ‖β n‖ ≤ x ^ (ε / 100)) →
        (∀ n ∈ β.support, 1 ≤ ψ (((n : ℝ) - t₀) / N)) →
      ∀ (c : (ℕ × ℕ) → ℤ → ℂ),
        (∀ q ∈ F, ∀ h ∈ J, ‖c q h‖ ≤ L) →
      let βℤ : ℤ →₀ ℂ := Finsupp.embDomain (Nat.castEmbedding : ℕ ↪ ℤ) β
      (∑ q ∈ F, ‖∑ n ∈ βℤ.support,
        βℤ n * star (βℤ (n + ℓ * (r : ℤ))) *
          (sourceCompatibility r q₀ b₁ b₂ ℓ n : ℂ) *
          ∑ h ∈ J, c q h * sourceTheta r q₀ 1 q.1 q.2 a b₁ b₂ ℓ n h‖) ≤
        K * Q ^ 2 * N * (Int.gcd (q₀ : ℤ) ℓ : ℝ) / (q₀ : ℝ) ^ 2 *
          x ^ (-ε / 4) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hTNpos : 0 < TN := zero_lt_one.trans_le hTN
  have hεsmall : ε ≤ 1 / 100 := by
    have hp : (1000 : ℝ) ≤ 10 ^ 100 := by norm_num
    have hs := (lt_div_iff₀ (by positivity : (0 : ℝ) < 10 ^ 100)).mp hsmall
    nlinarith only [hp, hs, hworking, hω, hε, hδ]
  have hδsmall : δ + 4 * ε ≤ 1 / 12 := by
    have hp : (1000 : ℝ) ≤ 10 ^ 100 := by norm_num
    have hs := (lt_div_iff₀ (by positivity : (0 : ℝ) < 10 ^ 100)).mp hsmall
    nlinarith only [hp, hs, hworking, hω, hε, hδ]
  have hRQexponent : 1 / 2 + 2 * «ω» + ε ≤ 7 / 12 := by
    linarith only [hworking, hδ, hεsmall]
  obtain ⟨C₀, hC₀, hphase⟩ := sourceTheta_pair_finite_cauchy_bounds
    T A₀ A₁ 3 (ε / 1000) hT hA₀ hA₁ (by positivity)
  obtain ⟨Xg, hXg, hgcd⟩ := sourceSignedProduct_pair_gcd_sum_uniform
    10 (ε / 100) (by norm_num) (by positivity)
  obtain ⟨Xc, hXc⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).eventually_ge_atTop (100 * C))
  let K := Real.sqrt (2600 * C₀ * (1 + TN) * L ^ 2 * C ^ 12 + 1)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, max 1 (max Xg Xc), hK, le_max_left _ _, ?_⟩
  intro x hx M N R Q H γ hM hN hR hQ hMN hNγ hNR hRN hRQ hγlo hγhi
    r q₀ a b₁ b₂ hRr hrR hH hHone F J hF hJ ha hb₁ ℓ t₀ ψ hψ hψs hψ0 hψb
    β hβs hβ hψmajor c hc βℤ
  have hxone : 1 ≤ x := (le_max_left _ _).trans hx
  have hxpos : 0 < x := zero_lt_one.trans_le hxone
  have hxg : Xg ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxc : Xc ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hxlarge : 100 * C ≤ x ^ (1 / 100 : ℝ) := hXc x hxc
  by_cases hFempty : F = ∅
  · simp only [hFempty, Finset.sum_empty]
    positivity
  have hγlower : 5 / 12 ≤ γ := by linarith only [hγlo, hworking, hω, hδ]
  let P : (ℕ × ℕ) → (ℕ × ℕ) → ℕ := fun t s =>
    Nat.lcm (r * q₀ * t.1 * t.2) (r * q₀ * s.1 * s.2)
  let HN : ℕ := ⌊2 * H⌋₊
  let KN : ℕ := ⌊4 * Q ^ 2 / (q₀ : ℝ) ^ 2⌋₊
  obtain ⟨hq₀, hq₀N, hrx, hPbounds, hJcard, hFcard, hHK, hHKx, hJnat, hFnat⟩ :=
    sourceHighGamma_near_geometry «ω» δ ε C x M N R Q H γ r q₀ F J
      hC hxone hxlarge hε hεsmall hδsmall hRQexponent hM hN hR hQ
      hMN hNγ hNR hRN hRQ hγlower hγhi hRr hrR hH hHone
      (Finset.nonempty_iff_ne_empty.mpr hFempty) hF hJ
  have hq₀R : 0 < (q₀ : ℝ) := by exact_mod_cast hq₀
  have hq₀one : 1 ≤ (q₀ : ℝ) := by exact_mod_cast hq₀
  have hrpos : 0 < (r : ℝ) := hR.trans_le hRr
  have hrnat : 0 < r := by exact_mod_cast hrpos
  have hHpos : 0 < H := zero_lt_one.trans_le hHone
  have hPscale (t : ℕ × ℕ) (ht : t ∈ F) (s : ℕ × ℕ) (hs : s ∈ F) :
      N ≤ (P t s : ℝ) ^ (3 : ℝ) ∧ (P t s : ℝ) ≤ x ^ (10 : ℝ) :=
    ⟨(hPbounds t ht s hs).1, (hPbounds t ht s hs).2.1⟩
  have hPsqrt (t : ℕ × ℕ) (ht : t ∈ F) (s : ℕ × ℕ) (hs : s ∈ F) :
      Real.sqrt ((P t s / q₀ : ℕ) : ℝ) ≤ 6 * Real.sqrt R * Q ^ 2 / (q₀ : ℝ) ^ 2 :=
    (hPbounds t ht s hs).2.2
  let D : ℝ := x ^ (ε / 100)
  have hDpos : 0 < D := Real.rpow_pos_of_pos hxpos _
  have hDone : 1 ≤ D := Real.one_le_rpow hxone (by positivity)
  have hPε (t : ℕ × ℕ) (ht : t ∈ F) (s : ℕ × ℕ) (hs : s ∈ F) :
      (P t s : ℝ) ^ (ε / 1000) ≤ D := by
    calc
      _ ≤ (x ^ (10 : ℝ)) ^ (ε / 1000) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (hPscale t ht s hs).2 (by positivity)
      _ = D := by rw [← Real.rpow_mul hxpos.le]; congr 1; ring
  let G : ℝ := ∑ t ∈ F, ∑ s ∈ F, ∑ h ∈ J, ∑ k ∈ J,
    (Int.gcd (r : ℤ) (h * (s.1 : ℤ) * (s.2 : ℤ) -
      k * (t.1 : ℤ) * (t.2 : ℤ)) : ℝ)
  have hG : G ≤ D * (5 * H) * (4 * Q ^ 2 / (q₀ : ℝ) ^ 2) *
      (8 * H * Q ^ 2 / (q₀ : ℝ) ^ 2 + 2 * R) := by
    have hraw := hgcd x hxg r HN KN hrnat hrx hHKx J F hJnat hFnat
    have heq : G = ∑ h ∈ J, ∑ s ∈ F, ∑ k ∈ J, ∑ t ∈ F,
        (Int.gcd (h * (s.1 : ℤ) * (s.2 : ℤ) -
          k * (t.1 : ℤ) * (t.2 : ℤ)) (r : ℤ) : ℝ) := by
      calc
        G = ∑ s ∈ F, ∑ t ∈ F, ∑ h ∈ J, ∑ k ∈ J,
            (Int.gcd (r : ℤ) (h * (s.1 : ℤ) * (s.2 : ℤ) -
              k * (t.1 : ℤ) * (t.2 : ℤ)) : ℝ) := Finset.sum_comm
        _ = ∑ s ∈ F, ∑ h ∈ J, ∑ k ∈ J, ∑ t ∈ F,
            (Int.gcd (r : ℤ) (h * (s.1 : ℤ) * (s.2 : ℤ) -
              k * (t.1 : ℤ) * (t.2 : ℤ)) : ℝ) := by
          apply Finset.sum_congr rfl
          intro s _
          exact Finset.sum_comm_cycle.symm
        _ = ∑ h ∈ J, ∑ s ∈ F, ∑ k ∈ J, ∑ t ∈ F,
            (Int.gcd (r : ℤ) (h * (s.1 : ℤ) * (s.2 : ℤ) -
              k * (t.1 : ℤ) * (t.2 : ℤ)) : ℝ) := Finset.sum_comm
        _ = _ := by simp only [Int.gcd_comm]
    rw [heq]
    apply hraw.trans
    change D * (J.card : ℝ) * (F.card : ℝ) * ((HN : ℝ) * (KN : ℝ) + (r : ℝ)) ≤ _
    gcongr
  let B : ℝ := 6 * Real.sqrt R * Q ^ 2 / (q₀ : ℝ) ^ 2
  let A : ℝ := (N / (q₀ : ℝ) / (r : ℝ))
  let E : ℝ := ∑ t ∈ F, ∑ s ∈ F, ∑ h ∈ J, ∑ k ∈ J,
    (P t s : ℝ) ^ (ε / 1000) *
      (Real.sqrt ((P t s / q₀ : ℕ) : ℝ) +
        (N / (q₀ : ℝ)) *
          ((Int.gcd (r : ℤ) (h * (s.1 : ℤ) * (s.2 : ℤ) -
            k * (t.1 : ℤ) * (t.2 : ℤ)) : ℝ) / (r : ℝ)))
  have hEsum : E ≤ D *
      ((J.card : ℝ) ^ 2 * (F.card : ℝ) ^ 2 * B + A * G) := by
    calc
      E ≤ ∑ t ∈ F, ∑ s ∈ F, ∑ h ∈ J, ∑ k ∈ J,
          D * (B + A * (Int.gcd (r : ℤ)
            (h * (s.1 : ℤ) * (s.2 : ℤ) -
              k * (t.1 : ℤ) * (t.2 : ℤ)) : ℝ)) := by
        apply Finset.sum_le_sum
        intro t ht
        apply Finset.sum_le_sum
        intro s hs
        apply Finset.sum_le_sum
        intro h _
        apply Finset.sum_le_sum
        intro k _
        apply mul_le_mul (hPε t ht s hs) ?_ (by positivity) hDpos.le
        have hh := hPsqrt t ht s hs
        simpa only [A, B, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, add_comm] using
          add_le_add_right hh ((N / (q₀ : ℝ)) *
            ((Int.gcd (r : ℤ) (h * (s.1 : ℤ) * (s.2 : ℤ) -
              k * (t.1 : ℤ) * (t.2 : ℤ)) : ℝ) / (r : ℝ)))
      _ = _ := sourceHighGamma_four_sum_affine F J D B A
        (fun t s h k => (Int.gcd (r : ℤ)
          (h * (s.1 : ℤ) * (s.2 : ℤ) - k * (t.1 : ℤ) * (t.2 : ℤ)) : ℝ))
  have hEbound : E ≤ D ^ 2 *
      ((5 * H) ^ 2 * (4 * Q ^ 2 / (q₀ : ℝ) ^ 2) ^ 2 * B +
        A * (5 * H) * (4 * Q ^ 2 / (q₀ : ℝ) ^ 2) *
          (8 * H * Q ^ 2 / (q₀ : ℝ) ^ 2 + 2 * R)) := by
    apply hEsum.trans
    have hB0 : 0 ≤ B := by dsimp only [B]; positivity
    have hA0 : 0 ≤ A := by dsimp only [A]; positivity
    have hcards : (J.card : ℝ) ^ 2 * (F.card : ℝ) ^ 2 * B ≤
        (5 * H) ^ 2 * (4 * Q ^ 2 / (q₀ : ℝ) ^ 2) ^ 2 * B :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hJcard 2)
          (pow_le_pow_left₀ (Nat.cast_nonneg _) hFcard 2) (sq_nonneg _) (sq_nonneg _)) hB0
    calc
      D * ((J.card : ℝ) ^ 2 * (F.card : ℝ) ^ 2 * B + A * G) ≤
          D * ((5 * H) ^ 2 * (4 * Q ^ 2 / (q₀ : ℝ) ^ 2) ^ 2 * B +
            A * (D * (5 * H) * (4 * Q ^ 2 / (q₀ : ℝ) ^ 2) *
              (8 * H * Q ^ 2 / (q₀ : ℝ) ^ 2 + 2 * R))) :=
        mul_le_mul_of_nonneg_left
          (add_le_add hcards (mul_le_mul_of_nonneg_left hG hA0)) hDpos.le
      _ ≤ D * (D *
          ((5 * H) ^ 2 * (4 * Q ^ 2 / (q₀ : ℝ) ^ 2) ^ 2 * B +
            A * (5 * H) * (4 * Q ^ 2 / (q₀ : ℝ) ^ 2) *
              (8 * H * Q ^ 2 / (q₀ : ℝ) ^ 2 + 2 * R))) := by
        have hh : (5 * H) ^ 2 * (4 * Q ^ 2 / (q₀ : ℝ) ^ 2) ^ 2 * B ≤
            D * ((5 * H) ^ 2 * (4 * Q ^ 2 / (q₀ : ℝ) ^ 2) ^ 2 * B) :=
          le_mul_of_one_le_left (by positivity) hDone
        nlinarith only [mul_le_mul_of_nonneg_left hh hDpos.le]
      _ = _ := by ring
  let U : ℝ := ∑ t ∈ F, ‖∑ n ∈ βℤ.support,
    βℤ n * star (βℤ (n + ℓ * (r : ℤ))) *
      (sourceCompatibility r q₀ b₁ b₂ ℓ n : ℂ) *
      ∑ h ∈ J, c t h * sourceTheta r q₀ 1 t.1 t.2 a b₁ b₂ ℓ n h‖
  let g : ℝ := (Int.gcd (q₀ : ℤ) ℓ : ℝ)
  let Z : ℝ := Q ^ 2 * N * g / (q₀ : ℝ) ^ 2
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hg : 0 ≤ g := Nat.cast_nonneg _
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hraw := (hphase r q₀ a b₁ b₂ ⌊TN * N⌋₊ F J
    (fun t ht => (hF t ht).1) ha hb₁ ℓ N t₀ D L hq₀N hDpos.le hL
    (fun t ht s hs => (hPscale t ht s hs).1) ψ hψ hψs hψ0 hψb
    β hβs hβ hψmajor c hc).1
  change U ^ 2 ≤ C₀ * D ^ 4 * g ^ 2 *
    (1 + (⌊TN * N⌋₊ : ℝ) / (q₀ : ℝ)) * L ^ 2 * E at hraw
  have hmass : 1 + (⌊TN * N⌋₊ : ℝ) / (q₀ : ℝ) ≤ (1 + TN) * N / (q₀ : ℝ) := by
    have hf := Nat.floor_le (show 0 ≤ TN * N by positivity)
    calc
      _ ≤ N / (q₀ : ℝ) + (TN * N) / (q₀ : ℝ) :=
        add_le_add ((one_le_div hq₀R).mpr hq₀N)
          (div_le_div_of_nonneg_right hf hq₀R.le)
      _ = _ := by ring
  have hscale := (sourceHighGamma_scale_envelopes «ω» δ ε C x M N R Q H
    (q₀ : ℝ) γ hω hδ hε hworking hsmall hC hxone hM hN hR hQ hq₀one
    hMN hNγ hNR hRN hRQ hH hγhi).1 hγlo
  rw [← Real.sqrt_eq_rpow] at hscale
  have hnormalized := sourceHighGamma_normalized_completion_envelope
    H N R Q (r : ℝ) (q₀ : ℝ) (C ^ 12 * x ^ (-ε)) hHpos.le hN hR hQ hRr hq₀one
      hscale.1 hscale.2.1 hscale.2.2
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hUfinal : U ^ 2 ≤
      (2600 * C₀ * (1 + TN) * L ^ 2 * C ^ 12) * Z ^ 2 * D ^ 6 * x ^ (-ε) := by
    apply hraw.trans
    calc
      C₀ * D ^ 4 * g ^ 2 * (1 + (⌊TN * N⌋₊ : ℝ) / (q₀ : ℝ)) * L ^ 2 * E ≤
          C₀ * D ^ 4 * g ^ 2 * ((1 + TN) * N / (q₀ : ℝ)) * L ^ 2 *
            (D ^ 2 * ((5 * H) ^ 2 * (4 * Q ^ 2 / (q₀ : ℝ) ^ 2) ^ 2 * B +
              A * (5 * H) * (4 * Q ^ 2 / (q₀ : ℝ) ^ 2) *
                (8 * H * Q ^ 2 / (q₀ : ℝ) ^ 2 + 2 * R))) := by
        gcongr
      _ = (C₀ * (1 + TN) * L ^ 2 * g ^ 2 * D ^ 6) *
          ((N / (q₀ : ℝ)) *
            ((5 * H) ^ 2 * (4 * Q ^ 2 / (q₀ : ℝ) ^ 2) ^ 2 * B +
              A * (5 * H) * (4 * Q ^ 2 / (q₀ : ℝ) ^ 2) *
                (8 * H * Q ^ 2 / (q₀ : ℝ) ^ 2 + 2 * R))) := by ring
      _ ≤ (C₀ * (1 + TN) * L ^ 2 * g ^ 2 * D ^ 6) *
          (2600 * (Q ^ 2 * N / (q₀ : ℝ) ^ 2) ^ 2 * (C ^ 12 * x ^ (-ε))) :=
        mul_le_mul_of_nonneg_left hnormalized (by positivity)
      _ = _ := by dsimp only [Z]; ring
  have hpower : D ^ 6 * x ^ (-ε) ≤ x ^ (-ε / 2) := by
    calc
      D ^ 6 * x ^ (-ε) = x ^ (6 * (ε / 100) - ε) := by
        dsimp only [D]
        rw [← Real.rpow_mul_natCast hxpos.le, ← Real.rpow_add hxpos]
        congr 1
        ring
      _ ≤ x ^ (-ε / 2) := Real.rpow_le_rpow_of_exponent_le hxone (by linarith only [hε])
  have hKsq : K ^ 2 = 2600 * C₀ * (1 + TN) * L ^ 2 * C ^ 12 + 1 := by
    exact Real.sq_sqrt (by positivity)
  have hsq : U ^ 2 ≤ (K * Z * x ^ (-ε / 4)) ^ 2 := by
    calc
      U ^ 2 ≤ (2600 * C₀ * (1 + TN) * L ^ 2 * C ^ 12) * Z ^ 2 *
          (D ^ 6 * x ^ (-ε)) := by simpa only [mul_assoc] using hUfinal
      _ ≤ K ^ 2 * Z ^ 2 * x ^ (-ε / 2) := by
        gcongr
        · rw [hKsq]
          linarith
      _ = _ := by
        rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hxpos.le]
        congr 1
        ring_nf
  have hfinal : U ≤ K * Z * x ^ (-ε / 4) :=
    (sq_le_sq₀ hU (by positivity)).mp hsq
  change U ≤ _
  convert hfinal using 1
  dsimp only [Z, g]
  ring

open Classical in
theorem sourceTheta_split_typeI_uniform_power_saving
    («ω» δ ε C T TN A₀ A₁ L : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ) (hε : 0 < ε)
    (hworking : 68 * «ω» + 20 * δ < 1) (hsmall : ε < δ / 10 ^ 100)
    (hC : 1 ≤ C) (hT : 1 ≤ T) (hTN : 1 ≤ TN)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hL : 0 ≤ L) :
    ∃ K X : ℝ, 0 < K ∧ 1 ≤ X ∧
      ∀ x : ℝ, X ≤ x →
      ∀ M N R Q H V γ : ℝ,
        0 < M → 0 < N → 0 < R → 0 < Q → 0 < V →
        x / C ≤ M * N → N = x ^ γ →
        N ≤ C * x ^ (δ + 4 * ε) * R →
        R ≤ C * x ^ (-2 * ε) * N →
        R * Q ≤ C * x ^ (1 / 2 + 2 * «ω» + ε) →
        1 / 4 + 14 * «ω» + 4 * δ + 100 * ε ≤ γ →
        γ ≤ 1 / 2 - 2 * «ω» - δ / 2 →
      ∀ r q₀ u q₂ a b₁ b₂ : ℕ,
        R ≤ (r : ℝ) → (r : ℝ) ≤ 2 * R →
        H = x ^ ε * R * Q ^ 2 / ((q₀ : ℝ) * M) → 1 ≤ H →
        (u : ℝ) * V ≤ C * Q / (q₀ : ℝ) →
        (q₀ : ℝ) * (q₂ : ℝ) ≤ C * Q →
        x ^ (5 * ε) * H / (q₀ : ℝ) ≤ C * V →
        V ≤ C * x ^ (δ + 5 * ε) * H →
      ∀ (F : Finset ℕ) (J : Finset ℤ),
        (∀ v ∈ F, 0 < v ∧ (v : ℝ) ≤ C * V ∧ Squarefree (r * q₀ * (u * v) * q₂)) →
        (∀ h ∈ J, h ≠ 0 ∧ |(h : ℝ)| ≤ 2 * H) →
        Nat.Coprime a r → Nat.Coprime b₁ q₀ →
      ∀ (ℓ : ℤ) (t₀ : ℝ) (Y : Set.Ici (1 : ℝ)), (Y : ℝ) ≤ x ^ δ →
        (∀ v ∈ F,
          Nonempty (DenseDivisibilityWitness
            Y 1 (r * q₀ * (u * v))) ∧
          Nonempty (DenseDivisibilityWitness
            Y 1 (r * q₀ * q₂))) →
      ∀ (ψ : ℝ → ℝ), ContDiff ℝ 1 ψ → Function.support ψ ⊆ Set.Icc (-T) T →
        (∀ t : ℝ, 0 ≤ ψ t) →
        (∀ t : ℝ, |ψ t| ≤ A₀ ∧ |deriv ψ t| ≤ A₁) →
      ∀ (β : ℕ →₀ ℂ), β.support ⊆ Finset.Icc 1 ⌊TN * N⌋₊ →
        (∀ n ∈ β.support, ‖β n‖ ≤ x ^ (ε / 100)) →
        (∀ n ∈ β.support, 1 ≤ ψ (((n : ℝ) - t₀) / N)) →
      ∀ (c : ℕ → ℤ → ℂ), (∀ v ∈ F, ∀ h ∈ J, ‖c v h‖ ≤ L) →
      let βℤ : ℤ →₀ ℂ := Finsupp.embDomain (Nat.castEmbedding : ℕ ↪ ℤ) β
      (∑ v ∈ F, ‖∑ n ∈ βℤ.support,
        βℤ n * star (βℤ (n + ℓ * (r : ℤ))) *
          (sourceCompatibility r q₀ b₁ b₂ ℓ n : ℂ) *
          ∑ h ∈ J, c v h * sourceTheta r q₀ 1 (u * v) q₂ a b₁ b₂ ℓ n h‖) ≤
        K * (Int.gcd (q₀ : ℤ) ℓ : ℝ) * N * V * x ^ (-2 * ε) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hTNpos : 0 < TN := zero_lt_one.trans_le hTN
  have hεδ : 1000 * ε ≤ δ := by
    have hp : (1000 : ℝ) ≤ 10 ^ 100 := by norm_num
    have hs := (lt_div_iff₀ (by positivity : (0 : ℝ) < 10 ^ 100)).mp hsmall
    nlinarith only [hp, hs, hε]
  have hεsmall : ε ≤ 1 / 100 := by linarith only [hεδ, hworking, hω, hδ]
  have hδsmall : δ + 4 * ε ≤ 1 / 12 := by linarith only [hεδ, hworking, hω, hδ]
  have hδ₅ : δ + 5 * ε ≤ 1 / 10 := by linarith only [hεδ, hworking, hω, hδ]
  have hRQexponent : 1 / 2 + 2 * «ω» + ε ≤ 7 / 12 := by
    linarith only [hworking, hδ, hεsmall]
  obtain ⟨C₀, X₀, hC₀, hX₀, hraw⟩ := sourceTheta_split_fiber_dense_cauchy_bound
    T A₀ A₁ 10 (ε / 100) hT hA₀ hA₁ (by norm_num) (by positivity)
  obtain ⟨Xc, hXc⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).eventually_ge_atTop (100 * C))
  let K := Real.sqrt (65 * C₀ * (1 + TN) * L ^ 2 * C ^ 15 + 1)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, max 1 (max X₀ Xc), hK, le_max_left _ _, ?_⟩
  intro x hx M N R Q H V γ hM hN hR hQ hV hMN hNγ hNR hRN hRQ hγlo hγcut
    r q₀ u q₂ a b₁ b₂ hRr hrR hH hHone huV hq₂Q hVlower hVupper F J hF hJ
    ha hb₁ ℓ t₀ Y hYx hY ψ hψ hψs hψ0 hψb β hβs hβ hψmajor c hc βℤ
  have hxone : 1 ≤ x := (le_max_left _ _).trans hx
  have hxpos : 0 < x := zero_lt_one.trans_le hxone
  have hx₀ : X₀ ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxc : Xc ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hxlarge : 100 * C ≤ x ^ (1 / 100 : ℝ) := hXc x hxc
  by_cases hFempty : F = ∅
  · simp only [hFempty, Finset.sum_empty]
    positivity
  obtain ⟨v₀, hv₀⟩ := Finset.nonempty_iff_ne_empty.mpr hFempty
  have hsf := (hF v₀ hv₀).2.2
  have hq₀ : 0 < q₀ := Nat.pos_of_ne_zero hsf.of_mul_left.of_mul_left.of_mul_right.ne_zero
  have hu : 0 < u := Nat.pos_of_ne_zero hsf.of_mul_left.of_mul_right.of_mul_left.ne_zero
  have hq₂ : 0 < q₂ := Nat.pos_of_ne_zero hsf.of_mul_right.ne_zero
  have hqpos : 0 < (q₀ : ℝ) := by exact_mod_cast hq₀
  have hqone : 1 ≤ (q₀ : ℝ) := by exact_mod_cast hq₀
  have hrpos : 0 < (r : ℝ) := hR.trans_le hRr
  have hrnat : 0 < r := by exact_mod_cast hrpos
  have hHpos : 0 < H := zero_lt_one.trans_le hHone
  have hγlower : 1 / 4 ≤ γ := by linarith only [hγlo, hω, hδ, hε]
  have hγhi : γ ≤ 1 / 2 := by linarith only [hγcut, hω, hδ]
  let HN : ℕ := ⌊2 * H⌋₊
  let KN : ℕ := ⌊C * V⌋₊
  let P₀ : ℝ := (r : ℝ) * (q₀ : ℝ) * (u : ℝ) * (KN : ℝ) ^ 2 * (q₂ : ℝ)
  obtain ⟨hqN, hNr, hrx, hHKx, hPx, hPupper, hHK⟩ :=
    sourceHighGamma_split_geometry «ω» δ ε C x M N R Q H V γ r q₀ u q₂ hω.le hδ.le
      hC hxone hxlarge hε hεsmall hδsmall hδ₅ hRQexponent hM hN hR hQ hV hq₀ hu hq₂
      hMN hNγ hNR hRN hRQ hγlo hγlower hγhi hRr hrR hH hHone huV hq₂Q hVupper
  have hHN : (HN : ℝ) ≤ 2 * H := Nat.floor_le (by positivity)
  have hKN : (KN : ℝ) ≤ C * V := Nat.floor_le (by positivity)
  have hFnat (v : ℕ) (hv : v ∈ F) : 0 < v ∧ v ≤ KN ∧ Squarefree (r * q₀ * (u * v) * q₂) :=
    ⟨(hF v hv).1, (Nat.le_floor_iff (by positivity)).mpr (hF v hv).2.1, (hF v hv).2.2⟩
  have hKNpos : 0 < KN := (hFnat v₀ hv₀).1.trans_le (hFnat v₀ hv₀).2.1
  have hPpos : 0 < P₀ := by dsimp only [P₀]; positivity
  have hJnat (h : ℤ) (hh : h ∈ J) : h ≠ 0 ∧ -(HN : ℤ) ≤ h ∧ h ≤ (HN : ℤ) := by
    have hreal : (h.natAbs : ℝ) ≤ 2 * H := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact (hJ h hh).2
    have habs : h.natAbs ≤ HN := (Nat.le_floor_iff (by positivity)).mpr hreal
    exact ⟨(hJ h hh).1, by omega, by omega⟩
  have hFcard : (F.card : ℝ) ≤ C * V := by
    have hsub : F ⊆ Finset.Icc 1 KN := fun v hv =>
      Finset.mem_Icc.mpr ⟨(hFnat v hv).1, (hFnat v hv).2.1⟩
    have hh : F.card ≤ KN := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsub
    exact (Nat.cast_le.mpr hh).trans hKN
  have hJcard : (J.card : ℝ) ≤ 5 * H := by
    have hsub : J ⊆ Finset.Icc (-(HN : ℤ)) (HN : ℤ) :=
      fun h hh => Finset.mem_Icc.mpr (hJnat h hh).2
    have hcard := Int.card_Icc_of_le (a := -(HN : ℤ)) (b := (HN : ℤ)) (by omega)
    have hcardR : ((Finset.Icc (-(HN : ℤ)) (HN : ℤ)).card : ℝ) =
        (HN : ℝ) + 1 - (-(HN : ℝ)) := by exact_mod_cast hcard
    have hh : (J.card : ℝ) ≤ ((Finset.Icc (-(HN : ℤ)) (HN : ℤ)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    linarith only [hh, hcardR, hHN, hHone]
  let D : ℝ := x ^ (ε / 100)
  have hDpos : 0 < D := Real.rpow_pos_of_pos hxpos _
  have hDone : 1 ≤ D := Real.one_le_rpow hxone (by positivity)
  let A : ℝ := Real.sqrt (N / (q₀ : ℝ)) * (P₀ * (Y : ℝ)) ^ (1 / 6 : ℝ)
  let B : ℝ := N / (q₀ : ℝ) / (r : ℝ)
  have hYpos : 0 < (Y : ℝ) := zero_lt_one.trans_le Y.property
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hS0 : 0 ≤ (J.card : ℝ) ^ 2 * (F.card : ℝ) ^ 2 * A +
      B * (D * (J.card : ℝ) * (F.card : ℝ) * ((HN : ℝ) * (KN : ℝ) + (r : ℝ))) :=
    add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hA0)
      (mul_nonneg hB0 (mul_nonneg
        (mul_nonneg (mul_nonneg hDpos.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
        (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))))
  let U : ℝ := ∑ v ∈ F, ‖∑ n ∈ βℤ.support,
    βℤ n * star (βℤ (n + ℓ * (r : ℤ))) *
      (sourceCompatibility r q₀ b₁ b₂ ℓ n : ℂ) *
      ∑ h ∈ J, c v h * sourceTheta r q₀ 1 (u * v) q₂ a b₁ b₂ ℓ n h‖
  let g : ℝ := (Int.gcd (q₀ : ℤ) ℓ : ℝ)
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hg : 0 ≤ g := Nat.cast_nonneg _
  have hbound := hraw x hx₀ r q₀ u q₂ a b₁ b₂ ⌊TN * N⌋₊ HN KN
    hrnat hq₀ hu hq₂ hrx hHKx hPx F J hFnat hJnat ha hb₁
    ℓ N t₀ D L hqN hNr hDpos.le hL Y hY ψ hψ hψs hψ0 hψb β hβs hβ hψmajor c hc
  clear hraw
  change U ^ 2 ≤ C₀ * D ^ 4 * g ^ 2 * (1 + (⌊TN * N⌋₊ : ℝ) / (q₀ : ℝ)) * L ^ 2 * D *
    ((J.card : ℝ) ^ 2 * (F.card : ℝ) ^ 2 * A +
      B * (D * (J.card : ℝ) * (F.card : ℝ) * ((HN : ℝ) * (KN : ℝ) + (r : ℝ)))) at hbound
  have hmass : 1 + (⌊TN * N⌋₊ : ℝ) / (q₀ : ℝ) ≤ (1 + TN) * N / (q₀ : ℝ) := by
    have hf := Nat.floor_le (show 0 ≤ TN * N by positivity)
    calc
      _ ≤ N / (q₀ : ℝ) + (TN * N) / (q₀ : ℝ) :=
        add_le_add ((one_le_div hqpos).mpr hqN) (div_le_div_of_nonneg_right hf hqpos.le)
      _ = _ := by ring
  have hparts : (J.card : ℝ) ^ 2 * (F.card : ℝ) ^ 2 * A ≤ (5 * H) ^ 2 * (C * V) ^ 2 * A :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hJcard 2)
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hFcard 2) (sq_nonneg _) (sq_nonneg _)) hA0
  have hmean : (J.card : ℝ) * (F.card : ℝ) * ((HN : ℝ) * (KN : ℝ) + (r : ℝ)) ≤
      (5 * H) * (C * V) * (2 * C * H * V + (r : ℝ)) := by gcongr
  have hbracket : (J.card : ℝ) ^ 2 * (F.card : ℝ) ^ 2 * A +
      B * (D * (J.card : ℝ) * (F.card : ℝ) * ((HN : ℝ) * (KN : ℝ) + (r : ℝ))) ≤
      D * ((5 * H) ^ 2 * (C * V) ^ 2 * A + B * (5 * H) * (C * V) *
        (2 * C * H * V + (r : ℝ))) := by
    have hfirst : (J.card : ℝ) ^ 2 * (F.card : ℝ) ^ 2 * A ≤
        D * ((5 * H) ^ 2 * (C * V) ^ 2 * A) :=
      hparts.trans (le_mul_of_one_le_left (by positivity) hDone)
    have hsecond := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hmean hDpos.le) hB0
    nlinarith only [hfirst, hsecond]
  have hscale := ((sourceHighGamma_scale_envelopes «ω» δ ε C x M N R Q H
    (q₀ : ℝ) γ hω hδ hε hworking hsmall hC hxone hM hN hR hQ hqone
      hMN hNγ hNR hRN hRQ hH hγhi).2 hγlo hγcut).2 V hV hVlower
  have hnormalized := sourceHighGamma_split_normalized_envelope
    δ ε C x H N R Q V (r : ℝ) (q₀ : ℝ) P₀ (Y : ℝ) (C ^ 12 * x ^ (-5 * ε))
      hC hxone hHpos hN hR hQ hV hRr hqone hPpos
      (zero_lt_one.trans_le Y.property) hYx hPupper hVupper hscale.1 hscale.2.1 hscale.2.2
  change U ≤ K * g * N * V * x ^ (-2 * ε)
  exact sourceHighGamma_split_energy_finish C₀ C TN L x ε N V (q₀ : ℝ) U g
    (1 + (⌊TN * N⌋₊ : ℝ) / (q₀ : ℝ))
    ((J.card : ℝ) ^ 2 * (F.card : ℝ) ^ 2 * A +
      B * (D * (J.card : ℝ) * (F.card : ℝ) * ((HN : ℝ) * (KN : ℝ) + (r : ℝ))))
    ((5 * H) ^ 2 * (C * V) ^ 2 * A + B * (5 * H) * (C * V) *
      (2 * C * H * V + (r : ℝ)))
    hC₀ hC hTN hxone hε hN hV hqpos hU hg hS0
    hbound hmass hbracket hnormalized

open Classical in
theorem sourceHighGamma_near_uniform_band
    («ω» δ ε C cM TM TN T A₀ A₁ LM : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ) (hε : 0 < ε)
    (hworking : 68 * «ω» + 20 * δ < 1) (hsmall : ε < δ / 10 ^ 100)
    (hC : 1 ≤ C) (hcM : 0 < cM) (hMT : cM ≤ TM)
    (hTN : 1 ≤ TN) (hT : 1 ≤ T) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hLM : 0 ≤ LM) :
    ∃ K X : ℝ, 0 < K ∧ 1 ≤ X ∧
      ∀ x : ℝ, X ≤ x →
      ∀ M N R Q H γ : ℝ,
        0 < M → 0 < N → 0 < R → 0 < Q →
        x / C ≤ M * N → N = x ^ γ →
        N ≤ C * x ^ (δ + 4 * ε) * R →
        R ≤ C * x ^ (-2 * ε) * N →
        R * Q ≤ C * x ^ (1 / 2 + 2 * «ω» + ε) →
        1 / 2 - 2 * «ω» - δ / 2 ≤ γ → γ ≤ 1 / 2 →
      ∀ q₀ a b₁ b₂ : ℕ,
        H = x ^ ε * R * Q ^ 2 / ((q₀ : ℝ) * M) → 1 ≤ H →
      ∀ (𝒜 : Finset (ℕ × ℕ × ℕ × ℕ)) (J : Finset ℤ),
        (∀ t ∈ 𝒜,
          t.2.1 = 1 ∧ 0 < t.1 ∧ 0 < t.2.2.1 ∧ 0 < t.2.2.2 ∧
          Squarefree (t.1 * q₀ * t.2.1 * t.2.2.1 * t.2.2.2) ∧
          R ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) ≤ 2 * R ∧
          Q ≤ (q₀ * t.2.2.1 : ℕ) ∧ (q₀ * t.2.2.1 : ℕ) ≤ 2 * Q ∧
          Q ≤ (q₀ * t.2.2.2 : ℕ) ∧ (q₀ * t.2.2.2 : ℕ) ≤ 2 * Q) →
        (∀ h ∈ J, h ≠ 0 ∧ |(h : ℝ)| ≤ 2 * H) →
        (∀ t ∈ 𝒜, Nat.Coprime a t.1) → Nat.Coprime b₁ q₀ →
      ∀ (ν : ℕ × ℕ → ℂ),
        (∀ t ∈ 𝒜,
          ‖ν (q₀ * t.2.1 * t.2.2.1, t.1)‖ ≤ 1 ∧
          ‖ν (q₀ * t.2.2.2, t.1)‖ ≤ 1) →
      ∀ (ℓ : ℤ) (t₀ : ℝ) (ψM ψN : ℝ → ℝ),
        Function.support ψM ⊆ Set.Icc cM TM → (∀ t : ℝ, |ψM t| ≤ LM) →
        ContDiff ℝ 1 ψN → Function.support ψN ⊆ Set.Icc (-T) T →
        (∀ t : ℝ, 0 ≤ ψN t) →
        (∀ t : ℝ, |ψN t| ≤ A₀ ∧ |deriv ψN t| ≤ A₁) →
      ∀ (β : ℕ →₀ ℂ), β.support ⊆ Finset.Icc 1 ⌊TN * N⌋₊ →
        (∀ n ∈ β.support, ‖β n‖ ≤ x ^ (ε / 100)) →
        (∀ n ∈ β.support, 1 ≤ ψN (((n : ℝ) - t₀) / N)) →
      let βℤ : ℤ →₀ ℂ := Finsupp.embDomain (Nat.castEmbedding : ℕ ↪ ℤ) β
      let P : (ℕ × ℕ × ℕ × ℕ) → ℕ := fun t =>
        t.1 * q₀ * t.2.1 * t.2.2.1 * t.2.2.2
      (∑ t ∈ 𝒜,
        ‖ν (q₀ * t.2.1 * t.2.2.1, t.1) * star (ν (q₀ * t.2.2.2, t.1)) *
          ((M : ℂ) / (P t : ℂ)) *
            ∑ n ∈ βℤ.support.filter (fun n =>
              Int.gcd n ((t.1 * q₀ * t.2.1 * t.2.2.1 : ℕ) : ℤ) = 1 ∧
              Int.gcd (n + ℓ * (t.1 : ℤ)) ((q₀ * t.2.2.2 : ℕ) : ℤ) = 1),
              βℤ n * star (βℤ (n + ℓ * (t.1 : ℤ))) *
                (sourceCompatibility t.1 q₀ b₁ b₂ ℓ n : ℂ) *
                  ∑ h ∈ J, sourcePhi ψM M (P t) h *
                    sourceTheta t.1 q₀ t.2.1 t.2.2.1 t.2.2.2 a b₁ b₂ ℓ n h‖) ≤
        K * M * N * (Int.gcd (q₀ : ℤ) ℓ : ℝ) / (q₀ : ℝ) * x ^ (-ε / 4) := by
  have hTM : 0 < TM := hcM.trans_le hMT
  have hPhiBound : 0 ≤ TM * LM := mul_nonneg hTM.le hLM
  obtain ⟨K, X, hK, hX, hnear⟩ := sourceTheta_near_typeII_uniform_power_saving
    «ω» δ ε C T TN A₀ A₁ (TM * LM) hω hδ hε hworking hsmall hC hT hTN hA₀ hA₁ hPhiBound
  refine ⟨2 * K, X, mul_pos (by norm_num) hK, hX, ?_⟩
  intro x hx M N R Q H γ hM hN hR hQ hMN hNγ hNR hRN hRQ hγlo hγhi
    q₀ a b₁ b₂ hH hHone 𝒜 J h𝒜 hJ ha hb₁ ν hν ℓ t₀ ψM ψN hψMs hψMb
    hψN hψNs hψN0 hψNb β hβs hβ hψmajor βℤ P
  have hxone : 1 ≤ x := hX.trans hx
  have hxpos : 0 < x := zero_lt_one.trans_le hxone
  by_cases h𝒜empty : 𝒜 = ∅
  · simp only [h𝒜empty, Finset.sum_empty]
    positivity
  obtain ⟨t₀', ht₀'⟩ := Finset.nonempty_iff_ne_empty.mpr h𝒜empty
  have hsf := (h𝒜 t₀' ht₀').2.2.2.2.1
  have hq₀ : 0 < q₀ :=
    Nat.pos_of_ne_zero hsf.of_mul_left.of_mul_left.of_mul_left.of_mul_right.ne_zero
  have hqpos : 0 < (q₀ : ℝ) := by exact_mod_cast hq₀
  have hPhi (d : ℕ) (h : ℤ) : ‖sourcePhi ψM M d h‖ ≤ TM * LM := by
    have hb := sourcePhiRealFactor_sampling_and_norm cM TM M LM hcM hMT hM hLM
      ψM hψMs hψMb d h
    have heq := hb.2.1 1
    simp only [Nat.cast_one, Nat.one_mul] at heq
    simpa only [heq] using hb.2.2 (1 : ℝ)
  let Rs : Finset ℕ := 𝒜.image Prod.fst
  let F : ℕ → Finset (ℕ × ℕ) := fun r =>
    (𝒜.filter (fun t => t.1 = r)).image (fun t => t.2.2)
  let w : ℕ → (ℕ × ℕ) → ℝ := fun r q =>
    ‖∑ n ∈ βℤ.support, βℤ n * star (βℤ (n + ℓ * (r : ℤ))) *
      (sourceCompatibility r q₀ b₁ b₂ ℓ n : ℂ) *
        ∑ h ∈ J, sourcePhi ψM M (r * q₀ * q.1 * q.2) h *
          sourceTheta r q₀ 1 q.1 q.2 a b₁ b₂ ℓ n h‖
  have hw (r : ℕ) (q : ℕ × ℕ) : 0 ≤ w r q := norm_nonneg _
  have hF (r : ℕ) (q : ℕ × ℕ) (hq : q ∈ F r) :
      Squarefree (r * q₀ * q.1 * q.2) ∧
        Q ≤ (q₀ * q.1 : ℕ) ∧ (q₀ * q.1 : ℕ) ≤ 2 * Q ∧
        Q ≤ (q₀ * q.2 : ℕ) ∧ (q₀ * q.2 : ℕ) ≤ 2 * Q := by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨htA, htr⟩ := Finset.mem_filter.mp ht
    obtain ⟨hu, _, _, _, hsf, _, _, hq₁lo, hq₁hi, hq₂lo, hq₂hi⟩ := h𝒜 t htA
    refine ⟨?_, hq₁lo, hq₁hi, hq₂lo, hq₂hi⟩
    simpa only [hu, Nat.mul_one, htr] using hsf
  have hrow (t : ℕ × ℕ × ℕ × ℕ) (ht : t ∈ 𝒜) := by
    obtain ⟨hu, hr, hv, hq₂, _, hRr, _, hQ₁, _, hQ₂, _⟩ := h𝒜 t ht
    have hraw := sourceHighGamma_weighted_row_norm t.1 q₀ t.2.1 t.2.2.1 t.2.2.2
      a b₁ b₂ ℓ M R Q hM hR hQ hr hq₀ (by omega) hv hq₂ hRr
      (by simpa only [hu, Nat.mul_one] using hQ₁) hQ₂
      (ν (q₀ * t.2.1 * t.2.2.1, t.1)) (ν (q₀ * t.2.2.2, t.1))
      (hν t ht).1 (hν t ht).2 βℤ.support J βℤ (fun h => sourcePhi ψM M (P t) h)
    dsimp only at hraw
    conv_rhs at hraw => simp only [P, hu, Nat.mul_one]
    exact hraw
  have hlocal (r : ℕ) (hr : r ∈ Rs) :
      (∑ q ∈ F r, w r q) ≤
        K * Q ^ 2 * N * (Int.gcd (q₀ : ℤ) ℓ : ℝ) / (q₀ : ℝ) ^ 2 * x ^ (-ε / 4) := by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨_, _, _, _, _, hRr, hrR, _, _, _, _⟩ := h𝒜 t ht
    exact hnear x hx M N R Q H γ hM hN hR hQ hMN hNγ hNR hRN hRQ hγlo hγhi
      t.1 q₀ a b₁ b₂ hRr hrR hH hHone (F t.1) J (hF t.1) hJ (ha t ht) hb₁
      ℓ t₀ ψN hψN hψNs hψN0 hψNb β hβs hβ hψmajor
      (fun q h => sourcePhi ψM M (t.1 * q₀ * q.1 * q.2) h)
      (fun _ _ h _ => hPhi _ h)
  have hsumr (r : ℕ) :
      (∑ t ∈ 𝒜.filter (fun t => t.1 = r), w t.1 t.2.2) = ∑ q ∈ F r, w r q := by
    have hinj : Set.InjOn (fun t : ℕ × ℕ × ℕ × ℕ => t.2.2)
        (𝒜.filter (fun t => t.1 = r) : Set _) := by
      intro t ht s hs heq
      obtain ⟨htA, htr⟩ := Finset.mem_filter.mp ht
      obtain ⟨hsA, hsr⟩ := Finset.mem_filter.mp hs
      exact Prod.ext (htr.trans hsr.symm)
        (Prod.ext ((h𝒜 t htA).1.trans (h𝒜 s hsA).1.symm) heq)
    calc
      _ = ∑ t ∈ 𝒜.filter (fun t => t.1 = r), w r t.2.2 := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [(Finset.mem_filter.mp ht).2]
      _ = _ := (Finset.sum_image hinj).symm
  have hRcard : (Rs.card : ℝ) ≤ 2 * R := by
    have hsub : Rs ⊆ Finset.Icc 1 ⌊2 * R⌋₊ := by
      intro r hr
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨_, hr, _, _, _, _, hrR, _, _, _, _⟩ := h𝒜 t ht
      exact Finset.mem_Icc.mpr ⟨hr, (Nat.le_floor_iff (by positivity)).mpr hrR⟩
    have hh : Rs.card ≤ ⌊2 * R⌋₊ := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsub
    exact (Nat.cast_le.mpr hh).trans (Nat.floor_le (by positivity))
  have hfamily : (∑ t ∈ 𝒜, w t.1 t.2.2) ≤
      (2 * R) * (K * Q ^ 2 * N * (Int.gcd (q₀ : ℤ) ℓ : ℝ) /
        (q₀ : ℝ) ^ 2 * x ^ (-ε / 4)) := by
    calc
      _ = ∑ r ∈ Rs, ∑ t ∈ 𝒜.filter (fun t => t.1 = r), w t.1 t.2.2 :=
        (Finset.sum_fiberwise_of_maps_to (s := 𝒜) (t := Rs) (g := Prod.fst)
          (fun t ht => Finset.mem_image_of_mem Prod.fst ht) _).symm
      _ = ∑ r ∈ Rs, ∑ q ∈ F r, w r q := Finset.sum_congr rfl (fun r _ => hsumr r)
      _ ≤ ∑ _r ∈ Rs,
          K * Q ^ 2 * N * (Int.gcd (q₀ : ℤ) ℓ : ℝ) / (q₀ : ℝ) ^ 2 * x ^ (-ε / 4) :=
        Finset.sum_le_sum hlocal
      _ = (Rs.card : ℝ) *
          (K * Q ^ 2 * N * (Int.gcd (q₀ : ℤ) ℓ : ℝ) / (q₀ : ℝ) ^ 2 * x ^ (-ε / 4)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hRcard (by positivity)
  calc
    _ ≤ ∑ t ∈ 𝒜, (M * (q₀ : ℝ) / (R * Q ^ 2)) * w t.1 t.2.2 := Finset.sum_le_sum hrow
    _ = (M * (q₀ : ℝ) / (R * Q ^ 2)) * ∑ t ∈ 𝒜, w t.1 t.2.2 := (Finset.mul_sum ..).symm
    _ ≤ (M * (q₀ : ℝ) / (R * Q ^ 2)) *
        ((2 * R) * (K * Q ^ 2 * N * (Int.gcd (q₀ : ℤ) ℓ : ℝ) /
          (q₀ : ℝ) ^ 2 * x ^ (-ε / 4))) :=
      mul_le_mul_of_nonneg_left hfamily (by positivity)
    _ = _ := by field_simp [hR.ne', hQ.ne', hqpos.ne']

open Classical in
theorem sourceHighGamma_split_uniform_band
    («ω» δ ε C cM TM TN T A₀ A₁ LM : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ) (hε : 0 < ε)
    (hworking : 68 * «ω» + 20 * δ < 1) (hsmall : ε < δ / 10 ^ 100)
    (hC : 1 ≤ C) (hcM : 0 < cM) (hMT : cM ≤ TM)
    (hTN : 1 ≤ TN) (hT : 1 ≤ T) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hLM : 0 ≤ LM) :
    ∃ K X : ℝ, 0 < K ∧ 1 ≤ X ∧
      ∀ x : ℝ, X ≤ x →
      ∀ M N R Q H U V γ : ℝ,
        0 < M → 0 < N → 0 < R → 0 < Q → 0 < U → 0 < V →
        x / C ≤ M * N → N = x ^ γ →
        N ≤ C * x ^ (δ + 4 * ε) * R →
        R ≤ C * x ^ (-2 * ε) * N →
        R * Q ≤ C * x ^ (1 / 2 + 2 * «ω» + ε) →
        1 / 4 + 14 * «ω» + 4 * δ + 100 * ε ≤ γ →
        γ ≤ 1 / 2 - 2 * «ω» - δ / 2 →
      ∀ q₀ a b₁ b₂ : ℕ, 0 < q₀ →
        H = x ^ ε * R * Q ^ 2 / ((q₀ : ℝ) * M) → 1 ≤ H →
        U * V ≤ C * Q / (q₀ : ℝ) →
        x ^ (5 * ε) * H / (q₀ : ℝ) ≤ C * V →
        V ≤ C * x ^ (δ + 5 * ε) * H →
      ∀ (Y : Set.Ici (1 : ℝ)), (Y : ℝ) ≤ x ^ δ →
      ∀ (𝒜 : Finset (ℕ × ℕ × ℕ × ℕ)) (J : Finset ℤ),
        (∀ t ∈ 𝒜,
          0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.1 ∧ 0 < t.2.2.2 ∧
          Squarefree (t.1 * q₀ * t.2.1 * t.2.2.1 * t.2.2.2) ∧
          R ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) ≤ 2 * R ∧
          (t.2.1 : ℝ) ≤ C * U ∧ (t.2.2.1 : ℝ) ≤ C * V ∧
          Q ≤ (q₀ * t.2.1 * t.2.2.1 : ℕ) ∧
          Q ≤ (q₀ * t.2.2.2 : ℕ) ∧ (q₀ * t.2.2.2 : ℕ) ≤ C * Q) →
        (∀ t ∈ 𝒜,
          Nonempty (DenseDivisibilityWitness
            Y 1 (t.1 * q₀ * t.2.1 * t.2.2.1)) ∧
          Nonempty (DenseDivisibilityWitness
            Y 1 (t.1 * q₀ * t.2.2.2))) →
        (∀ h ∈ J, h ≠ 0 ∧ |(h : ℝ)| ≤ 2 * H) →
        (∀ t ∈ 𝒜, Nat.Coprime a t.1) → Nat.Coprime b₁ q₀ →
      ∀ (ν : ℕ × ℕ → ℂ),
        (∀ t ∈ 𝒜,
          ‖ν (q₀ * t.2.1 * t.2.2.1, t.1)‖ ≤ 1 ∧
          ‖ν (q₀ * t.2.2.2, t.1)‖ ≤ 1) →
      ∀ (ℓ : ℤ) (t₀ : ℝ) (ψM ψN : ℝ → ℝ),
        Function.support ψM ⊆ Set.Icc cM TM → (∀ t : ℝ, |ψM t| ≤ LM) →
        ContDiff ℝ 1 ψN → Function.support ψN ⊆ Set.Icc (-T) T →
        (∀ t : ℝ, 0 ≤ ψN t) →
        (∀ t : ℝ, |ψN t| ≤ A₀ ∧ |deriv ψN t| ≤ A₁) →
      ∀ (β : ℕ →₀ ℂ), β.support ⊆ Finset.Icc 1 ⌊TN * N⌋₊ →
        (∀ n ∈ β.support, ‖β n‖ ≤ x ^ (ε / 100)) →
        (∀ n ∈ β.support, 1 ≤ ψN (((n : ℝ) - t₀) / N)) →
      let βℤ : ℤ →₀ ℂ := Finsupp.embDomain (Nat.castEmbedding : ℕ ↪ ℤ) β
      let P : (ℕ × ℕ × ℕ × ℕ) → ℕ := fun t =>
        t.1 * q₀ * t.2.1 * t.2.2.1 * t.2.2.2
      (∑ t ∈ 𝒜,
        ‖ν (q₀ * t.2.1 * t.2.2.1, t.1) * star (ν (q₀ * t.2.2.2, t.1)) *
          ((M : ℂ) / (P t : ℂ)) *
            ∑ n ∈ βℤ.support.filter (fun n =>
              Int.gcd n ((t.1 * q₀ * t.2.1 * t.2.2.1 : ℕ) : ℤ) = 1 ∧
              Int.gcd (n + ℓ * (t.1 : ℤ)) ((q₀ * t.2.2.2 : ℕ) : ℤ) = 1),
              βℤ n * star (βℤ (n + ℓ * (t.1 : ℤ))) *
                (sourceCompatibility t.1 q₀ b₁ b₂ ℓ n : ℂ) *
                  ∑ h ∈ J, sourcePhi ψM M (P t) h *
                    sourceTheta t.1 q₀ t.2.1 t.2.2.1 t.2.2.2 a b₁ b₂ ℓ n h‖) ≤
        K * M * N * (Int.gcd (q₀ : ℤ) ℓ : ℝ) / (q₀ : ℝ) * x ^ (-ε / 4) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hTM : 0 < TM := hcM.trans_le hMT
  let D : ℝ := 4 * C ^ 2
  have hCD : C ≤ D := by dsimp only [D]; nlinarith only [hC, sq_nonneg (C - 1)]
  have hC₂D : C ^ 2 ≤ D := by dsimp only [D]; nlinarith only [sq_nonneg C]
  have hD : 1 ≤ D := hC.trans hCD
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  obtain ⟨K, X, hK, hX, hsplit⟩ := sourceTheta_split_typeI_uniform_power_saving
    «ω» δ ε D T TN A₀ A₁ (TM * LM) hω hδ hε hworking hsmall hD hT hTN
      hA₀ hA₁ (mul_nonneg hTM.le hLM)
  refine ⟨2 * C ^ 3 * K, X, by positivity, hX, ?_⟩
  intro x hx M N R Q H U V γ hM hN hR hQ hU hV hMN hNγ hNR hRN hRQ hγlo hγcut
    q₀ a b₁ b₂ hq₀ hH hHone hUV hVlo hVhi Y hYx 𝒜 J h𝒜 h𝒜Y hJ ha hb₁
    ν hν ℓ t₀ ψM ψN hψMs hψMb hψN hψNs hψN0 hψNb β hβs hβ hψmajor βℤ P
  have hxone : 1 ≤ x := hX.trans hx
  have hxpos : 0 < x := zero_lt_one.trans_le hxone
  have hqpos : 0 < (q₀ : ℝ) := by exact_mod_cast hq₀
  have hMN' : x / D ≤ M * N :=
    (div_le_div_of_nonneg_left hxpos.le hCpos hCD).trans hMN
  have hNR' : N ≤ D * x ^ (δ + 4 * ε) * R := hNR.trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hxpos.le _)) hR.le)
  have hRN' : R ≤ D * x ^ (-2 * ε) * N := hRN.trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hxpos.le _)) hN.le)
  have hRQ' : R * Q ≤ D * x ^ (1 / 2 + 2 * «ω» + ε) := hRQ.trans
    (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hxpos.le _))
  have hVlo' : x ^ (5 * ε) * H / (q₀ : ℝ) ≤ D * V :=
    hVlo.trans (mul_le_mul_of_nonneg_right hCD hV.le)
  have hVhi' : V ≤ D * x ^ (δ + 5 * ε) * H := hVhi.trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hxpos.le _))
      (zero_le_one.trans hHone))
  have hPhi (d : ℕ) (h : ℤ) : ‖sourcePhi ψM M d h‖ ≤ TM * LM := by
    have hh := sourcePhiRealFactor_sampling_and_norm cM TM M LM hcM hMT hM hLM
      ψM hψMs hψMb d h
    have heq := hh.2.1 1
    simp only [Nat.cast_one, Nat.one_mul] at heq
    simpa only [heq] using hh.2.2 (1 : ℝ)
  let π : (ℕ × ℕ × ℕ × ℕ) → ℕ × ℕ × ℕ := fun t => (t.1, t.2.1, t.2.2.2)
  let I : Finset (ℕ × ℕ × ℕ) := 𝒜.image π
  let F : (ℕ × ℕ × ℕ) → Finset ℕ := fun i =>
    (𝒜.filter (fun t => π t = i)).image (fun t => t.2.2.1)
  let w : (ℕ × ℕ × ℕ) → ℕ → ℝ := fun i v =>
    ‖∑ n ∈ βℤ.support, βℤ n * star (βℤ (n + ℓ * (i.1 : ℤ))) *
      (sourceCompatibility i.1 q₀ b₁ b₂ ℓ n : ℂ) *
        ∑ h ∈ J, sourcePhi ψM M (i.1 * q₀ * (i.2.1 * v) * i.2.2) h *
          sourceTheta i.1 q₀ 1 (i.2.1 * v) i.2.2 a b₁ b₂ ℓ n h‖
  have hFmem (i : ℕ × ℕ × ℕ) (v : ℕ) (hv : v ∈ F i) :
      (i.1, i.2.1, v, i.2.2) ∈ 𝒜 := by
    obtain ⟨t, ht, htv⟩ := Finset.mem_image.mp hv
    obtain ⟨htA, hti⟩ := Finset.mem_filter.mp ht
    have hfirst : t.1 = i.1 := congrArg (fun p : ℕ × ℕ × ℕ => p.1) hti
    have hsecond : t.2.1 = i.2.1 := congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) hti
    have hfourth : t.2.2.2 = i.2.2 := by
      simpa only [π] using congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hti
    have heq : t = (i.1, i.2.1, v, i.2.2) :=
      Prod.ext hfirst (Prod.ext hsecond (Prod.ext htv hfourth))
    exact heq ▸ htA
  have hTheta (r u v q₂ : ℕ) (n h : ℤ) :
      sourceTheta r q₀ u v q₂ a b₁ b₂ ℓ n h =
        sourceTheta r q₀ 1 (u * v) q₂ a b₁ b₂ ℓ n h := by
    let θ : ℕ → ℂ := fun z =>
      if hp : r ≠ 0 ∧ z ≠ 0 ∧ q₂ ≠ 0 then
        let _ : NeZero r := ⟨hp.1⟩
        let _ : NeZero z := ⟨hp.2.1⟩
        let _ : NeZero q₂ := ⟨hp.2.2⟩
        reciprocalUnitPhase r ((a : ZMod r) * (h : ZMod r))
          ((n : ZMod r) * ((z * q₂ : ℕ) : ZMod r)) *
        reciprocalUnitPhase z ((b₁ : ZMod z) * (h : ZMod z))
          ((n : ZMod z) * ((r * q₂ : ℕ) : ZMod z)) *
        reciprocalUnitPhase q₂ ((b₂ : ZMod q₂) * (h : ZMod q₂))
          (((n + ℓ * (r : ℤ) : ℤ) : ZMod q₂) * ((r * z : ℕ) : ZMod q₂))
      else 0
    have hf (u v : ℕ) : sourceTheta r q₀ u v q₂ a b₁ b₂ ℓ n h = θ (q₀ * u * v) := by
      unfold sourceTheta
      dsimp only [θ]
      split_ifs
      · congr 3
        push_cast
        ring
      · rfl
    rw [hf u v, hf 1 (u * v)]
    congr 1
    ring
  have hrow (t : ℕ × ℕ × ℕ × ℕ) (ht : t ∈ 𝒜) :
      ‖ν (q₀ * t.2.1 * t.2.2.1, t.1) * star (ν (q₀ * t.2.2.2, t.1)) *
        ((M : ℂ) / (P t : ℂ)) *
          ∑ n ∈ βℤ.support.filter (fun n =>
            Int.gcd n ((t.1 * q₀ * t.2.1 * t.2.2.1 : ℕ) : ℤ) = 1 ∧
            Int.gcd (n + ℓ * (t.1 : ℤ)) ((q₀ * t.2.2.2 : ℕ) : ℤ) = 1),
            βℤ n * star (βℤ (n + ℓ * (t.1 : ℤ))) *
              (sourceCompatibility t.1 q₀ b₁ b₂ ℓ n : ℂ) *
                ∑ h ∈ J, sourcePhi ψM M (P t) h *
                  sourceTheta t.1 q₀ t.2.1 t.2.2.1 t.2.2.2 a b₁ b₂ ℓ n h‖ ≤
        (M * (q₀ : ℝ) / (R * Q ^ 2)) * w (π t) t.2.2.1 := by
    obtain ⟨hr, hu, hv, hq₂, _, hRr, _, _, _, hQ₁, hQ₂, _⟩ := h𝒜 t ht
    have hh := sourceHighGamma_weighted_row_norm t.1 q₀ t.2.1 t.2.2.1 t.2.2.2
      a b₁ b₂ ℓ M R Q hM hR hQ hr hq₀ hu hv hq₂ hRr hQ₁ hQ₂
      (ν (q₀ * t.2.1 * t.2.2.1, t.1)) (ν (q₀ * t.2.2.2, t.1))
      (hν t ht).1 (hν t ht).2 βℤ.support J βℤ (fun h => sourcePhi ψM M (P t) h)
    dsimp only at hh
    have hTh : sourceTheta t.1 q₀ t.2.1 t.2.2.1 t.2.2.2 a b₁ b₂ ℓ =
        sourceTheta t.1 q₀ 1 (t.2.1 * t.2.2.1) t.2.2.2 a b₁ b₂ ℓ :=
      funext fun n => funext fun h => hTheta _ _ _ _ n h
    conv_rhs at hh => rw [hTh]
    simpa only [P, w, π, Nat.mul_assoc] using hh
  have hlocal (i : ℕ × ℕ × ℕ) (hi : i ∈ I) :
      (∑ v ∈ F i, w i v) ≤
        K * (Int.gcd (q₀ : ℤ) ℓ : ℝ) * N * V * x ^ (-2 * ε) := by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨_, _, _, _, _, hRr, hrR, huU, _, _, _, hq₂Q⟩ := h𝒜 t ht
    have huV : (t.2.1 : ℝ) * V ≤ D * Q / (q₀ : ℝ) := by
      calc
        _ ≤ (C * U) * V := mul_le_mul_of_nonneg_right huU hV.le
        _ = C * (U * V) := by ring
        _ ≤ C * (C * Q / (q₀ : ℝ)) := mul_le_mul_of_nonneg_left hUV hCpos.le
        _ = C ^ 2 * Q / (q₀ : ℝ) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC₂D hQ.le) hqpos.le
    have hq₂Q' : (q₀ : ℝ) * (t.2.2.2 : ℝ) ≤ D * Q := by
      have hh : (q₀ : ℝ) * (t.2.2.2 : ℝ) ≤ C * Q := by
        simpa only [Nat.cast_mul] using hq₂Q
      exact hh.trans (mul_le_mul_of_nonneg_right hCD hQ.le)
    have hFdata (v : ℕ) (hv : v ∈ F (π t)) :
        0 < v ∧ (v : ℝ) ≤ D * V ∧ Squarefree (t.1 * q₀ * (t.2.1 * v) * t.2.2.2) := by
      obtain ⟨_, _, hvpos, _, hsf, _, _, _, hvV, _, _, _⟩ :=
        h𝒜 _ (hFmem (π t) v hv)
      refine ⟨hvpos, hvV.trans (mul_le_mul_of_nonneg_right hCD hV.le), ?_⟩
      simpa only [π, Nat.mul_assoc] using hsf
    have hFdense (v : ℕ) (hv : v ∈ F (π t)) :
        Nonempty (DenseDivisibilityWitness
          Y 1 (t.1 * q₀ * (t.2.1 * v))) ∧
        Nonempty (DenseDivisibilityWitness
          Y 1 (t.1 * q₀ * t.2.2.2)) := by
      simpa only [π, Nat.mul_assoc] using h𝒜Y _ (hFmem (π t) v hv)
    exact hsplit x hx M N R Q H V γ hM hN hR hQ hV hMN' hNγ hNR' hRN' hRQ'
      hγlo hγcut t.1 q₀ t.2.1 t.2.2.2 a b₁ b₂ hRr hrR hH hHone huV hq₂Q'
      hVlo' hVhi' (F (π t)) J hFdata hJ (ha t ht) hb₁ ℓ t₀ Y hYx hFdense
      ψN hψN hψNs hψN0 hψNb β hβs hβ hψmajor
      (fun v h => sourcePhi ψM M (t.1 * q₀ * (t.2.1 * v) * t.2.2.2) h)
      (fun _ _ h _ => hPhi _ h)
  have hsumfiber (i : ℕ × ℕ × ℕ) :
      (∑ t ∈ 𝒜.filter (fun t => π t = i), w (π t) t.2.2.1) =
        ∑ v ∈ F i, w i v := by
    have hinj : Set.InjOn (fun t : ℕ × ℕ × ℕ × ℕ => t.2.2.1)
        (𝒜.filter (fun t => π t = i) : Set _) := by
      intro t ht s hs hv
      have heq : π t = π s := (Finset.mem_filter.mp ht).2.trans
        (Finset.mem_filter.mp hs).2.symm
      have hfirst : t.1 = s.1 := congrArg (fun p : ℕ × ℕ × ℕ => p.1) heq
      have hsecond : t.2.1 = s.2.1 := congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) heq
      have hfourth : t.2.2.2 = s.2.2.2 := by
        simpa only [π] using congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) heq
      exact Prod.ext hfirst (Prod.ext hsecond (Prod.ext hv hfourth))
    calc
      _ = ∑ t ∈ 𝒜.filter (fun t => π t = i), w i t.2.2.1 := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [(Finset.mem_filter.mp ht).2]
      _ = _ := (Finset.sum_image hinj).symm
  have hIcard : (I.card : ℝ) ≤ 2 * C ^ 2 * R * U * Q / (q₀ : ℝ) := by
    let IR := Finset.Icc 1 ⌊2 * R⌋₊
    let IU := Finset.Icc 1 ⌊C * U⌋₊
    let IQ := Finset.Icc 1 ⌊C * Q / (q₀ : ℝ)⌋₊
    have hsub : I ⊆ IR ×ˢ (IU ×ˢ IQ) := by
      intro i hi
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨hr, hu, _, hq₂, _, _, hrR, huU, _, _, _, hq₂Q⟩ := h𝒜 t ht
      have hq₂bound : (t.2.2.2 : ℝ) ≤ C * Q / (q₀ : ℝ) := by
        apply (le_div_iff₀ hqpos).mpr
        simpa only [Nat.cast_mul, mul_comm] using hq₂Q
      exact Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨hr, Nat.le_floor hrR⟩,
          Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hu, Nat.le_floor huU⟩,
            Finset.mem_Icc.mpr ⟨hq₂, Nat.le_floor hq₂bound⟩⟩⟩
    have hc : I.card ≤ ⌊2 * R⌋₊ * (⌊C * U⌋₊ * ⌊C * Q / (q₀ : ℝ)⌋₊) := by
      simpa only [Finset.card_product, IR, IU, IQ, Nat.card_Icc, Nat.add_sub_cancel] using
        Finset.card_le_card hsub
    calc
      (I.card : ℝ) ≤ (⌊2 * R⌋₊ : ℝ) *
          ((⌊C * U⌋₊ : ℝ) * (⌊C * Q / (q₀ : ℝ)⌋₊ : ℝ)) := by exact_mod_cast hc
      _ ≤ (2 * R) * ((C * U) * (C * Q / (q₀ : ℝ))) := by
        gcongr <;> exact Nat.floor_le (by positivity)
      _ = _ := by ring
  have hfamily : (∑ t ∈ 𝒜, w (π t) t.2.2.1) ≤
      (2 * C ^ 2 * R * U * Q / (q₀ : ℝ)) *
        (K * (Int.gcd (q₀ : ℤ) ℓ : ℝ) * N * V * x ^ (-2 * ε)) := by
    calc
      _ = ∑ i ∈ I, ∑ t ∈ 𝒜.filter (fun t => π t = i), w (π t) t.2.2.1 :=
        (Finset.sum_fiberwise_of_maps_to (s := 𝒜) (t := I) (g := π)
          (fun t ht => Finset.mem_image_of_mem π ht) _).symm
      _ = ∑ i ∈ I, ∑ v ∈ F i, w i v :=
        Finset.sum_congr rfl (fun i _ => hsumfiber i)
      _ ≤ ∑ _i ∈ I, K * (Int.gcd (q₀ : ℤ) ℓ : ℝ) * N * V * x ^ (-2 * ε) :=
        Finset.sum_le_sum hlocal
      _ = (I.card : ℝ) *
          (K * (Int.gcd (q₀ : ℤ) ℓ : ℝ) * N * V * x ^ (-2 * ε)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hIcard (by positivity)
  have hpow : x ^ (-2 * ε) ≤ x ^ (-ε / 4) :=
    Real.rpow_le_rpow_of_exponent_le hxone (by linarith only [hε])
  calc
    _ ≤ ∑ t ∈ 𝒜, (M * (q₀ : ℝ) / (R * Q ^ 2)) * w (π t) t.2.2.1 :=
      Finset.sum_le_sum hrow
    _ = (M * (q₀ : ℝ) / (R * Q ^ 2)) * ∑ t ∈ 𝒜, w (π t) t.2.2.1 :=
      (Finset.mul_sum ..).symm
    _ ≤ (M * (q₀ : ℝ) / (R * Q ^ 2)) *
        ((2 * C ^ 2 * R * U * Q / (q₀ : ℝ)) *
          (K * (Int.gcd (q₀ : ℤ) ℓ : ℝ) * N * V * x ^ (-2 * ε))) :=
      mul_le_mul_of_nonneg_left hfamily (by positivity)
    _ = (2 * C ^ 2 * K * M * N * (Int.gcd (q₀ : ℤ) ℓ : ℝ)) *
        ((U * V) / Q) * x ^ (-2 * ε) := by
      field_simp [hR.ne', hQ.ne', hqpos.ne']
    _ ≤ (2 * C ^ 2 * K * M * N * (Int.gcd (q₀ : ℤ) ℓ : ℝ)) *
        (C / (q₀ : ℝ)) * x ^ (-ε / 4) := by
      apply mul_le_mul _ hpow (Real.rpow_nonneg hxpos.le _) (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        (U * V) / Q ≤ (C * Q / (q₀ : ℝ)) / Q :=
          div_le_div_of_nonneg_right hUV hQ.le
        _ = C / (q₀ : ℝ) := by field_simp [hQ.ne', hqpos.ne']
    _ = _ := by ring

#print axioms sourceTheta_near_typeII_uniform_power_saving
#print axioms sourceTheta_split_typeI_uniform_power_saving
#print axioms sourceHighGamma_near_uniform_band
#print axioms sourceHighGamma_split_uniform_band

end PrimeGap182Audit
