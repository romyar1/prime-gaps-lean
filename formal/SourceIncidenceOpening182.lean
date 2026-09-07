import SourceIncidenceSelected182
import SourceIncidenceGamma182

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
theorem opening_incidence_uniform_band
    («ω» δ ε γlo γhi C cM TM cN TN : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ) (hε : 0 < ε)
    (hωsmall : «ω» < 1 / 16) (hδsmall : δ < 1 / 8) (hεsmall : ε < 1 / 1000)
    (hγmin : 1 / 4 + 4 * «ω» + δ + 100 * ε ≤ γlo)
    (hγsource : 8 * «ω» + 2 * δ + 100 * ε ≤ γlo)
    (hγmax : γhi ≤ 1 / 2 - 2 * «ω» - 50 * ε)
    (hsecondary : IncidenceSecondaryEstimate «ω» δ ε γlo γhi)
    (hC : 1 ≤ C) (hcM : 0 < cM) (hMT : cM ≤ TM)
    (hcN : 0 < cN) (hNT : cN ≤ TN)
    (dβ : ℕ) (Eβ : ℝ) (CM CN : ℕ → ℝ)
    (henvelopes : ∀ j : ℕ, 0 ≤ CM j ∧ 0 ≤ CN j)
    (ψM ψN : ℝ → ℝ) (hψM : ContDiff ℝ ∞ ψM) (hψN : ContDiff ℝ ∞ ψN)
    (hsupportM : Function.support ψM ⊆ Set.Icc cM TM)
    (hsupportN : Function.support ψN ⊆ Set.Icc cN TN)
    (hnonneg : ∀ t : ℝ, 0 ≤ ψM t ∧ 0 ≤ ψN t)
    (hderivatives : ∀ (j : ℕ) (t : ℝ),
      |iteratedDeriv j ψM t| ≤ CM j ∧ |iteratedDeriv j ψN t| ≤ CN j) :
    ∃ K X₀ : ℝ, 0 < K ∧ Real.exp 1 ≤ X₀ ∧
      ∀ x : ℝ, X₀ ≤ x →
      ∀ q₀ : ℕ, 0 < q₀ → Squarefree q₀ →
      ∀ a b₁ b₂ : ℕ, Nat.Coprime (a * b₁ * b₂) q₀ →
      ∀ (ℓ : ℤ) (M N R Q U V H Hstar γ : ℝ),
      0 < M → 0 < N → 0 < R → 0 < Q → 0 < U → 0 < V →
      x / C ≤ M * N → M * N ≤ C * x → N = x ^ γ →
      γlo ≤ γ →
      γ ≤ γhi →
      N ≤ C * x ^ (δ + 4 * ε) * R →
      R ≤ C * x ^ (-2 * ε) * N →
      x ^ (1 / 2 - ε) ≤ C * R * Q →
      R * Q ≤ C * x ^ (1 / 2 + 2 * «ω» + ε) → N ≤ x →
      H = x ^ ε * R * Q ^ 2 / ((q₀ : ℝ) * M) → 1 ≤ H →
      x ^ (-δ - 5 * ε) * Q / ((q₀ : ℝ) * H) ≤ C * U →
      U ≤ C * x ^ (-5 * ε) * Q / H →
      x ^ (5 * ε) * H / (q₀ : ℝ) ≤ C * V →
      V ≤ C * x ^ (δ + 5 * ε) * H →
      Q / (q₀ : ℝ) ≤ C * U * V → U * V ≤ C * Q / (q₀ : ℝ) →
      (q₀ : ℝ) ≤ C * Q →
      (∀ p ∈ q₀.primeFactors,
        Real.exp ((Real.log x) ^ (1 / 3 : ℝ)) < (p : ℝ)) →
      ℓ ≠ 0 → |(ℓ : ℝ)| ≤ C * N / R →
      Hstar ≠ 0 → 1 ≤ C * |Hstar| → |Hstar| ≤ C * H →
      ∀ β : ℕ →₀ ℂ,
      (∀ n ∈ β.support, 0 < n ∧ (n : ℝ) ≤ TN * N ∧
        ‖β n‖ ≤ C * (n.divisors.card : ℝ) ^ dβ * (Real.log x) ^ Eβ ∧
        1 ≤ ψN ((n : ℝ) / N)) →
      ∀ (c : ℕ × ℕ → ℂ) (𝒜 : Finset (ℕ × ℕ × ℕ × ℕ)),
      (∀ t ∈ 𝒜,
        0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.1 ∧ 0 < t.2.2.2 ∧
        R ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) ≤ 2 * R ∧
        U / C ≤ (t.2.1 : ℝ) ∧ (t.2.1 : ℝ) ≤ C * U ∧
        V / C ≤ (t.2.2.1 : ℝ) ∧ (t.2.2.1 : ℝ) ≤ C * V ∧
        Q / (C * (q₀ : ℝ)) ≤ (t.2.2.2 : ℝ) ∧
        (t.2.2.2 : ℝ) ≤ C * Q / (q₀ : ℝ) ∧
        Q ≤ ((q₀ * t.2.1 * t.2.2.1 : ℕ) : ℝ) ∧
        Q ≤ ((q₀ * t.2.2.2 : ℕ) : ℝ) ∧
        Nonempty (DenseDivisibilityWitness
          ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩ 1 t.1) ∧
        Squarefree (t.1 * q₀ * t.2.1 * t.2.2.1 * t.2.2.2) ∧
        Nat.Coprime (a * b₁ * b₂) (t.1 * q₀ * t.2.1 * t.2.2.1 * t.2.2.2)) →
      (∀ t ∈ 𝒜,
        ‖c (q₀ * t.2.1 * t.2.2.1, t.1)‖ ≤ 1 ∧
        ‖c (q₀ * t.2.2.2, t.1)‖ ≤ 1) →
      let Hbound : ℕ := ⌊2 * |Hstar|⌋₊
      let J : Finset ℤ :=
        (Finset.Icc (-(Hbound : ℤ)) (Hbound : ℤ)).filter
          (fun h => 1 ≤ (h : ℝ) / Hstar ∧ (h : ℝ) / Hstar < 2)
      let γβ : ℤ →₀ ℂ := Finsupp.embDomain (Nat.castEmbedding : ℕ ↪ ℤ) β
      let P : (ℕ × ℕ × ℕ × ℕ) → ℕ := fun t =>
        t.1 * q₀ * t.2.1 * t.2.2.1 * t.2.2.2
      (∑ t ∈ 𝒜,
        ‖c (q₀ * t.2.1 * t.2.2.1, t.1) *
          star (c (q₀ * t.2.2.2, t.1)) * ((M : ℂ) / (P t : ℂ)) *
            ∑ n ∈ γβ.support.filter (fun n =>
              Int.gcd n ((t.1 * q₀ * t.2.1 * t.2.2.1 : ℕ) : ℤ) = 1 ∧
              Int.gcd (n + ℓ * (t.1 : ℤ)) ((q₀ * t.2.2.2 : ℕ) : ℤ) = 1),
              γβ n * star (γβ (n + ℓ * (t.1 : ℤ))) *
                (sourceCompatibility t.1 q₀ b₁ b₂ ℓ n : ℂ) *
                  ∑ h ∈ J, sourcePhi ψM M (P t) h *
                    sourceTheta t.1 q₀ t.2.1 t.2.2.1 t.2.2.2
                      a b₁ b₂ ℓ n h‖) ≤
        K * M * N * (Int.gcd (q₀ : ℤ) ℓ : ℝ) / (q₀ : ℝ) *
          x ^ (-3 * ε / 2) := by
  let CSigma : ℝ := max 2 C
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hCCSigma : C ≤ CSigma := le_max_right _ _
  have htwoCSigma : 2 ≤ CSigma := le_max_left _ _
  have hCSigmaone : 1 ≤ CSigma := hC.trans hCCSigma
  have hCSigmapos : 0 < CSigma := hCpos.trans_le hCCSigma
  have hTNpos : 0 < TN := hcN.trans_le hNT
  obtain ⟨KSigma, XSigma, hKSigma, hXSigma, hSigma⟩ :=
    sourceSigmaOne_selected_family_bound_of_incidence «ω» δ ε γlo γhi CSigma cM TM cN TN
      hω hδ hε hωsmall hδsmall hεsmall hγsource
      (by linarith only [hγmax, hω, hε]) hsecondary hCSigmaone hcM hMT hcN hNT
      CM (fun _ => 0) CN (fun _ => 0) henvelopes
  obtain ⟨XΓ, hGamma⟩ := Filter.eventually_atTop.mp
    (sourceGamma_incidence_subpower_bound dβ Eβ 1 ε C TN CSigma C C (1 / C) (1 / C)
      C «ω» δ ε (by norm_num) hε hCpos.le hTNpos hCSigmapos hCpos hCpos
      (div_pos zero_lt_one hCpos) (div_pos zero_lt_one hCpos) hCpos hω hδ hε)
  refine ⟨C * Real.sqrt KSigma + 1, max XSigma XΓ, ?_, hXSigma.trans (le_max_left _ _), ?_⟩
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hCpos.le (Real.sqrt_nonneg KSigma)) zero_lt_one
  intro x hx q₀ hq₀ hq₀sf a b₁ b₂ hprimitive ℓ M N R Q U V H Hstar γ
    hM hN hR hQ hU hV hMNlo hMNhi hNγ hγlo hγhi hNR hRN hRQlo hRQhi hNx
    hHdef hHone hUlo hUhi hVlo hVhi hUVlo hUVhi hq₀Q hrough hℓ hℓbound
    hHstar hHstarlo hHstarhi β hβ c 𝒜 h𝒜 hc Hbound J γβ P
  have hxSigma : XSigma ≤ x := (le_max_left _ _).trans hx
  have hxΓ : XΓ ≤ x := (le_max_right _ _).trans hx
  have hxe : Real.exp 1 ≤ x := hXSigma.trans hxSigma
  have hxone : 1 ≤ x := (Real.one_le_exp zero_le_one).trans hxe
  have hxpos : 0 < x := zero_lt_one.trans_le hxone
  have hqreal : 0 < (q₀ : ℝ) := by exact_mod_cast hq₀
  have hHpos : 0 < H := zero_lt_one.trans_le hHone
  have hp (a : ℝ) : 0 < x ^ a := Real.rpow_pos_of_pos hxpos a
  have hb₁ : Nat.Coprime b₁ q₀ :=
    (Nat.coprime_mul_iff_left.mp (Nat.coprime_mul_iff_left.mp hprimitive).1).2
  have hIntPrimitive : Int.gcd ((a : ℤ) * b₁ * b₂) (q₀ : ℤ) = 1 := by
    have hh : Int.gcd ((a * b₁ * b₂ : ℕ) : ℤ) (q₀ : ℤ) = 1 := by
      rw [Int.gcd_natCast_natCast]
      exact hprimitive
    simpa only [Nat.cast_mul] using hh
  have hNlower : x ^ (1 / 4 + 4 * «ω» + δ + 100 * ε) ≤ N := by
    rw [hNγ]
    exact Real.rpow_le_rpow_of_exponent_le hxone (hγmin.trans hγlo)
  have hRlower : (1 / C) * x ^ (-δ - 4 * ε) * N ≤ R := by
    calc
      (1 / C) * x ^ (-δ - 4 * ε) * N ≤
          ((1 / C) * x ^ (-δ - 4 * ε)) * (C * x ^ (δ + 4 * ε) * R) :=
        mul_le_mul_of_nonneg_left hNR (by positivity)
      _ = R := by
        rw [show -δ - 4 * ε = -(δ + 4 * ε) by ring, Real.rpow_neg hxpos.le]
        field_simp [hCpos.ne', (hp (δ + 4 * ε)).ne']
  have hGammaFamily : ∀ t ∈ 𝒜,
      0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.2 ∧ Nat.Coprime t.1 q₀ ∧
      (t.1 : ℝ) ≤ CSigma * R ∧ (t.2.1 : ℝ) ≤ C * U ∧
      ((q₀ * t.2.2.2 : ℕ) : ℝ) ≤ C * Q := by
    intro t ht
    obtain ⟨hr, hu, _, hq₂, _, hrhi, _, huhi, _, _, _, hq₂hi,
      _, _, _, hsf, _⟩ := h𝒜 t ht
    have hrq₀ : Nat.Coprime t.1 q₀ :=
      Nat.coprime_of_squarefree_mul hsf.of_mul_left.of_mul_left.of_mul_left
    refine ⟨hr, hu, hq₂, hrq₀,
      hrhi.trans (mul_le_mul_of_nonneg_right htwoCSigma hR.le), huhi, ?_⟩
    have hh := (le_div_iff₀ hqreal).1 hq₂hi
    simpa only [Nat.cast_mul, mul_comm] using hh
  have hΓ := (hGamma x hxΓ 𝒜 β q₀ b₁ b₂ ℓ M N R Q U hq₀ hb₁
    hM hN hR hQ hU (by simpa only [Real.rpow_one] using hNx) hNlower
    (by simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hMNlo)
    hRlower hRQhi (by simpa only [← hHdef] using hHone)
    (fun n hn => ⟨(hβ n hn).1, (hβ n hn).2.1⟩)
    (fun n hn => (hβ n hn).2.2.1) hGammaFamily).2
  let Ω := (𝒜 ×ˢ 𝒜).filter (fun p =>
    p.2.1 = p.1.1 ∧ p.2.2.1 = p.1.2.1 ∧ p.2.2.2.2 = p.1.2.2.2)
  let 𝒯 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := Ω.image (fun p =>
    (p.1.1, p.1.2.1, p.1.2.2.1, p.2.2.2.1, p.1.2.2.2))
  have hTFamily : ∀ t ∈ 𝒯,
      0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.1 ∧ 0 < t.2.2.2.1 ∧ 0 < t.2.2.2.2 ∧
      R / CSigma ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) ≤ CSigma * R ∧
      U / CSigma ≤ (t.2.1 : ℝ) ∧ (t.2.1 : ℝ) ≤ CSigma * U ∧
      V / CSigma ≤ (t.2.2.1 : ℝ) ∧ (t.2.2.1 : ℝ) ≤ CSigma * V ∧
      V / CSigma ≤ (t.2.2.2.1 : ℝ) ∧ (t.2.2.2.1 : ℝ) ≤ CSigma * V ∧
      Q / (CSigma * (q₀ : ℝ)) ≤ (t.2.2.2.2 : ℝ) ∧
      (t.2.2.2.2 : ℝ) ≤ CSigma * Q / (q₀ : ℝ) ∧
      Nonempty (DenseDivisibilityWitness
        ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩ 1 t.1) ∧
      Squarefree (t.1 * q₀ * t.2.1 * t.2.2.1 * t.2.2.2.2) ∧
      Squarefree (t.1 * q₀ * t.2.1 * t.2.2.2.1 * t.2.2.2.2) ∧
      Int.gcd ((a : ℤ) * b₁ * b₂)
        ((t.1 * q₀ * t.2.1 * t.2.2.1 * t.2.2.2.1 * t.2.2.2.2 : ℕ) : ℤ) = 1 := by
    clear * - h𝒜 hCpos hCSigmaone htwoCSigma hCCSigma hR hU hV hQ hqreal
    intro t ht
    obtain ⟨p, hpΩ, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hpA, hpEq⟩ := Finset.mem_filter.mp hpΩ
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hpA
    rcases p with ⟨⟨r, u, v₁, q₂⟩, ⟨s, w, v₂, z⟩⟩
    change s = r ∧ w = u ∧ z = q₂ at hpEq
    rcases hpEq with ⟨hs, hw, hz⟩
    subst s
    subst w
    subst z
    obtain ⟨hr, hu, hv₁, hq₂, hrlo, hrhi, hulo, huhi, hv₁lo, hv₁hi,
      hq₂lo, hq₂hi, _, _, hdense, hsf₁, hprimitive₁⟩ := h𝒜 _ hp₁
    obtain ⟨_, _, hv₂, _, _, _, _, _, hv₂lo, hv₂hi, _, _, _, _, _,
      hsf₂, hprimitive₂⟩ := h𝒜 _ hp₂
    have hprimitiveV₂ : Nat.Coprime (a * b₁ * b₂) v₂ :=
      hprimitive₂.of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left v₂ (r * q₀ * u)) q₂)
    have hfull : Nat.Coprime (a * b₁ * b₂) (r * q₀ * u * v₁ * v₂ * q₂) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        hprimitive₁.mul_right hprimitiveV₂
    have hfullInt : Int.gcd ((a : ℤ) * b₁ * b₂)
        ((r * q₀ * u * v₁ * v₂ * q₂ : ℕ) : ℤ) = 1 := by
      have hh : Int.gcd ((a * b₁ * b₂ : ℕ) : ℤ)
          ((r * q₀ * u * v₁ * v₂ * q₂ : ℕ) : ℤ) = 1 := by
        rw [Int.gcd_natCast_natCast]
        exact hfull
      simpa only [Nat.cast_mul] using hh
    refine ⟨hr, hu, hv₁, hv₂, hq₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hdense, hsf₁, hsf₂, hfullInt⟩
    · exact (div_le_self hR.le hCSigmaone).trans hrlo
    · exact hrhi.trans (mul_le_mul_of_nonneg_right htwoCSigma hR.le)
    · exact (div_le_div_of_nonneg_left hU.le hCpos hCCSigma).trans hulo
    · exact huhi.trans (mul_le_mul_of_nonneg_right hCCSigma hU.le)
    · exact (div_le_div_of_nonneg_left hV.le hCpos hCCSigma).trans hv₁lo
    · exact hv₁hi.trans (mul_le_mul_of_nonneg_right hCCSigma hV.le)
    · exact (div_le_div_of_nonneg_left hV.le hCpos hCCSigma).trans hv₂lo
    · exact hv₂hi.trans (mul_le_mul_of_nonneg_right hCCSigma hV.le)
    · exact (div_le_div_of_nonneg_left hQ.le (mul_pos hCpos hqreal)
        (mul_le_mul_of_nonneg_right hCCSigma hqreal.le)).trans hq₂lo
    · exact hq₂hi.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCCSigma hQ.le) hqreal.le)
  have hMNloSigma : x / CSigma ≤ M * N :=
    (div_le_div_of_nonneg_left hxpos.le hCpos hCCSigma).trans hMNlo
  have hMNhiSigma : M * N ≤ CSigma * x :=
    hMNhi.trans (mul_le_mul_of_nonneg_right hCCSigma hxpos.le)
  have hNRSigma : N ≤ CSigma * x ^ (δ + 4 * ε) * R :=
    hNR.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCCSigma (hp (δ + 4 * ε)).le) hR.le)
  have hRNSigma : R ≤ CSigma * x ^ (-2 * ε) * N :=
    hRN.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCCSigma (hp (-2 * ε)).le) hN.le)
  have hRQloSigma : x ^ (1 / 2 - ε) ≤ CSigma * R * Q :=
    hRQlo.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCCSigma hR.le) hQ.le)
  have hRQhiSigma : R * Q ≤ CSigma * x ^ (1 / 2 + 2 * «ω» + ε) :=
    hRQhi.trans (mul_le_mul_of_nonneg_right hCCSigma (hp (1 / 2 + 2 * «ω» + ε)).le)
  have hUloSigma : x ^ (-δ - 5 * ε) * Q / ((q₀ : ℝ) * H) ≤ CSigma * U :=
    hUlo.trans (mul_le_mul_of_nonneg_right hCCSigma hU.le)
  have hUhiSigma : U ≤ CSigma * x ^ (-5 * ε) * Q / H :=
    hUhi.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCCSigma (hp (-5 * ε)).le) hQ.le) hHpos.le)
  have hVloSigma : x ^ (5 * ε) * H / (q₀ : ℝ) ≤ CSigma * V :=
    hVlo.trans (mul_le_mul_of_nonneg_right hCCSigma hV.le)
  have hVhiSigma : V ≤ CSigma * x ^ (δ + 5 * ε) * H :=
    hVhi.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCCSigma (hp (δ + 5 * ε)).le) hHpos.le)
  have hUVloSigma : Q / (q₀ : ℝ) ≤ CSigma * U * V :=
    hUVlo.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCCSigma hU.le) hV.le)
  have hUVhiSigma : U * V ≤ CSigma * Q / (q₀ : ℝ) :=
    hUVhi.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCCSigma hQ.le) hqreal.le)
  have hq₀QSigma : (q₀ : ℝ) ≤ CSigma * Q :=
    hq₀Q.trans (mul_le_mul_of_nonneg_right hCCSigma hQ.le)
  have hℓboundSigma : |(ℓ : ℝ)| ≤ CSigma * N / R :=
    hℓbound.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCCSigma hN.le) hR.le)
  have hHstarloSigma : 1 ≤ CSigma * |Hstar| :=
    hHstarlo.trans (mul_le_mul_of_nonneg_right hCCSigma (abs_nonneg Hstar))
  have hHstarhiSigma : |Hstar| ≤ CSigma * H :=
    hHstarhi.trans (mul_le_mul_of_nonneg_right hCCSigma hHpos.le)
  have hSigma := hSigma x hxSigma q₀ hq₀ hq₀sf (a : ℤ) (b₁ : ℤ) (b₂ : ℤ) ℓ
    hIntPrimitive M N R Q U V H Hstar γ hM hN hR hQ hU hV
    hMNloSigma hMNhiSigma hNγ hγlo hγhi hNRSigma hRNSigma hRQloSigma hRQhiSigma hHdef hHone
    hUloSigma hUhiSigma hVloSigma hVhiSigma hUVloSigma hUVhiSigma hq₀QSigma hrough hℓ hℓboundSigma
    hHstar hHstarloSigma hHstarhiSigma ψM ψN hψM hψN hsupportM hsupportN hnonneg
    (by intro j t; simpa only [Real.rpow_zero, mul_one] using hderivatives j t)
    𝒯 hTFamily
  have hBasicFamily : ∀ t ∈ 𝒜,
      0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.1 ∧ 0 < t.2.2.2 ∧
      R ≤ (t.1 : ℝ) ∧ Q ≤ ((q₀ * t.2.1 * t.2.2.1 : ℕ) : ℝ) ∧
      Q ≤ ((q₀ * t.2.2.2 : ℕ) : ℝ) := by
    intro t ht
    obtain ⟨hr, hu, hv, hq₂, hrlo, _, _, _, _, _, _, _, hq₁, hq₂orig,
      _, _, _⟩ := h𝒜 t ht
    exact ⟨hr, hu, hv, hq₂, hrlo, hq₁, hq₂orig⟩
  have hBound := opening_band_cauchy 𝒜 β c q₀ a b₁ b₂ ℓ J ψM ψN
    C KSigma x ε cN TN M N R Q U V hq₀ hCpos.le hKSigma.le hxpos hcN hNT
    hM hN hR hQ hU.le hV.le hUVhi hsupportN (fun t => (hnonneg t).2)
    (fun n hn => (hβ n hn).2.2.2) hBasicFamily hc hΓ hSigma
  apply hBound.trans
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hM.le)
          hN.le) (Nat.cast_nonneg _)) hqreal.le)
    (Real.rpow_nonneg hxpos.le _)

#print axioms opening_incidence_uniform_band
end PrimeGap182Audit
