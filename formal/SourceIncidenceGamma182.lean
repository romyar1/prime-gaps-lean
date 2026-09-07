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
theorem sourceGamma_incidence_subpower_bound
    (d : ℕ) (E κ η B₀ Cβ Cr Cu Cq cMN cR CRQ «ω» δ ε : ℝ)
    (hκ : 0 ≤ κ) (hη : 0 < η) (hB₀ : 0 ≤ B₀)
    (hCβ : 0 < Cβ) (hCr : 0 < Cr) (hCu : 0 < Cu) (hCq : 0 < Cq)
    (hcMN : 0 < cMN) (hcR : 0 < cR) (hCRQ : 0 < CRQ)
    (_hω : 0 < «ω») (_hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in Filter.atTop,
      ∀ (𝒜 : Finset (ℕ × ℕ × ℕ × ℕ)) (β : ℕ →₀ ℂ)
        (q₀ b₁ b₂ : ℕ) (ℓ : ℤ) (M N R Q U : ℝ),
        0 < q₀ → Nat.Coprime b₁ q₀ →
        0 < M → 0 < N → 0 < R → 0 < Q → 0 < U →
        N ≤ x ^ κ →
        x ^ ((1 : ℝ) / 4 + 4 * «ω» + δ + 100 * ε) ≤ N →
        cMN * x ≤ M * N →
        cR * x ^ (-δ - 4 * ε) * N ≤ R →
        R * Q ≤ CRQ * x ^ ((1 : ℝ) / 2 + 2 * «ω» + ε) →
        1 ≤ x ^ ε * R * Q ^ 2 / ((q₀ : ℝ) * M) →
        (∀ n ∈ β.support, 0 < n ∧ (n : ℝ) ≤ Cβ * N) →
        (∀ n ∈ β.support,
          ‖β n‖ ≤ B₀ * (n.divisors.card : ℝ) ^ d * (Real.log x) ^ E) →
        (∀ t ∈ 𝒜,
          0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.2 ∧
          Nat.Coprime t.1 q₀ ∧
          (t.1 : ℝ) ≤ Cr * R ∧ (t.2.1 : ℝ) ≤ Cu * U ∧
          ((q₀ * t.2.2.2 : ℕ) : ℝ) ≤ Cq * Q) →
        let γ : ℤ →₀ ℂ := Finsupp.embDomain (Nat.castEmbedding : ℕ ↪ ℤ) β
        let B : Finset (ℕ × ℕ × ℕ) := 𝒜.image (fun t => (t.1, t.2.1, t.2.2.2))
        let Γ : ℝ := ∑ t ∈ B, ∑ n ∈ γ.support,
          if Int.gcd n ((t.1 * q₀ * t.2.1 : ℕ) : ℤ) = 1 ∧
              Int.gcd (n + ℓ * (t.1 : ℤ)) ((q₀ * t.2.2 : ℕ) : ℤ) = 1
          then sourceCompatibility t.1 q₀ b₁ b₂ ℓ n *
            ‖γ n * star (γ (n + ℓ * (t.1 : ℤ)))‖ ^ 2
          else 0
        x ^ ((1 : ℝ) / 8) ≤ N / (q₀ : ℝ) ∧
          Γ ≤ x ^ η * (Int.gcd (q₀ : ℤ) ℓ : ℝ) * R * Q * U * N / (q₀ : ℝ) ^ 2 := by
  let ρ : ℝ := η / (8 * (κ + 1))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hκρ : κ * ρ ≤ η / 8 := by
    have hidentity : ρ * (8 * (κ + 1)) = η := by
      dsimp [ρ]
      exact div_mul_cancel₀ η (by positivity)
    nlinarith
  obtain ⟨D, hD, hdivisor⟩ := exists_divisorPower_bound d hρ
  let L : ℝ := B₀ * D * Cβ ^ ρ
  let J : ℝ := Cr * Cu * Cq * (1 + Cβ) * L ^ 4
  let K : ℝ := CRQ ^ 2 / (cR * cMN)
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hJ : 0 ≤ J := by
    dsimp [J]
    positivity
  have hsmall : ∀ᶠ x : ℝ in Filter.atTop,
      ‖J * (Real.log x) ^ (4 * E)‖ ≤ ‖x ^ (η / 2)‖ := by
    simpa only [one_mul] using
      ((isLittleO_log_rpow_rpow_atTop (4 * E)
        (by positivity : 0 < η / 2)).const_mul_left J).bound
          (show (0 : ℝ) < 1 by norm_num)
  have hlarge : ∀ᶠ x : ℝ in Filter.atTop, K ≤ x ^ ((1 : ℝ) / 8) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).eventually_ge_atTop K
  filter_upwards [hsmall, hlarge, Filter.eventually_ge_atTop (Real.exp 1)]
    with x hxsmall hxlarge hx
  intro 𝒜 β q₀ b₁ b₂ ℓ M N R Q U hq₀ hb₁ hM hN hR hQ hU
    hNupper hNlower hMN hRlower hRQ hH hsupport hβ h𝒜
  let : NeZero q₀ := ⟨ne_of_gt hq₀⟩
  have hqreal : (0 : ℝ) < q₀ := Nat.cast_pos.mpr hq₀
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hxone : 1 ≤ x := (Real.one_le_exp zero_le_one).trans hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hxone
  let s : ℝ := 4 * «ω» + δ + 7 * ε
  have hMRlower : cR * cMN * x ^ (1 - δ - 4 * ε) ≤ M * R := by
    calc
      _ = cR * x ^ (-δ - 4 * ε) * (cMN * x) := by
        rw [show (1 - δ - 4 * ε : ℝ) = (-δ - 4 * ε) + 1 by ring,
          Real.rpow_add_one hxpos.ne']
        ring
      _ ≤ cR * x ^ (-δ - 4 * ε) * (M * N) :=
        mul_le_mul_of_nonneg_left hMN
          (mul_nonneg hcR.le (Real.rpow_nonneg hxpos.le _))
      _ = M * (cR * x ^ (-δ - 4 * ε) * N) := by ring
      _ ≤ M * R := mul_le_mul_of_nonneg_left hRlower hM.le
  have hHmul : (q₀ : ℝ) * M ≤ x ^ ε * R * Q ^ 2 := by
    simpa only [one_mul] using (le_div_iff₀ (mul_pos hqreal hM)).mp hH
  have hMRupper :
      (q₀ : ℝ) * (M * R) ≤ CRQ ^ 2 * x ^ (1 + 4 * «ω» + 3 * ε) := by
    have hsquare : (R * Q) ^ 2 ≤
        (CRQ * x ^ ((1 : ℝ) / 2 + 2 * «ω» + ε)) ^ 2 :=
      (sq_le_sq₀ (mul_nonneg hR.le hQ.le)
        (mul_nonneg hCRQ.le (Real.rpow_nonneg hxpos.le _))).mpr hRQ
    calc
      _ = ((q₀ : ℝ) * M) * R := by ring
      _ ≤ (x ^ ε * R * Q ^ 2) * R :=
        mul_le_mul_of_nonneg_right hHmul hR.le
      _ = x ^ ε * (R * Q) ^ 2 := by ring
      _ ≤ x ^ ε * (CRQ * x ^ ((1 : ℝ) / 2 + 2 * «ω» + ε)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare (Real.rpow_nonneg hxpos.le _)
      _ = CRQ ^ 2 *
          (x ^ ε * x ^ (((1 : ℝ) / 2 + 2 * «ω» + ε) * 2)) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hxpos.le]
        ring_nf
      _ = _ := by
        rw [← Real.rpow_add hxpos]
        congr 2
        ring
  have hqbound : (q₀ : ℝ) ≤ K * x ^ s := by
    have hden : 0 < cR * cMN * x ^ (1 - δ - 4 * ε) := by positivity
    have hcombined :
        (q₀ : ℝ) * (cR * cMN * x ^ (1 - δ - 4 * ε)) ≤
          CRQ ^ 2 * x ^ (1 + 4 * «ω» + 3 * ε) :=
      (mul_le_mul_of_nonneg_left hMRlower hqreal.le).trans hMRupper
    calc
      _ ≤ (CRQ ^ 2 * x ^ (1 + 4 * «ω» + 3 * ε)) /
          (cR * cMN * x ^ (1 - δ - 4 * ε)) :=
        (le_div_iff₀ hden).mpr hcombined
      _ = K * x ^ s := by
        dsimp [K, s]
        rw [mul_div_mul_comm, ← Real.rpow_sub hxpos]
        congr 2
        ring
  have hscale : x ^ ((1 : ℝ) / 8) ≤ N / (q₀ : ℝ) := by
    apply (le_div_iff₀ hqreal).mpr
    calc
      _ ≤ x ^ ((1 : ℝ) / 8) * (K * x ^ s) :=
        mul_le_mul_of_nonneg_left hqbound (Real.rpow_nonneg hxpos.le _)
      _ ≤ x ^ ((1 : ℝ) / 8) * (x ^ ((1 : ℝ) / 8) * x ^ s) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hxlarge (Real.rpow_nonneg hxpos.le _))
          (Real.rpow_nonneg hxpos.le _)
      _ = x ^ ((1 : ℝ) / 4 + s) := by
        rw [← mul_assoc, ← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
        congr 1
        ring
      _ ≤ x ^ ((1 : ℝ) / 4 + 4 * «ω» + δ + 100 * ε) :=
        Real.rpow_le_rpow_of_exponent_le hxone (by dsimp [s]; linarith)
      _ ≤ N := hNlower
  have hratio : 1 ≤ N / (q₀ : ℝ) :=
    (Real.one_le_rpow hxone (by norm_num : (0 : ℝ) ≤ 1 / 8)).trans hscale
  refine ⟨hscale, ?_⟩
  let T : ℕ := ⌊Cβ * N⌋₊
  let W : ℝ := L * x ^ (η / 8) * (Real.log x) ^ E
  let B : Finset (ℕ × ℕ × ℕ) := 𝒜.image (fun t => (t.1, t.2.1, t.2.2.2))
  let g : ℝ := (Int.gcd (q₀ : ℤ) ℓ : ℝ)
  let P : ℝ := g * R * Q * U * N / (q₀ : ℝ) ^ 2
  have hg : 0 ≤ g := Nat.cast_nonneg _
  have hP : 0 ≤ P := by
    dsimp [P]
    positivity
  have hW : 0 ≤ W :=
    mul_nonneg (mul_nonneg hL (Real.rpow_nonneg hxpos.le _))
      (Real.rpow_nonneg hlog E)
  have hT : (T : ℝ) ≤ Cβ * N := Nat.floor_le (mul_nonneg hCβ.le hN.le)
  have hsupportT : β.support ⊆ Finset.Icc 1 T := by
    intro n hn
    obtain ⟨hnpos, hnupper⟩ := hsupport n hn
    exact Finset.mem_Icc.mpr ⟨hnpos, Nat.le_floor hnupper⟩
  have hβW : ∀ n ∈ β.support, ‖β n‖ ≤ W := by
    intro n hn
    obtain ⟨hnpos, hnupper⟩ := hsupport n hn
    have hnscale : (n : ℝ) ≤ Cβ * x ^ κ :=
      hnupper.trans (mul_le_mul_of_nonneg_left hNupper hCβ.le)
    have hdiv : (n.divisors.card : ℝ) ^ d ≤ D * Cβ ^ ρ * x ^ (η / 8) := by
      calc
        _ ≤ D * (n : ℝ) ^ ρ := hdivisor n (ne_of_gt hnpos)
        _ ≤ D * (Cβ * x ^ κ) ^ ρ :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Nat.cast_nonneg n) hnscale hρ.le) hD.le
        _ = D * Cβ ^ ρ * x ^ (κ * ρ) := by
          rw [Real.mul_rpow hCβ.le (Real.rpow_nonneg hxpos.le κ),
            ← Real.rpow_mul hxpos.le κ ρ]
          ring
        _ ≤ D * Cβ ^ ρ * x ^ (η / 8) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hxone hκρ)
            (mul_nonneg hD.le (Real.rpow_nonneg hCβ.le ρ))
    calc
      _ ≤ B₀ * (n.divisors.card : ℝ) ^ d * (Real.log x) ^ E := hβ n hn
      _ ≤ B₀ * (D * Cβ ^ ρ * x ^ (η / 8)) * (Real.log x) ^ E :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv hB₀)
          (Real.rpow_nonneg hlog E)
      _ = W := by
        dsimp [W, L]
        ring
  let rCap : ℕ := ⌊Cr * R⌋₊
  let uCap : ℕ := ⌊Cu * U⌋₊
  let qCap : ℕ := ⌊Cq * Q / (q₀ : ℝ)⌋₊
  have hbase : B ⊆ (Finset.Icc 1 rCap).product
      ((Finset.Icc 1 uCap).product (Finset.Icc 1 qCap)) := by
    intro t ht
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hrpos, hupos, hqpos, _hcop, hrbound, hubound, hqbound⟩ := h𝒜 a ha
    have hqbound' : (a.2.2.2 : ℝ) ≤ Cq * Q / (q₀ : ℝ) := by
      apply (le_div_iff₀ hqreal).mpr
      simpa only [Nat.cast_mul, mul_comm] using hqbound
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hrpos, Nat.le_floor hrbound⟩,
        Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨hupos, Nat.le_floor hubound⟩,
            Finset.mem_Icc.mpr ⟨hqpos, Nat.le_floor hqbound'⟩⟩⟩
  have hcardNat : B.card ≤ rCap * (uCap * qCap) := by
    simpa using Finset.card_le_card hbase
  have hrCap : (rCap : ℝ) ≤ Cr * R := Nat.floor_le (mul_nonneg hCr.le hR.le)
  have huCap : (uCap : ℝ) ≤ Cu * U := Nat.floor_le (mul_nonneg hCu.le hU.le)
  have hqCap : (qCap : ℝ) ≤ Cq * Q / (q₀ : ℝ) :=
    Nat.floor_le (div_nonneg (mul_nonneg hCq.le hQ.le) hqreal.le)
  have hcard : (B.card : ℝ) ≤ Cr * Cu * Cq * R * U * Q / (q₀ : ℝ) := by
    calc
      _ ≤ (rCap : ℝ) * ((uCap : ℝ) * (qCap : ℝ)) := by exact_mod_cast hcardNat
      _ ≤ (Cr * R) * ((Cu * U) * (Cq * Q / (q₀ : ℝ))) :=
        mul_le_mul hrCap
          (mul_le_mul huCap hqCap (Nat.cast_nonneg qCap) (mul_nonneg hCu.le hU.le))
          (mul_nonneg (Nat.cast_nonneg uCap) (Nat.cast_nonneg qCap))
          (mul_nonneg hCr.le hR.le)
      _ = _ := by ring
  have hremainder :
      1 + (T : ℝ) / (q₀ : ℝ) ≤ (1 + Cβ) * N / (q₀ : ℝ) := by
    calc
      _ ≤ N / (q₀ : ℝ) + (Cβ * N) / (q₀ : ℝ) :=
        add_le_add hratio (div_le_div_of_nonneg_right hT hqreal.le)
      _ = _ := by ring
  have hfinite := sourceGamma_coefficient_moment_le 𝒜 β q₀ b₁ b₂ T ℓ W
    hW hb₁ (fun t ht => (h𝒜 t ht).2.2.2.1) hsupportT hβW
  have hWpower : W ^ 4 = L ^ 4 * x ^ (η / 2) * (Real.log x) ^ (4 * E) := by
    dsimp [W]
    rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hxpos.le,
      ← Real.rpow_mul_natCast hlog]
    simp only [Nat.cast_ofNat]
    rw [show η / 8 * (4 : ℝ) = η / 2 by ring, show E * (4 : ℝ) = 4 * E by ring]
  have htotal :
      (B.card : ℝ) * g * (1 + (T : ℝ) / (q₀ : ℝ)) * W ^ 4 ≤
        J * (Real.log x) ^ (4 * E) * x ^ (η / 2) * P := by
    calc
      _ ≤ (Cr * Cu * Cq * R * U * Q / (q₀ : ℝ)) * g *
          ((1 + Cβ) * N / (q₀ : ℝ)) * W ^ 4 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_right hcard hg) hremainder
            (by positivity) (by positivity)) (pow_nonneg hW 4)
      _ = _ := by
        rw [hWpower]
        dsimp [J, P]
        ring
  have hscalar : J * (Real.log x) ^ (4 * E) ≤ x ^ (η / 2) := by
    simpa only [Real.norm_of_nonneg
      (mul_nonneg hJ (Real.rpow_nonneg hlog (4 * E))),
      Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le (η / 2))] using hxsmall
  have hfinal :
      (B.card : ℝ) * g * (1 + (T : ℝ) / (q₀ : ℝ)) * W ^ 4 ≤
        x ^ η * g * R * Q * U * N / (q₀ : ℝ) ^ 2 := by
    calc
      _ ≤ J * (Real.log x) ^ (4 * E) * x ^ (η / 2) * P := htotal
      _ ≤ x ^ (η / 2) * x ^ (η / 2) * P :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hscalar (Real.rpow_nonneg hxpos.le _)) hP
      _ = _ := by
        rw [← Real.rpow_add hxpos, show η / 2 + η / 2 = η by ring]
        dsimp [P]
        ring
  exact hfinite.trans hfinal

#print axioms sourceGamma_incidence_subpower_bound
end PrimeGap182Audit
