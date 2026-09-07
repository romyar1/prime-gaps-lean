import SourceIncidenceOpening182
import SourceOpeningResources182
import SourceIncidenceDiagonal182

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
theorem sourceDeltaZero_rough_dyadic_uniform_log_saving_of_incidence
    («ω» δ ε γlo γhi C cM TM cN TN : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ) (hε : 0 < ε)
    (hωsmall : «ω» < 1 / 16) (hδsmall : δ < 1 / 8) (hεsmall : ε < 1 / 1000)
    (hγmin : 1 / 4 + 4 * «ω» + δ + 100 * ε ≤ γlo)
    (hγsource : 8 * «ω» + 2 * δ + 100 * ε ≤ γlo)
    (hγmax : γhi ≤ 1 / 2 - 2 * «ω» - 50 * ε)
    (hsecondary : IncidenceSecondaryEstimate «ω» δ ε γlo γhi)
    (hC : 1 ≤ C) (hcM : 0 < cM) (hMT : cM ≤ TM)
    (hcN : 0 < cN) (hNT : cN ≤ TN)
    (dα dβ : ℕ) (Eα Eβ A η : ℝ) (hA : 0 < A) (hη : 0 < η) :
    ∃ X₀ : ℝ, Real.exp 1 ≤ X₀ ∧
      ∀ (x : ℝ), X₀ ≤ x →
      ∀ (M N R Q γ : ℝ),
      0 < M → 0 < N → 0 < R → 0 < Q →
      x / C ≤ M * N → M * N ≤ C * x → N = x ^ γ →
      γlo ≤ γ →
      γ ≤ γhi →
      N ≤ C * x ^ (δ + 4 * ε) * R →
      R ≤ C * x ^ (-2 * ε) * N →
      x ^ (1 / 2 - ε) ≤ C * R * Q →
      R * Q ≤ C * x ^ (1 / 2 + 2 * «ω» + ε) →
      ∀ (α β : ℕ →₀ ℂ),
      (∀ n ∈ α.support,
        cM * M ≤ (n : ℝ) ∧ (n : ℝ) ≤ TM * M ∧
        ‖α n‖ ≤ C * (n.divisors.card : ℝ) ^ dα * (Real.log x) ^ Eα) →
      (∀ n ∈ β.support,
        cN * N ≤ (n : ℝ) ∧ (n : ℝ) ≤ TN * N ∧
        ‖β n‖ ≤ C * (n.divisors.card : ℝ) ^ dβ * (Real.log x) ^ Eβ) →
      ∀ (S : Finset (ℕ × ℕ)),
      (∀ p ∈ S,
        0 < p.1 ∧ 0 < p.2 ∧ Squarefree (p.1 * p.2) ∧
        Q ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * Q ∧
        R ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * R ∧
        Nonempty (DenseDivisibilityWitness
          ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩ 1 p.1) ∧
        Nonempty (DenseDivisibilityWitness
          ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩ 1 p.2) ∧
        (∀ t ∈ p.1.primeFactors,
          Real.exp ((Real.log x) ^ (1 / 3 : ℝ)) < (t : ℝ))) →
      ∀ (a b₁ b₂ : ℕ),
      (∀ p ∈ S, Nat.Coprime (a * b₁ * b₂) (p.1 * p.2)) →
      (∑ p ∈ S,
        ‖deltaZero (finiteConvolution α β) p.1 p.2 a b₁ b₂‖) ≤
          η * (M * N) * (Real.log x) ^ (-A)
:= by
  classical
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hTMpos : 0 < TM := hcM.trans_le hMT
  have hTNpos : 0 < TN := hcN.trans_le hNT
  have hεone : ε ≤ 1 := by linarith only [hεsmall]
  obtain ⟨ψM, hψM, hsM, hMnonneg, hMmajor, hMderivatives⟩ := opening_majorant cM TM hcM hMT
  obtain ⟨ψN, hψN, hsN, hNnonneg, hNmajor, hNderivatives⟩ := opening_majorant cN TN hcN hNT
  choose CM hCM hCMbound using hMderivatives
  choose CN hCN hCNbound using hNderivatives
  let C₀ : ℝ := 4 * (C + TM + TN + 1)
  have hC₀four : 4 ≤ C₀ := by dsimp only [C₀]; nlinarith
  have hC₀ : 1 ≤ C₀ := by linarith
  have hC₀pos : 0 < C₀ := zero_lt_one.trans_le hC₀
  have hCC₀ : C ≤ C₀ := by dsimp only [C₀]; nlinarith
  have hTN₀ : 2 * TN ≤ C₀ := by dsimp only [C₀]; nlinarith
  have hMinterval : cM / 2 ≤ 2 * TM := by linarith
  have hNinterval : cN / 2 ≤ 2 * TN := by linarith
  obtain ⟨Kband, Xband, hKband, hXband, hBandAt⟩ :=
    opening_incidence_uniform_band «ω» δ ε γlo γhi C₀ (cM / 2) (2 * TM) (cN / 2) (2 * TN)
      hω hδ hε hωsmall hδsmall hεsmall hγmin hγsource hγmax hsecondary hC₀ (by positivity) hMinterval (by positivity) hNinterval
      dβ Eβ CM CN (fun j => ⟨hCM j, hCN j⟩) ψM ψN hψM hψN hsM hsN
      (fun t => ⟨hMnonneg t, hNnonneg t⟩)
      (fun j t => ⟨by simpa only [Real.norm_eq_abs] using hCMbound j t,
        by simpa only [Real.norm_eq_abs] using hCNbound j t⟩)
  obtain ⟨Kα, Fα, hKα, hMomentAt⟩ := opening_moment dα Eα C TM hCpos.le hTMpos
  let D : ℝ := 2 * A + |Fα| + 2
  have hD : 0 < D := by dsimp only [D]; positivity
  let k : ℕ := Nat.ceil ((1 + ((2 * dβ + 5 : ℕ) : ℝ) * 2 + 2) / ε)
  let Ltail : ℝ := max (CM 0) (CM (k + 2))
  have hLtail : 0 ≤ Ltail := (hCM 0).trans (le_max_left _ _)
  have hTailAt := (opening_padded_truncation dβ Eβ 2 C ε 1
    (by norm_num) hCpos.le hε (by norm_num)).2
      (cM / 2) (2 * TM) Ltail 0 (by positivity) hMinterval hLtail
  let Lzero : ℝ := max (CM 0) (max (CM 1) (CM 2))
  have hLzero : 0 ≤ Lzero := (hCM 0).trans (le_max_left _ _)
  have hZeroAt := opening_zero_mode dβ Eβ C TN (2 * TM) Lzero ε D
    hCpos hTNpos (by positivity) hLzero hε ψM (hψM.of_le (by simp))
    (hsM.trans (Set.Icc_subset_Icc_left (by linarith))) (by
      intro t
      refine ⟨(by simpa only [iteratedDeriv_zero, Real.norm_eq_abs] using
        (hCMbound 0 t).trans (le_max_left _ _)), ?_, ?_⟩
      · simpa only [iteratedDeriv_one, Real.norm_eq_abs] using
          (hCMbound 1 t).trans ((le_max_left _ _).trans (le_max_right _ _))
      · simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero,
          Real.norm_eq_abs] using
          (hCMbound 2 t).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hDiagonalAt := mixedCorrelation_diagonal_incidence_scale_uniform dβ «ω» δ ε C₀
    (2 * TM) C (CM 0) Eβ 0 D hω hδ hε hC₀ (by positivity) hCpos.le (hCM 0) hD.le
  let Bcount : ℝ := 2 + 4 / Real.log 2
  have hBcount : 0 < Bcount := by
    dsimp only [Bcount]
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  let Koff : ℝ := 36 * Kband * Bcount ^ 2 * (2 * TN)
  have hKoff : 0 < Koff := by dsimp only [Koff]; positivity
  have hLogAbsorb (K E ρ : ℝ) (hρ : 0 < ρ) :
      ∀ᶠ x : ℝ in Filter.atTop, K * (Real.log x) ^ E ≤ x ^ ρ := by
    clear * - hρ
    filter_upwards [((isLittleO_log_rpow_rpow_atTop E hρ).const_mul_left K).eventuallyLE,
      Filter.eventually_ge_atTop (0 : ℝ)] with x hx hx0
    exact (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 ρ)] using hx)
  have hmain : ∀ᶠ x : ℝ in Filter.atTop,
      ∀ (M N R Q γ : ℝ), 0 < M → 0 < N → 0 < R → 0 < Q →
      x / C ≤ M * N → M * N ≤ C * x → N = x ^ γ →
      γlo ≤ γ →
      γ ≤ γhi →
      N ≤ C * x ^ (δ + 4 * ε) * R → R ≤ C * x ^ (-2 * ε) * N →
      x ^ (1 / 2 - ε) ≤ C * R * Q → R * Q ≤ C * x ^ (1 / 2 + 2 * «ω» + ε) →
      ∀ (α β : ℕ →₀ ℂ),
      (∀ n ∈ α.support, cM * M ≤ (n : ℝ) ∧ (n : ℝ) ≤ TM * M ∧
        ‖α n‖ ≤ C * (n.divisors.card : ℝ) ^ dα * (Real.log x) ^ Eα) →
      (∀ n ∈ β.support, cN * N ≤ (n : ℝ) ∧ (n : ℝ) ≤ TN * N ∧
        ‖β n‖ ≤ C * (n.divisors.card : ℝ) ^ dβ * (Real.log x) ^ Eβ) →
      ∀ (S : Finset (ℕ × ℕ)),
      (∀ p ∈ S, 0 < p.1 ∧ 0 < p.2 ∧ Squarefree (p.1 * p.2) ∧
        Q ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * Q ∧
        R ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * R ∧
        Nonempty (DenseDivisibilityWitness
          ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩ 1 p.1) ∧
        Nonempty (DenseDivisibilityWitness
          ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩ 1 p.2) ∧
        (∀ t ∈ p.1.primeFactors,
          Real.exp ((Real.log x) ^ (1 / 3 : ℝ)) < (t : ℝ))) →
      ∀ (a b₁ b₂ : ℕ), (∀ p ∈ S, Nat.Coprime (a * b₁ * b₂) (p.1 * p.2)) →
      (∑ p ∈ S, ‖deltaZero (finiteConvolution α β) p.1 p.2 a b₁ b₂‖) ≤
        η * (M * N) * (Real.log x) ^ (-A) := by
    filter_upwards [opening_incidence_scale_resources C₀ «ω» δ ε γlo γhi hC₀ hω hδ hε hεsmall hγmin hγmax,
      hMomentAt, hZeroAt, hDiagonalAt, hTailAt,
      hLogAbsorb Koff (4 + D) (3 * ε / 2) (by positivity),
      hLogAbsorb 1 D 1 zero_lt_one,
      Filter.eventually_ge_atTop Xband,
      Filter.eventually_ge_atTop (max (C₀ ^ 2) (max (2 * TN)
        (Real.exp (max 1 (26 * Kα / η ^ 2)))))]
      with x hscales hmomentAt hzeroAt hdiagonalAt htailAt hoffAbsorb htailAbsorb hxband hxlarge
    obtain ⟨hxexp, hxtwo, htarget, hscaleAt⟩ := hscales
    have hx1 : 1 ≤ x := (by norm_num : (1 : ℝ) ≤ 2).trans hxtwo
    have hx0 : 0 < x := zero_lt_one.trans_le hx1
    have hlog1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxexp
    have hlog0 : 0 < Real.log x := zero_lt_one.trans_le hlog1
    have hC₀square : C₀ ^ 2 ≤ x := (le_max_left _ _).trans hxlarge
    have hTNx : 2 * TN ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hxlarge)
    intro M N R Q γ hM hN hR hQ hMNlo hMNhi hNγ hγlo hγhi hNR hRhi hRQlo hRQhi
      α β hα hβ S hS a b₁ b₂ hprim
    have hMNlo₀ : x / C₀ ≤ M * N :=
      (div_le_div_of_nonneg_left hx0.le hCpos hCC₀).trans hMNlo
    have hMNhi₀ : M * N ≤ C₀ * x := hMNhi.trans
      (mul_le_mul_of_nonneg_right hCC₀ hx0.le)
    have hNR₀ : N ≤ C₀ * x ^ (δ + 4 * ε) * R := hNR.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCC₀ (Real.rpow_nonneg hx0.le _)) hR.le)
    have hRhi₀ : R ≤ C₀ * x ^ (-2 * ε) * N := hRhi.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCC₀ (Real.rpow_nonneg hx0.le _)) hN.le)
    have hRQlo₀ : x ^ (1 / 2 - ε) ≤ C₀ * R * Q := hRQlo.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC₀ hR.le) hQ.le)
    have hRQhi₀ : R * Q ≤ C₀ * x ^ (1 / 2 + 2 * «ω» + ε) := hRQhi.trans
      (mul_le_mul_of_nonneg_right hCC₀ (Real.rpow_nonneg hx0.le _))
    obtain ⟨hNone, hNx, hMone, hMx, hRx, hQx, hMshort⟩ :=
      hscaleAt M N R Q γ hM hN hR hQ hMNlo₀ hMNhi₀ hNγ hγlo hγhi hNR₀ hRhi₀ hRQhi₀
    have hSsimple : ∀ p ∈ S, 0 < p.1 ∧ 0 < p.2 ∧ Squarefree (p.1 * p.2) := by
      intro p hp
      exact ⟨(hS p hp).1, (hS p hp).2.1, (hS p hp).2.2.1⟩
    have hScoprime : ∀ p ∈ S, Nat.Coprime p.1 p.2 :=
      fun p hp => Nat.coprime_of_squarefree_mul (hSsimple p hp).2.2
    have hβpos (n : ℕ) (hn : n ∈ β.support) : 0 < n := by
      exact_mod_cast (mul_pos hcN hN).trans_le (hβ n hn).1
    have hαpos (n : ℕ) (hn : n ∈ α.support) : 0 < n := by
      exact_mod_cast (mul_pos hcM hM).trans_le (hα n hn).1
    let NI : ℕ := ⌊TN * N⌋₊
    have hβsupport : β.support ⊆ Finset.Icc 1 NI := fun n hn =>
      Finset.mem_Icc.mpr ⟨hβpos n hn, Nat.le_floor (hβ n hn).2.1⟩
    have hNI : (NI : ℝ) ≤ TN * N := Nat.floor_le (by positivity)
    have hNIx : (NI : ℝ) ≤ x ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      calc
        (NI : ℝ) ≤ TN * N := hNI
        _ ≤ x * x := mul_le_mul (by linarith only [hTNx, hTNpos]) hNx hN.le hx0.le
        _ = x ^ 2 := (pow_two x).symm
    have hNIscale : (NI : ℝ) ≤ C₀ * N := hNI.trans
      (mul_le_mul_of_nonneg_right (by linarith only [hTN₀, hTNpos]) hN.le)
    let sm : Finset ℕ := Finset.Icc 1 ⌊(2 * TM) * M⌋₊
    let w : ℕ → ℝ := fun n => ψM ((n : ℝ) / M)
    have hsm : α.support ⊆ sm := by
      intro n hn
      refine Finset.mem_Icc.mpr ⟨hαpos n hn, Nat.le_floor ?_⟩
      exact (hα n hn).2.1.trans (by nlinarith only [hTMpos, hM])
    have hw0 : ∀ n ∈ sm, 0 ≤ w n := fun n _ => hMnonneg _
    have hw1 : ∀ n ∈ α.support, 1 ≤ w n := by
      intro n hn
      exact hMmajor _ ⟨(le_div_iff₀ hM).mpr (hα n hn).1,
        (div_le_iff₀ hM).mpr (hα n hn).2.1⟩
    have hψNmajor : ∀ n ∈ β.support, 1 ≤ ψN ((n : ℝ) / N) := by
      intro n hn
      exact hNmajor _ ⟨(le_div_iff₀ hN).mpr (hβ n hn).1,
        (div_le_iff₀ hN).mpr (hβ n hn).2.1⟩
    have hαmoment := hmomentAt M hM hMx α (fun n hn =>
      ⟨hαpos n hn, (hα n hn).2.1, (hα n hn).2.2⟩)
    let H : ℕ → ℝ := fun g => x ^ ε * R * Q ^ 2 / ((g : ℝ) * M)
    let X : ℕ → ℝ := fun g => x ^ (-5 * ε) * Q / H g
    let Y : Set.Ici (1 : ℝ) :=
      ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩
    obtain ⟨u₀, hu₀⟩ := opening_coherent_dense_selector Y Q hQ X
    let u : ℕ → ℕ → ℕ := fun g q => if 1 ≤ H g then u₀ g (g * q) else 1
    let shells : ℕ → ℕ := fun g => if H g < 1 then 0 else Nat.log 2 ⌊H g⌋₊ + 1
    let J : ℕ → Finset ℤ := fun g =>
      (Finset.Ioo (-((2 : ℤ) ^ shells g)) ((2 : ℤ) ^ shells g)).erase 0
    have hXwindow (g : ℕ) (hg : 0 < g) (hH : 1 ≤ H g) : 1 ≤ X g ∧ X g ≤ Q :=
      opening_selector_target_window C₀ x ε Q (H g) (1 / 2 - 2 * «ω» - γhi - 7 * ε)
        g hC₀ hx1 hε.le hQ hH hg htarget
        (opening_incidence_selector_target_lower C₀ x «ω» ε γhi M N R Q (H g) γ g hC₀ hx1
          hM hN hR hQ hg hMNlo₀ hNγ hγhi hRQhi₀ rfl)
    have hu : ∀ p₁ ∈ S, ∀ p₂ ∈ S, p₁.2 = p₂.2 →
        let g := Nat.gcd p₁.1 p₂.1
        0 < u g (p₁.1 / g) ∧ u g (p₁.1 / g) ∣ p₁.1 / g := by
      intro p₁ hp₁ p₂ hp₂ _ g
      have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (hSsimple p₁ hp₁).1
      have hgq : g ∣ p₁.1 := Nat.gcd_dvd_left _ _
      by_cases hH : 1 ≤ H g
      · have hrec : g * (p₁.1 / g) = p₁.1 := Nat.mul_div_cancel' hgq
        have hw := hXwindow g hg hH
        obtain ⟨_, _, _, hlo, hhi, _, _, hdense, _, _⟩ := hS p₁ hp₁
        have hs := hu₀ g p₁.1 hg hgq hlo hhi hdense hw.1 hw.2
        simpa only [u, ite_eq_left hH, hrec] using ⟨hs.1, hs.2.2.1⟩
      · simp only [u, ite_eq_right hH, zero_lt_one, one_dvd, and_self]
    let Ω : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
      (S ×ˢ S).filter (fun p => p.1.2 = p.2.2)
    let G : Finset ℕ := Ω.image (fun p => Nat.gcd p.1.1 p.2.1)
    let 𝒜 : ℕ → Finset (ℕ × ℕ × ℕ × ℕ) := fun g =>
      (Ω.filter (fun p => Nat.gcd p.1.1 p.2.1 = g)).image (fun p =>
        (p.1.2, u g (p.1.1 / g), (p.1.1 / g) / u g (p.1.1 / g), p.2.1 / g))
    let γβ : ℤ →₀ ℂ := Finsupp.embDomain (Nat.castEmbedding : ℕ ↪ ℤ) β
    let L : ℕ → Finset ℤ := fun r =>
      ((γβ.support ×ˢ γβ.support).filter
        (fun p => p.1 ≠ p.2 ∧ Int.ModEq (r : ℤ) p.1 p.2)).image
          (fun p => (p.2 - p.1) / (r : ℤ))
    let LI : ℕ := ⌊(2 * TN) * N / R⌋₊
    let Lall : Finset ℤ := (Finset.Icc (-(LI : ℤ)) (LI : ℤ)).erase 0
    let bins : ℕ → Finset ℕ := fun g => (𝒜 g).image (fun t => Nat.log 2 t.2.1)
    let block : ℕ → ℤ → ℕ → Finset (ℕ × ℕ × ℕ × ℕ) := fun g ℓ i =>
      (𝒜 g).filter (fun t => ℓ ∈ L t.1 ∧ Nat.log 2 t.2.1 = i)
    have hfactor := mixedFourier_offDiagonal_gcd_shift_factorization
      sm w S β (fun _ => 0) a b₁ b₂ J u hSsimple hprim hu
    have hGdata (g : ℕ) (hg : g ∈ G) :
        0 < g ∧ Squarefree g ∧ (g : ℝ) ≤ 2 * Q ∧
        Nat.Coprime (a * b₁ * b₂) g ∧
        ∀ p ∈ g.primeFactors,
          Real.exp ((Real.log x) ^ (1 / 3 : ℝ)) < (p : ℝ) := by
      obtain ⟨p, hpΩ, hpg⟩ := Finset.mem_image.mp hg
      obtain ⟨hp₁, _⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hpΩ).1
      obtain ⟨hq, _, hsf, _, hqhi, _, _, _, _, hrough⟩ := hS p.1 hp₁
      have hgdvd : g ∣ p.1.1 := by
        rw [← hpg]
        exact Nat.gcd_dvd_left _ _
      have hgpos : 0 < g := by
        rw [← hpg]
        exact Nat.gcd_pos_of_pos_left _ hq
      have hgle : (g : ℝ) ≤ (p.1.1 : ℝ) := by
        exact_mod_cast Nat.le_of_dvd hq hgdvd
      refine ⟨hgpos, hsf.of_mul_left.squarefree_of_dvd hgdvd, hgle.trans hqhi,
        (hprim p.1 hp₁).of_dvd_right (dvd_mul_of_dvd_left hgdvd p.1.2), ?_⟩
      intro t ht
      exact hrough t (Nat.primeFactors_mono hgdvd hq.ne' ht)
    have hLall : ∀ r ∈ S.image Prod.snd, L r ⊆ Lall := by
      intro r hr ℓ hℓ
      have hℓne : ℓ ≠ 0 := (hfactor.2.1 r hr ℓ hℓ).1
      have hsupport0 : β.support ⊆ Finset.Icc 0 (0 + NI) := by
        intro n hn
        exact Finset.mem_Icc.mpr
          ⟨Nat.zero_le n, by simpa only [zero_add] using (Finset.mem_Icc.mp (hβsupport hn)).2⟩
      have hnat : ℓ.natAbs * r ≤ NI := hfactor.2.2.1 0 NI hsupport0 r hr ℓ hℓ
      have hRr : R ≤ (r : ℝ) := by
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
        obtain ⟨_, _, _, _, _, hrlow, _, _, _, _⟩ := hS p hp
        exact hrlow
      have hreal : (ℓ.natAbs : ℝ) * (r : ℝ) ≤ (NI : ℝ) := by exact_mod_cast hnat
      have hratio : (ℓ.natAbs : ℝ) ≤ (2 * TN) * N / R := by
        apply (le_div_iff₀ hR).2
        calc
          (ℓ.natAbs : ℝ) * R ≤ (ℓ.natAbs : ℝ) * (r : ℝ) :=
            mul_le_mul_of_nonneg_left hRr (Nat.cast_nonneg _)
          _ ≤ (NI : ℝ) := hreal
          _ ≤ TN * N := hNI
          _ ≤ (2 * TN) * N :=
            mul_le_mul_of_nonneg_right (by linarith only [hTNpos]) hN.le
      have hℓLI : ℓ.natAbs ≤ LI := Nat.le_floor hratio
      have hℓabs : |ℓ| ≤ (LI : ℤ) := by
        have hh : (ℓ.natAbs : ℤ) ≤ (LI : ℤ) := by exact_mod_cast hℓLI
        simpa only [Int.natCast_natAbs] using hh
      exact Finset.mem_erase.mpr ⟨hℓne, Finset.mem_Icc.mpr (abs_le.mp hℓabs)⟩
    have hSelected (g : ℕ) (hg : g ∈ G) (hH : 1 ≤ H g)
        (t : ℕ × ℕ × ℕ × ℕ) (ht : t ∈ 𝒜 g) :
        X g / ((g : ℝ) * x ^ δ) ≤ (t.2.1 : ℝ) ∧ (t.2.1 : ℝ) ≤ X g := by
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
      have hpg := (Finset.mem_filter.mp hp).2
      have hpΩ := Finset.mem_filter.mp (Finset.mem_filter.mp hp).1
      obtain ⟨hp₁, _⟩ := Finset.mem_product.mp hpΩ.1
      have hgpos := (hGdata g hg).1
      have hgq : g ∣ p.1.1 := by rw [← hpg]; exact Nat.gcd_dvd_left _ _
      have hrec : g * (p.1.1 / g) = p.1.1 := Nat.mul_div_cancel' hgq
      obtain ⟨_, _, _, hqlo, hqhi, _, _, hdense, _, _⟩ := hS p.1 hp₁
      have hwindow := hXwindow g hgpos hH
      have hchoice := hu₀ g p.1.1 hgpos hgq hqlo hqhi hdense hwindow.1 hwindow.2
      have hY : (Y : ℝ) = x ^ δ := max_eq_right (Real.one_le_rpow hx1 hδ.le)
      simpa only [u, ite_eq_left hH, hrec, hY] using
        And.intro hchoice.2.2.2.2.1 hchoice.2.2.2.2.2.1
    have hBins (g : ℕ) (hg : g ∈ G) :
        ((bins g).card : ℝ) ≤ Bcount * Real.log x := by
      have hgpos := (hGdata g hg).1
      have hQsquare : 2 * Q ≤ x ^ 2 :=
        (opening_frequency_cutoff_power_bounds x ε M R Q g hxtwo hεone hMone
          hR.le hQ.le hRx hQx hgpos).2
      have hsubset : bins g ⊆ Finset.range (⌊2 * Real.log x / Real.log 2⌋₊ + 1) := by
        intro i hi
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨_, huPos, _, _, htS, _, _, _, _, _⟩ := (hfactor.1 g hg).2 t ht
        have hqPos : 0 < g * t.2.1 * t.2.2.1 := (hSsimple _ htS).1
        have huDvd : t.2.1 ∣ g * t.2.1 * t.2.2.1 :=
          dvd_mul_of_dvd_left (dvd_mul_left t.2.1 g) t.2.2.1
        have huUpper : (t.2.1 : ℝ) ≤ x ^ 2 := by
          calc
            (t.2.1 : ℝ) ≤ ((g * t.2.1 * t.2.2.1 : ℕ) : ℝ) := by
              exact_mod_cast Nat.le_of_dvd hqPos huDvd
            _ ≤ 2 * Q := by
              obtain ⟨_, _, _, _, hqhi, _, _, _, _, _⟩ := hS _ htS
              exact hqhi
            _ ≤ x ^ 2 := hQsquare
        simpa only [Nat.log2_eq_log_two] using
          (opening_selected_dyadic_log_budget x hx1 t.2.1 huPos huUpper).1
      have hcard : ((bins g).card : ℝ) ≤
          ((Finset.range (⌊2 * Real.log x / Real.log 2⌋₊ + 1)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      have hbudget := (opening_selected_dyadic_log_budget x hx1 1 (by decide)
        (by simpa only [Nat.cast_one] using
          (show (1 : ℝ) ≤ x ^ 2 from by nlinarith only [hxtwo]))).2
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hnonneg : 0 ≤ (2 / Real.log 2) * Real.log x := by positivity
      calc
        ((bins g).card : ℝ) ≤ 2 * Real.log x / Real.log 2 + 1 := hcard.trans hbudget
        _ = (2 / Real.log 2) * Real.log x + 1 := by ring
        _ ≤ (2 / Real.log 2) * Real.log x + Real.log x := add_le_add_right hlog1 _
        _ ≤ 2 * ((2 / Real.log 2) * Real.log x + Real.log x) := by
          linarith only [hnonneg, hlog0.le]
        _ = Bcount * Real.log x := by dsimp only [Bcount]; ring
    have hShells (g : ℕ) (hg : g ∈ G) : (shells g : ℝ) ≤ Bcount * Real.log x := by
      have hupper := (opening_frequency_cutoff_power_bounds x ε M R Q g
        hxtwo hεone hMone hR.le hQ.le
        hRx hQx (hGdata g hg).1).1
      have hupperReal : H g ≤ x ^ (4 : ℝ) := by
        simpa only [H, Real.rpow_ofNat] using hupper
      simpa only [shells, Bcount] using opening_padded_count x (H g) hxexp hupperReal
    let Ebase : ℝ := M * N ^ 2 / R * (Real.log x) ^ (-D)
    have hEbase : 0 ≤ Ebase := by dsimp only [Ebase]; positivity
    have hSwitch (q : ℕ) (hq : Nat.Coprime (a * b₁ * b₂) q)
        (b : ℕ) (hb : b ∈ ({b₁, b₂} : Finset ℕ))
        (b' : ℕ) (hb' : b' ∈ ({b₁, b₂} : Finset ℕ)) :
        Nat.Coprime (a * b * b') q := by
      have ha : Nat.Coprime a q := hq.coprime_mul_right.coprime_mul_right
      have h₁ : Nat.Coprime b₁ q := hq.coprime_mul_right.coprime_mul_left
      have h₂ : Nat.Coprime b₂ q := hq.coprime_mul_left
      have hside (z : ℕ) (hz : z ∈ ({b₁, b₂} : Finset ℕ)) : Nat.Coprime z q := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact h₁
        · exact h₂
      exact (ha.mul_left (hside b hb)).mul_left (hside b' hb')
    have hOffDiagonalBound (c : ℕ × ℕ → ℂ)
        (hc : ∀ p ∈ S, ‖c p‖ ≤ 1)
        (b : ℕ) (hb : b ∈ ({b₁, b₂} : Finset ℕ))
        (b' : ℕ) (hb' : b' ∈ ({b₁, b₂} : Finset ℕ)) :
        ‖∑ r ∈ S.image Prod.snd,
          ∑ p₁ ∈ S.filter (fun p => p.2 = r),
            ∑ p₂ ∈ S.filter (fun p => p.2 = r),
              c p₁ * star (c p₂) *
                ∑ n₁ ∈ β.support, ∑ n₂ ∈ β.support,
                  if n₁ = n₂ then 0 else
                    β n₁ * star (β n₂) *
                      ∑ h ∈ J (Nat.gcd p₁.1 p₂.1),
                        mixedFiberFourierCoefficient sm w p₁.1 p₂.1 r a b b' n₁ n₂
                          ((h : ZMod (r * Nat.lcm p₁.1 p₂.1)).val)‖ ≤ Ebase := by
      clear htailAt hzeroAt hdiagonalAt hαmoment
      have hprimSides : ∀ p ∈ S, Nat.Coprime (a * b * b') (p.1 * p.2) :=
        fun p hp => hSwitch _ (hprim p hp) b hb b' hb'
      let F : ℕ → ℤ → Finset (ℕ × ℕ × ℕ × ℕ) → Finset ℤ → ℂ :=
        fun g ℓ B J' =>
          ∑ t ∈ B,
            c (g * t.2.1 * t.2.2.1, t.1) * star (c (g * t.2.2.2, t.1)) *
              ((M : ℂ) / ((t.1 * g * t.2.1 * t.2.2.1 * t.2.2.2 : ℕ) : ℂ)) *
                ∑ n ∈ γβ.support.filter (fun n =>
                  Int.gcd n ((t.1 * g * t.2.1 * t.2.2.1 : ℕ) : ℤ) = 1 ∧
                  Int.gcd (n + ℓ * (t.1 : ℤ)) ((g * t.2.2.2 : ℕ) : ℤ) = 1),
                  γβ n * star (γβ (n + ℓ * (t.1 : ℤ))) *
                    (sourceCompatibility t.1 g b b' ℓ n : ℂ) *
                      ∑ h ∈ J', sourcePhi ψM M
                        (t.1 * g * t.2.1 * t.2.2.1 * t.2.2.2) h *
                          sourceTheta t.1 g t.2.1 t.2.2.1 t.2.2.2 a b b' ℓ n h
      let Jpos : ℕ → Finset ℤ := fun j =>
        Finset.Ico ((2 : ℤ) ^ j) ((2 : ℤ) ^ (j + 1))
      let Jneg : ℕ → Finset ℤ := fun j =>
        Finset.Ioc (-((2 : ℤ) ^ (j + 1))) (-((2 : ℤ) ^ j))
      let Fband : ℕ → ℤ → ℕ → ℕ → Bool → ℂ := fun g ℓ i j side =>
        F g ℓ (block g ℓ i) (if side then Jneg j else Jpos j)
      have hPoint : ∀ g ∈ G, ∀ ℓ ∈ (Finset.Icc (-(LI : ℤ)) (LI : ℤ)).erase 0,
          ∀ i ∈ bins g, ∀ j ∈ Finset.range (shells g), ∀ side : Bool,
            ‖Fband g ℓ i j side‖ ≤
              Kband * M * N * (Int.gcd (g : ℤ) ℓ : ℝ) / (g : ℝ) *
                x ^ (-3 * ε / 2) := by
        intro g hg ℓ hℓ i _hi j hj side
        have hgpos : 0 < g := (hGdata g hg).1
        by_cases hempty : block g ℓ i = ∅
        · simp only [Fband, F, hempty, Finset.sum_empty, norm_zero]
          positivity
        have hHone : 1 ≤ H g := by
          by_contra hbad
          have hsmallH : H g < 1 := lt_of_not_ge hbad
          simp [shells, hsmallH] at hj
        obtain ⟨t₀, ht₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        let U : ℝ := (2 : ℝ) ^ i
        let V : ℝ := Q / ((g : ℝ) * U)
        have hBlockGpos : 0 < (g : ℝ) := by exact_mod_cast (hGdata g hg).1
        have hBlockHpos : 0 < H g := zero_lt_one.trans_le hHone
        have hBlockTwo : (2 : ℝ) ≤ C₀ := (by norm_num : (2 : ℝ) ≤ 4).trans hC₀four
        have hU : 0 < U := by dsimp only [U]; positivity
        have hTupleGeometry (t : ℕ × ℕ × ℕ × ℕ) (ht : t ∈ block g ℓ i) :
            0 < U ∧ 0 < V ∧ U * V = Q / (g : ℝ) ∧
            U ≤ (t.2.1 : ℝ) ∧ (t.2.1 : ℝ) ≤ 2 * U ∧
            V / 2 ≤ (t.2.2.1 : ℝ) ∧ (t.2.2.1 : ℝ) ≤ 2 * V ∧
            x ^ (-δ - 5 * ε) * Q / ((g : ℝ) * H g) ≤ 2 * U ∧
            U ≤ x ^ (-5 * ε) * Q / H g ∧
            x ^ (5 * ε) * H g / (g : ℝ) ≤ V ∧
            V ≤ 2 * x ^ (δ + 5 * ε) * H g := by
          have htA : t ∈ 𝒜 g := (Finset.mem_filter.mp ht).1
          have htbin : Nat.log 2 t.2.1 = i := (Finset.mem_filter.mp ht).2.2
          obtain ⟨_, htu, _, _, htS, _, _, _, _, _⟩ := (hfactor.1 g hg).2 t htA
          have huLo : U ≤ (t.2.1 : ℝ) := by
            have hn : 2 ^ i ≤ t.2.1 := by
              simpa only [htbin] using Nat.pow_log_le_self 2 htu.ne'
            dsimp only [U]
            exact_mod_cast hn
          have huHi : (t.2.1 : ℝ) < 2 * U := by
            have hn : t.2.1 < 2 ^ (i + 1) := by
              simpa only [htbin] using
                Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) t.2.1
            have hr : (t.2.1 : ℝ) < (2 : ℝ) ^ (i + 1) := by exact_mod_cast hn
            simpa only [U, pow_succ, mul_comm] using hr
          obtain ⟨_, _, _, hqLo, hqHi, _, _, _, _, _⟩ := hS _ htS
          have hselection := hSelected g hg hHone t htA
          exact opening_one_bin_geometry x δ ε Q (H g) U g t.2.1 t.2.2.1
            hx1 hQ hBlockHpos hU (hGdata g hg).1 huLo huHi.le
            (by simpa only [Nat.cast_mul] using hqLo)
            (by simpa only [Nat.cast_mul] using hqHi) hselection.1 hselection.2
        obtain ⟨_, hV, hUV, _, _, _, _, hUloTwo, hUhiOne, hVloOne, hVhiTwo⟩ :=
          hTupleGeometry t₀ ht₀
        have hUlo : x ^ (-δ - 5 * ε) * Q / ((g : ℝ) * H g) ≤ C₀ * U :=
          hUloTwo.trans (mul_le_mul_of_nonneg_right hBlockTwo hU.le)
        have hUhi : U ≤ C₀ * x ^ (-5 * ε) * Q / H g := by
          apply hUhiOne.trans
          have hh := mul_le_mul_of_nonneg_right hC₀
            (show 0 ≤ x ^ (-5 * ε) * Q / H g from by positivity)
          simpa only [one_mul, mul_div_assoc, mul_assoc] using hh
        have hVlo : x ^ (5 * ε) * H g / (g : ℝ) ≤ C₀ * V :=
          hVloOne.trans (le_mul_of_one_le_left hV.le hC₀)
        have hVhi : V ≤ C₀ * x ^ (δ + 5 * ε) * H g :=
          hVhiTwo.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hBlockTwo (Real.rpow_nonneg hx0.le _))
            hBlockHpos.le)
        have hUVlo : Q / (g : ℝ) ≤ C₀ * U * V := by
          calc
            Q / (g : ℝ) = U * V := hUV.symm
            _ ≤ C₀ * (U * V) := le_mul_of_one_le_left (mul_nonneg hU.le hV.le) hC₀
            _ = C₀ * U * V := by ring
        have hUVhi : U * V ≤ C₀ * Q / (g : ℝ) := by
          rw [hUV]
          exact div_le_div_of_nonneg_right (le_mul_of_one_le_left hQ.le hC₀)
            hBlockGpos.le
        have hFamily : ∀ t ∈ block g ℓ i,
            0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.1 ∧ 0 < t.2.2.2 ∧
            R ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) ≤ 2 * R ∧
            U / C₀ ≤ (t.2.1 : ℝ) ∧ (t.2.1 : ℝ) ≤ C₀ * U ∧
            V / C₀ ≤ (t.2.2.1 : ℝ) ∧ (t.2.2.1 : ℝ) ≤ C₀ * V ∧
            Q / (C₀ * (g : ℝ)) ≤ (t.2.2.2 : ℝ) ∧
            (t.2.2.2 : ℝ) ≤ C₀ * Q / (g : ℝ) ∧
            Q ≤ ((g * t.2.1 * t.2.2.1 : ℕ) : ℝ) ∧
            Q ≤ ((g * t.2.2.2 : ℕ) : ℝ) ∧
            Nonempty (DenseDivisibilityWitness
              ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩ 1 t.1) ∧
            Squarefree (t.1 * g * t.2.1 * t.2.2.1 * t.2.2.2) ∧
            Nat.Coprime (a * b * b') (t.1 * g * t.2.1 * t.2.2.1 * t.2.2.2) := by
          intro t ht
          have htA : t ∈ 𝒜 g := (Finset.mem_filter.mp ht).1
          obtain ⟨hrt, htu, htv, htq, htS₁, htS₂, _, _, hsf, hprimitive⟩ :=
            (hfactor.1 g hg).2 t htA
          obtain ⟨_, _, _, hq₁lo, _, hrlo, hrhi, _, hdense, _⟩ := hS _ htS₁
          obtain ⟨_, _, _, hq₂lo, hq₂hi, _, _, _, _, _⟩ := hS _ htS₂
          obtain ⟨_, _, _, huLo, huHi, hvLo, hvHi, _, _, _, _⟩ := hTupleGeometry t ht
          have hq₂lower : Q / (g : ℝ) ≤ (t.2.2.2 : ℝ) := by
            apply (div_le_iff₀ hBlockGpos).2
            simpa only [Nat.cast_mul, mul_comm] using hq₂lo
          have hq₂upper : (t.2.2.2 : ℝ) ≤ 2 * Q / (g : ℝ) := by
            apply (le_div_iff₀ hBlockGpos).2
            simpa only [Nat.cast_mul, mul_comm] using hq₂hi
          refine ⟨hrt, htu, htv, htq, hrlo, hrhi,
            (div_le_self hU.le hC₀).trans huLo,
            huHi.trans (mul_le_mul_of_nonneg_right hBlockTwo hU.le),
            (div_le_div_of_nonneg_left hV.le (by norm_num : (0 : ℝ) < 2)
              hBlockTwo).trans hvLo,
            hvHi.trans (mul_le_mul_of_nonneg_right hBlockTwo hV.le), ?_, ?_,
            hq₁lo, hq₂lo, hdense, hsf, hSwitch _ hprimitive.symm b hb b' hb'⟩
          · apply le_trans _ hq₂lower
            exact div_le_div_of_nonneg_left hQ.le hBlockGpos
              (le_mul_of_one_le_left hBlockGpos.le hC₀)
          · exact hq₂upper.trans (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hBlockTwo hQ.le) hBlockGpos.le)
        have hPhase : ∀ t ∈ block g ℓ i,
            ‖c (g * t.2.1 * t.2.2.1, t.1)‖ ≤ 1 ∧
            ‖c (g * t.2.2.2, t.1)‖ ≤ 1 := by
          intro t ht
          obtain ⟨_, _, _, _, hp₁, hp₂, _, _, _, _⟩ :=
            (hfactor.1 g hg).2 t (Finset.mem_filter.mp ht).1
          exact ⟨hc _ hp₁, hc _ hp₂⟩
        have hℓne : ℓ ≠ 0 := (Finset.mem_erase.mp hℓ).1
        have hℓLI : |(ℓ : ℝ)| ≤ (LI : ℝ) := by
          apply abs_le.mpr
          exact ⟨by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_erase.mp hℓ).2).1,
            by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_erase.mp hℓ).2).2⟩
        have hℓbound : |(ℓ : ℝ)| ≤ C₀ * N / R := by
          calc
            |(ℓ : ℝ)| ≤ (LI : ℝ) := hℓLI
            _ ≤ (2 * TN) * N / R := Nat.floor_le (by positivity)
            _ ≤ C₀ * N / R := div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hTN₀ hN.le) hR.le
        have hjShell : j ∈ Finset.range (Nat.log 2 ⌊H g⌋₊ + 1) := by
          simpa only [shells, ite_eq_right (not_lt_of_ge hHone)] using hj
        have hShellWindow : 1 ≤ (2 : ℝ) ^ j ∧ (2 : ℝ) ^ j ≤ H g :=
          (padded_dyadic_cutoff_bounds (H g) hHone).2.2.2.2.2.2 j hjShell
        let Hstar : ℝ := if side then -((2 : ℝ) ^ j) else (2 : ℝ) ^ j
        have hstarabs : |Hstar| = (2 : ℝ) ^ j := by
          cases side <;> simp [Hstar, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) j)]
        have hstarne : Hstar ≠ 0 := by
          have hpositive : 0 < (2 : ℝ) ^ j := by positivity
          intro hz
          rw [hz, abs_zero] at hstarabs
          exact hpositive.ne hstarabs
        have hstarlo : 1 ≤ C₀ * |Hstar| := by
          rw [hstarabs]
          exact hShellWindow.1.trans
            (le_mul_of_one_le_left (zero_le_one.trans hShellWindow.1) hC₀)
        have hstarhi : |Hstar| ≤ C₀ * H g := by
          rw [hstarabs]
          exact hShellWindow.2.trans
            (le_mul_of_one_le_left (zero_le_one.trans hHone) hC₀)
        have hJstar :
            ((Finset.Icc (-((⌊2 * |Hstar|⌋₊ : ℕ) : ℤ))
              ((⌊2 * |Hstar|⌋₊ : ℕ) : ℤ)).filter
                (fun h : ℤ => 1 ≤ (h : ℝ) / Hstar ∧ (h : ℝ) / Hstar < 2)) =
              (if side then Jneg j else Jpos j) := by
          cases side with
          | false => simpa [Hstar, Jpos] using (signed_dyadic_profile_window j).1
          | true => simpa [Hstar, Jneg, abs_neg] using (signed_dyadic_profile_window j).2
        have hβBand : ∀ n ∈ β.support,
            0 < n ∧ (n : ℝ) ≤ (2 * TN) * N ∧
            ‖β n‖ ≤ C₀ * (n.divisors.card : ℝ) ^ dβ * (Real.log x) ^ Eβ ∧
            1 ≤ ψN ((n : ℝ) / N) := by
          intro n hn
          refine ⟨hβpos n hn, (hβ n hn).2.1.trans ?_,
            (hβ n hn).2.2.trans ?_, hψNmajor n hn⟩
          · exact mul_le_mul_of_nonneg_right (by linarith only [hTNpos]) hN.le
          · exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hCC₀ (pow_nonneg (Nat.cast_nonneg _) _))
              (Real.rpow_nonneg hlog0.le _)
        have hgQ : (g : ℝ) ≤ C₀ * Q :=
          (hGdata g hg).2.2.1.trans
            (mul_le_mul_of_nonneg_right (by linarith only [hC₀four]) hQ.le)
        have hraw := hBandAt x hxband g hgpos (hGdata g hg).2.1
          a b b' (hSwitch _ (hGdata g hg).2.2.2.1 b hb b' hb')
          ℓ M N R Q U V (H g) Hstar γ hM hN hR hQ hU hV
          hMNlo₀ hMNhi₀ hNγ hγlo hγhi hNR₀ hRhi₀ hRQlo₀ hRQhi₀ hNx
          rfl hHone hUlo hUhi hVlo hVhi hUVlo hUVhi hgQ
          (hGdata g hg).2.2.2.2 hℓne hℓbound hstarne hstarlo hstarhi
          β hβBand c (block g ℓ i) hFamily hPhase
        dsimp only at hraw
        rw [hJstar] at hraw
        dsimp only [Fband, F]
        exact (norm_sum_le _ _).trans hraw
      have htwoQ : 2 * Q ≤ x ^ 2 := by
        calc
          2 * Q ≤ 2 * x := mul_le_mul_of_nonneg_left hQx (by norm_num)
          _ ≤ x * x := mul_le_mul_of_nonneg_right hxtwo hx0.le
          _ = x ^ 2 := (pow_two x).symm
      have hQI : (⌊2 * Q⌋₊ : ℝ) ≤ x ^ 2 :=
        (Nat.floor_le (by positivity : 0 ≤ 2 * Q)).trans htwoQ
      have hGI : ∀ g ∈ G, 0 < g ∧ g ≤ ⌊2 * Q⌋₊ :=
        fun g hg => ⟨(hGdata g hg).1, Nat.le_floor (hGdata g hg).2.2.1⟩
      have hLI : (LI : ℝ) ≤ (2 * TN) * N / R := Nat.floor_le (by positivity)
      have hsum := opening_summed_bands x ε Kband Bcount (2 * TN) M N R
        hxexp hKband.le hBcount.le (by positivity) hM.le hN.le hR
        G ⌊2 * Q⌋₊ LI bins shells Fband hGI hQI hLI hBins hShells hPoint
      have hsplit := opening_off_diagonal_split (cM / 2) (2 * TM) M
        (by positivity) hMinterval hM ψM hsM S β c a b b' shells u
        hSsimple hprimSides hu Lall hLall
      have hLogProduct :
          (Real.log x) ^ (4 + D) * (Real.log x) ^ (-D) = (Real.log x) ^ 4 := by
        rw [← Real.rpow_add hlog0, show (4 + D) + (-D) = (4 : ℝ) by ring]
        norm_num
      have hXProduct : x ^ (3 * ε / 2) * x ^ (-3 * ε / 2) = 1 := by
        rw [← Real.rpow_add hx0, show 3 * ε / 2 + (-3 * ε / 2) = 0 by ring,
          Real.rpow_zero]
      have hOffScalar :
          Koff * (Real.log x) ^ 4 * x ^ (-3 * ε / 2) ≤ (Real.log x) ^ (-D) := by
        calc
          _ = (Koff * (Real.log x) ^ (4 + D)) *
              ((Real.log x) ^ (-D) * x ^ (-3 * ε / 2)) := by
            calc
              _ = Koff * ((Real.log x) ^ (4 + D) * (Real.log x) ^ (-D)) *
                  x ^ (-3 * ε / 2) := by rw [hLogProduct]
              _ = _ := by ring
          _ ≤ x ^ (3 * ε / 2) *
              ((Real.log x) ^ (-D) * x ^ (-3 * ε / 2)) :=
            mul_le_mul_of_nonneg_right hoffAbsorb (by positivity)
          _ = (Real.log x) ^ (-D) := by
            calc
              _ = (Real.log x) ^ (-D) *
                  (x ^ (3 * ε / 2) * x ^ (-3 * ε / 2)) := by ring
              _ = _ := by rw [hXProduct, mul_one]
      calc
        _ ≤ ∑ g ∈ G, ∑ ℓ ∈ Lall, ∑ i ∈ bins g, ∑ j ∈ Finset.range (shells g),
            (‖F g ℓ (block g ℓ i) (Jpos j)‖ +
              ‖F g ℓ (block g ℓ i) (Jneg j)‖) := hsplit
        _ ≤ 36 * Kband * Bcount ^ 2 * (2 * TN) * (M * N ^ 2 / R) *
            (Real.log x) ^ 4 * x ^ (-3 * ε / 2) := by
          simpa only [Fband, Bool.false_eq_true, ↓reduceIte] using hsum
        _ = (M * N ^ 2 / R) *
            (Koff * (Real.log x) ^ 4 * x ^ (-3 * ε / 2)) := by
          dsimp only [Koff]
          ring
        _ ≤ (M * N ^ 2 / R) * (Real.log x) ^ (-D) :=
          mul_le_mul_of_nonneg_left hOffScalar (by positivity)
        _ = Ebase := rfl
    clear hBandAt hfactor hSelected hGdata hLall hBins hShells hu hu₀ hXwindow hψNmajor
    have hbaseOne : 1 ≤ M * N ^ 2 / R := by
      have hRsmall : R ≤ C₀ * N := hRhi₀.trans (by
        have hpow := Real.rpow_le_one_of_one_le_of_nonpos hx1
          (show -2 * ε ≤ 0 by linarith only [hε])
        simpa only [mul_one] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hC₀pos.le) hN.le)
      have hMNbig : C₀ ≤ M * N := by
        calc
          C₀ = C₀ ^ 2 / C₀ := by field_simp
          _ ≤ x / C₀ := div_le_div_of_nonneg_right hC₀square hC₀pos.le
          _ ≤ M * N := hMNlo₀
      apply (le_div_iff₀ hR).mpr
      calc
        1 * R = R := one_mul R
        _ ≤ C₀ * N := hRsmall
        _ ≤ (M * N) * N := mul_le_mul_of_nonneg_right hMNbig hN.le
        _ = M * N ^ 2 := by ring
    have hTailSmall : x ^ (-1 : ℝ) ≤ Ebase := by
      have hlogpower : (Real.log x) ^ D ≤ x := by
        simpa only [one_mul, Real.rpow_one] using htailAbsorb
      have hinv := inv_anti₀ (Real.rpow_pos_of_pos hlog0 D) hlogpower
      calc
        x ^ (-1 : ℝ) ≤ (Real.log x) ^ (-D) := by
          simpa only [Real.rpow_neg_one, Real.rpow_neg hlog0.le] using hinv
        _ ≤ M * N ^ 2 / R * (Real.log x) ^ (-D) :=
          le_mul_of_one_le_left (Real.rpow_nonneg hlog0.le _) hbaseOne
    have hRlower : x ^ (-δ - 4 * ε) * N / C₀ ≤ R := by
      calc
        x ^ (-δ - 4 * ε) * N / C₀ = N / (C₀ * x ^ (δ + 4 * ε)) := by
          rw [show -δ - 4 * ε = -(δ + 4 * ε) by ring, Real.rpow_neg hx0.le]
          ring_nf
        _ ≤ R := (div_le_iff₀ (mul_pos hC₀pos (Real.rpow_pos_of_pos hx0 _))).mpr
          (by simpa only [mul_comm, mul_left_comm, mul_assoc] using hNR₀)
    have hScales : ∀ p ∈ S, 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
        Q ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * Q ∧
        R ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * R ∧
        (p.1 : ℝ) ≤ x ^ (2 : ℝ) ∧ (p.2 : ℝ) ≤ x ^ (2 : ℝ) := by
      intro p hp
      obtain ⟨hq, hr, _, hqlo, hqhi, hrlo, hrhi, _, _, _⟩ := hS p hp
      have hQ2 : 2 * Q ≤ x ^ 2 := by nlinarith only [hQx, hxtwo]
      have hR2 : 2 * R ≤ x ^ 2 := by nlinarith only [hRx, hxtwo]
      exact ⟨hq, hr, hScoprime p hp, hqlo, hqhi, hrlo, hrhi,
        by simpa only [Real.rpow_two] using hqhi.trans hQ2,
        by simpa only [Real.rpow_two] using hrhi.trans hR2⟩
    have hEnergy : ∀ c : ℕ × ℕ → ℂ, (∀ p ∈ S, ‖c p‖ = 1) →
        dispersionEnergy sm w S β c a b₁ b₂ ≤ 13 * Ebase := by
      intro c hc
      have hc' : ∀ p ∈ S, ‖c p‖ ≤ 1 := fun p hp => (hc p hp).le
      let Dcorr : ℕ → ℕ → ℂ := fun b b' =>
        ∑ r ∈ S.image Prod.snd,
          ∑ p₁ ∈ S.filter (fun p => p.2 = r),
            ∑ p₂ ∈ S.filter (fun p => p.2 = r),
              c p₁ * star (c p₂) *
                ∑ n ∈ β.support, β n * star (β n) *
                  (mixedFiberMass sm w p₁.1 p₂.1 r a b b' n n : ℂ)
      let Ocorr : ℕ → ℕ → ℂ := fun b b' =>
        ∑ r ∈ S.image Prod.snd,
          ∑ p₁ ∈ S.filter (fun p => p.2 = r),
            ∑ p₂ ∈ S.filter (fun p => p.2 = r),
              c p₁ * star (c p₂) *
                ∑ n₁ ∈ β.support, ∑ n₂ ∈ β.support,
                  if n₁ = n₂ then 0 else β n₁ * star (β n₂) *
                    ∑ h ∈ J (Nat.gcd p₁.1 p₂.1),
                      mixedFiberFourierCoefficient sm w p₁.1 p₂.1 r a b b' n₁ n₂
                        ((h : ZMod (r * Nat.lcm p₁.1 p₂.1)).val)
      apply opening_four_energy sm w S β c a b₁ b₂ Ebase Dcorr Ocorr
      · intro b hb b' hb'
        have hprimitive : ∀ p ∈ S, Nat.Coprime (a * b * b') (p.1 * p.2) :=
          fun p hp => hSwitch _ (hprim p hp) b hb b' hb'
        have htail := htailAt S β c NI M Q R hM hQ hR hβsupport hNIx
          (fun n hn => (hβ n hn).2.2) hc' hScales a b b' hprimitive ψM hψM hsM
          (by
            intro t
            simp only [Real.rpow_zero, mul_one]
            exact ⟨by simpa only [iteratedDeriv_zero] using
              (hCMbound 0 t).trans (le_max_left _ _),
              (hCMbound (k + 2) t).trans (le_max_right _ _)⟩) hMshort
        let V : ℕ → ℕ → ℕ → ℕ → ℕ → ℂ := fun r q₁ q₂ n₁ n₂ =>
          if n₁ = n₂ then (mixedFiberMass sm w q₁ q₂ r a b b' n₁ n₂ : ℂ)
          else mixedFiberFourierCoefficient sm w q₁ q₂ r a b b' n₁ n₂ 0 +
            ∑ h ∈ J (Nat.gcd q₁ q₂),
              mixedFiberFourierCoefficient sm w q₁ q₂ r a b b' n₁ n₂
                ((h : ZMod (r * Nat.lcm q₁ q₂)).val)
        have htail' :
            ‖mixedCorrelation sm w S β c a b b' -
                (∑ r ∈ S.image Prod.snd,
                  ∑ p₁ ∈ S.filter (fun p => p.2 = r),
                    ∑ p₂ ∈ S.filter (fun p => p.2 = r),
                      c p₁ * star (c p₂) *
                        ∑ n₁ ∈ β.support, ∑ n₂ ∈ β.support,
                          β n₁ * star (β n₂) * V r p₁.1 p₂.1 n₁ n₂)‖ ≤ x ^ (-1 : ℝ) := by
          clear * - htail
          simpa only [opening_padded_window, V, J, shells, H, sm, w] using htail
        have hidentity := opening_truncated_identity sm w S β c a b b' J
        change
          (∑ r ∈ S.image Prod.snd,
            ∑ p₁ ∈ S.filter (fun p => p.2 = r),
              ∑ p₂ ∈ S.filter (fun p => p.2 = r),
                c p₁ * star (c p₂) *
                  ∑ n₁ ∈ β.support, ∑ n₂ ∈ β.support,
                    β n₁ * star (β n₂) * V r p₁.1 p₂.1 n₁ n₂) =
            Dcorr b b' + offDiagonalZeroMode sm w S β c a b b' + Ocorr b b' at hidentity
        rw [hidentity] at htail'
        refine ⟨htail'.trans hTailSmall, ?_, hOffDiagonalBound c hc' b hb b' hb'⟩
        have hdiag := hdiagonalAt γ M Q R NI
          (by linarith only [hγmin, hγlo, hε])
          (by linarith only [hγmax, hγhi, hω, hε]) hM hQ hR
          (by simpa only [← hNγ] using hMNlo₀)
          (by simpa only [← hNγ] using hMNhi₀)
          (by simpa only [← hNγ] using hRlower)
          (by simpa only [← hNγ] using hRhi₀) hRQhi₀
          (by simpa only [← hNγ] using hNIscale) S β c hβsupport
          (fun n hn => (hβ n hn).2.2) hc'
          (fun p hp => by
            obtain ⟨hq, hr, hcp, hqlo, hqhi, hrlo, hrhi, _, _⟩ := hScales p hp
            exact ⟨hq, hr, hcp, hqlo, hqhi, hrlo, hrhi⟩)
          a b b' ψM (by
            intro t
            simpa only [Real.rpow_zero, mul_one, iteratedDeriv_zero, Real.norm_eq_abs]
              using hCMbound 0 t)
        calc
          ‖Dcorr b b'‖ ≤
              ∑ r ∈ S.image Prod.snd,
                ∑ p₁ ∈ S.filter (fun p => p.2 = r),
                  ∑ p₂ ∈ S.filter (fun p => p.2 = r),
                    ‖c p₁ * star (c p₂) *
                      (∑ n ∈ β.support, β n * star (β n) *
                        (mixedFiberMass sm w p₁.1 p₂.1 r a b b' n n : ℂ))‖ := by
            dsimp only [Dcorr]
            apply norm_sum_le_of_le
            intro r _
            apply norm_sum_le_of_le
            intro p₁ _
            exact norm_sum_le _ _
          _ ≤ Ebase := by simpa only [← hNγ, sm, w, Ebase] using hdiag
      · have hz := hzeroAt M N R Q hM hN hR hQ hMone hNx hQx hRhi
          sm S β c a b₁ b₂
          (fun n hn => ⟨hβpos n hn, (hβ n hn).2.1, (hβ n hn).2.2⟩) hc'
          (fun p hp => by
            obtain ⟨hq, hr, hcp, _, hqhi, hrlo, hrhi, _, _⟩ := hScales p hp
            exact ⟨hq, hr, hcp, hrlo, hrhi, hqhi⟩)
          hprim (fun p hp => (hS p hp).2.2.2.2.2.2.2.2.2)
        exact hz
    clear hOffDiagonalBound htailAt hzeroAt hdiagonalAt
    have hCauchy := opening_final_cauchy α β S sm w a b₁ b₂ R (13 * Ebase) hR
      (mul_nonneg (by norm_num) hEbase)
      (fun p hp => by
        obtain ⟨hq, hr, _, _, _, _, hrhi, _, _, _⟩ := hS p hp
        exact ⟨hq, hr, hrhi⟩) hprim hsm hw0 hw1 hEnergy
    refine opening_cauchy_logarithmic_absorption
      hM hN hR hKα hη hlog1
      ((le_max_right _ _).trans ((le_max_right _ _).trans hxlarge))
      (Finset.sum_nonneg fun _ _ => norm_nonneg _) hαmoment ?_
    simpa only [Ebase, D] using hCauchy
  obtain ⟨X₀, hX₀⟩ := hmain.exists_forall_of_atTop
  refine ⟨max (Real.exp 1) X₀, le_max_left _ _, ?_⟩
  intro x hx
  exact hX₀ x ((le_max_right _ _).trans hx)

#print axioms sourceDeltaZero_rough_dyadic_uniform_log_saving_of_incidence
end PrimeGap182Audit
