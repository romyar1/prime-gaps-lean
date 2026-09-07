import IncidenceFixedSourceBlock
import IncidenceTaylorRemainder
import IncidenceRawBlockInterface
import SourceIncidencePacket182
import SourceIncidenceTaylor182
import IncidenceEmptyEnergy

/-! The complete raw source energy estimate from the prime-local rank-four
bound. Constants and the Taylor cutoff are chosen before the actual source
data. Every coefficient, row, support and remainder is the literal source
object from the public positive Cauchy identity. -/

noncomputable section
namespace PrimeGap182Audit
open Classical PrimeGap186
open scoped BigOperators ContDiff

set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

theorem incidenceRawBlockEstimate_of_rank_four
    (hK4 : AllIncidenceRankFourBounds) («ω» δ ε γlo γhi : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ) (hε : 0 < ε)
    (hgap : 600 * ε ≤ 5 * γlo - 3 / 2 - 40 * «ω» - 16 * δ)
    (hrowgap : 250 * ε ≤ 2 * γlo - 1 / 2 - 16 * «ω» - 6 * δ)
    (hdensity : 100 * ε ≤ 1 - 2 * γhi - 4 * «ω» - 2 * δ) :
    IncidenceRawBlockEstimate «ω» δ ε γlo γhi := by
  intro C cM TM cN TN hC hcM hMT hcN hNT CM EM CN EN CD henvelopes
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hTM : 0 < TM := hcM.trans_le hMT
  have hTN : 0 < TN := hcN.trans_le hNT
  let R : ℝ := max 1 TN
  have hR : 1 ≤ R := le_max_left _ _
  obtain ⟨JT, hJT⟩ := incidenceTaylorRemainder_cutoff ε hε
  obtain ⟨Cj, hCj, hTaylor⟩ := incidenceRawSource_positive_taylor JT
  let Lrow : ℝ := (5 / 2 : ℝ) ^ (2 * JT)
  have hLrow : 0 ≤ Lrow := by dsimp only [Lrow]; positivity
  obtain ⟨K, hK, hFixed⟩ := incidenceFixedSourceBlock_bound hK4 ε C R hε hC hR
    CN EN (fun j => (henvelopes j).2.1)
  obtain ⟨Xfixed, hFixedAt⟩ := Filter.eventually_atTop.mp hFixed
  obtain ⟨Xloss, hLossAt⟩ := Filter.eventually_atTop.mp
    (incidenceSourceLosses_eventually «ω» δ γlo γhi ε C R K Lrow Cj TM (CM 0) (EM 0)
      JT hε hC hR hgap hrowgap hdensity)
  let Kscale : ℝ := C + 4 * TM * C ^ 8
  obtain ⟨Xrem, hRemAt⟩ := Filter.eventually_atTop.mp
    (incidenceTaylorRemainder_eventually ε hε JT hJT Cj TM (5 / 2) Kscale
      (CM 0) (CN 0) (EM 0) (EN 0) hCj.le hTM.le (by norm_num)
      (by dsimp only [Kscale]; positivity) (henvelopes 0).1 (henvelopes 0).2.1)
  let thresholds : Finset ℝ := {Real.exp 1, 3, C, TN, Xfixed, Xloss, Xrem}
  have hthresholds : thresholds.Nonempty := ⟨Real.exp 1, by simp [thresholds]⟩
  let Xtwo := thresholds.sup' hthresholds id
  have hthreshold (z : ℝ) (hz : z ∈ thresholds) : z ≤ Xtwo := Finset.le_sup' id hz
  refine ⟨Xtwo, hthreshold _ (by simp [thresholds]), ?_⟩
  intro x hx r₁ q₀ u₁ v₁ v₂ q₂ aN b₁N b₂N ℓ
    hr₁ hq₀ hu₁ hv₁ hv₂ hq₂ hsq hcop M N R₀ Q U V H Hstar Δ d₀ γ
    hM hN hR₀ hQ hU hV hΔone hMNlo hMNhi hNγ hγlo hγhi
    hNR hRhi hRQlo hRQhi hHdef hH hUlo hUhi hVlo hVhi hUVlo hUVhi
    hrlo hrhi hulo huhi hv₁lo hv₁hi hv₂lo hv₂hi hq₂lo hq₂hi hq₀Q hrough
    hΔlo hΔhi hd₀lo hd₀hi hℓne hℓbound hHstarne hHstarlo hHstarhi
    hNone hNx hRx hQx hHx hUx hCVx ψM ψN ψD hψM hψN hψD hsM hsN hsD
    hvalues hDvalues hderivatives hDderiv Hbound J hJdata m Δ₁ Dmax I
    w w₂ Y hw hwmax hwm Aint Bint hAint hBr hBW hBq E hEcard hCompat
    Fset R₁ R₂ amp ρ
  have hxt (z : ℝ) (hz : z ∈ thresholds) : z ≤ x := (hthreshold z hz).trans hx
  have hxe : Real.exp 1 ≤ x := hxt _ (by simp [thresholds])
  have hx3 : 3 ≤ x := hxt _ (by simp [thresholds])
  have hxC : C ≤ x := hxt _ (by simp [thresholds])
  have hxTN : TN ≤ x := hxt _ (by simp [thresholds])
  have hx1 : 1 ≤ x := by linarith only [hx3]
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hlogx : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxe
  have hpow (z : ℝ) : 0 < x ^ z := Real.rpow_pos_of_pos hx0 z
  have hΔpos : 0 < Δ := zero_lt_one.trans_le hΔone
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hqone : (1 : ℝ) ≤ q₀ := by exact_mod_cast hq₀
  have hwone : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hwR : 0 < (w : ℝ) := by exact_mod_cast hw
  have hmpos : 0 < m := Nat.pos_of_ne_zero hsq.ne_zero
  have : NeZero m := ⟨hsq.ne_zero⟩
  have : NeZero w := ⟨hw.ne'⟩
  have : NeZero q₀ := ⟨hq₀.ne'⟩
  let g : ℕ := Nat.gcd v₁ v₂
  have hg : 0 < g := Nat.gcd_pos_of_pos_left v₂ hv₁
  have hgR : 0 < (g : ℝ) := by exact_mod_cast hg
  have hgOne : (1 : ℝ) ≤ g := by exact_mod_cast hg
  let κ : ℝ := (Int.gcd (q₀ : ℤ) ℓ : ℝ)
  have hκone : 1 ≤ κ := by
    have hk : 0 < Int.gcd (q₀ : ℤ) ℓ :=
      Int.gcd_pos_of_ne_zero_left ℓ (by exact_mod_cast hq₀.ne')
    simpa only [κ, Nat.cast_one] using
      (Nat.cast_le.mpr (show 1 ≤ Int.gcd (q₀ : ℤ) ℓ from hk) :
        ((1 : ℕ) : ℝ) ≤ (Int.gcd (q₀ : ℤ) ℓ : ℝ))
  have hΔ₁pos : 0 < Δ₁ := mul_pos (hpow _) hΔpos
  have hd₀pos : 0 < d₀ := (div_pos hΔpos hC0).trans_le hd₀lo
  have hΔshort : Δ₁ ≤ Δ := mul_le_of_le_one_left hΔpos.le
    (Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith only [hε]))
  have hden : 1 ≤ (q₀ : ℝ) ^ 2 * x ^ (50 * ε) * H ^ 2 :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hqone)
        (Real.one_le_rpow hx1 (by linarith only [hε]))) (one_le_pow₀ hH)
  have hΔupper : Δ ≤ x ^ (2 : ℕ) := by
    calc
      Δ ≤ C * N / ((q₀ : ℝ) ^ 2 * x ^ (50 * ε) * H ^ 2) := hΔhi
      _ ≤ C * N := div_le_self (mul_pos hC0 hN).le hden
      _ ≤ x * x := mul_le_mul hxC hNx hN.le hx0.le
      _ = _ := by ring
  have hCQx : C * Q ≤ x ^ (5 : ℕ) := by
    calc
      C * Q ≤ x * x ^ (4 : ℕ) := mul_le_mul hxC hQx hQ.le hx0.le
      _ = _ := by ring
  have hr₁x : (r₁ : ℝ) ≤ x ^ (29 : ℕ) := by
    calc
      (r₁ : ℝ) ≤ (r₁ : ℝ) * Δ := le_mul_of_one_le_right (Nat.cast_nonneg _) hΔone
      _ ≤ C * R₀ := hrhi
      _ ≤ x * x ^ (2 : ℕ) := mul_le_mul hxC hRx hR₀.le hx0.le
      _ = x ^ (3 : ℕ) := by ring
      _ ≤ _ := pow_le_pow_right₀ hx1 (by decide)
  have hq₀x : (q₀ : ℝ) ≤ x ^ (5 : ℕ) := hq₀Q.trans hCQx
  have hu₁x : (u₁ : ℝ) ≤ x ^ (6 : ℕ) := by
    calc
      (u₁ : ℝ) ≤ C * U := huhi
      _ ≤ x * x ^ (5 : ℕ) := mul_le_mul hxC hUx hU.le hx0.le
      _ = _ := by ring
  have hv₁x : (v₁ : ℝ) ≤ x ^ (15 : ℕ) := hv₁hi.trans hCVx
  have hv₂x : (v₂ : ℝ) ≤ x ^ (15 : ℕ) := hv₂hi.trans hCVx
  have hq₂x : (q₂ : ℝ) ≤ x ^ (5 : ℕ) :=
    hq₂hi.trans ((div_le_self (mul_pos hC0 hQ).le hqone).trans hCQx)
  obtain ⟨_hDmax, hDfour, hDhundred, hmBound, hφmem, _hHbound, _hJbound, hFreqcard, hLdata⟩ :=
    sourceSecondary_literal_support_census
      x C H Hstar Δ Δ₁ d₀ (5 / 2) r₁ q₀ u₁ v₁ v₂ q₂
      hx3 hC hxC (by linarith only [hx3]) hΔpos hΔ₁pos hd₀pos (by norm_num)
      hΔshort hd₀hi hΔupper hHpos.le hHx hHstarhi hv₁ hv₂
      hr₁x hq₀x hu₁x hv₁x hv₂x hq₂x
  have hFsub : Fset ⊆ ((J ×ˢ J).filter (fun h => h.1 * (v₂ : ℤ) ≠ h.2 * (v₁ : ℤ))) :=
    Finset.filter_subset _ _
  have hFheight : ∀ h ∈ Fset,
      ((incidenceReducedFrequency v₁ v₂ h).natAbs : ℝ) ≤ x ^ (100 : ℝ) :=
    fun h hh => (hLdata _ (hφmem h (hFsub hh))).2
  have hF100 : (Fset.card : ℝ) ≤ x ^ (100 : ℕ) := by
    calc
      _ ≤ (((J ×ˢ J).filter (fun h => h.1 * (v₂ : ℤ) ≠ h.2 * (v₁ : ℤ))).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hFsub)
      _ ≤ x ^ (30 : ℕ) := hFreqcard
      _ ≤ _ := pow_le_pow_right₀ hx1 (by decide)
  have hIrange : ∀ n ∈ I, (0 : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ TN * N := by
    intro n hn
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hn
    have hlo : cN * N ≤ (n : ℝ) :=
      (Int.le_ceil _).trans (by exact_mod_cast hnlo)
    have hhi : (n : ℝ) ≤ (⌊TN * N⌋ : ℤ) := by exact_mod_cast hnhi
    exact ⟨(mul_pos hcN hN).le.trans hlo, hhi.trans (Int.floor_le _)⟩
  have hIcard : (I.card : ℝ) ≤ TN * N + 1 := by
    simpa only [sub_zero, add_comm] using
      int_finset_card_le_of_mem_real_Icc I 0 (TN * N) (mul_pos hTN hN).le hIrange
  have hI100 : (I.card : ℝ) ≤ x ^ (100 : ℕ) := by
    calc
      _ ≤ TN * N + 1 := hIcard
      _ ≤ x * x + 1 := by
        simpa only [add_comm] using add_le_add_right (mul_le_mul hxTN hNx hN.le hx0.le) 1
      _ ≤ x ^ (3 : ℕ) := by nlinarith only [hx3, sq_nonneg x]
      _ ≤ _ := pow_le_pow_right₀ hx1 (by decide)
  have hD100 : (Dmax : ℝ) / w ≤ x ^ (100 : ℕ) :=
    (div_le_self (Nat.cast_nonneg _) hwone).trans
      (hDfour.trans (pow_le_pow_right₀ hx1 (by decide)))
  let LM : ℝ := CM 0 * (Real.log x) ^ EM 0
  let LN : ℝ := CN 0 * (Real.log x) ^ EN 0
  have hLM : 0 ≤ LM := mul_nonneg (henvelopes 0).1 (Real.rpow_nonneg (zero_le_one.trans hlogx) _)
  have hLN : 0 ≤ LN := mul_nonneg (henvelopes 0).2.1 (Real.rpow_nonneg (zero_le_one.trans hlogx) _)
  have hMbound (y : ℝ) : |ψM y| ≤ LM := by
    simpa only [iteratedDeriv_zero] using (hderivatives 0 y).1
  have hNbound (y : ℝ) : |ψN y| ≤ LN := by
    simpa only [iteratedDeriv_zero] using (hderivatives 0 y).2
  have hsD0 : Function.support ψD ⊆ Set.Icc 0 (5 / 2) := by
    intro y hy
    exact ⟨(by norm_num : (0 : ℝ) ≤ 1 / 2).trans (hsD hy).1, (hsD hy).2⟩
  let S : ℝ := Δ₁ / d₀ *
    (1 + TM * M * (2 * C * H) / d₀ * ((R₁ : ℝ)⁻¹ + (R₂ : ℝ)⁻¹))
  have hS0 : 0 ≤ S := by dsimp only [S]; positivity
  have hSbound : S ≤ Kscale * x ^ (-4 * ε) :=
    incidenceSourceTaylorScale_from_actual_scales C x ε R₀ Q U V Δ M H d₀ TM
      r₁ q₀ u₁ v₁ v₂ q₂ hC hx1 hε hR₀ hQ hU hV hΔpos hM hHpos hTM.le
      ⟨hr₁, hq₀, hu₁, hv₁, hv₂, hq₂⟩ hrlo hulo hv₁lo hv₂lo hq₂lo hUVlo hd₀lo hHdef
  obtain ⟨hSone, hErr⟩ := (hRemAt x (hxt _ (by simp [thresholds]))).2 S
    (Fset.card : ℝ) (I.card : ℝ) ((Dmax : ℝ) / w)
    hS0 hSbound (Nat.cast_nonneg _) hF100 (Nat.cast_nonneg _) hI100 (by positivity) hD100
  have hFcoords : ∀ h ∈ Fset, |(h.1 : ℝ)| ≤ 2 * C * H ∧ |(h.2 : ℝ)| ≤ 2 * C * H := by
    intro h hh
    have hp := Finset.mem_product.mp (Finset.mem_filter.mp (hFsub hh)).1
    exact ⟨(hJdata h.1 hp.1).2, (hJdata h.2 hp.2).2⟩
  have hperiods : 0 < R₁ ∧ 0 < R₂ := by
    dsimp only [R₁, R₂]
    constructor <;> positivity
  have ht := hTaylor Fset cM TM M (2 * C * H) LM LN d₀ Δ₁ (5 / 2)
    hcM hMT hM (by positivity) hLM hLN hd₀pos hΔ₁pos (by norm_num)
    ψM ψN ψD hsM hMbound hNbound hsD0 hDvalues r₁ q₀ u₁ v₁ v₂ q₂ hperiods hFcoords
  let Phi : (ℤ × ℤ) → ℝ → ℂ := fun h d =>
    sourcePhiRealFactor ψM M R₁ h.1 d * star (sourcePhiRealFactor ψM M R₂ h.2 d)
  let coeff : (ℤ × ℤ) → ℕ → ℂ := fun h j =>
    (Δ₁ ^ j / (j.factorial : ℝ)) • iteratedDeriv j (Phi h) d₀
  let Rows := incidenceSupportedEnergyRows Dmax w m ρ
  let Main : ℕ → ℝ := fun j => ∑ e ∈ Rows,
    (ρ (w * e) * ((((w : ℝ) * e - d₀) / Δ₁) ^ j) ^ 2) *
      incidencePhysicalEnergyOrZero (m := m) (w := w) e Aint Bint
        (Fset.image (incidenceQuotientFrequency w v₁ v₂)) I
        (incidenceGroupedCoefficient Fset (incidenceQuotientFrequency w v₁ v₂) (fun h => coeff h j))
        (incidenceSourceNumerator r₁ q₀ u₁ v₁ v₂ q₂ (w * e) ℓ E ψN N)
  have hRawTaylor := ht.2 m w Dmax hwm Aint Bint ℓ E N I (incidenceQuotientFrequency w v₁ v₂)
  let P : ℝ := x ^ (ε / 100)
  let Bamp : ℝ := Cj * (TM * LM) ^ 2
  have hP : 1 ≤ P := Real.one_le_rpow hx1 (by positivity)
  have hBamp : 0 ≤ Bamp := by dsimp only [Bamp]; positivity
  have hLoss := hLossAt x (hxt _ (by simp [thresholds])) γ hγlo hγhi
  have hCeps : C ≤ x ^ ε := hLoss.C_small.trans
    (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith only [hε]))
  have hmprod : (m : ℝ) * (g : ℝ) =
      (r₁ : ℝ) * (q₀ : ℝ) * (u₁ : ℝ) * (v₁ : ℝ) * (v₂ : ℝ) * (q₂ : ℝ) := by
    exact_mod_cast incidenceSourceModulus_gcd_lcm r₁ q₀ u₁ v₁ v₂ q₂
  obtain ⟨hmlo, hmhi⟩ := incidenceSourceModulus_scale
    C R₀ Q U V Δ (q₀ : ℝ) (g : ℝ) (m : ℝ)
    (r₁ : ℝ) (u₁ : ℝ) (v₁ : ℝ) (v₂ : ℝ) (q₂ : ℝ)
    hC0 hR₀ hQ hU hV hΔpos (by exact_mod_cast hq₀) hgR (by exact_mod_cast hmpos)
    (by exact_mod_cast hr₁) (by exact_mod_cast hu₁) (by exact_mod_cast hv₁)
    (by exact_mod_cast hv₂) (by exact_mod_cast hq₂) hmprod
    hrlo hrhi hulo huhi hv₁lo hv₁hi hv₂lo hv₂hi hq₂lo hq₂hi hUVlo hUVhi
  have hp := sourceIncidence_envelope_of_actual_scales
    C x «ω» δ ε γ M N R₀ Q V H (q₀ : ℝ) (g : ℝ) (w : ℝ) Δ (m : ℝ)
    hC hx1 hCeps hω.le hδ.le hε hM hR₀ hQ hV hH hqone hgOne hwone
    hΔpos (by exact_mod_cast hmpos) hNγ hMNlo hMNhi hNR hRQhi hHdef hVlo hVhi
    hΔlo hΔhi hmlo hmhi
  have hRowsSub : Rows ⊆ Finset.Icc 1 Dmax := by
    intro e he
    have hd := (incidenceSupportedEnergyRows_mem Dmax w m ρ e).mp he
    exact Finset.mem_Icc.mpr ⟨hd.1, hd.2.1.trans (Nat.div_le_self _ _)⟩
  have hRowsGeom : ∀ e ∈ Rows, Nat.Coprime e m ∧ Nat.Coprime w e ∧
      |(w : ℝ) * e - d₀| ≤ (5 / 2) * Δ₁ ∧
      (1 / C ^ 2) * (C * Δ / w) ≤ (e : ℝ) ∧ (e : ℝ) ≤ 2 * (C * Δ / w) := by
    intro e he
    have hd := (incidenceSupportedEnergyRows_mem Dmax w m ρ e).mp he
    have hl := incidenceSupportedEnergyRows_local Dmax w m d₀ Δ₁ 0 (5 / 2)
      hΔ₁pos le_rfl ψD hsD0 e he
    have hshort : (5 / 2 : ℝ) * Δ₁ ≤ C * Δ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hLoss.short hΔpos.le
    have hh := incidenceSourceRows_comparable C Δ Δ₁ d₀ (5 / 2) (w : ℝ) (e : ℝ)
      hC hΔpos hΔ₁pos hwR hd₀lo hd₀hi hshort ⟨hl.1, hl.2.1⟩
    exact ⟨hd.2.2.2.1, hd.2.2.1.symm, hh.2.2, hh.1, hh.2.1⟩
  have hq₀m : q₀ ∣ m := ⟨r₁ * u₁ * Nat.lcm v₁ v₂ * q₂, by dsimp only [m]; ring⟩
  have hwq : Nat.Coprime w q₀ := hwm.of_dvd_right hq₀m
  let Scompat : ZMod q₀ → Finset (ZMod q₀) := fun r => E ((w : ZMod q₀) * r)
  have hScompat : ∀ r, IsUnit r → ((Scompat r).card : ℝ) ≤ κ := by
    intro r hr
    exact hEcard _ (((ZMod.isUnit_iff_coprime w q₀).mpr hwq).mul hr)
  have hsNR : Function.support ψN ⊆ Set.Icc (-R) R := by
    intro y hy
    have hlo : -R ≤ cN := by dsimp only [R]; linarith only [le_max_left (1 : ℝ) TN, hcN]
    exact ⟨hlo.trans (hsN hy).1,
      (hsN hy).2.trans (le_max_right _ _)⟩
  have hsI : ∀ n : ℤ, ψN ((n : ℝ) / N) ≠ 0 → n ∈ I := by
    intro n hn
    have hh := hsN hn
    exact Finset.mem_Icc.mpr
      ⟨Int.ceil_le.mpr ((le_div_iff₀ hN).mp hh.1), Int.le_floor.mpr ((div_le_iff₀ hN).mp hh.2)⟩
  have hMain : ∀ j ≤ JT,
      Main j ≤ ((q₀ : ℝ) * κ * (g : ℝ) * N) ^ 2 * (81 * P ^ 7 * x ^ (-49 * ε)) := by
    intro j hj
    by_cases hFempty : Fset = ∅
    · simp only [Main, hFempty, Finset.image_empty, incidencePhysicalEnergyOrZero_empty,
        mul_zero, Finset.sum_const_zero]
      positivity
    have hFne : Fset.Nonempty := Finset.nonempty_iff_ne_empty.mpr hFempty
    have ha : ∀ h ∈ Fset, ‖coeff h j‖ ≤ Bamp := by
      intro h hh
      exact (ht.1 h hh j hj).trans (mul_le_of_le_one_right hBamp (pow_le_one₀ hS0 hSone))
    let ρj : ℕ → ℝ := fun e => ρ (w * e) * ((((w : ℝ) * e - d₀) / Δ₁) ^ j) ^ 2
    have hρj : ∀ e ∈ Rows, 0 ≤ ρj e ∧ ρj e ≤ Lrow := by
      intro e he
      simpa only [ρj, ρ, Nat.cast_mul, Lrow] using
        incidenceSupportedRows_taylor_weight Dmax w m JT j d₀ Δ₁ (5 / 2)
          hΔ₁pos (by norm_num) hj ψD hsD0 hDvalues e he
    have hFixedBound := hFixedAt x (hxt _ (by simp [thresholds]))
      q₀ v₁ v₂ m w w₂ Dmax hq₀ hv₁ hv₂ hsq hq₀m hw hwmax hwm hmBound hDhundred
      «ω» δ γ (C ^ 10 * x ^ (8 * ε)) (x ^ (54 * ε)) (x ^ (5 * ε))
      M N H Hstar V Δ₁ Δ d₀ P Bamp Lrow κ hp hV hHstarhi hVlo hv₁lo hv₁hi hv₂hi hVhi
      hBamp hLrow (zero_le_one.trans hκone) hΔshort JT hLoss
      ψN hψN hsNR (fun j y => (hderivatives j y).2) Y hFne hFheight
      Rows hRowsSub hRowsGeom ρj hρj Aint Bint hAint Scompat hScompat (fun h => coeff h j) ha I hsI
    have heq : Main j = ∑ e ∈ Rows, ρj e * incidencePhysicalEnergyOrZero
        (m := m) (w := w) e Aint Bint
        (incidenceSourceQuotientSet J v₁ v₂ m w w₂ Y) I
        (incidenceGroupedCoefficient Fset (incidenceQuotientFrequency w v₁ v₂) (fun h => coeff h j))
        (fun n => if (n : ZMod q₀) ∈ Scompat (e : ZMod q₀)
          then (ψN ((n : ℝ) / N) : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      have hedata := (incidenceSupportedEnergyRows_mem Dmax w m ρ e).mp he
      have : NeZero e := ⟨hedata.1.ne'⟩
      congr 1
      rw [incidencePhysicalEnergyOrZero_of_ne, incidencePhysicalEnergyOrZero_of_ne]
      have hdq : Nat.Coprime (w * e) q₀ := Nat.coprime_mul_iff_left.mpr
        ⟨hwq, hedata.2.2.2.1.of_dvd_right hq₀m⟩
      simpa only [Scompat, Nat.cast_mul, incidenceSourceQuotientSet, Fset] using
        incidencePhysicalEnergy_absorb_source r₁ q₀ u₁ v₁ v₂ q₂ w e b₁N b₂N Aint Bint ℓ E ψN N
          hBr hBW (by simpa only [Int.cast_mul, Int.cast_natCast] using hBq) (hCompat (w * e) hdq)
          (incidenceSourceQuotientSet J v₁ v₂ m w w₂ Y) I
          (incidenceGroupedCoefficient Fset (incidenceQuotientFrequency w v₁ v₂) (fun h => coeff h j))
    exact heq.trans_le hFixedBound
  let scale : ℝ := ((q₀ : ℝ) * κ * (g : ℝ) * N) ^ 2
  have hscale : 1 ≤ scale := one_le_pow₀
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hqone hκone) hgOne) hNone)
  have hMainSum := incidenceTaylorMain_collect JT Main x ε P scale hx1 hε hP le_rfl
    (zero_le_one.trans hscale) hLoss.taylor_count hMain
  exact incidenceRawTaylor_collect x ε scale _ _ _ hx1 hε hscale
    ((by norm_num : (2 : ℝ) ≤ 11).trans hLoss.large) hRawTaylor hMainSum hErr

theorem incidenceRawBlockFamily_of_rank_four (hK4 : AllIncidenceRankFourBounds)
    («ω» δ γlo γhi : ℝ) (hω : 0 < «ω») (hδ : 0 < δ)
    (hlo : 12 * «ω» + 6 * δ < γlo) (hhi : γhi < 1 / 2 - 2 * «ω»)
    (hdensity : 2 * γhi + 4 * «ω» + 2 * δ < 1)
    (hfour : 16 * «ω» + 7 * δ < γlo)
    (hfive : 3 / 2 + 40 * «ω» + 16 * δ < 5 * γlo) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      IncidenceRawBlockEstimate «ω» δ ε γlo γhi := by
  obtain ⟨ε₀, hε₀, hsmall⟩ := incidenceStrictGuards_arbitrarily_small_epsilon
    «ω» δ γlo γhi hω hδ hlo hhi hdensity hfour hfive
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεsmall
  obtain ⟨hgap, hrowgap, _, _, hdens, _⟩ := hsmall ε hε hεsmall
  exact incidenceRawBlockEstimate_of_rank_four hK4 «ω» δ ε γlo γhi hω hδ hε hgap hrowgap hdens

#print axioms incidenceRawBlockEstimate_of_rank_four
#print axioms incidenceRawBlockFamily_of_rank_four

end PrimeGap182Audit
