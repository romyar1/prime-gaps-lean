import IncidenceRawBlockInterface
import IncidencePublicEnergy182

/-! The actual positive Cauchy transfer from the raw incidence energy to
the secondary source estimate. All supports, CRT classes, masks, block
counts, and the final square root refer to the literal public source sums.
The raw estimate is a proved intermediate input in the final assembly. -/

noncomputable section
namespace PrimeGap182Audit
open Classical PrimeGap186
open scoped BigOperators ContDiff

set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem incidenceSecondaryEstimate_of_raw
    {«ω» δ ε γlo γhi : ℝ} (hε : 0 < ε)
    (hraw : IncidenceRawBlockEstimate «ω» δ ε γlo γhi) :
    IncidenceSecondaryEstimate «ω» δ ε γlo γhi := by
  intro C₁ cM TM cN TN hC₁ hcM hMT hcN hNT CM EM CN EN CD henvelopes
  obtain ⟨Xraw, hXraw, hRawAt⟩ :=
    hraw C₁ cM TM cN TN hC₁ hcM hMT hcN hNT CM EM CN EN CD henvelopes
  obtain ⟨Xloss, hLoss⟩ := Filter.eventually_atTop.mp
    (sourceSecondary_uniform_loss_packet ε (CM 0) (EM 0) (CN 0) (EN 0)
      (CD 0) 0 1 1 C₁ (5 / 2) 0 hε)
  let Xtwo : ℝ := max (max Xraw Xloss) (max 3 C₁)
  have hXt : Real.exp 1 ≤ Xtwo :=
    hXraw.trans ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨1, Xtwo, zero_lt_one, hXt, ?_⟩
  intro x hx r₁ q₀ u₁ v₁ v₂ q₂ aN b₁N b₂N ℓ
    hr₁ hq₀ hu₁ hv₁ hv₂ hq₂ hsq hcop M N R₀ Q U V H Hstar Δ d₀ γ
    hM hN hR₀ hQ hU hV hΔone hMNlo hMNhi hNγ hγlo hγhi
    hNR hRhi hRQlo hRQhi hHdef hH hUlo hUhi hVlo hVhi hUVlo hUVhi
    hrlo hrhi hulo huhi hv₁lo hv₁hi hv₂lo hv₂hi hq₂lo hq₂hi hq₀Q hrough
    hΔlo hΔhi hd₀lo hd₀hi hℓne hℓbound hHstarne hHstarlo hHstarhi
    hNone hNx hRx hQx hHx hUx hCVx ψM ψN ψD hψM hψN hψD hsM hsN hsD
    hvalues hDvalues hderivatives hDderiv Hbound J hJdata
  have hxraw : Xraw ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxloss : Xloss ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx3 : 3 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxC : C₁ ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hxe : Real.exp 1 ≤ x := hXt.trans hx
  have hx1 : 1 ≤ x := by linarith only [hx3]
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hCpos : 0 < C₁ := zero_lt_one.trans_le hC₁
  have hΔpos : 0 < Δ := zero_lt_one.trans_le hΔone
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hqone : (1 : ℝ) ≤ q₀ := by exact_mod_cast hq₀
  have hlogx : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxe
  have hpow (z : ℝ) : 0 < x ^ z := Real.rpow_pos_of_pos hx0 z
  let m : ℕ := r₁ * q₀ * u₁ * Nat.lcm v₁ v₂ * q₂
  let g : ℕ := Nat.gcd v₁ v₂
  let Δ₁ : ℝ := x ^ (-5 * ε) * Δ
  have hmpos : 0 < m := Nat.pos_of_ne_zero hsq.ne_zero
  have hΔ₁pos : 0 < Δ₁ := mul_pos (hpow _) hΔpos
  have hd₀pos : 0 < d₀ := (div_pos hΔpos hCpos).trans_le hd₀lo
  have hΔshort : Δ₁ ≤ Δ := mul_le_of_le_one_left hΔpos.le
    (Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith only [hε]))
  have hden : 1 ≤ (q₀ : ℝ) ^ 2 * x ^ (50 * ε) * H ^ 2 :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hqone)
        (Real.one_le_rpow hx1 (by linarith only [hε]))) (one_le_pow₀ hH)
  have hΔupper : Δ ≤ x ^ (2 : ℕ) := by
    calc
      Δ ≤ C₁ * N / ((q₀ : ℝ) ^ 2 * x ^ (50 * ε) * H ^ 2) := hΔhi
      _ ≤ C₁ * N := div_le_self (mul_pos hCpos hN).le hden
      _ ≤ x * x := mul_le_mul hxC hNx hN.le hx0.le
      _ = _ := by ring
  have hCQx : C₁ * Q ≤ x ^ (5 : ℕ) := by
    calc
      C₁ * Q ≤ x * x ^ (4 : ℕ) := mul_le_mul hxC hQx hQ.le hx0.le
      _ = _ := by ring
  have hr₁x : (r₁ : ℝ) ≤ x ^ (29 : ℕ) := by
    calc
      (r₁ : ℝ) ≤ (r₁ : ℝ) * Δ := le_mul_of_one_le_right (Nat.cast_nonneg _) hΔone
      _ ≤ C₁ * R₀ := hrhi
      _ ≤ x * x ^ (2 : ℕ) := mul_le_mul hxC hRx hR₀.le hx0.le
      _ = x ^ (3 : ℕ) := by ring
      _ ≤ _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hq₀x : (q₀ : ℝ) ≤ x ^ (5 : ℕ) := hq₀Q.trans hCQx
  have hu₁x : (u₁ : ℝ) ≤ x ^ (6 : ℕ) := by
    calc
      (u₁ : ℝ) ≤ C₁ * U := huhi
      _ ≤ x * x ^ (5 : ℕ) := mul_le_mul hxC hUx hU.le hx0.le
      _ = _ := by ring
  have hv₁x : (v₁ : ℝ) ≤ x ^ (15 : ℕ) := hv₁hi.trans hCVx
  have hv₂x : (v₂ : ℝ) ≤ x ^ (15 : ℕ) := hv₂hi.trans hCVx
  have hq₂x : (q₂ : ℝ) ≤ x ^ (5 : ℕ) :=
    hq₂hi.trans ((div_le_self (mul_pos hCpos hQ).le hqone).trans hCQx)
  let φ : ℤ × ℤ → ℤ := fun h =>
    h.1 * ((v₂ / g : ℕ) : ℤ) - h.2 * ((v₁ / g : ℕ) : ℤ)
  let Freq : Finset (ℤ × ℤ) := (J ×ˢ J).filter
    (fun h => h.1 * (v₂ : ℤ) ≠ h.2 * (v₁ : ℤ))
  let L : Finset ℤ := ((J ×ˢ J).image φ).erase 0
  let Dmax : ℕ := ⌊d₀ + (5 / 2) * Δ₁⌋₊
  let D : Finset ℕ := Finset.Icc 1 Dmax
  let I : Finset ℤ := Finset.Icc ⌈cN * N⌉ ⌊TN * N⌋
  let supported : ℤ → ℕ := fun y => ∏ p ∈ m.primeFactors, p ^ y.natAbs.factorization p
  let W : Finset ℕ := D.filter (fun w => Squarefree w ∧ Nat.Coprime w m)
  let W₂ : Finset ℕ := L.image supported
  let Ys : Finset ℤ := L.image (fun y =>
    Int.sign y * ((2 ^ Nat.log 2 y.natAbs : ℕ) : ℤ))
  let Blocks : Finset (ℕ × ℕ × ℤ) := W ×ˢ W₂ ×ˢ Ys
  obtain ⟨hDmax, _, hDhundred, hmBound, hφmem, _, _, _, hLdata⟩ :=
    sourceSecondary_literal_support_census
      x C₁ H Hstar Δ Δ₁ d₀ (5 / 2) r₁ q₀ u₁ v₁ v₂ q₂
      hx3 hC₁ hxC (by linarith only [hx3]) hΔpos hΔ₁pos hd₀pos (by norm_num)
      hΔshort hd₀hi hΔupper hHpos.le hHx hHstarhi hv₁ hv₂
      hr₁x hq₀x hu₁x hv₁x hv₂x hq₂x
  obtain ⟨_, hW₂x, _, _, _, _, _, _, hDSmall, _, _, _, hDyadicX, hHarmonicX⟩ :=
    hLoss x hxloss
  have hWsubset : W ⊆ Finset.Icc 1 Dmax := Finset.filter_subset _ _
  let : NeZero q₀ := ⟨hq₀.ne'⟩
  let E : ZMod q₀ → Finset (ZMod q₀) := fun r =>
    if IsUnit r then Finset.univ.filter (fun n =>
      IsUnit (n * (n + (ℓ : ZMod q₀) * r * (r₁ : ZMod q₀))) ∧
      (b₁N : ZMod q₀) * n⁻¹ =
        (b₂N : ZMod q₀) * (n + (ℓ : ZMod q₀) * r * (r₁ : ZMod q₀))⁻¹)
    else ∅
  obtain ⟨A, B, hAr, hAW, hAq, hBr, hBW, hBq, hAcop, hEcard, _, hCompat⟩ :=
    sourceSecondary_crt_and_compatibility_family
      r₁ q₀ u₁ v₁ v₂ q₂ aN b₁N b₂N ⟨hr₁, hq₀, hu₁, hv₁, hv₂, hq₂⟩ hsq hcop ℓ
  have hAunit : IsUnit ((A.val : ℤ) : ZMod m) := by
    simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime A.val m).mpr hAcop
  let Fblock : ℕ → ℕ → ℤ → Finset (ℤ × ℤ) := fun w w₂ Y =>
    Freq.filter (fun h => (w : ℤ) ∣ φ h ∧ supported (φ h) = w₂ ∧
      1 ≤ (φ h : ℝ) / (Y : ℝ) ∧ (φ h : ℝ) / (Y : ℝ) < 2)
  let R₁ : ℕ := r₁ * q₀ * u₁ * v₁ * q₂
  let R₂ : ℕ := r₁ * q₀ * u₁ * v₂ * q₂
  let Four : (ℤ × ℤ) → (ℤ × ℤ) → ℝ → ℂ := fun h h' d =>
    sourcePhiRealFactor ψM M R₁ h.1 d * star (sourcePhiRealFactor ψM M R₂ h.2 d) *
      star (sourcePhiRealFactor ψM M R₁ h'.1 d) * sourcePhiRealFactor ψM M R₂ h'.2 d
  let kernel : ℕ → ℕ → ℤ → ℤ → ℂ := fun w d y y' =>
    ∑ n ∈ I, ∑ n' ∈ I, sourceSecondaryPairTerm m r₁ q₀ u₁ v₁ v₂ q₂ w
      (A.val : ℤ) (B.val : ℤ) ℓ E ψN N y y' ⊤ d n n'
  let energy : ℕ → ℕ → ℤ → ℂ := fun w w₂ Y => ∑ d ∈ D,
    if w ∣ d ∧ Nat.Coprime (d / w) w then
      (ψD (((d : ℝ) - d₀) / Δ₁) : ℂ) *
        ∑ h ∈ Fblock w w₂ Y, ∑ h' ∈ Fblock w w₂ Y,
          if Int.gcd ((d / w : ℕ) : ℤ) (((m : ℤ) * φ h * φ h') / (w : ℤ) ^ 2) = 1 then
            kernel w d (φ h) (φ h') * Four h h' (d : ℝ) else 0
    else 0
  let maxEnergy : ℝ :=
    ((Blocks.sup (fun b => Real.toNNReal (energy b.1 b.2.1 b.2.2).re) : NNReal) : ℝ)
  have hInitialBound : sourceSigmaTwo J ψM (fun z => ψN (z / N)) ψD M Δ₁ d₀
      r₁ q₀ u₁ v₁ v₂ q₂ aN b₁N b₂N ℓ ≤
        1 * x ^ (5 * ε / 2) * Δ * Real.sqrt maxEnergy := by
    exact (sourceSecondary_positive_block_cauchy
      x ε 1 C₁ Δ hx1 hε le_rfl hC₁ hΔpos
      r₁ q₀ u₁ v₁ v₂ q₂ aN b₁N b₂N ⟨hr₁, hq₀, hu₁, hv₁, hv₂, hq₂⟩ hsq ℓ
      A B E hAr hAW hAq hBr hBW hBq hCompat
      M N Δ₁ d₀ cM TM cN TN (1 / 2) (5 / 2) (CM 0 * (Real.log x) ^ EM 0)
      hM hN hΔ₁pos hd₀pos hcM hMT hcN hNT (by norm_num) (by norm_num)
      (mul_nonneg (henvelopes 0).1 (Real.rpow_nonneg (zero_le_one.trans hlogx) _))
      ψM ψN ψD hsM hsN hsD (fun t => (hDvalues t).1)
      (fun t => by simpa only [iteratedDeriv_zero] using (hderivatives 0 t).1)
      (fun t => (hDvalues t).2.trans (Real.one_le_rpow hx1 (by linarith only [hε])))
      J hφmem (hW₂x m hmpos hmBound L hLdata) (hDyadicX L hLdata)
      hDmax hDSmall (hHarmonicX Dmax W hWsubset hDhundred)).2
  let Qmain : ℝ := (q₀ : ℝ) * (Int.gcd (q₀ : ℤ) ℓ : ℝ) * (g : ℝ) * N
  have hQmain : 0 ≤ Qmain := by dsimp only [Qmain]; positivity
  have hRaw := hRawAt x hxraw r₁ q₀ u₁ v₁ v₂ q₂ aN b₁N b₂N ℓ
    hr₁ hq₀ hu₁ hv₁ hv₂ hq₂ hsq hcop M N R₀ Q U V H Hstar Δ d₀ γ
    hM hN hR₀ hQ hU hV hΔone hMNlo hMNhi hNγ hγlo hγhi
    hNR hRhi hRQlo hRQhi hHdef hH hUlo hUhi hVlo hVhi hUVlo hUVhi
    hrlo hrhi hulo huhi hv₁lo hv₁hi hv₂lo hv₂hi hq₂lo hq₂hi hq₀Q hrough
    hΔlo hΔhi hd₀lo hd₀hi hℓne hℓbound hHstarne hHstarlo hHstarhi
    hNone hNx hRx hQx hHx hUx hCVx ψM ψN ψD hψM hψN hψD hsM hsN hsD
    hvalues hDvalues hderivatives hDderiv hJdata
  have hEnergy (b : ℕ × ℕ × ℤ) (hb : b ∈ Blocks) :
      (energy b.1 b.2.1 b.2.2).re ≤ Qmain ^ 2 * x ^ (-40 * ε) := by
    obtain ⟨hwD, _hwsq, hwcop⟩ := Finset.mem_filter.mp (Finset.mem_product.mp hb).1
    obtain ⟨hwpos, hwmax⟩ := Finset.mem_Icc.mp hwD
    have hr := hRaw b.1 b.2.1 b.2.2 hwpos hwmax hwcop
      (A.val : ℤ) (B.val : ℤ) hAunit
      (by simpa only [Int.cast_natCast] using hBr)
      (by simpa only [Int.cast_natCast] using hBW)
      (by simpa only [Int.cast_natCast] using hBq)
      E (fun r _ => by exact_mod_cast hEcard r) hCompat
    have he := incidencePublicEnergy_eq_rawBlockEnergy
      m b.1 b.2.1 Dmax r₁ q₀ u₁ v₁ v₂ q₂ (A.val : ℤ) (B.val : ℤ) ℓ b.2.2 E
      ψM ψN ψD M N Δ₁ d₀ J I
    change energy b.1 b.2.1 b.2.2 = _ at he
    rw [he]
    exact hr
  have hMax : maxEnergy ≤ Qmain ^ 2 * x ^ (-40 * ε) :=
    (Real.le_toNNReal_iff_coe_le (by positivity)).mp
      (Finset.sup_le fun b hb => Real.toNNReal_mono (hEnergy b hb))
  have hWsq : (Qmain * x ^ (-20 * ε)) ^ 2 = Qmain ^ 2 * x ^ (-40 * ε) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hx0.le]
    congr 2
    norm_num
    ring
  have hsqrt : Real.sqrt maxEnergy ≤ Qmain * x ^ (-20 * ε) :=
    Real.sqrt_le_iff.mpr ⟨mul_nonneg hQmain (hpow _).le, hMax.trans_eq hWsq.symm⟩
  calc
    sourceSigmaTwo J ψM (fun z => ψN (z / N)) ψD M Δ₁ d₀
        r₁ q₀ u₁ v₁ v₂ q₂ aN b₁N b₂N ℓ ≤
        1 * x ^ (5 * ε / 2) * Δ * Real.sqrt maxEnergy := hInitialBound
    _ ≤ 1 * x ^ (5 * ε / 2) * Δ * (Qmain * x ^ (-20 * ε)) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = Qmain * Δ * x ^ (5 * ε / 2 + -20 * ε) := by
      rw [Real.rpow_add hx0]
      ring
    _ ≤ Qmain * Δ * x ^ (-10 * ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith only [hε])) (mul_nonneg hQmain hΔpos.le)
    _ = _ := by dsimp only [Qmain, g]; ring

#print axioms incidenceSecondaryEstimate_of_raw

end PrimeGap182Audit
