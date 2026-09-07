import SourceIncidenceResources182

/-! The actual selected source family estimate from the explicit new
secondary bound. The divisor extraction retains q0 squared in its
target; every finite fiber, residue and frequency sum is unchanged.
Adapted from Apache-2.0 PrimeGaps186 at the pinned source hash. -/

noncomputable section
open scoped BigOperators Topology ContDiff
open Filter Asymptotics PrimeGap186
namespace PrimeGap182Audit
set_option maxHeartbeats 1600000

open Classical in
theorem sourceSigmaOne_selected_family_bound_of_incidence
    («ω» δ ε γlo γhi C cM TM cN TN : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ) (hε : 0 < ε)
    (hωsmall : «ω» < 1 / 16) (hδsmall : δ < 1 / 8) (hεsmall : ε < 1 / 1000)
    (hγmin : 8 * «ω» + 2 * δ + 100 * ε ≤ γlo) (hγmax : γhi ≤ 1)
    (hsecondary : IncidenceSecondaryEstimate «ω» δ ε γlo γhi)
    (hC : 1 ≤ C) (hcM : 0 < cM) (hMT : cM ≤ TM)
    (hcN : 0 < cN) (hNT : cN ≤ TN)
    (CM EM CN EN : ℕ → ℝ)
    (henvelopes : ∀ j : ℕ, 0 ≤ CM j ∧ 0 ≤ CN j) :
    ∃ K X₀ : ℝ, 0 < K ∧ Real.exp 1 ≤ X₀ ∧
      ∀ (x : ℝ), X₀ ≤ x →
      ∀ (q₀ : ℕ), 0 < q₀ → Squarefree q₀ →
      ∀ (a b₁ b₂ ℓ : ℤ),
      Int.gcd (a * b₁ * b₂) (q₀ : ℤ) = 1 →
      ∀ (M N R₀ Q U V H Hstar γ : ℝ),
      0 < M → 0 < N → 0 < R₀ → 0 < Q → 0 < U → 0 < V →
      x / C ≤ M * N → M * N ≤ C * x → N = x ^ γ →
      γlo ≤ γ →
      γ ≤ γhi →
      N ≤ C * x ^ (δ + 4 * ε) * R₀ →
      R₀ ≤ C * x ^ (-2 * ε) * N →
      x ^ (1 / 2 - ε) ≤ C * R₀ * Q →
      R₀ * Q ≤ C * x ^ (1 / 2 + 2 * «ω» + ε) →
      H = x ^ ε * R₀ * Q ^ 2 / ((q₀ : ℝ) * M) → 1 ≤ H →
      x ^ (-δ - 5 * ε) * Q / ((q₀ : ℝ) * H) ≤ C * U →
      U ≤ C * x ^ (-5 * ε) * Q / H →
      x ^ (5 * ε) * H / (q₀ : ℝ) ≤ C * V →
      V ≤ C * x ^ (δ + 5 * ε) * H →
      Q / (q₀ : ℝ) ≤ C * U * V → U * V ≤ C * Q / (q₀ : ℝ) →
      (q₀ : ℝ) ≤ C * Q →
      (∀ p ∈ q₀.primeFactors,
        Real.exp ((Real.log x) ^ (1 / 3 : ℝ)) < (p : ℝ)) →
      ℓ ≠ 0 → |(ℓ : ℝ)| ≤ C * N / R₀ →
      Hstar ≠ 0 → 1 ≤ C * |Hstar| → |Hstar| ≤ C * H →
      ∀ (ψM ψN : ℝ → ℝ), ContDiff ℝ ∞ ψM → ContDiff ℝ ∞ ψN →
      Function.support ψM ⊆ Set.Icc cM TM →
      Function.support ψN ⊆ Set.Icc cN TN →
      (∀ t : ℝ, 0 ≤ ψM t ∧ 0 ≤ ψN t) →
      (∀ (j : ℕ) (t : ℝ),
        |iteratedDeriv j ψM t| ≤ CM j * (Real.log x) ^ EM j ∧
        |iteratedDeriv j ψN t| ≤ CN j * (Real.log x) ^ EN j) →
      ∀ (𝒯 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ)),
      (∀ t ∈ 𝒯,
        0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.1 ∧
        0 < t.2.2.2.1 ∧ 0 < t.2.2.2.2 ∧
        R₀ / C ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) ≤ C * R₀ ∧
        U / C ≤ (t.2.1 : ℝ) ∧ (t.2.1 : ℝ) ≤ C * U ∧
        V / C ≤ (t.2.2.1 : ℝ) ∧ (t.2.2.1 : ℝ) ≤ C * V ∧
        V / C ≤ (t.2.2.2.1 : ℝ) ∧ (t.2.2.2.1 : ℝ) ≤ C * V ∧
        Q / (C * (q₀ : ℝ)) ≤ (t.2.2.2.2 : ℝ) ∧
        (t.2.2.2.2 : ℝ) ≤ C * Q / (q₀ : ℝ) ∧
        Nonempty (DenseDivisibilityWitness
          ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩ 1 t.1) ∧
        Squarefree (t.1 * q₀ * t.2.1 * t.2.2.1 * t.2.2.2.2) ∧
        Squarefree (t.1 * q₀ * t.2.1 * t.2.2.2.1 * t.2.2.2.2) ∧
        Int.gcd (a * b₁ * b₂)
          ((t.1 * q₀ * t.2.1 * t.2.2.1 * t.2.2.2.1 * t.2.2.2.2 : ℕ) : ℤ) = 1) →
      let Hbound : ℕ := ⌊2 * |Hstar|⌋₊
      let J : Finset ℤ :=
        (Finset.Icc (-(Hbound : ℤ)) (Hbound : ℤ)).filter
          (fun h => 1 ≤ (h : ℝ) / Hstar ∧ (h : ℝ) / Hstar < 2)
      (∑ t ∈ 𝒯,
        ‖sourceSignedDispersionFrequencyBlock (J ×ˢ J)
          ψM (fun z => ψN (z / N)) M
          t.1 q₀ t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 a b₁ b₂ ℓ‖) ≤
        K * (Int.gcd (q₀ : ℤ) ℓ : ℝ) * R₀ * Q * N * U * V ^ 2 *
          x ^ (-4 * ε)
:= by
  classical
  have hLogAbsorb (A B η : ℝ) (hη : 0 < η) :
      ∀ᶠ x : ℝ in Filter.atTop, A * (Real.log x) ^ B ≤ x ^ η := by
    clear * - hη
    filter_upwards [((isLittleO_log_rpow_rpow_atTop B hη).const_mul_left A).eventuallyLE,
      Filter.eventually_ge_atTop (0 : ℝ)] with x hx hx0
    exact (le_abs_self (A * (Real.log x) ^ B)).trans (by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 η)] using hx)
  have hPrimeWindowMass (ψ : ℝ → ℝ) (c T N A E x : ℝ)
      (hc : 0 < c) (hcT : c ≤ T) (hN : 1 ≤ N) (hA : 0 ≤ A)
      (hx : Real.exp 1 ≤ x) (hs : Function.support ψ ⊆ Set.Icc c T)
      (hb : ∀ t : ℝ, |ψ t| ≤ A * (Real.log x) ^ E) :
      let I : Finset ℤ := Finset.Icc ⌈c * N⌉ ⌊T * N⌋
      (∀ n ∉ I, ψ ((n : ℝ) / N) = 0) ∧
        (∑ n ∈ I, |ψ ((n : ℝ) / N)|) ≤
          (T + 1) * A * N * (Real.log x) ^ E := by
    clear * - hc hcT hN hA hx hs hb
    intro I
    have hNpos : 0 < N := zero_lt_one.trans_le hN
    have hTpos : 0 < T := hc.trans_le hcT
    have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
    have hlog : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hx
    have hweight : 0 ≤ A * (Real.log x) ^ E := by positivity
    have hcard : (I.card : ℝ) ≤ (T + 1) * N := by
      have hcount := int_finset_card_le_of_mem_real_Icc I 0 (T * N)
        (mul_nonneg hTpos.le hNpos.le) (by
          intro n hn
          obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
          exact ⟨(mul_nonneg hc.le hNpos.le).trans (Int.ceil_le.mp hlo),
            Int.le_floor.mp hhi⟩)
      nlinarith
    constructor
    · intro n hn
      by_contra hn0
      have hsupport := hs hn0
      exact hn (Finset.mem_Icc.mpr
        ⟨Int.ceil_le.mpr ((le_div_iff₀ hNpos).mp hsupport.1),
          Int.le_floor.mpr ((div_le_iff₀ hNpos).mp hsupport.2)⟩)
    · calc
        (∑ n ∈ I, |ψ ((n : ℝ) / N)|) ≤
            ∑ _n ∈ I, A * (Real.log x) ^ E := Finset.sum_le_sum fun n _ => hb _
        _ = (I.card : ℝ) * (A * (Real.log x) ^ E) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((T + 1) * N) * (A * (Real.log x) ^ E) :=
          mul_le_mul_of_nonneg_right hcard hweight
        _ = _ := by ring
  have hChooseDivisor (R : Finset ℕ) (Y D : ℝ) (hY : 1 ≤ Y) (hD : 1 ≤ D)
      (hupper : ∀ r ∈ R, D ≤ Y * (r : ℝ))
      (hdense : ∀ r ∈ R, Nonempty
        (DenseDivisibilityWitness ⟨Y, hY⟩ 1 r)) :
      ∃ d : ℕ → ℕ, ∀ r ∈ R,
        0 < d r ∧ d r ∣ r ∧ D / Y ≤ (d r : ℝ) ∧ (d r : ℝ) ≤ D := by
    clear * - hY hD hupper hdense
    classical
    have hex (r : ℕ) : ∃ e : ℕ, r ∈ R →
        0 < e ∧ e ∣ r ∧ D / Y ≤ (e : ℝ) ∧ (e : ℝ) ≤ D := by
      by_cases hr : r ∈ R
      · obtain ⟨u, v, hproduct, _, hv, hlower, hbound⟩ :=
          (denseDivisibility_succ_iff.mp (hdense r hr)).2
            0 0 rfl D hD (hupper r hr)
        exact ⟨v, fun _ => ⟨denseDivisibility_pos hv,
          ⟨u, by simpa only [mul_comm] using hproduct⟩, hlower, hbound⟩⟩
      · exact ⟨1, fun h => False.elim (hr h)⟩
    choose d hd using hex
    exact ⟨d, hd⟩
  have hLiteralJWindow (C H Hstar : ℝ) (hstar : |Hstar| ≤ C * H) :
      let Hbound : ℕ := ⌊2 * |Hstar|⌋₊
      let J : Finset ℤ := (Finset.Icc (-(Hbound : ℤ)) (Hbound : ℤ)).filter
        (fun h => 1 ≤ (h : ℝ) / Hstar ∧ (h : ℝ) / Hstar < 2)
      (∀ h ∈ J, h ≠ 0 ∧ |(h : ℝ)| ≤ 2 * C * H) ∧
        J ⊆ (Finset.Icc (-(Hbound : ℤ)) (Hbound : ℤ)).filter (fun h => h ≠ 0) := by
    clear * - hstar
    intro Hbound J
    have hpoint (h : ℤ) (hh : h ∈ J) : h ≠ 0 ∧ |(h : ℝ)| ≤ 2 * C * H := by
      obtain ⟨hinterval, hratio⟩ := Finset.mem_filter.mp hh
      obtain ⟨hlower, hupper⟩ := Finset.mem_Icc.mp hinterval
      refine ⟨?_, ?_⟩
      · intro hzero
        simp only [hzero, Int.cast_zero, zero_div] at hratio
        norm_num at hratio
      · have habs : |(h : ℝ)| ≤ (Hbound : ℝ) := by
          apply abs_le.mpr
          exact ⟨by exact_mod_cast hlower, by exact_mod_cast hupper⟩
        calc
          |(h : ℝ)| ≤ (Hbound : ℝ) := habs
          _ ≤ 2 * |Hstar| := Nat.floor_le (by positivity)
          _ ≤ 2 * (C * H) := mul_le_mul_of_nonneg_left hstar (by norm_num)
          _ = 2 * C * H := by ring
    refine ⟨hpoint, ?_⟩
    intro h hh
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hh).1, (hpoint h hh).1⟩
  let C₁ : ℝ := 2 * C
  have hC₁two : 2 ≤ C₁ := by dsimp only [C₁]; linarith
  have hC₁ : 1 ≤ C₁ := by linarith
  have hC₁pos : 0 < C₁ := zero_lt_one.trans_le hC₁
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hCC₁ : C ≤ C₁ := by dsimp only [C₁]; linarith
  obtain ⟨ψD, CD, hψD, hsD, hDvalues, hDone, hCDpos, hDbound, hcoverUniform⟩ :=
    exists_source_scale_positive_short_cover
  obtain ⟨Xcover, hXcover, hcoverAt⟩ := hcoverUniform ε hε
  obtain ⟨K₂, Xtwo, hK₂, hXtwo, hTwoAt⟩ :=
    hsecondary C₁ cM TM cN TN hC₁ hcM hMT hcN hNT
      CM EM CN EN CD
      (fun j => ⟨(henvelopes j).1, (henvelopes j).2, (hCDpos j).le⟩)
  obtain ⟨Xtarget, hXtarget, hTargetAt⟩ :=
    sourceIncidence_divisor_target_resources C₁ «ω» δ ε hC₁ hω hδ hε
  let AM : ℝ := CM 0
  let AN : ℝ := (TN + 1) * CN 0
  let EM₀ : ℝ := max 0 (EM 0)
  let EN₀ : ℝ := max 0 (EN 0)
  let Efinal : ℝ := 2 * EM₀ + EN₀ + 1
  let Kfiber : ℝ := 128 * C₁ ^ 5 * (TM * AM) ^ 2 * AN + 48 * K₂ * C₁ ^ 2
  let Ktotal : ℝ := C₁ ^ 3 * Kfiber * (1 + 1 / Real.log 2)
  have hAM : 0 ≤ AM := (henvelopes 0).1
  have hAN : 0 ≤ AN := by
    clear * - hcN hNT henvelopes
    have hTN : 0 < TN := hcN.trans_le hNT
    dsimp only [AN]
    exact mul_nonneg (by positivity) (henvelopes 0).2
  have hEM₀ : 0 ≤ EM₀ := le_max_left _ _
  have hEN₀ : 0 ≤ EN₀ := le_max_left _ _
  have hEfinal : 0 ≤ Efinal := by dsimp only [Efinal]; positivity
  have hKfiber : 0 ≤ Kfiber := by dsimp only [Kfiber]; positivity
  obtain ⟨Xlog, hLogAt⟩ := (hLogAbsorb Ktotal (Efinal + 1) ε hε).exists_forall_of_atTop
  let thresholds : Finset ℝ :=
    {Real.exp 1, 3, C₁, Xcover, Xtwo, Xtarget, Xlog}
  have hthresholds : thresholds.Nonempty := ⟨Real.exp 1, by simp [thresholds]⟩
  let X₀ : ℝ := thresholds.sup' hthresholds id
  have hthreshold (z : ℝ) (hz : z ∈ thresholds) : z ≤ X₀ := Finset.le_sup' id hz
  refine ⟨1, X₀, zero_lt_one, hthreshold _ (by simp [thresholds]), ?_⟩
  intro x hx q₀ hq₀ hq₀sq a b₁ b₂ ℓ hprimitive₀ M N R₀ Q U V H Hstar γ
    hM hN hR₀ hQ hU hV hMNlo hMNhi hNγ hγlo hγhi hNR hRhi hRQlo hRQhi
    hHdef hH hUlo hUhi hVlo hVhi hUVlo hUVhi hq₀Q hrough hℓne hℓbound
    hHstarne hHstarlo hHstarhi ψM ψN hψM hψN hsM hsN hvalues hderivatives
    𝒯 h𝒯 Hbound J
  have hxt (z : ℝ) (hz : z ∈ thresholds) : z ≤ x := (hthreshold z hz).trans hx
  have hxe : Real.exp 1 ≤ x := hxt _ (by simp [thresholds])
  have hx3 : 3 ≤ x := hxt _ (by simp [thresholds])
  have hxC : C₁ ≤ x := hxt _ (by simp [thresholds])
  have hxtwo : Xtwo ≤ x := hxt _ (by simp [thresholds])
  have hxcover : Xcover ≤ x := hxt _ (by simp [thresholds])
  have hxtarget : Xtarget ≤ x := hxt _ (by simp [thresholds])
  have hxlog : Xlog ≤ x := hxt _ (by simp [thresholds])
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hpow (z : ℝ) : 0 < x ^ z := Real.rpow_pos_of_pos hx0 z
  have hlogx : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxe
  have hq₀one : (1 : ℝ) ≤ (q₀ : ℝ) := by exact_mod_cast hq₀
  have hq₀real : 0 < (q₀ : ℝ) := by exact_mod_cast hq₀
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  let g₀ : ℕ := Int.gcd (q₀ : ℤ) ℓ
  have hg₀nat : 0 < g₀ := Int.gcd_pos_of_ne_zero_left ℓ (by exact_mod_cast hq₀.ne')
  have hg₀one : (1 : ℝ) ≤ (g₀ : ℝ) := by exact_mod_cast hg₀nat
  have hg₀real : 0 < (g₀ : ℝ) := by exact_mod_cast hg₀nat
  let : NeZero q₀ := ⟨hq₀.ne'⟩
  have hMNlo₁ : x / C₁ ≤ M * N :=
    (div_le_div_of_nonneg_left hx0.le hCpos hCC₁).trans hMNlo
  have hMNhi₁ : M * N ≤ C₁ * x := hMNhi.trans (by gcongr)
  have hNR₁ : N ≤ C₁ * x ^ (δ + 4 * ε) * R₀ := hNR.trans (by gcongr)
  have hRhi₁ : R₀ ≤ C₁ * x ^ (-2 * ε) * N := hRhi.trans (by gcongr)
  have hRQlo₁ : x ^ (1 / 2 - ε) ≤ C₁ * R₀ * Q := hRQlo.trans (by gcongr)
  have hRQhi₁ : R₀ * Q ≤ C₁ * x ^ (1 / 2 + 2 * «ω» + ε) := hRQhi.trans (by gcongr)
  have hUlo₁ : x ^ (-δ - 5 * ε) * Q / ((q₀ : ℝ) * H) ≤ C₁ * U :=
    hUlo.trans (by gcongr)
  have hUhi₁ : U ≤ C₁ * x ^ (-5 * ε) * Q / H := hUhi.trans (by gcongr)
  have hVlo₁ : x ^ (5 * ε) * H / (q₀ : ℝ) ≤ C₁ * V := hVlo.trans (by gcongr)
  have hVhi₁ : V ≤ C₁ * x ^ (δ + 5 * ε) * H := hVhi.trans (by gcongr)
  have hUVlo₁ : Q / (q₀ : ℝ) ≤ C₁ * U * V := hUVlo.trans (by gcongr)
  have hUVhi₁ : U * V ≤ C₁ * Q / (q₀ : ℝ) := hUVhi.trans (by gcongr)
  have hq₀Q₁ : (q₀ : ℝ) ≤ C₁ * Q := hq₀Q.trans (by gcongr)
  have hℓbound₁ : |(ℓ : ℝ)| ≤ C₁ * N / R₀ := hℓbound.trans (by gcongr)
  have hHstarlo₁ : 1 ≤ C₁ * |Hstar| := hHstarlo.trans (by gcongr)
  have hHstarhi₁ : |Hstar| ≤ C₁ * H := hHstarhi.trans (by gcongr)
  let Dtarget : ℝ := N / (x ^ (50 * ε) * ((q₀ : ℝ) * H) ^ 2)
  obtain ⟨hHrough, hNone, hNx, hDtargetpos, hDtargetone, hDtargetN, hxδ, hDtargetUpper⟩ :=
    hTargetAt x hxtarget q₀ hq₀ M N R₀ Q H γ hM hN hR₀ hQ hH hNγ
      (hγmin.trans hγlo) (hγhi.trans hγmax) hMNlo₁ hNR₁ hRQhi₁ hHdef
  obtain ⟨hJdata, hJwindow⟩ := hLiteralJWindow C₁ H Hstar hHstarhi₁
  have hDderiv (j : ℕ) (t : ℝ) :
      |iteratedDeriv j ψD t| ≤ CD j * (Real.log x) ^ (0 : ℝ) := by
    simpa only [Real.rpow_zero, mul_one, Real.norm_eq_abs] using hDbound j t
  have hMamp (t : ℝ) : |ψM t| ≤ AM * (Real.log x) ^ EM₀ := by
    clear * - hderivatives hlogx hAM
    have hh := (hderivatives 0 t).1
    simp only [iteratedDeriv_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hlogx (le_max_right 0 (EM 0))) hAM)
  have hNamp (t : ℝ) : |ψN t| ≤ CN 0 * (Real.log x) ^ EN₀ := by
    clear * - hderivatives hlogx henvelopes
    have hh := (hderivatives 0 t).2
    simp only [iteratedDeriv_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hlogx (le_max_right 0 (EN 0))) (henvelopes 0).2)
  let Isupport : Finset ℤ := Finset.Icc ⌈cN * N⌉ ⌊TN * N⌋
  obtain ⟨hNzero, hNmass⟩ :=
    hPrimeWindowMass ψN cN TN N (CN 0) EN₀ x hcN hNT hNone (henvelopes 0).2 hxe hsN hNamp
  have hxneg (e : ℝ) (he : 0 ≤ e) : x ^ (-e) ≤ 1 := by
    clear * - hx1 he
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hx1 (show -e ≤ 0 by linarith)
  have hRsimple : R₀ ≤ C₁ * N := by
    clear * - hRhi₁ hxneg hε hN hC₁pos
    calc
      R₀ ≤ C₁ * x ^ (-2 * ε) * N := hRhi₁
      _ ≤ C₁ * 1 * N := by
        gcongr
        simpa only [neg_mul] using hxneg (2 * ε) (by positivity)
      _ = _ := by ring
  have hUsimple : U * H ≤ C₁ * Q := by
    clear * - hUhi₁ hHpos hxneg hε hQ hC₁pos
    have hu := (le_div_iff₀ hHpos).mp hUhi₁
    calc
      U * H ≤ C₁ * x ^ (-5 * ε) * Q := hu
      _ ≤ C₁ * 1 * Q := by
        gcongr
        simpa only [neg_mul] using hxneg (5 * ε) (by positivity)
      _ = _ := by ring
  have hHmul : H * (q₀ : ℝ) * M = x ^ ε * R₀ * Q ^ 2 := by
    clear * - hHdef hq₀real hM
    have hh := (eq_div_iff (mul_ne_zero hq₀real.ne' hM.ne')).mp hHdef
    simpa only [mul_assoc] using hh
  obtain ⟨_hMx, hRx, hQx, hHx, hUx, hVx⟩ :=
    sourceIncidence_coarse_heights «ω» δ ε C₁ x M N R₀ Q U V H (q₀ : ℝ)
      hωsmall hδsmall hεsmall hC₁ hx1 hxC hM hNone hNx hR₀ hQ hU hV hH hq₀one
      hMNhi₁ hNR₁ hRsimple hRQhi₁ hHrough hUsimple hVhi₁
  have hCVx : C₁ * V ≤ x ^ (15 : ℕ) := by
    clear * - hxC hVx hV hx0
    calc
      C₁ * V ≤ x * x ^ (14 : ℕ) := mul_le_mul hxC hVx hV.le hx0.le
      _ = _ := by ring
  let Kv : ℕ := ⌊C₁ * V⌋₊
  have hKvbound : (Kv : ℝ) ≤ C₁ * V := Nat.floor_le (mul_pos hC₁pos hV).le
  have hlogKv : 1 + Real.log (Kv : ℝ) ≤ 16 * Real.log x := by
    clear * - hlogx hKvbound hCVx
    by_cases hz : Kv = 0
    · simp only [hz, Nat.cast_zero, Real.log_zero]
      linarith
    · have hp : 0 < (Kv : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)
      have hlog := Real.log_le_log hp (hKvbound.trans hCVx)
      rw [Real.log_pow] at hlog
      norm_num at hlog
      linarith
  have hHV : H / V ≤ C₁ * (q₀ : ℝ) * x ^ (-5 * ε) := by
    clear * - hVlo₁ hV hq₀real hx0 hpow hC₁pos
    have hmul := (div_le_iff₀ hq₀real).mp hVlo₁
    apply (div_le_iff₀ hV).mpr
    calc
      H = (x ^ (5 * ε) * H) * x ^ (-5 * ε) := by
        have hp : x ^ (5 * ε) * x ^ (-5 * ε) = 1 := by
          rw [← Real.rpow_add hx0, show 5 * ε + -5 * ε = 0 by ring, Real.rpow_zero]
        rw [mul_right_comm, hp, one_mul]
      _ ≤ (C₁ * V * (q₀ : ℝ)) * x ^ (-5 * ε) :=
        mul_le_mul_of_nonneg_right hmul (hpow _).le
      _ = _ := by ring
  have hHbound : (Hbound : ℝ) ≤ 2 * C₁ * H :=
    (Nat.floor_le (by positivity : 0 ≤ 2 * |Hstar|)).trans (by
      calc
        2 * |Hstar| ≤ 2 * (C₁ * H) :=
          mul_le_mul_of_nonneg_left hHstarhi₁ (by norm_num)
        _ = 2 * C₁ * H := by ring)
  clear hTargetAt
  let Rs : Finset ℕ := 𝒯.image Prod.fst
  obtain ⟨d, hd⟩ := hChooseDivisor Rs (x ^ δ) Dtarget hxδ hDtargetone
    (by
      intro r hr
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨_, _, _, _, _, hrlo, _⟩ := h𝒯 t ht
      exact hDtargetUpper t.1
        ((div_le_div_of_nonneg_left hR₀.le hCpos hCC₁).trans hrlo))
    (by
      intro r hr
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hden, _⟩ := h𝒯 t ht
      simpa only [max_eq_right hxδ] using hden)
  have hd𝒯 (t : ℕ × ℕ × ℕ × ℕ × ℕ) (ht : t ∈ 𝒯) :
      0 < d t.1 ∧ d t.1 ∣ t.1 ∧ Dtarget / x ^ δ ≤ (d t.1 : ℝ) ∧
        (d t.1 : ℝ) ≤ Dtarget := hd t.1 (Finset.mem_image_of_mem Prod.fst ht)
  let key : (ℕ × ℕ × ℕ × ℕ × ℕ) → ℕ := fun t => Nat.log2 (d t.1)
  let aKey : (ℕ × ℕ × ℕ × ℕ × ℕ) → ℕ × ℕ × ℕ :=
    fun t => (t.1 / d t.1, t.2.1, t.2.2.2.2)
  let value : (ℕ × ℕ × ℕ × ℕ × ℕ) → ℕ × ℕ × ℕ :=
    fun t => (d t.1, t.2.2.1, t.2.2.2.1)
  let reconstruct : (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) → ℕ × ℕ × ℕ × ℕ × ℕ :=
    fun z p => (p.1 * z.1, z.2.1, p.2.1, p.2.2, z.2.2)
  let Ks : Finset ℕ := 𝒯.image key
  let As : ℕ → Finset (ℕ × ℕ × ℕ) :=
    fun k => (𝒯.filter fun t => key t = k).image aKey
  let Fs : ℕ → (ℕ × ℕ × ℕ) → Finset (ℕ × ℕ × ℕ) :=
    fun k z => (𝒯.filter fun t => key t = k ∧ aKey t = z).image value
  let Δs : ℕ → ℝ := fun k => (2 ^ k : ℕ)
  let Δshorts : ℕ → ℝ := fun k => x ^ (-5 * ε) * Δs k
  let Ds : ℕ → Finset ℕ := fun k => Finset.Icc (2 ^ k) (2 * 2 ^ k)
  let grids : ℕ → Finset ℕ := fun k => Finset.range (⌈Δs k / Δshorts k⌉₊ + 1)
  let centers : ℕ → ℕ → ℝ := fun k i => Δs k - Δshorts k + (i : ℝ) * Δshorts k
  let Dcut : ℕ → Finset ℕ := fun k => (grids k).biUnion (fun i =>
    Finset.Icc 1 ⌊centers k i + (5 / 2 : ℝ) * Δshorts k⌋₊)
  have hΔsone (k : ℕ) : 1 ≤ Δs k := by
    dsimp only [Δs]
    exact_mod_cast Nat.one_le_pow k 2 (by decide)
  have hΔspos (k : ℕ) : 0 < Δs k := zero_lt_one.trans_le (hΔsone k)
  have hcoverData (k : ℕ) := hcoverAt x hxcover (Δs k) (hΔspos k)
  have hcenterData (k i : ℕ) (hi : i ∈ grids k) :
      Δs k / 2 ≤ centers k i ∧ centers k i ≤ 2 * Δs k :=
    (hcoverData k).2.2.2.2.2.2.1 i hi
  have hgridCard (k : ℕ) : ((grids k).card : ℝ) ≤ 3 * x ^ (5 * ε) :=
    (hcoverData k).2.2.2.2.2.1
  have hcenterNonneg (k i : ℕ) (hi : i ∈ grids k) : 0 ≤ centers k i :=
    (div_nonneg (hΔspos k).le (by norm_num)).trans (hcenterData k i hi).1
  have hcoverD (k : ℕ) (d' : ℕ) (hd' : d' ∈ Ds k) :
      ∃ i ∈ grids k, Δshorts k ≤ (d' : ℝ) - centers k i ∧
        (d' : ℝ) - centers k i ≤ 2 * Δshorts k := by
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hd'
    apply (hcoverData k).2.2.2.2.2.2.2.1
    exact ⟨by
      change ((2 ^ k : ℕ) : ℝ) ≤ (d' : ℝ)
      exact_mod_cast hlo, by
      change (d' : ℝ) ≤ 2 * ((2 ^ k : ℕ) : ℝ)
      exact_mod_cast hhi⟩
  have hDcutpos (k : ℕ) (d' : ℕ) (hd' : d' ∈ Dcut k) : 0 < d' := by
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hd'
    exact (Finset.mem_Icc.mp hi).1
  have hAspos (k : ℕ) (z : ℕ × ℕ × ℕ) (hz : z ∈ As k) :
      0 < z.1 ∧ 0 < z.2.1 ∧ 0 < z.2.2 := by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    have ht' := (Finset.mem_filter.mp ht).1
    obtain ⟨hr, hu, _, _, hq₂, _⟩ := h𝒯 t ht'
    obtain ⟨hdpos, hdvd, _, _⟩ := hd𝒯 t ht'
    exact ⟨Nat.div_pos (Nat.le_of_dvd hr hdvd) hdpos, hu, hq₂⟩
  have hFsource (k : ℕ) (z p : ℕ × ℕ × ℕ) (hp : p ∈ Fs k z) :
      reconstruct z p ∈ 𝒯 ∧ d (reconstruct z p).1 = p.1 ∧
        Nat.log2 p.1 = k := by
    obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hp
    obtain ⟨ht𝒯, hkey, haKey⟩ := Finset.mem_filter.mp ht
    have hrecon : reconstruct (aKey t) (value t) = t := by
      rcases t with ⟨r, u, v₁, v₂, q₂⟩
      change (d r * (r / d r), u, v₁, v₂, q₂) = (r, u, v₁, v₂, q₂)
      rw [Nat.mul_div_cancel' (hd𝒯 (r, u, v₁, v₂, q₂) ht𝒯).2.1]
    have hrecon' : reconstruct z p = t := by
      simpa only [haKey, heq] using hrecon
    refine ⟨hrecon'.symm ▸ ht𝒯, ?_, ?_⟩
    · rw [hrecon']
      exact congrArg Prod.fst heq
    · have he := congrArg (fun p : ℕ × ℕ × ℕ => Nat.log2 p.1) heq
      exact he.symm.trans hkey
  have hFspos (k : ℕ) (z p : ℕ × ℕ × ℕ) (hp : p ∈ Fs k z) :
      0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 := by
    obtain ⟨ht, hd', _⟩ := hFsource k z p hp
    obtain ⟨_, _, hv₁, hv₂, _⟩ := h𝒯 _ ht
    exact ⟨hd' ▸ (hd𝒯 _ ht).1, hv₁, hv₂⟩
  have hFiberGeometry (k : ℕ) (z p : ℕ × ℕ × ℕ) (hp : p ∈ Fs k z) :
      p.1 ∈ Ds k ∧ R₀ / C₁ ≤ (z.1 : ℝ) * Δs k ∧
      (z.1 : ℝ) * Δs k ≤ C₁ * R₀ ∧
      N ≤ C₁ * (q₀ : ℝ) ^ 2 * x ^ (δ + 50 * ε) * H ^ 2 * Δs k ∧
      Δs k ≤ C₁ * N / ((q₀ : ℝ) ^ 2 * x ^ (50 * ε) * H ^ 2) ∧
      ((Ds k).card : ℝ) ≤ 2 * Δs k := by
    obtain ⟨ht, hd', hkey⟩ := hFsource k z p hp
    obtain ⟨hr, _, _, _, _, hrlo, hrhi, _⟩ := h𝒯 _ ht
    obtain ⟨hdpos, _, hdlo, hdhi⟩ := hd𝒯 _ ht
    rw [hd'] at hdpos hdlo hdhi
    have hzpos : 0 < z.1 :=
      Nat.pos_of_mul_pos_left hr
    have hh := sourceSigmaOne_dyadic_source_geometry C x δ ε N ((q₀ : ℝ) * H) R₀ hC hx1 hδ hε hN (by positivity) hR₀
      (p.1 * z.1) p.1 z.1 hr hdpos hzpos rfl hrlo hrhi hdlo hdhi
    obtain ⟨_, hlo, hhi, hrlo', hrhi', hΔlo, hΔhi, hcard⟩ := hh
    rw [hkey] at hlo hhi hrlo' hrhi' hΔlo hΔhi hcard
    refine ⟨Finset.mem_Icc.mpr ⟨hlo, hhi⟩, hrlo', hrhi', ?_, ?_, hcard⟩
    · simpa only [C₁, Δs, mul_pow, mul_assoc, mul_comm, mul_left_comm] using hΔlo
    · simpa only [C₁, Δs, mul_pow, mul_assoc, mul_comm, mul_left_comm] using hΔhi
  have hFnonempty (k : ℕ) (z : ℕ × ℕ × ℕ) (hz : z ∈ As k) :
      (Fs k z).Nonempty := by
    obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hz
    obtain ⟨ht𝒯, hkey⟩ := Finset.mem_filter.mp ht
    exact ⟨value t, Finset.mem_image.mpr
      ⟨t, Finset.mem_filter.mpr ⟨ht𝒯, hkey, heq⟩, rfl⟩⟩
  obtain ⟨P, hP, _, hcommon⟩ := sourceSigmaOne_global_cutoff_residues Ks As Fs Dcut q₀ hq₀
    (fun k _ z hz => hAspos k z hz)
    (fun k _ z _ p hp => hFspos k z p hp)
    (fun k _ d' hd' => hDcutpos k d' hd')
  let : NeZero P := ⟨hP.ne'⟩
  let aN : ℕ := (a : ZMod P).val
  let b₁N : ℕ := (b₁ : ZMod P).val
  let b₂N : ℕ := (b₂ : ZMod P).val
  have hcommon' := hcommon a b₁ b₂
  let f : (ℕ × ℕ × ℕ × ℕ × ℕ) → ℝ := fun t =>
    ‖sourceSignedDispersionFrequencyBlock (J ×ˢ J) ψM (fun z => ψN (z / N)) M
      t.1 q₀ t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 a b₁ b₂ ℓ‖
  have hFibers (k : ℕ) (hk : k ∈ Ks) (z : ℕ × ℕ × ℕ) (hz : z ∈ As k) :
      (∑ p ∈ Fs k z, f (reconstruct z p)) ≤
        Kfiber * (q₀ : ℝ) * (g₀ : ℝ) * Δs k * N * V ^ 2 *
          x ^ (-5 * ε) * (Real.log x) ^ Efinal := by
    obtain ⟨hr₁, hu₁, hq₂⟩ := hAspos k z hz
    obtain ⟨p₀, hp₀⟩ := hFnonempty k z hz
    obtain ⟨_, hrlo, hrhi, hΔlo, hΔhi, hDcard⟩ := hFiberGeometry k z p₀ hp₀
    have hΔ₁pos : 0 < Δshorts k := (hcoverData k).1
    have hDmajor (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2) : 1 ≤ ψD t :=
      (hDone t ht).ge
    have hF (p : ℕ × ℕ × ℕ) (hp : p ∈ Fs k z) :
        p.1 ∈ Ds k ∧ p.2.1 ∈ Finset.Icc 1 Kv ∧ p.2.2 ∈ Finset.Icc 1 Kv ∧
        V / C₁ ≤ ((max p.2.1 p.2.2 : ℕ) : ℝ) ∧
        Squarefree ((p.1 * z.1) * q₀ * z.2.1 * p.2.1 * z.2.2) ∧
        Squarefree ((p.1 * z.1) * q₀ * z.2.1 * p.2.2 * z.2.2) ∧
        Nat.Coprime ((p.1 * z.1) * q₀ * z.2.1 * p.2.1 * p.2.2 * z.2.2)
          (aN * b₁N * b₂N) := by
      obtain ⟨ht, _, _⟩ := hFsource k z p hp
      obtain ⟨_, _, hv₁, hv₂, _, _, _, _, _, hv₁lo, hv₁hi,
        _, hv₂hi, _, _, _, hs₁, hs₂, hprim⟩ := h𝒯 _ ht
      have hv₁upper : (p.2.1 : ℝ) ≤ C₁ * V := hv₁hi.trans (by gcongr)
      have hv₂upper : (p.2.2 : ℝ) ≤ C₁ * V := hv₂hi.trans (by gcongr)
      refine ⟨(hFiberGeometry k z p hp).1,
        Finset.mem_Icc.mpr ⟨hv₁, Nat.le_floor hv₁upper⟩,
        Finset.mem_Icc.mpr ⟨hv₂, Nat.le_floor hv₂upper⟩, ?_, hs₁, hs₂, ?_⟩
      · exact ((div_le_div_of_nonneg_left hV.le hCpos hCC₁).trans hv₁lo).trans
          (by exact_mod_cast le_max_left p.2.1 p.2.2)
      · exact (hcommon' k hk z hz p (Finset.mem_union_left _ hp)).2.1.mpr hprim
    have hbase := (sourceSelectedBlock_le_diagonal_add_sigmaTwo (Fs k z) (Ds k)
      (grids k) (centers k) J Isupport Hbound Kv (V / C₁) cM TM M
      (AM * (Real.log x) ^ EM₀) (Δshorts k) (1 / 2) (5 / 2)
      ψM (fun t => ψN (t / N)) ψD z.1 q₀ z.2.1 z.2.2 aN b₁N b₂N ℓ
      hr₁ hq₀ hu₁ hq₂ (div_pos hV hC₁pos) hcM hMT hM (by positivity)
      hsM hMamp hNzero hJwindow hΔ₁pos (by norm_num) (by norm_num)
      hsD (fun t => (hDvalues t).1) hDmajor (hcenterNonneg k) (hcoverD k) hF).1
    have htwo (v : ℕ × ℕ) (hv : v ∈ (Fs k z).image Prod.snd)
        (i : ℕ) (hi : i ∈ grids k) :
        sourceSigmaTwo J ψM (fun t => ψN (t / N)) ψD M (Δshorts k) (centers k i)
          z.1 q₀ z.2.1 v.1 v.2 z.2.2 aN b₁N b₂N ℓ ≤
            K₂ * (q₀ : ℝ) * (g₀ : ℝ) * Δs k * N * (Nat.gcd v.1 v.2 : ℝ) *
              x ^ (-10 * ε) := by
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨ht, _, _⟩ := hFsource k z p hp
      obtain ⟨_, _, hv₁, hv₂, _, _, _, hulo, huhi, hv₁lo, hv₁hi,
        hv₂lo, hv₂hi, hq₂lo, hq₂hi, _⟩ := h𝒯 _ ht
      have hbasecop : Nat.Coprime (z.1 * q₀ * z.2.1 * p.2.1 * p.2.2 * z.2.2)
          (aN * b₁N * b₂N) := by
        apply Nat.Coprime.of_dvd_left (b := aN * b₁N * b₂N) ?_ (hF p hp).2.2.2.2.2.2
        exact ⟨p.1, by ring⟩
      have hcenterlo : Δs k / C₁ ≤ centers k i :=
        (div_le_div_of_nonneg_left (hΔspos k).le (by norm_num) hC₁two).trans
          (hcenterData k i hi).1
      have hcenterhi : centers k i ≤ C₁ * Δs k :=
        (hcenterData k i hi).2.trans (mul_le_mul_of_nonneg_right hC₁two (hΔspos k).le)
      exact hTwoAt x hxtwo z.1 q₀ z.2.1 p.2.1 p.2.2 z.2.2 aN b₁N b₂N ℓ
        hr₁ hq₀ hu₁ hv₁ hv₂ hq₂
        (hbase p.2 (Finset.mem_image_of_mem Prod.snd hp)).1 hbasecop
        M N R₀ Q U V H Hstar (Δs k) (centers k i) γ
        hM hN hR₀ hQ hU hV (hΔsone k)
        hMNlo₁ hMNhi₁ hNγ hγlo hγhi hNR₁ hRhi₁ hRQlo₁ hRQhi₁ hHdef hH
        hUlo₁ hUhi₁ hVlo₁ hVhi₁ hUVlo₁ hUVhi₁ hrlo hrhi
        ((div_le_div_of_nonneg_left hU.le hCpos hCC₁).trans hulo)
        (huhi.trans (by gcongr))
        ((div_le_div_of_nonneg_left hV.le hCpos hCC₁).trans hv₁lo)
        (hv₁hi.trans (by gcongr))
        ((div_le_div_of_nonneg_left hV.le hCpos hCC₁).trans hv₂lo)
        (hv₂hi.trans (by gcongr))
        ((div_le_div_of_nonneg_left hQ.le (mul_pos hCpos hq₀real)
          (mul_le_mul_of_nonneg_right hCC₁ hq₀real.le)).trans hq₂lo)
        (hq₂hi.trans (by gcongr)) hq₀Q₁ hrough hΔlo hΔhi hcenterlo hcenterhi
        hℓne hℓbound₁ hHstarne hHstarlo₁ hHstarhi₁
        hNone hNx hRx hQx hHx hUx hCVx
        ψM ψN ψD hψM hψN hψD hsM hsN hsD hvalues hDvalues hderivatives hDderiv hJdata
    have hphysical := sourceSigmaOne_fixed_fiber_bound
      (Fs k z) (Ds k) (grids k) (centers k) J Isupport
      Hbound Kv x ε C₁ (Δs k) (Δshorts k) N V H cM TM M AM EM₀ AN EN₀ K₂ (g₀ : ℝ)
      ψM (fun t => ψN (t / N)) ψD z.1 q₀ z.2.1 z.2.2 aN b₁N b₂N ℓ
      hxe hε hC₁ (hΔspos k) hN hV hHpos rfl hr₁ hq₀ hu₁ hq₂
      hcM hMT hM hAM hAN hEM₀ hEN₀ hK₂ hg₀one hsM hMamp hNzero hNmass hJwindow
      hsD (fun t => (hDvalues t).1) hDmajor (hcenterNonneg k) (hcoverD k) hF
      hDcard (hgridCard k) hHbound hKvbound hlogKv hHV htwo
    have heq : (∑ p ∈ Fs k z, f (reconstruct z p)) =
        ∑ p ∈ Fs k z, ‖sourceDispersionFrequencyBlock (J ×ˢ J) ψM
          (fun t => ψN (t / N)) M (p.1 * z.1) q₀ z.2.1 p.2.1 p.2.2 z.2.2
            aN b₁N b₂N ℓ‖ := by
      apply Finset.sum_congr rfl
      intro p hp
      exact congrArg norm ((hcommon' k hk z hz p
        (Finset.mem_union_left _ hp)).2.2 (J ×ˢ J) ψM (fun t => ψN (t / N)) M ℓ).symm
    rw [heq]
    exact hphysical
  have htotal := sourceSigmaOne_total_fiber_bound 𝒯 d C₁ R₀ Q N U V (g₀ : ℝ) x ε Efinal Kfiber q₀
    hC₁ hR₀ hQ hN hU hV hg₀one hq₀ hxe hε hEfinal hKfiber
    (by
      intro t ht
      obtain ⟨hr, hu, _, _, hq₂, _, hrhi, _, huhi, _, _, _, _, _, hq₂hi, _⟩ := h𝒯 t ht
      obtain ⟨hdpos, hdvd, _, hdhi⟩ := hd𝒯 t ht
      exact ⟨hr, hu, hq₂, hdpos, hdvd, hrhi.trans (by gcongr),
        huhi.trans (by gcongr), hq₂hi.trans (by gcongr), hdhi.trans (hDtargetN.trans hNx)⟩)
    f hFibers
  have hlogAbsorb : Ktotal * (Real.log x) ^ (Efinal + 1) ≤ x ^ ε := hLogAt x hxlog
  have hpowers : x ^ (-5 * ε) * x ^ ε = x ^ (-4 * ε) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  calc
    (∑ t ∈ 𝒯, f t) ≤ Ktotal * (g₀ : ℝ) * R₀ * Q * N * U * V ^ 2 *
        x ^ (-5 * ε) * (Real.log x) ^ (Efinal + 1) := htotal
    _ = ((g₀ : ℝ) * R₀ * Q * N * U * V ^ 2 * x ^ (-5 * ε)) *
        (Ktotal * (Real.log x) ^ (Efinal + 1)) := by ring
    _ ≤ ((g₀ : ℝ) * R₀ * Q * N * U * V ^ 2 * x ^ (-5 * ε)) * x ^ ε :=
      mul_le_mul_of_nonneg_left hlogAbsorb (by positivity)
    _ = 1 * (Int.gcd (q₀ : ℤ) ℓ : ℝ) * R₀ * Q * N * U * V ^ 2 * x ^ (-4 * ε) := by
      rw [mul_assoc, hpowers]
      simp only [g₀, one_mul]

#print axioms sourceSigmaOne_selected_family_bound_of_incidence
end PrimeGap182Audit
