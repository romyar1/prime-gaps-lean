import IncidenceSourceLosses
import IncidenceSourceIndexBounds
import IncidenceSourceCoefficientPacket
import IncidenceSourceRowScales
import IncidenceMaskedFour

/-!
# The actual fixed-coefficient source block

The coefficient array is grouped from the literal signed source window.
The modulus split, frequency units, row divisors, Farey density and angular
count are all derived here. The local rank-four premise is the only
finite-field estimate used in this analytic step.
-/

noncomputable section
namespace PrimeGap182Audit
open Classical
open scoped BigOperators ContDiff

set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

theorem incidenceFixedSourceBlock_bound (hK4 : AllIncidenceRankFourBounds)
    (ε C R : ℝ) (hε : 0 < ε) (hC : 1 ≤ C) (hR : 1 ≤ R)
    (Ap Ep : ℕ → ℝ) (hAp : ∀ j, 0 ≤ Ap j) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in Filter.atTop,
      ∀ q₀ v₁ v₂ m w w₂ Dmax : ℕ,
      ∀ [NeZero m] [NeZero w],
      0 < q₀ → 0 < v₁ → 0 < v₂ → Squarefree m → q₀ ∣ m →
      0 < w → w ≤ Dmax → Nat.Coprime w m →
      (m : ℝ) ≤ x ^ (100 : ℝ) → (Dmax : ℝ) ≤ x ^ (100 : ℝ) →
      ∀ «ω» δ γ L Z A M N H Hstar V Δ₁ Δ d₀ P Bamp Lrow κ : ℝ,
      IncidenceSourceEnvelope x «ω» δ γ L Z A M N H q₀ (Nat.gcd v₁ v₂) w Δ₁ Δ m →
      0 < V → |Hstar| ≤ C * H →
      x ^ (5 * ε) * H / (q₀ : ℝ) ≤ C * V →
      V / C ≤ (v₁ : ℝ) → (v₁ : ℝ) ≤ C * V → (v₂ : ℝ) ≤ C * V →
      V ≤ C * x ^ (δ + 5 * ε) * H →
      0 ≤ Bamp → 0 ≤ Lrow → 0 ≤ κ → Δ₁ ≤ Δ →
      ∀ JT : ℕ,
      IncidenceSourceLosses x «ω» δ γ ε (ε / 100000) C R L Z P K Lrow Bamp JT →
      ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → Function.support ψ ⊆ Set.Icc (-R) R →
      (∀ j y, |iteratedDeriv j ψ y| ≤ Ap j * (Real.log x) ^ Ep j) →
      let Hbound : ℕ := ⌊2 * |Hstar|⌋₊
      let J : Finset ℤ := (Finset.Icc (-(Hbound : ℤ)) (Hbound : ℤ)).filter
        (fun h => 1 ≤ (h : ℝ) / Hstar ∧ (h : ℝ) / Hstar < 2)
      ∀ Y : ℤ,
      (incidenceSourceFrequencyBlock J v₁ v₂ m w w₂ Y).Nonempty →
      (∀ h ∈ incidenceSourceFrequencyBlock J v₁ v₂ m w w₂ Y,
        ((incidenceReducedFrequency v₁ v₂ h).natAbs : ℝ) ≤ x ^ (100 : ℝ)) →
      ∀ D : Finset ℕ, D ⊆ Finset.Icc 1 Dmax →
      (∀ e ∈ D, Nat.Coprime e m ∧ Nat.Coprime w e ∧
        |(w : ℝ) * e - d₀| ≤ (5 / 2) * Δ₁ ∧
        (1 / C ^ 2) * (C * Δ / w) ≤ (e : ℝ) ∧ (e : ℝ) ≤ 2 * (C * Δ / w)) →
      ∀ ρ : ℕ → ℝ, (∀ e ∈ D, 0 ≤ ρ e ∧ ρ e ≤ Lrow) →
      ∀ Aint Bint : ℤ, IsUnit (Aint : ZMod m) →
      ∀ S : ZMod q₀ → Finset (ZMod q₀),
      (∀ r, IsUnit r → ((S r).card : ℝ) ≤ κ) →
      ∀ a : ℤ × ℤ → ℂ,
      (∀ h ∈ incidenceSourceFrequencyBlock J v₁ v₂ m w w₂ Y, ‖a h‖ ≤ Bamp) →
      ∀ I : Finset ℤ, (∀ n : ℤ, ψ ((n : ℝ) / N) ≠ 0 → n ∈ I) →
      let F := incidenceSourceFrequencyBlock J v₁ v₂ m w w₂ Y
      let Frequencies := incidenceSourceQuotientSet J v₁ v₂ m w w₂ Y
      let coeff := incidenceGroupedCoefficient F (incidenceQuotientFrequency w v₁ v₂) a
      (∑ e ∈ D, ρ e * incidencePhysicalEnergyOrZero (m := m) (w := w)
        e Aint Bint Frequencies I coeff
          (fun n => if (n : ZMod q₀) ∈ S (e : ZMod q₀)
            then (ψ ((n : ℝ) / N) : ℂ) else 0)) ≤
        ((q₀ : ℝ) * κ * (Nat.gcd v₁ v₂ : ℝ) * N) ^ 2 *
          (81 * P ^ 7 * x ^ (-49 * ε)) := by
  let η := ε / 100000
  have hη : 0 < η := by dsimp only [η]; positivity
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  obtain ⟨K, hK, hwindow⟩ := incidenceMaskedPhysical_four_contributions
    hK4 η (1 / C ^ 2) R hη (by positivity) (zero_le_one.trans hR) Ap Ep hAp
  refine ⟨K, hK, ?_⟩
  filter_upwards [hwindow] with x hxwindow
  intro q₀ v₁ v₂ m w w₂ Dmax _ _ hq₀ hv₁ hv₂ hm hq₀m hw hwmax hwm hmheight hDmax
    «ω» δ γ L Z A M N H Hstar V Δ₁ Δ d₀ P Bamp Lrow κ
    hp hV hstar hVlo hv₁lo hv₁hi hv₂hi hVhi hBamp hLrow hκ hshort
    JT hs ψ hψ hsψ hder Hbound J Y hFnonempty hFheight D hDsub hDgeom ρ hρ
    Aint Bint hAint S hS a ha I hsI F Frequencies coeff
  obtain ⟨hx0, hL, hZ, hA, hM, hN, hH, hqR, hv₀, hwR, hΔ₁, hΔ, hmR⟩ := hp.positive
  have hx := hp.hx
  have hP : 1 ≤ P := by rw [hs.power]; exact Real.one_le_rpow hx (by positivity)
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have : NeZero q₀ := ⟨hq₀.ne'⟩
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  let g := Nat.gcd w₂ (m / q₀)
  let q := incidenceOscillatoryModulus m q₀ w₂
  obtain ⟨_, hg, hq, hmsplit, hcop0, hcopg, hqSF, hw₂q, hgw₂⟩ :=
    incidenceOscillatoryModulus_spec m q₀ w₂ hm hq₀m
  change m = q₀ * (g * q) at hmsplit
  have : NeZero g := ⟨hg.ne'⟩
  have : NeZero q := ⟨hq.ne'⟩
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hgpos : 0 < (g : ℝ) := by exact_mod_cast hg
  have hqm : q ∣ m := by
    rw [hmsplit]
    exact (dvd_mul_left q g).trans (dvd_mul_left _ q₀)
  have hqheight : (q : ℝ) ≤ x ^ (100 : ℝ) :=
    (Nat.cast_le.mpr (Nat.le_of_dvd hmpos hqm)).trans hmheight
  have hqsmall : (q : ℝ) ^ η ≤ P := by
    rw [hs.power]
    calc
      _ ≤ (x ^ (100 : ℝ)) ^ η := Real.rpow_le_rpow (Nat.cast_nonneg _) hqheight hη.le
      _ = x ^ (100 * η) := (Real.rpow_mul hx0.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx (by dsimp only [η]; linarith)
  have hq₀qm : (q₀ : ℝ) * q ≤ (m : ℝ) := by
    rw [hmsplit]
    simp only [Nat.cast_mul]
    have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
    nlinarith only [mul_le_mul_of_nonneg_left hg1 (mul_pos hqR hqpos).le]
  have hmquot : (m : ℝ) / ((q₀ : ℝ) * g) = q := by
    rw [hmsplit]
    simp only [Nat.cast_mul]
    field_simp
  obtain ⟨hHb, _, hJsub, hJcard⟩ := incidenceSource_window_bounds
    C x ε V H Hstar q₀ hC hx hε.le hV hp.hH hq₀ hstar hVlo
  obtain ⟨hYpos, hYheight⟩ := incidenceSource_block_frequency_height
    C x δ ε V H Hbound v₁ v₂ m w w₂ J hC hx0 hV hH hv₁ hv₂ hHb hJsub
    hv₁hi hv₂hi hVhi Y hFnonempty
  have hY : |(Y : ℝ)| ≤ L * (q₀ : ℝ) * x ^ δ * H ^ 2 / (Nat.gcd v₁ v₂ : ℝ) := by
    apply hYheight.trans
    calc
      _ = (4 * C ^ 3 * x ^ (5 * ε)) * x ^ δ * H ^ 2 / (Nat.gcd v₁ v₂ : ℝ) := by
        rw [Real.rpow_add hx0]
        ring
      _ ≤ L * x ^ δ * H ^ 2 / (Nat.gcd v₁ v₂ : ℝ) := by gcongr; exact hs.frequency
      _ ≤ _ := by
        have hqone : (1 : ℝ) ≤ q₀ := by exact_mod_cast hq₀
        have hh : L ≤ L * (q₀ : ℝ) := le_mul_of_one_le_right hL.le hqone
        gcongr
  obtain ⟨h₀, hh₀⟩ := hFnonempty
  have hquot₀ := incidenceSourceFrequencyBlock_quotient J v₁ v₂ m w w₂ hm.ne_zero hw.ne' hwm Y h₀ hh₀
  have hw₂ : 0 < w₂ := hquot₀.2.1
  have hw₂R : 1 ≤ (w₂ : ℝ) := by exact_mod_cast hw₂
  have hgwR : (g : ℝ) ≤ w₂ := by exact_mod_cast Nat.le_of_dvd hw₂ hgw₂
  have hFrequency (l : ℤ) (hl : l ∈ Frequencies) :=
    incidenceSourceQuotientSet_properties J v₁ v₂ m w w₂ hm.ne_zero hw hwm Y l hl
  have hFreqheight (l : ℤ) (hl : l ∈ Frequencies) :
      l ≠ 0 ∧ (l.natAbs : ℝ) ≤ x ^ (100 : ℝ) :=
    ⟨(hFrequency l hl).1,
      incidenceSourceQuotientSet_height J v₁ v₂ m w w₂ Y _ hFheight l hl⟩
  have hw₂e (e : ℕ) (he : e ∈ D) : Nat.Coprime w₂ e := by
    have hh := incidenceSupportedPart_coprime m e
      (incidenceQuotientFrequency w v₁ v₂ h₀).natAbs (hDgeom e he).1.symm
    change Nat.Coprime (incidenceFullSupportedPart m (incidenceQuotientFrequency w v₁ v₂ h₀)) e at hh
    rw [hquot₀.2.2.2.2] at hh
    exact hh
  have hRowDivSub : incidenceRowDivisors D ⊆ Finset.Icc 1 Dmax :=
    incidenceRowDivisors_subset D Dmax hDsub
  have hharm : (∑ t ∈ incidenceRowDivisors D, (t : ℝ)⁻¹) ≤ P :=
    hs.harmonic Dmax _ hRowDivSub hDmax
  have htpositive (t : ℕ) (ht : t ∈ incidenceRowDivisors D) : 0 < t :=
    (Finset.mem_Icc.mp (hRowDivSub ht)).1
  have hta (t : ℕ) (_ht : t ∈ incidenceRowDivisors D) (b : ℤ)
      (hb : b ∈ incidenceDividedCoefficientSet Frequencies (t * w₂)) :
      (b.natAbs.divisors.card : ℝ) ≤ P := by
    have hh := incidenceDividedCoefficientSet_height Frequencies (t * w₂)
      _ hFreqheight b hb
    exact hs.divisors _ (Int.natAbs_ne_zero.mpr hh.1) hh.2
  obtain ⟨hpoint, hpointSq, henergy⟩ := incidenceSource_coefficients_from_scales
    C x ε V H Hstar q₀ v₁ v₂ m w w₂ hC hx hε.le hV hp.hH
    hq₀ hv₁ hv₂ hstar hVlo hv₁lo Y a Bamp hBamp ha
  have hcommon := incidenceSource_coefficient_common_loss C Bamp P H q₀ (Nat.gcd v₁ v₂)
    coeff hC hq₀ hs.coefficient hpointSq henergy
  let Bcoeff := 6 * C ^ 3 * q₀ * (Nat.gcd v₁ v₂ : ℝ) * Bamp
  let E₀ := P * (q₀ : ℝ) ^ 2 * (Nat.gcd v₁ v₂ : ℝ) * H ^ 2
  have hBcoeff : 0 ≤ Bcoeff := by dsimp only [Bcoeff]; positivity
  have hE₀ : 0 ≤ E₀ := by dsimp only [E₀]; positivity
  have hBsq : Bcoeff ^ 2 ≤ P * (q₀ : ℝ) ^ 2 * (Nat.gcd v₁ v₂ : ℝ) ^ 2 := by
    have h36 : 36 * C ^ 6 * Bamp ^ 2 ≤ P :=
      (by nlinarith only [sq_nonneg Bamp, pow_nonneg hC0.le 6] :
        36 * C ^ 6 * Bamp ^ 2 ≤ 150 * C ^ 6 * Bamp ^ 2).trans hs.coefficient
    calc
      _ = (36 * C ^ 6 * Bamp ^ 2) * ((q₀ : ℝ) ^ 2 * (Nat.gcd v₁ v₂ : ℝ) ^ 2) := by
        dsimp only [Bcoeff]
        ring
      _ ≤ P * ((q₀ : ℝ) ^ 2 * (Nat.gcd v₁ v₂ : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right h36 (by positivity)
      _ = _ := by ring
  let esc := C * Δ / (w : ℝ)
  let Λ := |(Y : ℝ)| / (w : ℝ)
  let Ewidth := (5 / 2 : ℝ) * Δ₁
  let Js : ℕ → ℕ := fun c => max 1 ⌈Λ / (N / ((c : ℝ) * q₀ * esc))⌉₊
  let V₀ : ℕ → ℝ := fun c => (R / (1 / C ^ 2) + 2) * (N / ((c : ℝ) * q₀ * esc))
  have hesc : 0 < esc := by dsimp only [esc]; positivity
  have hΛ : 0 < Λ := div_pos hYpos hwR
  have hEwidth : 0 < Ewidth := by dsimp only [Ewidth]; positivity
  have hcdata (c : ℕ) (hc : c ∈ w.divisors) : 1 ≤ (c : ℝ) ∧ (c : ℝ) ≤ w := by
    exact ⟨by exact_mod_cast Nat.pos_of_mem_divisors hc,
      by exact_mod_cast Nat.le_of_dvd hw (Nat.dvd_of_mem_divisors hc)⟩
  have hVdata (c : ℕ) (hc : c ∈ w.divisors) :
      H ^ 2 ≤ V₀ c ∧ V₀ c ≤ (R * C ^ 2 + 2) * (N * w / ((q₀ : ℝ) * Δ)) :=
    (hp.source_actual_farey_scale C R c hC hR (hcdata c hc).1 (hcdata c hc).2).imp_right And.left
  have hJdata (c : ℕ) (hc : c ∈ w.divisors) :
      0 < Js c ∧ Λ ≤ (Js c : ℝ) * (N / ((c : ℝ) * q₀ * esc)) ∧
        (Js c : ℝ) ≤ 2 * C * L * x ^ δ :=
    hp.source_actual_angular_count C c |(Y : ℝ)| hC (hcdata c hc).1 (hcdata c hc).2 hYpos hY
  have hdensity (c : ℕ) (hc : c ∈ w.divisors) (t : ℕ)
      (ht : t ∈ incidenceRowDivisors D) :
      (Λ / ((t * w₂ : ℕ) : ℝ)) * V₀ c ≤ (q₀ : ℝ) * q := by
    have htR : 1 ≤ (t : ℝ) := by exact_mod_cast htpositive t ht
    have hd := hp.source_actual_incidence_density C R c |(Y : ℝ)| w₂ t g
      hC hR (hcdata c hc).1 (hcdata c hc).2 hYpos hw₂R htR hgpos hgwR hY
    change _ ≤ _ at hd
    have hd' : ((Λ / ((t * w₂ : ℕ) : ℝ)) * V₀ c) / (q : ℝ) ≤ (q₀ : ℝ) := by
      calc
        _ = (|(Y : ℝ)| / ((w : ℝ) * w₂ * t)) * V₀ c / ((m : ℝ) / ((q₀ : ℝ) * g)) := by
          rw [hmquot]
          dsimp only [Λ]
          rw [Nat.cast_mul]
          ring
        _ ≤ (R * C ^ 2 + 2) * ((q₀ : ℝ) * L ^ 4 * x ^ (2 * γ + 4 * «ω» + 2 * δ - 1)) := hd
        _ = (q₀ : ℝ) * ((R * C ^ 2 + 2) * L ^ 4 * x ^ (2 * γ + 4 * «ω» + 2 * δ - 1)) := by ring
        _ ≤ (q₀ : ℝ) * 1 := mul_le_mul_of_nonneg_left hs.density hqR.le
        _ = _ := mul_one _
    exact (div_le_iff₀ hqpos).mp hd'
  have hcard (c : ℕ) (hc : c ∈ w.divisors) (t : ℕ)
      (_ht : t ∈ incidenceRowDivisors D) :
      ((incidenceDividedCoefficientSet Frequencies (t * w₂)).card : ℝ) ≤
        (25 * C ^ 2) * V₀ c := by
    exact (incidenceSourceDividedCoefficientSet_card J v₁ v₂ m w w₂ Y (t * w₂)
      C H (by positivity) hJcard).trans
        (mul_le_mul_of_nonneg_left (hVdata c hc).1 (by positivity))
  have hterms (c : ℕ) (hc : c ∈ w.divisors) :
      V₀ c * incidenceFourTerms η (Ewidth / ((w : ℝ) * q₀)) esc q Λ w₂ Bcoeff E₀ P
        (∑ t ∈ incidenceRowDivisors D, (t : ℝ)⁻¹) (Js c) /
          ((Nat.gcd v₁ v₂ : ℝ) ^ 2 * N ^ 2) ≤ x ^ (-49 * ε) := by
    have hVlarge : V₀ c ≤ P * N * w / ((q₀ : ℝ) * Δ) :=
      (hVdata c hc).2.trans (by
        have hh := mul_le_mul_of_nonneg_right hs.geometry
          (show 0 ≤ N * w / ((q₀ : ℝ) * Δ) by positivity)
        simpa only [mul_div_assoc, mul_assoc] using hh)
    have hΛlarge : Λ ≤ L * (q₀ : ℝ) * x ^ δ * H ^ 2 / ((w : ℝ) * (Nat.gcd v₁ v₂ : ℝ)) := by
      exact (div_le_div_of_nonneg_right hY hwR.le).trans_eq (by ring)
    have hmass : P * E₀ ≤ P ^ 2 * (q₀ : ℝ) ^ 2 * (Nat.gcd v₁ v₂ : ℝ) * H ^ 2 := by
      apply le_of_eq
      dsimp only [E₀]
      ring
    have hpointmass : Bcoeff ^ 2 * (∑ t ∈ incidenceRowDivisors D, (t : ℝ)⁻¹) ≤
        P ^ 2 * (q₀ : ℝ) ^ 2 * (Nat.gcd v₁ v₂ : ℝ) ^ 2 := by
      calc
        _ ≤ (P * (q₀ : ℝ) ^ 2 * (Nat.gcd v₁ v₂ : ℝ) ^ 2) * P :=
          mul_le_mul hBsq hharm (by positivity) (by positivity)
        _ = _ := by ring
    have hn := incidenceFourTerms_normalize x δ η P L (2 * C * L)
      q q₀ m (V₀ c) (Ewidth / ((w : ℝ) * q₀)) esc Λ w w₂ (Nat.gcd v₁ v₂)
      H N Δ₁ Δ Bcoeff E₀ P (∑ t ∈ incidenceRowDivisors D, (t : ℝ)⁻¹) (Js c)
      hx0 hP hL (by positivity) hqpos hqR hmR hwR hw₂R hv₀ hH hN hΔ₁ hΔ
      ((sq_nonneg H).trans (hVdata c hc).1) (by positivity) hesc.le hΛ.le hE₀ hP0.le
      (by positivity) hq₀qm hqsmall hshort hVlarge
      (by dsimp only [Ewidth]; gcongr; exact hs.width)
      (by dsimp only [esc]; gcongr; exact hs.C_small)
      hΛlarge (by simpa only [mul_assoc] using (hJdata c hc).2.2) hmass hpointmass
    exact hn.trans (incidenceCorrectedContributions_saving hp ε P L (2 * C * L)
      hε hP hL (by positivity) (le_of_eq hs.power) hs.envelope
      (hs.envelope.trans (Real.rpow_le_rpow_of_exponent_le hx (by linarith))) hs.angular
      hs.retreat hs.oscillatory_gap hs.row_gap hs.large)
  have hDwindow (e : ℕ) (he : e ∈ D) :
      e ≠ 0 ∧ Nat.Coprime e (q₀ * (g * q)) ∧ Nat.Coprime w e ∧
        Nat.Coprime w₂ e ∧ (e.divisors.card : ℝ) ≤ P ∧
        |(w : ℝ) * e - d₀| ≤ Ewidth ∧ (1 / C ^ 2) * esc ≤ (e : ℝ) ∧ (e : ℝ) ≤ 2 * esc := by
    have he0 : 0 < e := (Finset.mem_Icc.mp (hDsub he)).1
    exact ⟨he0.ne', by simpa only [← hmsplit] using (hDgeom e he).1,
      (hDgeom e he).2.1, hw₂e e he,
      hs.divisors e he0.ne' ((Nat.cast_le.mpr (Finset.mem_Icc.mp (hDsub he)).2).trans hDmax),
      (hDgeom e he).2.2⟩
  have hb := hxwindow ψ hψ hsψ hder q₀ g q w hcop0 hcopg hqSF
    (by simpa only [← hmsplit] using hwm) Aint Bint
    (by
      rw [incidenceIntegerUnit_iff] at hAint ⊢
      simpa only [← hmsplit] using hAint) w₂ hw₂ hw₂q hgw₂
    N esc Λ Ewidth d₀ Lrow κ (25 * C ^ 2) Bcoeff E₀ P P P q₀
    hN hesc hΛ hEwidth hLrow hκ (by positivity) hBcoeff hP0.le hP0.le hP0.le
    (by exact_mod_cast hq₀) D ρ hρ hDwindow S hS Frequencies
    (fun l hl => ⟨(hFrequency l hl).2.2.1, (hFrequency l hl).2.2.2.2.2.1,
      (hFrequency l hl).2.2.2.2.2.2,
      incidenceIntegerUnit_of_dvd hqm _ (hFrequency l hl).2.2.2.1⟩)
    (fun l hl => hs.divisors _ (Int.natAbs_ne_zero.mpr (hFreqheight l hl).1) (hFreqheight l hl).2)
    hta coeff (fun l _ => hpoint l) (hcommon.2 Frequencies) I hsI Js
    (fun c hc => ⟨(hJdata c hc).1, (hJdata c hc).2.1⟩) hdensity hcard
  have hb' : (∑ e ∈ D, ρ e * incidencePhysicalEnergyOrZero (m := m) (w := w)
        e Aint Bint Frequencies I coeff
          (fun n => if (n : ZMod q₀) ∈ S (e : ZMod q₀)
            then (ψ ((n : ℝ) / N) : ℂ) else 0)) ≤
      (w.divisors.card : ℝ) * κ * P *
        ((q₀ : ℝ) * κ * ((1 + x ^ (2 * η)) * K * Lrow) *
          (9 * (q₀ : ℝ) * (25 * C ^ 2 + 8 * P))) *
        ∑ c ∈ w.divisors, V₀ c * incidenceFourTerms η (Ewidth / ((w : ℝ) * q₀))
          esc q Λ w₂ Bcoeff E₀ P (∑ t ∈ incidenceRowDivisors D, (t : ℝ)⁻¹) (Js c) := by
    simpa only [← hmsplit] using hb
  have hwdiv : (w.divisors.card : ℝ) ≤ P :=
    hs.divisors w hw.ne' ((Nat.cast_le.mpr hwmax).trans hDmax)
  exact incidenceMaskedMain_collect w.divisors
    (fun c => V₀ c * incidenceFourTerms η (Ewidth / ((w : ℝ) * q₀)) esc q Λ w₂ Bcoeff E₀ P
      (∑ t ∈ incidenceRowDivisors D, (t : ℝ)⁻¹) (Js c))
    _ P q₀ κ (Nat.gcd v₁ v₂) N (w.divisors.card : ℝ) P (1 + x ^ (2 * η)) K Lrow
    (25 * C ^ 2) P (x ^ (-49 * ε)) hP hqR.le hκ hv₀ hN (by positivity)
    ⟨Nat.cast_nonneg _, hwdiv⟩ ⟨hP0.le, le_rfl⟩ ⟨by positivity, hs.window⟩
    ⟨hK.le, hs.kernel⟩ ⟨hLrow, hs.row⟩ ⟨by positivity, hs.cardinal⟩
    ⟨hP0.le, le_rfl⟩ hwdiv hterms hb'

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceFixedSourceBlock_bound
