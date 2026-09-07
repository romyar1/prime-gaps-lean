import Selberg39

/-! Ordinary Selberg moments at the new support radius.

The first proof generalizes the checked 39-coordinate CRT argument from
Selberg39 to every positive radius S with rho*S < 1/2. The two following
proofs adapt the pinned public PrimeGaps186 harmonic/ordinary theorems
(lines 201212--201416) from 40 to 39 coordinates and this general radius.
The upstream attribution and license notices in Selberg39 apply to the
adapted portions. No analytic limit or distribution estimate is assumed.
-/

noncomputable section
open MeasureTheory Filter PrimeGap186
open scoped BigOperators Topology

namespace PrimeGap182.Selberg

open Classical in
theorem selberg39_uniform_real_diagonal_radius
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (S : ℝ) (hS : 0 < S)
    (hsmall : (2624989 / 10000000 : ℝ) * S < 1 / 2)
    (M : ℝ) (hM : 0 ≤ M) :
    let ρ : ℝ := 2624989 / 10000000
    let h : Fin 39 → ℕ :=
      𝓗.orderEmbOfFin h𝓗_card
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℝ in Filter.atTop,
        let W := presievingModulus 𝓗 x
        let R := x ^ ρ
        let B := fragmentNormalization W R
        ∀ (y : (Fin 39 → ℕ) →₀ ℝ) (v : ℕ),
          (∀ r ∈ y.support,
            Squarefree (∏ i, r i) ∧ Nat.Coprime (∏ i, r i) W ∧
              ((∏ i, r i : ℕ) : ℝ) ≤ R ^ S) →
          (∀ r, |y r| ≤ M / B ^ 39) →
          let D := y.support.biUnion
            (fun r => Fintype.piFinset (fun i => (r i).divisors))
          |(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
              if Nat.ModEq W n v then
                (∑ d ∈ D, if ∀ i, d i ∣ n + h i then
                  selbergCoefficient y d else 0) ^ 2 else 0) -
            x / (W : ℝ) *
              y.sum (fun r yr => yr ^ 2 / (∏ i, ((r i).totient : ℝ)))| ≤
            ε * (x / (W : ℝ) / B ^ 39) := by
  intro ρ h ε hε
  let a : ℝ := ρ * S
  let J : ℕ := 2 ^ (39 + 2) - 1
  let C : ℝ := 8 * Real.exp 8 * 1482 * (Real.exp 8) ^ 1481
  let d₀ : ℝ → ℕ := fun x => ⌊Real.log (Real.log (Real.log x))⌋₊
  have hρ : 0 < ρ := by norm_num [ρ]
  have ha : 0 < a := mul_pos hρ hS
  have ha1 : a < 1 := by
    dsimp only [a, ρ]
    linarith only [hsmall]
  have hδ : 0 < 1 - 2 * a := by
    dsimp only [a, ρ]
    linarith only [hsmall]
  have hM2 : 0 ≤ M ^ 2 := by simpa only [pow_two] using mul_nonneg hM hM
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hε2 : 0 < ε / 2 := half_pos hε
  have hDnat : Tendsto d₀ atTop atTop :=
    tendsto_nat_floor_atTop.comp (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop))
  have hDreal : Tendsto (fun x => (d₀ x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hDnat
  have hmass := harmonic_fragment_normalizer_tendsto 𝓗 ρ S hρ hS
  have hcrossLimit : Tendsto
      (fun x : ℝ => M ^ 2 * C *
        (harmonicFragmentMass (presievingModulus 𝓗 x) (x ^ ρ) S /
          fragmentNormalization (presievingModulus 𝓗 x) (x ^ ρ)) ^ 39 /
            (d₀ x : ℝ)) atTop (nhds 0) :=
    ((hmass.pow 39).const_mul (M ^ 2 * C)).div_atTop hDreal
  have hlogLimit : Tendsto
      (fun x : ℝ => Real.log x ^ (2 * J + 1) / x ^ (1 - 2 * a))
      atTop (nhds 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop ((2 * J + 1 : ℕ) : ℝ) hδ).tendsto_div_nhds_zero
  have hcrtLimit : Tendsto
      (fun x : ℝ => 2 * M ^ 2 * Real.log x ^ (2 * J + 1) / x ^ (1 - 2 * a))
      atTop (nhds 0) := by
    simpa only [mul_zero, mul_div_assoc] using hlogLimit.const_mul (2 * M ^ 2)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    presieving_le_mul_log_eventually 𝓗 ρ hρ,
    presieving_le_mul_log_eventually 𝓗 1 zero_lt_one,
    floor_rpow_log_envelope a ha ha1, hDnat.eventually_gt_atTop 0,
    hcrtLimit.eventually_le_const hε2, hcrossLimit.eventually_le_const hε2]
    with x hx hWρ hWlog hfloor hD₀ hcrt hcross
  intro W R B
  let D₀ : ℕ := d₀ x
  let L : ℕ := ⌊R ^ S⌋₊
  let Q : ℝ := (1 + Real.log (L : ℝ)) ^ J
  let F : ℝ := ∑ n ∈ Finset.Icc 1 L,
    if Squarefree n ∧ Nat.Coprime n W then 1 / (n.totient : ℝ) else 0
  let T : ℝ := harmonicFragmentMass W R S
  let A : ℝ := x / (W : ℝ) / B ^ 39
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have hW : 0 < W := presieving_pos 𝓗 x
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hD₀R : (0 : ℝ) < D₀ := by exact_mod_cast hD₀
  have hcapEq : R ^ S = x ^ a := by
    change (x ^ ρ) ^ S = x ^ a
    rw [← Real.rpow_mul hx0.le]
  have hcap : 1 ≤ R ^ S := by
    rw [hcapEq]
    exact (Nat.one_le_floor_iff _).mp hfloor.1
  have hLle : (L : ℝ) ≤ x ^ a := by
    dsimp only [L]
    rw [hcapEq]
    exact Nat.floor_le (Real.rpow_nonneg hx0.le a)
  have hlogL0 : 0 ≤ 1 + Real.log (L : ℝ) := by
    simpa only [L, hcapEq] using hfloor.2.1
  have hlogL : 1 + Real.log (L : ℝ) ≤ Real.log x := by
    simpa only [L, hcapEq] using hfloor.2.2
  have hQ0 : 0 ≤ Q := pow_nonneg hlogL0 J
  have hQle : Q ≤ Real.log x ^ J := pow_le_pow_left₀ hlogL0 hlogL J
  have hφ : (1 : ℝ) ≤ (Nat.totient W : ℝ) := by
    exact_mod_cast (show 1 ≤ Nat.totient W from Nat.totient_pos.mpr hW)
  have hB1 : 1 ≤ B := by
    change 1 ≤ ((Nat.totient W : ℝ) / (W : ℝ)) * Real.log (x ^ ρ)
    rw [Real.log_rpow hx0, div_mul_eq_mul_div]
    exact (one_le_div hWR).mpr
      (hWρ.trans (le_mul_of_one_le_left (mul_nonneg hρ.le hlog) hφ))
  have hB : 0 < B := zero_lt_one.trans_le hB1
  have hA : 0 < A := div_pos (div_pos hx0 hWR) (pow_pos hB 39)
  have hWlog' : (W : ℝ) ≤ Real.log x := by simpa only [one_mul] using hWlog
  have hF0 : 0 ≤ F := by
    dsimp only [F]
    exact Finset.sum_nonneg fun n _ =>
      ite_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg n.totient)) le_rfl
  have hFT : F ≤ T := finite_mean_le_fragment_mass W R S hcap
  have hCeq :
      (8 * Real.exp 8 / (D₀ : ℝ)) * 1482 * (Real.exp 8) ^ 1481 = C / (D₀ : ℝ) := by
    dsimp only [C]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  have hinj : Function.Injective h :=
    (𝓗.orderEmbOfFin h𝓗_card).injective
  have hcover : ∀ i j : Fin 39, h i ≠ h j → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h i) (h j) → p ∣ W := by
    intro i j hij p hp hpd
    exact difference_prime_dvd_presieving 𝓗 x
      (𝓗.orderEmbOfFin_mem h𝓗_card i)
      (𝓗.orderEmbOfFin_mem h𝓗_card j) hij hp hpd
  intro y v hy hbound D
  have hD (e : DecidableEq (Fin 39)) :
      y.support.biUnion (fun r => @Fintype.piFinset (Fin 39) e inferInstance
        (fun _ => ℕ) (fun i => (r i).divisors)) = D := by
    ext d
    simp only [D, Finset.mem_biUnion, Fintype.mem_piFinset]
  have hyL : ∀ r ∈ y.support,
      Squarefree (∏ i, r i) ∧ Nat.Coprime (∏ i, r i) W ∧ (∏ i, r i) ≤ L := by
    intro r hr
    exact ⟨(hy r hr).1, (hy r hr).2.1,
      (Nat.le_floor_iff (zero_le_one.trans hcap)).mpr (hy r hr).2.2⟩
  have hl1 := selbergCoefficient_l1_le y L (M / B ^ 39)
    (fun r hr => ⟨(hyL r hr).1, (hyL r hr).2.2⟩) hbound
  simp only [hD, Fintype.card_fin] at hl1
  change (∑ d ∈ D, |selbergCoefficient y d|) ≤ M / B ^ 39 * (L : ℝ) * Q at hl1
  have hsum0 : 0 ≤ ∑ d ∈ D, |selbergCoefficient y d| :=
    Finset.sum_nonneg fun d _ => abs_nonneg _
  have hprod₁ :
      2 * M ^ 2 * (W : ℝ) * (L : ℝ) ^ 2 ≤
        2 * M ^ 2 * Real.log x * (x ^ a) ^ 2 :=
    mul_le_mul
      (mul_le_mul_of_nonneg_left hWlog' (mul_nonneg (by norm_num) hM2))
      (pow_le_pow_left₀ (Nat.cast_nonneg L) hLle 2)
      (sq_nonneg (L : ℝ)) (mul_nonneg (mul_nonneg (by norm_num) hM2) hlog)
  have hprod₂ :
      2 * M ^ 2 * (W : ℝ) * (L : ℝ) ^ 2 * Q ^ 2 ≤
        2 * M ^ 2 * Real.log x * (x ^ a) ^ 2 * (Real.log x ^ J) ^ 2 :=
    mul_le_mul hprod₁ (pow_le_pow_left₀ hQ0 hQle 2) (sq_nonneg Q)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM2) hlog) (sq_nonneg _))
  have hcrtNorm :
      2 * (∑ d ∈ D, |selbergCoefficient y d|) ^ 2 / A ≤
        2 * M ^ 2 * Real.log x ^ (2 * J + 1) / x ^ (1 - 2 * a) := by
    calc
      _ ≤ 2 * (M / B ^ 39 * (L : ℝ) * Q) ^ 2 / A :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsum0 hl1 2) (by norm_num)) hA.le
      _ ≤ 2 * M ^ 2 * (W : ℝ) * (L : ℝ) ^ 2 * Q ^ 2 / x :=
        normalized_square_le M B (L : ℝ) Q x (W : ℝ) hB1 hx0 hWR
      _ ≤ 2 * M ^ 2 * Real.log x * (x ^ a) ^ 2 * (Real.log x ^ J) ^ 2 / x :=
        div_le_div_of_nonneg_right hprod₂ hx0.le
      _ = _ := crt_power_identity M x a J hx0
  have hcrossNorm :
      (x / (W : ℝ) * ((M / B ^ 39) ^ 2 * (C / (D₀ : ℝ)) * F ^ 39)) / A ≤
        M ^ 2 * C * (T / B) ^ 39 / (D₀ : ℝ) := by
    calc
      _ = M ^ 2 * C * (F / B) ^ 39 / (D₀ : ℝ) :=
        normalized_cross_eq M B F C (D₀ : ℝ) x (W : ℝ) 39 hB hD₀R hx0 hWR
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (div_nonneg hF0 hB.le)
            (div_le_div_of_nonneg_right hFT hB.le) 39) (mul_nonneg hM2 hC)) hD₀R.le
  have hite (n : ℕ) (d : Fin 39 → ℕ) :
      @ite ℝ (∀ i, d i ∣ n + h i) Fintype.decidableForallFintype
        (selbergCoefficient y d) 0 =
          if ∀ i, d i ∣ n + h i then selbergCoefficient y d else 0 :=
    ite_cond_congr rfl
  have htwo := selberg_square_real_interval_two_error h hinj y L W v D₀ (M / B ^ 39)
    hW hD₀ (primorial_dvd_presieving 𝓗 x) hyL hbound hcover x hx0.le
  simp only [hD, hite, Fintype.card_fin] at htwo
  change _ ≤ 2 * (∑ d ∈ D, |selbergCoefficient y d|) ^ 2 +
    x / (W : ℝ) * ((M / B ^ 39) ^ 2 *
      ((8 * Real.exp 8 / (D₀ : ℝ)) * 1482 * (Real.exp 8) ^ 1481) * F ^ 39) at htwo
  rw [hCeq] at htwo
  exact htwo.trans (by
    calc
      _ ≤ (ε / 2) * A + (ε / 2) * A := add_le_add
        ((div_le_iff₀ hA).mp (hcrtNorm.trans hcrt))
        ((div_le_iff₀ hA).mp (hcrossNorm.trans hcross))
      _ = ε * A := by ring)


theorem canonical39_fixed_band_harmonic_tendsto
    {𝓗 : Finset ℕ}
    {m : ℕ} (κ : ℝ) (hκ : 0 < κ)
    (a : Fin (m + 2) → ℝ) (ha : StrictMono a)
    (ha0 : a 0 = 0) (haLast : a (Fin.last (m + 1)) = κ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hF : Measurable F) (hbF : Bornology.IsBounded (Set.range F)) :
    let ν : Measure (Fin (m + 1) → ℝ) :=
      ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * κ) •
        Measure.map (fragmentBandMasses a) (fragmentLaw κ)
    (∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => ν), ContinuousAt F X) →
    let ρ : ℝ := 2624989 / 10000000
    let W : ℝ → ℕ := presievingModulus 𝓗
    let R : ℝ → ℝ := fun x => x ^ ρ
    let B : ℝ → ℝ := fun x => fragmentNormalization (W x) (R x)
    let q : ℝ → ℕ := fun x =>
      ∏ p ∈ fragmentPrimes (W x) (R x) κ, p
    let T : ℝ → Finset (Fin 39 → ℕ) := fun x =>
      (Fintype.piFinset (fun _ : Fin 39 => (q x).divisors)).filter
        (fun r => Squarefree (∏ j, r j))
    let X : ℝ → ℕ → Fin (m + 1) → ℝ := fun x s =>
      fragmentBandMasses a (primeLogConfiguration (R x) s)
    let y : ℝ → ((Fin 39 → ℕ) →₀ ℝ) := fun x =>
      ∑ r ∈ T x, Finsupp.single r (F (fun j => X x (r j)) / B x ^ 39)
    Filter.Tendsto
      (fun x : ℝ => B x ^ 39 *
        (y x).sum (fun r yr => yr ^ 2 / (∏ j, ((r j).totient : ℝ))))
      Filter.atTop
      (nhds (∫ X : Fin 39 → Fin (m + 1) → ℝ, F X ^ 2
        ∂Measure.pi (fun _ : Fin 39 => ν))) := by
  classical
  intro ν hFc ρ W R B q T X y
  have hρ : 0 < ρ := by norm_num [ρ]
  have hbSquare : Bornology.IsBounded (Set.range (fun X => F X ^ 2)) := by
    simpa only [← Set.range_comp'] using isBounded_pow hbF 2
  have hcSquare : ∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => ν),
      ContinuousAt (fun X => F X ^ 2) X := hFc.mono fun _ h => h.pow 2
  have hraw := tendsto_restricted_harmonic_pi_sum
    𝓗 ρ κ a hρ hκ ha ha0 haLast
    (fun r : Fin 39 → ℕ => Squarefree (∏ j, r j))
    (fun S hS r hr h => exists_shared_prime_of_not_squarefree_prod S hS r hr h)
    (fun X => F X ^ 2) (hF.pow_const 2) hbSquare hcSquare
  apply hraw.congr'
  filter_upwards [(tendsto_rpow_atTop hρ).eventually_gt_atTop 1] with x hx
  have hWpos : 0 < W x := presieving_pos 𝓗 x
  have hBpos : 0 < B x := by
    change 0 < ((W x).totient : ℝ) / (W x : ℝ) * Real.log (R x)
    exact mul_pos
      (div_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr hWpos)) (Nat.cast_pos.mpr hWpos))
      (Real.log_pos hx)
  have hBpow : B x ^ 39 ≠ 0 := pow_ne_zero _ hBpos.ne'
  have hy : y x = Finsupp.indicator (T x)
      (fun r _ => F (fun j => X x (r j)) / B x ^ 39) :=
    (Finsupp.indicator_eq_sum_single (T x)
      (fun r => F (fun j => X x (r j)) / B x ^ 39)).symm
  have hysupport : (y x).support ⊆ T x := by
    rw [hy]
    exact Finsupp.support_indicator_subset _ _
  have hyvalue (r : Fin 39 → ℕ) (hr : r ∈ T x) :
      y x r = F (fun j => X x (r j)) / B x ^ 39 := by
    rw [hy, Finsupp.indicator_of_mem hr]
  have hscalar (b v w : ℝ) (hb : b ≠ 0) :
      b * ((v / b) ^ 2 * w) = b⁻¹ * (w * v ^ 2) := by
    field_simp [hb]
  symm
  calc
    B x ^ 39 * (y x).sum (fun r yr => yr ^ 2 / (∏ j, ((r j).totient : ℝ))) =
        B x ^ 39 * ∑ r ∈ T x,
          (F (fun j => X x (r j)) / B x ^ 39) ^ 2 /
            (∏ j, ((r j).totient : ℝ)) := by
      apply congrArg (fun z : ℝ => B x ^ 39 * z)
      rw [Finsupp.sum_of_support_subset _ hysupport _ (by simp)]
      apply Finset.sum_congr rfl
      intro r hr
      rw [hyvalue r hr]
    _ = (B x ^ 39)⁻¹ * ∑ r ∈ T x,
        (∏ j, ((r j).totient : ℝ)⁻¹) * F (fun j => X x (r j)) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      simpa only [div_eq_mul_inv, Finset.prod_inv_distrib] using
        hscalar (B x ^ 39) (F (fun j => X x (r j)))
          ((∏ j, ((r j).totient : ℝ))⁻¹) hBpow
    _ = (B x ^ 39)⁻¹ *
        ∑ r ∈ Fintype.piFinset (fun _ : Fin 39 => (q x).divisors),
          (∏ j, ((r j).totient : ℝ)⁻¹) *
            (if Squarefree (∏ j, r j) then F (fun j => X x (r j)) ^ 2 else 0) := by
      simp only [T, Finset.sum_filter, mul_ite, mul_zero]

theorem canonical39_fixed_band_ordinary_square_radius
    {𝓗 : Finset ℕ}
    {h𝓗_card : 𝓗.card = 39}
    {m : ℕ} (κ : ℝ) (hκ : 0 < κ)
    (Srad : ℝ) (hS : 0 < Srad)
    (hsmall : (2624989 / 10000000 : ℝ) * Srad < 1 / 2)
    (a : Fin (m + 2) → ℝ) (ha : StrictMono a)
    (ha0 : a 0 = 0) (haLast : a (Fin.last (m + 1)) = κ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hF : Measurable F) (hbF : Bornology.IsBounded (Set.range F))
    (hRadius : ∀ (W : ℕ) (R : ℝ), 1 < R → ∀ r : Fin 39 → ℕ,
      Squarefree (∏ j, r j) →
      (∀ j, r j ∈ (∏ p ∈ fragmentPrimes W R κ, p).divisors) →
      F (fun j => fragmentBandMasses a
        (primeLogConfiguration R (r j))) ≠ 0 →
      ((∏ j, r j : ℕ) : ℝ) ≤ R ^ Srad) :
    let ν : Measure (Fin (m + 1) → ℝ) :=
      ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * κ) •
        Measure.map (fragmentBandMasses a) (fragmentLaw κ)
    (∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => ν), ContinuousAt F X) →
    let ρ : ℝ := 2624989 / 10000000
    let h : Fin 39 → ℕ :=
      𝓗.orderEmbOfFin h𝓗_card
    let W : ℝ → ℕ := presievingModulus 𝓗
    let R : ℝ → ℝ := fun x => x ^ ρ
    let B : ℝ → ℝ := fun x => fragmentNormalization (W x) (R x)
    let q : ℝ → ℕ := fun x =>
      ∏ p ∈ fragmentPrimes (W x) (R x) κ, p
    let T : ℝ → Finset (Fin 39 → ℕ) := fun x =>
      (Fintype.piFinset (fun _ : Fin 39 => (q x).divisors)).filter
        (fun r => Squarefree (∏ j, r j))
    let X : ℝ → ℕ → Fin (m + 1) → ℝ := fun x s =>
      fragmentBandMasses a (primeLogConfiguration (R x) s)
    let y : ℝ → ((Fin 39 → ℕ) →₀ ℝ) := fun x =>
      ∑ r ∈ T x, Finsupp.single r (F (fun j => X x (r j)) / B x ^ 39)
    let D : ℝ → Finset (Fin 39 → ℕ) := fun x =>
      (y x).support.biUnion
        (fun r => Fintype.piFinset (fun j : Fin 39 => (r j).divisors))
    let A : ℝ → ℕ → ℝ := fun x n =>
      ∑ d ∈ D x, if ∀ j : Fin 39, d j ∣ n + h j then selbergCoefficient (y x) d else 0
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.atTop, ∀ v : ℕ,
      |(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
          if Nat.ModEq (W x) n v then A x n ^ 2 else 0) -
        (∫ X : Fin 39 → Fin (m + 1) → ℝ, F X ^ 2
          ∂Measure.pi (fun _ : Fin 39 => ν)) *
          (x / (W x : ℝ) / B x ^ 39)| ≤
        ε * (x / (W x : ℝ) / B x ^ 39) := by
  classical
  intro ν hFc ρ h W R B q T X y D A
  obtain ⟨M, hM, hFM⟩ := hbF.exists_pos_norm_le
  have hFabs (Z : Fin 39 → Fin (m + 1) → ℝ) : |F Z| ≤ M := by
    simpa only [Real.norm_eq_abs] using hFM _ ⟨Z, rfl⟩
  have hρ : 0 < ρ := by norm_num [ρ]
  have hbase : ∀ᶠ x : ℝ in Filter.atTop, 1 < x ∧ 1 < R x ∧ 0 < B x := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hR : 1 < R x := Real.one_lt_rpow hx hρ
    have hW : 0 < W x := presieving_pos 𝓗 x
    refine ⟨hx, hR, ?_⟩
    change 0 < ((W x).totient : ℝ) / (W x : ℝ) * Real.log (R x)
    exact mul_pos
      (div_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr hW)) (Nat.cast_pos.mpr hW))
      (Real.log_pos hR)
  have hyvalue (x : ℝ) (r : Fin 39 → ℕ) :
      y x r = if r ∈ T x then F (fun j => X x (r j)) / B x ^ 39 else 0 := by
    dsimp only [y]
    simp only [← Finsupp.indicator_eq_sum_single, Finsupp.indicator_apply, dite_eq_ite]
  have hyroots (x : ℝ) (hR : 1 < R x) (r : Fin 39 → ℕ)
      (hr : r ∈ (y x).support) :
      Squarefree (∏ j, r j) ∧ Nat.Coprime (∏ j, r j) (W x) ∧
        ((∏ j, r j : ℕ) : ℝ) ≤ (R x) ^ Srad := by
    have hyr : y x r ≠ 0 := Finsupp.mem_support_iff.mp hr
    have hmem : r ∈ T x := by
      by_contra hout
      exact hyr (by rw [hyvalue, ite_eq_right hout])
    obtain ⟨hpi, hsq⟩ := Finset.mem_filter.mp hmem
    have hdiv (j : Fin 39) : r j ∈ (q x).divisors := Fintype.mem_piFinset.mp hpi j
    have hFne : F (fun j => X x (r j)) ≠ 0 := by
      intro hz
      exact hyr (by rw [hyvalue, ite_eq_left hmem, hz, zero_div])
    refine ⟨hsq, ?_, hRadius (W x) (R x) hR r hsq hdiv hFne⟩
    exact Nat.Coprime.prod_left fun j _ =>
      ((mem_fragment_divisors_iff (W x) (R x) κ
        (Real.one_le_rpow hR.le hκ.le) (r j)).mp (hdiv j)).2.1
  have hybound (x : ℝ) (hB : 0 < B x) (r : Fin 39 → ℕ) :
      |y x r| ≤ M / B x ^ 39 := by
    rw [hyvalue]
    split_ifs with hr
    · rw [abs_div, abs_of_pos (pow_pos hB 39)]
      exact div_le_div_of_nonneg_right (hFabs _) (pow_nonneg hB.le _)
    · rw [abs_zero]
      exact div_nonneg hM.le (pow_nonneg hB.le _)
  let S : ℝ → ℕ → ℝ := fun x v =>
    ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
      if Nat.ModEq (W x) n v then A x n ^ 2 else 0
  let e : ℝ → ℝ := fun x =>
    (y x).sum (fun r yr => yr ^ 2 / (∏ j, ((r j).totient : ℝ)))
  let I : ℝ := ∫ X : Fin 39 → Fin (m + 1) → ℝ, F X ^ 2
    ∂Measure.pi (fun _ : Fin 39 => ν)
  have hlim : Filter.Tendsto (fun x => B x ^ 39 * e x) Filter.atTop (nhds I) :=
    canonical39_fixed_band_harmonic_tendsto (𝓗 := 𝓗) κ hκ a ha ha0 haLast F hF hbF hFc
  have hpos : ∀ᶠ x : ℝ in Filter.atTop,
      0 ≤ x / (W x : ℝ) ∧ 0 < B x ^ 39 := by
    filter_upwards [hbase] with x hx
    exact ⟨div_nonneg (zero_lt_one.trans hx.1).le (Nat.cast_nonneg _),
      pow_pos hx.2.2 39⟩
  have herr (ε : ℝ) (hε : 0 < ε) : ∀ᶠ x : ℝ in Filter.atTop, ∀ v : ℕ,
      |S x v - (x / (W x : ℝ)) * e x| ≤ ε * (x / (W x : ℝ) / B x ^ 39) := by
    filter_upwards [hbase, selberg39_uniform_real_diagonal_radius Srad hS hsmall
      (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) M hM.le ε hε] with x hx hdiag
    intro v
    exact hdiag (y x) v (hyroots x hx.2.1) (hybound x hx.2.2)
  have hcombined := uniform_scaled_error_of_normalized_tendsto S
    (fun x => x / (W x : ℝ)) (fun x => B x ^ 39) e I hpos hlim herr
  intro ε hε
  filter_upwards [hcombined ε hε] with x hx
  intro v
  simpa only [S, I, mul_comm (x / (W x : ℝ) / B x ^ 39)] using hx v


#print axioms selberg39_uniform_real_diagonal_radius
#print axioms canonical39_fixed_band_harmonic_tendsto
#print axioms canonical39_fixed_band_ordinary_square_radius

end PrimeGap182.Selberg
