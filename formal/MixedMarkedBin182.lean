import MixedAuxiliaryArithmetic182

/-!
The mixed marked-bin estimate with separately paired radial and auxiliary
radii. All arithmetic, period comparison, and prime-pair counting errors
are proved, uniformly in the actual finite diagonal arrays.
-/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186 PrimeGap182.Selberg

namespace PrimeGap182Analytic

open Classical in
theorem mixed_auxiliary_marked_bin_uniform
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (i : Fin 39) (κ r₁ ζ₁ r₂ ζ₂ M₁ N₁ M₂ N₂ ξ a l s : ℝ)
    (hκ : 0 < κ) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hζ₁ : 0 < ζ₁) (hζ₂ : 0 < ζ₂)
    (hM₁ : 0 ≤ M₁) (hN₁ : 0 ≤ N₁) (hM₂ : 0 ≤ M₂) (hN₂ : 0 ≤ N₂)
    (hξ : 0 < ξ) (hξa : ξ ≤ a) (hs : 0 ≤ s)
    (hcap : ((2624989 : ℝ) / 10000000) * κ < ξ)
    (hmargin₁ : s + 2 * (r₁ + ζ₁) < 1) (hmargin₂ : s + 2 * (r₂ + ζ₂) < 1) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
      let ρ : ℝ := 2624989 / 10000000
      let h : Fin 39 → ℕ := 𝓗.orderEmbOfFin h𝓗_card
      let W := presievingModulus 𝓗 x
      let Bx := fragmentNormalization W x
      let B := fragmentNormalization W (x ^ ρ)
      let q : ℕ := ∏ p ∈ fragmentPrimes W (x ^ ρ) κ, p
      let T := markedPrimePairBin x ξ a l s
      let pairMass : ℝ := ∑ v ∈ T, 1 / ((v.1 * v.2 : ℕ) : ℝ)
      1 < x ∧ 0 < Bx ∧ 0 < B ∧
        ∀ (u₁ u₂ : (Fin 1 → ℕ) →₀ ℝ) (z₁ z₂ : (Fin 38 → ℕ) →₀ ℝ),
          (∀ t ∈ u₁.support, t 0 ∈ q.divisors ∧ (t 0 : ℝ) ≤ x ^ ζ₁) →
          (∀ t ∈ u₂.support, t 0 ∈ q.divisors ∧ (t 0 : ℝ) ≤ x ^ ζ₂) →
          (∀ r ∈ z₁.support, Squarefree (∏ j, r j) ∧
            (∀ j, r j ∈ q.divisors) ∧ ((∏ j, r j : ℕ) : ℝ) ≤ x ^ r₁) →
          (∀ r ∈ z₂.support, Squarefree (∏ j, r j) ∧
            (∀ j, r j ∈ q.divisors) ∧ ((∏ j, r j : ℕ) : ℝ) ≤ x ^ r₂) →
          (∀ t, |u₁ t| ≤ N₁ / Bx) → (∀ t, |u₂ t| ≤ N₂ / Bx) →
          (∀ r, |z₁ r| ≤ M₁ / B ^ 38) → (∀ r, |z₂ r| ≤ M₂ / B ^ 38) →
          ∀ b : ℕ,
            |(∑ v ∈ T, ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
                if Nat.ModEq W n b ∧ v.1 * v.2 ∣ n + h i then
                  auxiliaryProductValue h i u₁ z₁ n * auxiliaryProductValue h i u₂ z₂ n else 0) -
              pairMass * (x / (W : ℝ) *
                (mixedHarmonic (fun t : Fin 1 → ℕ => ((t 0).totient : ℝ)) u₁ u₂ *
                  mixedHarmonic (fun r : Fin 38 → ℕ => ∏ j, ((r j).totient : ℝ)) z₁ z₂))| ≤
              ε * (x / (W : ℝ) / Bx / B ^ 38) := by
  intro ε hε
  obtain ⟨K, hK, hmass⟩ := markedPrimePairBin_reciprocal_eventually_bounded ξ a hξ hξa
  let ρ₀ : ℝ := 2624989 / 10000000
  let η : ℝ := ε / 4
  let δ : ℝ := ε * ρ₀ / (2 * (K + 1))
  have hρ : 0 < ρ₀ := by norm_num [ρ₀]
  have hρ1 : ρ₀ ≤ 1 := by norm_num [ρ₀]
  have hK1 : 0 < K + 1 := by linarith
  have hη : 0 < η := by dsimp only [η]; positivity
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  let J : ℕ := 7 + (2 ^ (38 + 2) - 1)
  have hlog₁ := PrimeGap182.Selberg.floor_rpow_log_envelope (r₁ + ζ₁)
    (add_pos_of_nonneg_of_pos hr₁ hζ₁) (by linarith : r₁ + ζ₁ < 1)
  have hlog₂ := PrimeGap182.Selberg.floor_rpow_log_envelope (r₂ + ζ₂)
    (add_pos_of_nonneg_of_pos hr₂ hζ₂) (by linarith : r₂ + ζ₂ < 1)
  filter_upwards [hmass, hlog₁, hlog₂,
    markedPrimePairBin_coprime_eventually 𝓗 ρ₀ κ ξ a l s hξ hcap,
    selberg39_marked_count_error_small (𝓗 := 𝓗) (r₁ + ζ₁) s M₁ N₁ J hmargin₁ η hη,
    selberg39_marked_count_error_small (𝓗 := 𝓗) (r₂ + ζ₂) s M₂ N₂ J hmargin₂ η hη,
    mixed_auxiliary_period_comparison (𝓗 := 𝓗) (h𝓗_card := h𝓗_card)
      i κ M₁ M₂ N₁ N₂ hκ hM₁ hM₂ hN₁ hN₂ δ hδ]
    with x hmassx hlogx₁ hlogx₂ hcop hsmall₁ hsmall₂ hperiod
  intro ρ h W Bx B q T pairMass
  obtain ⟨hx, hBx, hB, hsmall₁⟩ := hsmall₁
  have hsmall₂ := hsmall₂.2.2.2
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hW : (0 : ℝ) < W := Nat.cast_pos.mpr (presieving_pos 𝓗 x)
  have hB_eq : B = ρ₀ * Bx := by
    dsimp only [B, Bx, fragmentNormalization, ρ]
    rw [Real.log_rpow hx0]
    ring
  have hB_le : B ≤ Bx := by
    rw [hB_eq]
    exact mul_le_of_le_one_left hBx.le hρ1
  refine ⟨hx, hBx, hB, ?_⟩
  intro u₁ u₂ z₁ z₂ hu₁ hu₂ hz₁ hz₂ hu₁Bound hu₂Bound hz₁Bound hz₂Bound b
  let A : ℝ := x / (W : ℝ) / Bx / B ^ 38
  let E₁ : ℝ := (2 * M₁ ^ 2 * N₁ ^ 2 / (Bx ^ 2 * B ^ 76)) *
    x ^ (2 * (r₁ + ζ₁)) * Real.log x ^ (2 * J)
  let E₂ : ℝ := (2 * M₂ ^ 2 * N₂ ^ 2 / (Bx ^ 2 * B ^ 76)) *
    x ^ (2 * (r₂ + ζ₂)) * Real.log x ^ (2 * J)
  let mean := auxiliaryPeriodCross q h i u₁ u₂ z₁ z₂
  let harmonic := mixedHarmonic (fun t : Fin 1 → ℕ => ((t 0).totient : ℝ)) u₁ u₂ *
    mixedHarmonic (fun r : Fin 38 → ℕ => ∏ j, ((r j).totient : ℝ)) z₁ z₂
  let S : (ℕ × ℕ) → ℝ := fun v =>
    ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
      if Nat.ModEq W n b ∧ v.1 * v.2 ∣ n + h i then
        auxiliaryProductValue h i u₁ z₁ n * auxiliaryProductValue h i u₂ z₂ n else 0
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have hE₁ : 0 ≤ E₁ := by dsimp only [E₁]; positivity
  have hE₂ : 0 ≤ E₂ := by dsimp only [E₂]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hu₁Mem : ∀ t ∈ u₁.support, t 0 ∈ q.divisors := fun t ht => (hu₁ t ht).1
  have hu₂Mem : ∀ t ∈ u₂.support, t 0 ∈ q.divisors := fun t ht => (hu₂ t ht).1
  have hz₁Mem : ∀ r ∈ z₁.support, Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors :=
    fun r hr => ⟨(hz₁ r hr).1, (hz₁ r hr).2.1⟩
  have hz₂Mem : ∀ r ∈ z₂.support, Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors :=
    fun r hr => ⟨(hz₂ r hr).1, (hz₂ r hr).2.1⟩
  have hqsf : Squarefree q := squarefree_prime_prod _
    (fun p hp => Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1)
  have hL₁ : 2 * (selbergL1 u₁ * selbergL1 z₁) ^ 2 ≤ E₁ := by
    have hh := auxiliary_two_radius_l1_bound u₁ z₁ q x r₁ ζ₁ M₁ N₁ Bx B
      hx hr₁ hζ₁.le hM₁ hN₁ hBx hB hqsf hu₁
      (fun r hr => ⟨(hz₁ r hr).1, (hz₁ r hr).2.2⟩) hu₁Bound hz₁Bound hlogx₁.2.2
    simpa only [selbergL1, E₁, J, mul_pow, mul_assoc, finPiFinset_eq_classical] using hh
  have hL₂ : 2 * (selbergL1 u₂ * selbergL1 z₂) ^ 2 ≤ E₂ := by
    have hh := auxiliary_two_radius_l1_bound u₂ z₂ q x r₂ ζ₂ M₂ N₂ Bx B
      hx hr₂ hζ₂.le hM₂ hN₂ hBx hB hqsf hu₂
      (fun r hr => ⟨(hz₂ r hr).1, (hz₂ r hr).2.2⟩) hu₂Bound hz₂Bound hlogx₂.2.2
    simpa only [selbergL1, E₂, J, mul_pow, mul_assoc, finPiFinset_eq_classical] using hh
  have hmarked (v : ℕ × ℕ) (hv : v ∈ T) :
      |S v - (1 / ((v.1 * v.2 : ℕ) : ℝ)) * (x / (W : ℝ) * mean)| ≤ E₁ + E₂ := by
    have hbox := (Finset.mem_filter.mp hv).1
    have hp : Nat.Prime v.1 := Nat.prime_of_mem_primesLE (Finset.mem_product.mp hbox).1
    have hp' : Nat.Prime v.2 := Nat.prime_of_mem_primesLE (Finset.mem_product.mp hbox).2
    have hc := hcop.2 v hv
    have hcrt := mixed_auxiliary_crt_root_form (𝓗 := 𝓗) (h𝓗_card := h𝓗_card)
      i x κ hx hκ u₁ u₂ z₁ z₂ hu₁Mem hu₂Mem hz₁Mem hz₂Mem
      (v.1 * v.2) (Nat.mul_pos hp.pos hp'.pos) hc.1.symm
      (fun t ht => hc.2.symm.of_dvd_left (Nat.mem_divisors.mp (hu₁ t ht).1).1)
      (fun t ht => hc.2.symm.of_dvd_left (Nat.mem_divisors.mp (hu₂ t ht).1).1)
      (fun r hr => Nat.Coprime.prod_left fun j _ =>
        hc.2.symm.of_dvd_left (Nat.mem_divisors.mp ((hz₁ r hr).2.1 j)).1)
      (fun r hr => Nat.Coprime.prod_left fun j _ =>
        hc.2.symm.of_dvd_left (Nat.mem_divisors.mp ((hz₂ r hr).2.1 j)).1) b
    have hmain : x / ((W : ℝ) * ((v.1 * v.2 : ℕ) : ℝ)) * mean =
        (1 / ((v.1 * v.2 : ℕ) : ℝ)) * (x / (W : ℝ) * mean) := by
      simp only [div_eq_mul_inv, mul_inv]
      ring
    change |S v - x / ((W : ℝ) * ((v.1 * v.2 : ℕ) : ℝ)) * mean| ≤ _ at hcrt
    rw [hmain] at hcrt
    exact hcrt.trans (add_le_add hL₁ hL₂)
  have hbin : |(∑ v ∈ T, S v) - pairMass * (x / (W : ℝ) * mean)| ≤ (ε / 2) * A := by
    calc
      _ = |(∑ v ∈ T, (S v - (1 / ((v.1 * v.2 : ℕ) : ℝ)) * (x / (W : ℝ) * mean)))| := by
        rw [Finset.sum_sub_distrib, Finset.sum_mul]
      _ ≤ ∑ v ∈ T, |S v - (1 / ((v.1 * v.2 : ℕ) : ℝ)) * (x / (W : ℝ) * mean)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v ∈ T, (E₁ + E₂) := Finset.sum_le_sum hmarked
      _ = (T.card : ℝ) * (E₁ + E₂) := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ x ^ s * (E₁ + E₂) := mul_le_mul_of_nonneg_right
        (markedPrimePairBin_card_le x ξ a l s hx) (add_nonneg hE₁ hE₂)
      _ = x ^ s * E₁ + x ^ s * E₂ := mul_add _ _ _
      _ ≤ η * A + η * A := add_le_add hsmall₁ hsmall₂
      _ = _ := by dsimp only [η]; ring
  have hmean : |mean - harmonic| ≤ δ / B ^ 39 :=
    hperiod.2 u₁ u₂ z₁ z₂ hu₁Mem hu₂Mem hz₁Mem hz₂Mem
      (fun t => (hu₁Bound t).trans (div_le_div_of_nonneg_left hN₁ hB hB_le))
      (fun t => (hu₂Bound t).trans (div_le_div_of_nonneg_left hN₂ hB hB_le))
      hz₁Bound hz₂Bound
  have hmass0 : 0 ≤ pairMass := (hmassx l s).1
  have hmassK : pairMass ≤ K := (hmassx l s).2
  have hweighted : |pairMass * (x / (W : ℝ) * mean) -
      pairMass * (x / (W : ℝ) * harmonic)| ≤ (ε / 2) * A := by
    have heq : pairMass * (x / (W : ℝ) * mean) - pairMass * (x / (W : ℝ) * harmonic) =
        (pairMass * (x / (W : ℝ))) * (mean - harmonic) := by ring
    rw [heq, abs_mul, abs_of_nonneg (mul_nonneg hmass0 (div_nonneg hx0.le hW.le))]
    calc
      _ ≤ (K * (x / (W : ℝ))) * (δ / B ^ 39) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hmassK (div_nonneg hx0.le hW.le)) hmean
          (abs_nonneg _) (mul_nonneg hK.le (div_nonneg hx0.le hW.le))
      _ = (K / (K + 1)) * ((ε / 2) * A) := by
        dsimp only [δ, A]
        rw [hB_eq]
        field_simp [hBx.ne', hW.ne', hK1.ne', hρ.ne']
      _ ≤ 1 * ((ε / 2) * A) := mul_le_mul_of_nonneg_right
        ((div_le_one hK1).mpr (le_add_of_nonneg_right zero_le_one))
          (mul_nonneg (half_pos hε).le hA)
      _ = _ := one_mul _
  change |(∑ v ∈ T, S v) - pairMass * (x / (W : ℝ) * harmonic)| ≤ ε * A
  calc
    _ ≤ |(∑ v ∈ T, S v) - pairMass * (x / (W : ℝ) * mean)| +
        |pairMass * (x / (W : ℝ) * mean) - pairMass * (x / (W : ℝ) * harmonic)| :=
      abs_sub_le _ _ _
    _ ≤ (ε / 2) * A + (ε / 2) * A := add_le_add hbin hweighted
    _ = _ := by ring

#print axioms mixed_auxiliary_marked_bin_uniform

end PrimeGap182Analytic
