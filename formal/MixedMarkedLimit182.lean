import MixedMarkedBin182
import MixedHarmonicLimit182

/-!
Arithmetic orthogonality for radial blocks with different auxiliary arrays.
The mixed marked-bin sum is o(x/(W Bx B^38)) whenever the corresponding
normalized erased harmonic cross term tends to zero. The individual sharp
auxiliary diagonal limits suffice; no mixed auxiliary limit is assumed.
-/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186 PrimeGap182.Selberg

namespace PrimeGap182Analytic

open Classical in
theorem mixed_marked_bin_vanishes_of_harmonic_orthogonality
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (i : Fin 39) (κ r₁ ζ₁ r₂ ζ₂ M₁ N₁ M₂ N₂ ξ a l s : ℝ)
    (hκ : 0 < κ) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hζ₁ : 0 < ζ₁) (hζ₂ : 0 < ζ₂)
    (hM₁ : 0 ≤ M₁) (hN₁ : 0 ≤ N₁) (hM₂ : 0 ≤ M₂) (hN₂ : 0 ≤ N₂)
    (hξ : 0 < ξ) (hξa : ξ ≤ a) (hs : 0 ≤ s)
    (hcap : ((2624989 : ℝ) / 10000000) * κ < ξ)
    (hmargin₁ : s + 2 * (r₁ + ζ₁) < 1) (hmargin₂ : s + 2 * (r₂ + ζ₂) < 1)
    (u₁ u₂ : ℝ → ((Fin 1 → ℕ) →₀ ℝ))
    (z₁ z₂ : ℝ → ((Fin 38 → ℕ) →₀ ℝ)) (E₁ E₂ : ℝ) :
    let ρ : ℝ := 2624989 / 10000000
    let h : Fin 39 → ℕ := 𝓗.orderEmbOfFin h𝓗_card
    let W : ℝ → ℕ := presievingModulus 𝓗
    let Bx : ℝ → ℝ := fun x => fragmentNormalization (W x) x
    let B : ℝ → ℝ := fun x => fragmentNormalization (W x) (x ^ ρ)
    let q : ℝ → ℕ := fun x => ∏ p ∈ fragmentPrimes (W x) (x ^ ρ) κ, p
    (∀ᶠ x : ℝ in atTop,
      (∀ t ∈ (u₁ x).support, t 0 ∈ (q x).divisors ∧ (t 0 : ℝ) ≤ x ^ ζ₁) ∧
      (∀ t ∈ (u₂ x).support, t 0 ∈ (q x).divisors ∧ (t 0 : ℝ) ≤ x ^ ζ₂) ∧
      (∀ r ∈ (z₁ x).support, Squarefree (∏ j, r j) ∧
        (∀ j, r j ∈ (q x).divisors) ∧ ((∏ j, r j : ℕ) : ℝ) ≤ x ^ r₁) ∧
      (∀ r ∈ (z₂ x).support, Squarefree (∏ j, r j) ∧
        (∀ j, r j ∈ (q x).divisors) ∧ ((∏ j, r j : ℕ) : ℝ) ≤ x ^ r₂) ∧
      (∀ t, |u₁ x t| ≤ N₁ / Bx x) ∧ (∀ t, |u₂ x t| ≤ N₂ / Bx x) ∧
      (∀ r, |z₁ x r| ≤ M₁ / B x ^ 38) ∧ (∀ r, |z₂ x r| ≤ M₂ / B x ^ 38)) →
    Tendsto (fun x => Bx x * diagonalHarmonic
      (fun t : Fin 1 → ℕ => ((t 0).totient : ℝ)) (u₁ x)) atTop (nhds E₁) →
    Tendsto (fun x => Bx x * diagonalHarmonic
      (fun t : Fin 1 → ℕ => ((t 0).totient : ℝ)) (u₂ x)) atTop (nhds E₂) →
    Tendsto (fun x => B x ^ 38 * mixedHarmonic
      (fun r : Fin 38 → ℕ => ∏ j, ((r j).totient : ℝ)) (z₁ x) (z₂ x)) atTop (nhds 0) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, ∀ b : ℕ,
      |∑ v ∈ markedPrimePairBin x ξ a l s, ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
        if Nat.ModEq (W x) n b ∧ v.1 * v.2 ∣ n + h i then
          auxiliaryProductValue h i (u₁ x) (z₁ x) n *
            auxiliaryProductValue h i (u₂ x) (z₂ x) n else 0| ≤
        ε * (x / (W x : ℝ) / Bx x / B x ^ 38) := by
  intro ρ h W Bx B q hdata hU₁ hU₂ hZ
  let denU : (Fin 1 → ℕ) → ℝ := fun t => ((t 0).totient : ℝ)
  let denZ : (Fin 38 → ℕ) → ℝ := fun r => ∏ j, ((r j).totient : ℝ)
  let harmonic : ℝ → ℝ := fun x =>
    mixedHarmonic denU (u₁ x) (u₂ x) * mixedHarmonic denZ (z₁ x) (z₂ x)
  let pairMass : ℝ → ℝ := fun x =>
    ∑ v ∈ markedPrimePairBin x ξ a l s, 1 / ((v.1 * v.2 : ℕ) : ℝ)
  have hBx : ∀ᶠ x : ℝ in atTop, 0 ≤ Bx x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Real.log_nonneg hx.le)
  have hH : Tendsto (fun x => (Bx x * B x ^ 38) * harmonic x) atTop (nhds 0) :=
    mixed_harmonic_scaled_tendsto_zero atTop denU denZ (fun _ => Nat.cast_nonneg _)
      u₁ u₂ z₁ z₂ Bx (fun x => B x ^ 38) hBx E₁ E₂ hU₁ hU₂ hZ
  obtain ⟨K, hK, hmass⟩ := markedPrimePairBin_reciprocal_eventually_bounded ξ a hξ hξa
  have hbound : ∀ᶠ x : ℝ in atTop, |pairMass x| ≤ K := by
    filter_upwards [hmass] with x hx
    rw [abs_of_nonneg (hx l s).1]
    exact (hx l s).2
  have hscalar := bounded_mul_tendsto_zero atTop pairMass
    (fun x => (Bx x * B x ^ 38) * harmonic x) K hK.le hbound hH
  intro ε hε
  have hsmall := (hscalar.abs).eventually_le_const
    (show |(0 : ℝ)| < ε / 2 by simpa only [abs_zero] using half_pos hε)
  filter_upwards [hdata, hsmall,
    mixed_auxiliary_marked_bin_uniform (𝓗 := 𝓗) (h𝓗_card := h𝓗_card)
      i κ r₁ ζ₁ r₂ ζ₂ M₁ N₁ M₂ N₂ ξ a l s hκ hr₁ hr₂ hζ₁ hζ₂ hM₁ hN₁ hM₂ hN₂
      hξ hξa hs hcap hmargin₁ hmargin₂ (ε / 2) (half_pos hε)]
    with x hd hxsmall hc
  obtain ⟨hu₁, hu₂, hz₁, hz₂, hu₁Bound, hu₂Bound, hz₁Bound, hz₂Bound⟩ := hd
  have hx0 : 0 < x := zero_lt_one.trans hc.1
  have hBx0 : 0 < Bx x := hc.2.1
  have hB0 : 0 < B x := hc.2.2.1
  have hW0 : (0 : ℝ) < W x := Nat.cast_pos.mpr (presieving_pos 𝓗 x)
  let A : ℝ := x / (W x : ℝ) / Bx x / B x ^ 38
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  intro b
  let S : ℝ := ∑ v ∈ markedPrimePairBin x ξ a l s,
    ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
      if Nat.ModEq (W x) n b ∧ v.1 * v.2 ∣ n + h i then
        auxiliaryProductValue h i (u₁ x) (z₁ x) n *
          auxiliaryProductValue h i (u₂ x) (z₂ x) n else 0
  have harr : |S - pairMass x * (x / (W x : ℝ) * harmonic x)| ≤ (ε / 2) * A :=
    hc.2.2.2 (u₁ x) (u₂ x) (z₁ x) (z₂ x) hu₁ hu₂ hz₁ hz₂
      hu₁Bound hu₂Bound hz₁Bound hz₂Bound b
  have heq : pairMass x * (x / (W x : ℝ) * harmonic x) =
      A * (pairMass x * ((Bx x * B x ^ 38) * harmonic x)) := by
    dsimp only [A]
    field_simp [hW0.ne', hBx0.ne', hB0.ne']
  have hmain : |pairMass x * (x / (W x : ℝ) * harmonic x)| ≤ (ε / 2) * A := by
    rw [heq, abs_mul, abs_of_nonneg hA]
    exact (mul_le_mul_of_nonneg_left hxsmall hA).trans_eq (mul_comm _ _)
  change |S| ≤ ε * A
  calc
    _ = |(S - pairMass x * (x / (W x : ℝ) * harmonic x)) +
        pairMass x * (x / (W x : ℝ) * harmonic x)| := by rw [sub_add_cancel]
    _ ≤ |S - pairMass x * (x / (W x : ℝ) * harmonic x)| +
        |pairMass x * (x / (W x : ℝ) * harmonic x)| := abs_add_le _ _
    _ ≤ (ε / 2) * A + (ε / 2) * A := add_le_add harr hmain
    _ = _ := by ring

#print axioms mixed_marked_bin_vanishes_of_harmonic_orthogonality

end PrimeGap182Analytic
