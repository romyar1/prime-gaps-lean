import AuxiliaryProduct182

/-!
Mixed arithmetic CRT for the actual auxiliary and erased Selberg roots.
Each product retains its own divisor coefficient and therefore its own
total radius. The finite error is bounded by the sum of the two diagonal
L1 errors; no mixed-radius support assumption is needed.
-/

noncomputable section
open scoped BigOperators
open PrimeGap186 PrimeGap182.Selberg

namespace PrimeGap182Analytic

open Classical in
theorem mixed_auxiliary_marked_interval_period_crt
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (i : Fin 39) (x κ : ℝ) (hx : 1 < x) (hκ : 0 < κ) :
    let ρ : ℝ := 2624989 / 10000000
    let h : Fin 39 → ℕ := 𝓗.orderEmbOfFin h𝓗_card
    let W := presievingModulus 𝓗 x
    let q : ℕ := ∏ p ∈ fragmentPrimes W (x ^ ρ) κ, p
    ∀ (u₁ u₂ : (Fin 1 → ℕ) →₀ ℝ) (z₁ z₂ : (Fin 38 → ℕ) →₀ ℝ),
      (∀ s ∈ u₁.support, s 0 ∈ q.divisors) →
      (∀ s ∈ u₂.support, s 0 ∈ q.divisors) →
      (∀ r ∈ z₁.support, Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors) →
      (∀ r ∈ z₂.support, Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors) →
      let Du₁ := u₁.support.biUnion
        (fun r => Fintype.piFinset (fun j => (r j).divisors))
      let Du₂ := u₂.support.biUnion
        (fun r => Fintype.piFinset (fun j => (r j).divisors))
      let Dz₁ := z₁.support.biUnion
        (fun r => Fintype.piFinset (fun j => (r j).divisors))
      let Dz₂ := z₂.support.biUnion
        (fun r => Fintype.piFinset (fun j => (r j).divisors))
      let L₁ : ℕ → ℝ := fun t =>
        ∑ e ∈ Du₁, if e 0 ∣ t then PrimeGap182.Selberg.selbergCoefficient u₁ e else 0
      let L₂ : ℕ → ℝ := fun t =>
        ∑ e ∈ Du₂, if e 0 ∣ t then PrimeGap182.Selberg.selbergCoefficient u₂ e else 0
      let C₁ : ℕ → ℝ := fun n =>
        ∑ d ∈ Dz₁, if ∀ j, d j ∣ n + h (i.succAbove j) then
          PrimeGap182.Selberg.selbergCoefficient z₁ d else 0
      let C₂ : ℕ → ℝ := fun n =>
        ∑ d ∈ Dz₂, if ∀ j, d j ∣ n + h (i.succAbove j) then
          PrimeGap182.Selberg.selbergCoefficient z₂ d else 0
      let A₁ : ℝ := (∑ e ∈ Du₁, |PrimeGap182.Selberg.selbergCoefficient u₁ e|) *
        (∑ d ∈ Dz₁, |PrimeGap182.Selberg.selbergCoefficient z₁ d|)
      let A₂ : ℝ := (∑ e ∈ Du₂, |PrimeGap182.Selberg.selbergCoefficient u₂ e|) *
        (∑ d ∈ Dz₂, |PrimeGap182.Selberg.selbergCoefficient z₂ d|)
      ∀ M : ℕ, 0 < M → Nat.Coprime W M →
        (∀ s ∈ u₁.support, Nat.Coprime (s 0) M) →
        (∀ s ∈ u₂.support, Nat.Coprime (s 0) M) →
        (∀ r ∈ z₁.support, Nat.Coprime (∏ j, r j) M) →
        (∀ r ∈ z₂.support, Nat.Coprime (∏ j, r j) M) →
        ∀ b : ℕ,
          |(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
              if Nat.ModEq W n b ∧ M ∣ n + h i then
                (L₁ (n + h i) * C₁ n) * (L₂ (n + h i) * C₂ n) else 0) -
            x / ((W : ℝ) * (M : ℝ)) * ((1 / (q : ℝ)) *
              ∑ n ∈ Finset.range q,
                (L₁ (n + h i) * C₁ n) * (L₂ (n + h i) * C₂ n))| ≤
            2 * A₁ ^ 2 + 2 * A₂ ^ 2 := by
  intro ρ h W q u₁ u₂ z₁ z₂ hu₁ hu₂ hz₁ hz₂
    Du₁ Du₂ Dz₁ Dz₂ L₁ L₂ C₁ C₂ A₁ A₂ M hM hWM hu₁M hu₂M hz₁M hz₂M b
  obtain ⟨D₁, lam₁, hD₁, hV₁, hA₁⟩ :=
    auxiliary_product_divisor_representation (𝓗 := 𝓗) (h𝓗_card := h𝓗_card)
      i x κ hx hκ u₁ z₁ hu₁ hz₁ M hM hWM hu₁M hz₁M
  obtain ⟨D₂, lam₂, hD₂, hV₂, hA₂⟩ :=
    auxiliary_product_divisor_representation (𝓗 := 𝓗) (h𝓗_card := h𝓗_card)
      i x κ hx hκ u₂ z₂ hu₂ hz₂ M hM hWM hu₂M hz₂M
  have hinj : Function.Injective h := (𝓗.orderEmbOfFin h𝓗_card).injective
  have hW : 0 < W := presieving_pos 𝓗 x
  have hq : 0 < q := Finset.prod_pos fun p hp =>
    (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1).pos
  have hcover : ∀ a c : Fin 39, h a ≠ h c → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h a) (h c) → p ∣ W := by
    intro a c hac p hp hpd
    exact PrimeGap182.Selberg.difference_prime_dvd_presieving 𝓗 x
      (𝓗.orderEmbOfFin_mem h𝓗_card a) (𝓗.orderEmbOfFin_mem h𝓗_card c) hac hp hpd
  have hc := selberg_mixed_two_supports_interval_period_crt_marked h hinj i
    D₁ D₂ lam₁ lam₂ W b M q hW hM hq hWM hD₁ hD₂ hcover x (by linarith)
  have hL1 : (∑ d ∈ D₁, |lam₁ d|) ≤ A₁ := hA₁
  have hL2 : (∑ d ∈ D₂, |lam₂ d|) ≤ A₂ := hA₂
  have hsum0 : 0 ≤ (∑ d ∈ D₁, |lam₁ d|) + ∑ d ∈ D₂, |lam₂ d| :=
    add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have he : ((∑ d ∈ D₁, |lam₁ d|) + ∑ d ∈ D₂, |lam₂ d|) ^ 2 ≤
      2 * A₁ ^ 2 + 2 * A₂ ^ 2 := by
    calc
      _ ≤ (A₁ + A₂) ^ 2 := pow_le_pow_left₀ hsum0 (add_le_add hL1 hL2) 2
      _ ≤ _ := by nlinarith only [sq_nonneg (A₁ - A₂)]
  change (∀ n, L₁ (n + h i) * C₁ n = divisorRootOn D₁ lam₁ h n) at hV₁
  change (∀ n, L₂ (n + h i) * C₂ n = divisorRootOn D₂ lam₂ h n) at hV₂
  simp_rw [← hV₁, ← hV₂] at hc
  exact hc.trans he

/-- The mixed support margin is automatic from the two diagonal margins. -/
theorem mixed_radial_support_margin (s r₁ z₁ r₂ z₂ : ℝ)
    (h₁ : s + 2 * (r₁ + z₁) < 1) (h₂ : s + 2 * (r₂ + z₂) < 1) :
    s + (r₁ + z₁) + (r₂ + z₂) < 1 := by linarith

#print axioms mixed_auxiliary_marked_interval_period_crt
#print axioms mixed_radial_support_margin

end PrimeGap182Analytic
