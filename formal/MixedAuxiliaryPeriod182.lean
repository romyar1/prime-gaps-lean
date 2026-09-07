import SelbergPolarization182

/-!
The actual mixed period mean approaches the product of the two mixed
harmonic forms. The comparison is uniform in the arrays and uses amplitude
and prime support bounds only, without any radial support hypothesis.
-/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186 PrimeGap182.Selberg

namespace PrimeGap182Analytic

open Classical in
theorem auxiliary_period_comparison_plain
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (i : Fin 39) (κ M N : ℝ) (hκ : 0 < κ) (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
      let ρ : ℝ := 2624989 / 10000000
      let h : Fin 39 → ℕ := 𝓗.orderEmbOfFin h𝓗_card
      let W := presievingModulus 𝓗 x
      let B := fragmentNormalization W (x ^ ρ)
      let q : ℕ := ∏ p ∈ fragmentPrimes W (x ^ ρ) κ, p
      0 < B ∧ ∀ (u : (Fin 1 → ℕ) →₀ ℝ) (z : (Fin 38 → ℕ) →₀ ℝ),
        (∀ s ∈ u.support, s 0 ∈ q.divisors) →
        (∀ r ∈ z.support, Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors) →
        (∀ s, |u s| ≤ N / B) → (∀ r, |z r| ≤ M / B ^ 38) →
        |auxiliaryPeriodSquare q h i u z -
          diagonalHarmonic (fun t : Fin 1 → ℕ => ((t 0).totient : ℝ)) u *
            diagonalHarmonic (fun r : Fin 38 → ℕ => ∏ j, ((r j).totient : ℝ)) z| ≤
          ε / B ^ 39 := by
  intro ε hε
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    PrimeGap182.Selberg.selberg39_auxiliary_period_comparison
      (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i κ M N hκ hM hN ε hε]
    with x hx hc
  intro ρ h W B q
  refine ⟨hc.1, ?_⟩
  intro u z hu hz huBound hzBound
  let Du := u.support.biUnion (fun r => Fintype.piFinset (fun j => (r j).divisors))
  let Dz := z.support.biUnion (fun r => Fintype.piFinset (fun j => (r j).divisors))
  let L : ℕ → ℝ := fun t => ∑ e ∈ Du,
    if e 0 ∣ t then PrimeGap182.Selberg.selbergCoefficient u e else 0
  let C : ℕ → ℝ := fun n => ∑ d ∈ Dz,
    if ∀ j, d j ∣ n + h (i.succAbove j) then
      PrimeGap182.Selberg.selbergCoefficient z d else 0
  have hL (t : ℕ) : sampledSelbergRoot u (fun _ => t) = L t := by
    dsimp only [sampledSelbergRoot, L, Du]
    refine Finset.sum_congr ?_ ?_
    · ext d
      simp only [Finset.mem_biUnion, Fintype.mem_piFinset]
    · intro d _
      simp only [Fin.forall_fin_one]
  have hC (n : ℕ) : sampledSelbergRoot z (fun j => n + h (i.succAbove j)) = C n := by
    dsimp only [sampledSelbergRoot, C, Dz]
    refine Finset.sum_congr ?_ ?_
    · ext d
      simp only [Finset.mem_biUnion, Fintype.mem_piFinset]
    · intro d _
      by_cases hd : ∀ j, d j ∣ n + h (i.succAbove j) <;> simp only [hd, ite_false]
  have hraw := (hc.2 u z hu hz huBound hzBound 0).2.2
  obtain ⟨_, _, _, _, _, _, _, _, _, haffine⟩ :=
    PrimeGap182.Selberg.selberg39_auxiliary_exact_period_bridge
      (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i x κ hx hκ u z hu hz
  have heq : (1 / (q : ℝ)) *
      (∑ n ∈ Finset.range q, (L (W * n + h i) * C (W * n)) ^ 2) =
      (1 / (q : ℝ)) * ∑ n ∈ Finset.range q, (L (n + h i) * C n) ^ 2 := by
    simpa only [Nat.zero_add] using haffine 0
  change |(1 / (q : ℝ)) *
      (∑ n ∈ Finset.range q, (L (0 + W * n + h i) * C (0 + W * n)) ^ 2) -
      diagonalHarmonic (fun t : Fin 1 → ℕ => ((t 0).totient : ℝ)) u *
        diagonalHarmonic (fun r : Fin 38 → ℕ => ∏ j, ((r j).totient : ℝ)) z| ≤
      ε / B ^ 39 at hraw
  simp only [Nat.zero_add, heq] at hraw
  simpa only [auxiliaryPeriodSquare, hL, hC] using hraw

open Classical in
theorem mixed_auxiliary_period_comparison
    {𝓗 : Finset ℕ} {h𝓗_card : 𝓗.card = 39}
    (i : Fin 39) (κ M₁ M₂ N₁ N₂ : ℝ)
    (hκ : 0 < κ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
      let ρ : ℝ := 2624989 / 10000000
      let h : Fin 39 → ℕ := 𝓗.orderEmbOfFin h𝓗_card
      let W := presievingModulus 𝓗 x
      let B := fragmentNormalization W (x ^ ρ)
      let q : ℕ := ∏ p ∈ fragmentPrimes W (x ^ ρ) κ, p
      0 < B ∧ ∀ (u₁ u₂ : (Fin 1 → ℕ) →₀ ℝ) (z₁ z₂ : (Fin 38 → ℕ) →₀ ℝ),
        (∀ s ∈ u₁.support, s 0 ∈ q.divisors) →
        (∀ s ∈ u₂.support, s 0 ∈ q.divisors) →
        (∀ r ∈ z₁.support, Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors) →
        (∀ r ∈ z₂.support, Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors) →
        (∀ s, |u₁ s| ≤ N₁ / B) → (∀ s, |u₂ s| ≤ N₂ / B) →
        (∀ r, |z₁ r| ≤ M₁ / B ^ 38) → (∀ r, |z₂ r| ≤ M₂ / B ^ 38) →
        |auxiliaryPeriodCross q h i u₁ u₂ z₁ z₂ -
          mixedHarmonic (fun t : Fin 1 → ℕ => ((t 0).totient : ℝ)) u₁ u₂ *
            mixedHarmonic (fun r : Fin 38 → ℕ => ∏ j, ((r j).totient : ℝ)) z₁ z₂| ≤
          ε / B ^ 39 := by
  intro ε hε
  filter_upwards [auxiliary_period_comparison_plain (𝓗 := 𝓗) (h𝓗_card := h𝓗_card)
    i κ (M₁ + M₂) (N₁ + N₂) hκ (add_nonneg hM₁ hM₂) (add_nonneg hN₁ hN₂)
    (4 * ε) (by positivity)] with x hc
  intro ρ h W B q
  refine ⟨hc.1, ?_⟩
  intro u₁ u₂ z₁ z₂ hu₁ hu₂ hz₁ hz₂ hu₁Bound hu₂Bound hz₁Bound hz₂Bound
  have hUsupport (u : (Fin 1 → ℕ) →₀ ℝ) (hu : u.support ⊆ u₁.support ∪ u₂.support) :
      ∀ s ∈ u.support, s 0 ∈ q.divisors := by
    intro s hs
    rcases Finset.mem_union.mp (hu hs) with hs | hs
    · exact hu₁ s hs
    · exact hu₂ s hs
  have hZsupport (z : (Fin 38 → ℕ) →₀ ℝ) (hz : z.support ⊆ z₁.support ∪ z₂.support) :
      ∀ r ∈ z.support, Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ q.divisors := by
    intro r hr
    rcases Finset.mem_union.mp (hz hr) with hr | hr
    · exact hz₁ r hr
    · exact hz₂ r hr
  have hUplus (s : Fin 1 → ℕ) : |(u₁ + u₂) s| ≤ (N₁ + N₂) / B := by
    calc
      _ ≤ |u₁ s| + |u₂ s| := abs_add_le _ _
      _ ≤ N₁ / B + N₂ / B := add_le_add (hu₁Bound s) (hu₂Bound s)
      _ = _ := (add_div _ _ _).symm
  have hUminus (s : Fin 1 → ℕ) : |(u₁ - u₂) s| ≤ (N₁ + N₂) / B := by
    calc
      _ ≤ |u₁ s| + |u₂ s| := abs_sub _ _
      _ ≤ N₁ / B + N₂ / B := add_le_add (hu₁Bound s) (hu₂Bound s)
      _ = _ := (add_div _ _ _).symm
  have hZplus (r : Fin 38 → ℕ) : |(z₁ + z₂) r| ≤ (M₁ + M₂) / B ^ 38 := by
    calc
      _ ≤ |z₁ r| + |z₂ r| := abs_add_le _ _
      _ ≤ M₁ / B ^ 38 + M₂ / B ^ 38 := add_le_add (hz₁Bound r) (hz₂Bound r)
      _ = _ := (add_div _ _ _).symm
  have hZminus (r : Fin 38 → ℕ) : |(z₁ - z₂) r| ≤ (M₁ + M₂) / B ^ 38 := by
    calc
      _ ≤ |z₁ r| + |z₂ r| := abs_sub _ _
      _ ≤ M₁ / B ^ 38 + M₂ / B ^ 38 := add_le_add (hz₁Bound r) (hz₂Bound r)
      _ = _ := (add_div _ _ _).symm
  have hpp := abs_le.mp (hc.2 (u₁ + u₂) (z₁ + z₂)
    (hUsupport _ Finsupp.support_add) (hZsupport _ Finsupp.support_add) hUplus hZplus)
  have hmp := abs_le.mp (hc.2 (u₁ - u₂) (z₁ + z₂)
    (hUsupport _ Finsupp.support_sub) (hZsupport _ Finsupp.support_add) hUminus hZplus)
  have hpm := abs_le.mp (hc.2 (u₁ + u₂) (z₁ - z₂)
    (hUsupport _ Finsupp.support_add) (hZsupport _ Finsupp.support_sub) hUplus hZminus)
  have hmm := abs_le.mp (hc.2 (u₁ - u₂) (z₁ - z₂)
    (hUsupport _ Finsupp.support_sub) (hZsupport _ Finsupp.support_sub) hUminus hZminus)
  have hQ := auxiliaryPeriod_polarization q h i u₁ u₂ z₁ z₂
  have hH := mixed_harmonic_product_polarization
    (fun t : Fin 1 → ℕ => ((t 0).totient : ℝ))
    (fun r : Fin 38 → ℕ => ∏ j, ((r j).totient : ℝ)) u₁ u₂ z₁ z₂
  simp only [mul_div_assoc] at hpp hmp hpm hmm
  apply abs_le.mpr
  constructor <;> linarith only [hQ, hH, hpp.1, hpp.2, hmp.1, hmp.2, hpm.1, hpm.2, hmm.1, hmm.2]

#print axioms auxiliary_period_comparison_plain
#print axioms mixed_auxiliary_period_comparison

end PrimeGap182Analytic
