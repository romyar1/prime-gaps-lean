import PrimeGaps186

/-!
# The precise new secondary source estimate to be proved

This proposition records the shared analytic seam. It is not asserted
as an axiom or an available theorem. The incidence development must
prove it from the explicit local rank-four bound. Compared with the
public sourceSigmaOne_uniform_secondary_bound interface, the exponent
band is supplied explicitly and both selected-Δ bounds retain q₀².
-/

noncomputable section
namespace PrimeGap182Audit
open Classical
open scoped BigOperators ContDiff

def IncidenceSecondaryEstimate («ω» δ ε γlo γhi : ℝ) : Prop :=
  ∀ C₁ cM TM cN TN : ℝ,
    1 ≤ C₁ → 0 < cM → cM ≤ TM → 0 < cN → cN ≤ TN →
    ∀ CM EM CN EN CD : ℕ → ℝ,
    (∀ j : ℕ, 0 ≤ CM j ∧ 0 ≤ CN j ∧ 0 ≤ CD j) →
    ∃ K₂ Xtwo : ℝ, 0 < K₂ ∧ Real.exp 1 ≤ Xtwo ∧
      ∀ x : ℝ, Xtwo ≤ x →
      ∀ r₁ q₀ u₁ v₁ v₂ q₂ aN b₁N b₂N : ℕ, ∀ ℓ : ℤ,
      0 < r₁ → 0 < q₀ → 0 < u₁ → 0 < v₁ → 0 < v₂ → 0 < q₂ →
      Squarefree (r₁ * q₀ * u₁ * Nat.lcm v₁ v₂ * q₂) →
      Nat.Coprime (r₁ * q₀ * u₁ * v₁ * v₂ * q₂) (aN * b₁N * b₂N) →
      ∀ M N R₀ Q U V H Hstar Δ d₀ γ : ℝ,
      0 < M → 0 < N → 0 < R₀ → 0 < Q → 0 < U → 0 < V → 1 ≤ Δ →
      x / C₁ ≤ M * N → M * N ≤ C₁ * x → N = x ^ γ →
      γlo ≤ γ → γ ≤ γhi →
      N ≤ C₁ * x ^ (δ + 4 * ε) * R₀ →
      R₀ ≤ C₁ * x ^ (-2 * ε) * N →
      x ^ (1 / 2 - ε) ≤ C₁ * R₀ * Q →
      R₀ * Q ≤ C₁ * x ^ (1 / 2 + 2 * «ω» + ε) →
      H = x ^ ε * R₀ * Q ^ 2 / ((q₀ : ℝ) * M) → 1 ≤ H →
      x ^ (-δ - 5 * ε) * Q / ((q₀ : ℝ) * H) ≤ C₁ * U →
      U ≤ C₁ * x ^ (-5 * ε) * Q / H →
      x ^ (5 * ε) * H / (q₀ : ℝ) ≤ C₁ * V →
      V ≤ C₁ * x ^ (δ + 5 * ε) * H →
      Q / (q₀ : ℝ) ≤ C₁ * U * V → U * V ≤ C₁ * Q / (q₀ : ℝ) →
      R₀ / C₁ ≤ (r₁ : ℝ) * Δ → (r₁ : ℝ) * Δ ≤ C₁ * R₀ →
      U / C₁ ≤ (u₁ : ℝ) → (u₁ : ℝ) ≤ C₁ * U →
      V / C₁ ≤ (v₁ : ℝ) → (v₁ : ℝ) ≤ C₁ * V →
      V / C₁ ≤ (v₂ : ℝ) → (v₂ : ℝ) ≤ C₁ * V →
      Q / (C₁ * (q₀ : ℝ)) ≤ (q₂ : ℝ) → (q₂ : ℝ) ≤ C₁ * Q / (q₀ : ℝ) →
      (q₀ : ℝ) ≤ C₁ * Q →
      (∀ p ∈ q₀.primeFactors, Real.exp ((Real.log x) ^ (1 / 3 : ℝ)) < (p : ℝ)) →
      N ≤ C₁ * (q₀ : ℝ) ^ 2 * x ^ (δ + 50 * ε) * H ^ 2 * Δ →
      Δ ≤ C₁ * N / ((q₀ : ℝ) ^ 2 * x ^ (50 * ε) * H ^ 2) →
      Δ / C₁ ≤ d₀ → d₀ ≤ C₁ * Δ →
      ℓ ≠ 0 → |(ℓ : ℝ)| ≤ C₁ * N / R₀ →
      Hstar ≠ 0 → 1 ≤ C₁ * |Hstar| → |Hstar| ≤ C₁ * H →
      1 ≤ N → N ≤ x → R₀ ≤ x ^ (2 : ℕ) → Q ≤ x ^ (4 : ℕ) →
      H ≤ x ^ (12 : ℕ) → U ≤ x ^ (5 : ℕ) → C₁ * V ≤ x ^ (15 : ℕ) →
      ∀ ψM ψN ψD : ℝ → ℝ,
      ContDiff ℝ ∞ ψM → ContDiff ℝ ∞ ψN → ContDiff ℝ ∞ ψD →
      Function.support ψM ⊆ Set.Icc cM TM →
      Function.support ψN ⊆ Set.Icc cN TN →
      Function.support ψD ⊆ Set.Icc (1 / 2) (5 / 2) →
      (∀ y : ℝ, 0 ≤ ψM y ∧ 0 ≤ ψN y) →
      (∀ y : ℝ, 0 ≤ ψD y ∧ ψD y ≤ 1) →
      (∀ j : ℕ, ∀ y : ℝ,
        |iteratedDeriv j ψM y| ≤ CM j * (Real.log x) ^ EM j ∧
        |iteratedDeriv j ψN y| ≤ CN j * (Real.log x) ^ EN j) →
      (∀ j : ℕ, ∀ y : ℝ, |iteratedDeriv j ψD y| ≤ CD j * (Real.log x) ^ (0 : ℝ)) →
      let Hbound : ℕ := ⌊2 * |Hstar|⌋₊
      let J : Finset ℤ := (Finset.Icc (-(Hbound : ℤ)) (Hbound : ℤ)).filter
        (fun h => 1 ≤ (h : ℝ) / Hstar ∧ (h : ℝ) / Hstar < 2)
      (∀ h ∈ J, h ≠ 0 ∧ |(h : ℝ)| ≤ 2 * C₁ * H) →
      PrimeGap186.sourceSigmaTwo J ψM (fun z => ψN (z / N)) ψD
        M (x ^ (-5 * ε) * Δ) d₀ r₁ q₀ u₁ v₁ v₂ q₂ aN b₁N b₂N ℓ ≤
          K₂ * (q₀ : ℝ) * (Int.gcd (q₀ : ℤ) ℓ : ℝ) * Δ * N *
            (Nat.gcd v₁ v₂ : ℝ) * x ^ (-10 * ε)

end PrimeGap182Audit

#print axioms PrimeGap182Audit.IncidenceSecondaryEstimate
