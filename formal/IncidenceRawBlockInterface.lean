import IncidenceRawTaylor
import IncidenceSecondaryInterface

/-!
# Exact positive raw-block seam

This proposition uses the same literal source data as IncidenceSecondaryEstimate.
Its conclusion is an upper bound for the actual original d-summed, masked source
energy. It is an intermediate target to be proved from the local rank-four
hypothesis; no estimate is postulated here. The generic public positive Cauchy
identity transfers a proof of this proposition to the secondary estimate.
-/

noncomputable section
namespace PrimeGap182Audit
open Classical
open scoped BigOperators ContDiff

def IncidenceRawBlockEstimate («ω» δ ε γlo γhi : ℝ) : Prop :=
  ∀ C₁ cM TM cN TN : ℝ,
    1 ≤ C₁ → 0 < cM → cM ≤ TM → 0 < cN → cN ≤ TN →
    ∀ CM EM CN EN CD : ℕ → ℝ,
    (∀ j : ℕ, 0 ≤ CM j ∧ 0 ≤ CN j ∧ 0 ≤ CD j) →
    ∃ Xtwo : ℝ, Real.exp 1 ≤ Xtwo ∧
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
      let m := r₁ * q₀ * u₁ * Nat.lcm v₁ v₂ * q₂
      let Δ₁ := x ^ (-5 * ε) * Δ
      let Dmax : ℕ := ⌊d₀ + (5 / 2) * Δ₁⌋₊
      let I : Finset ℤ := Finset.Icc ⌈cN * N⌉ ⌊TN * N⌋
      ∀ w w₂ : ℕ, ∀ Y : ℤ, 0 < w → w ≤ Dmax → Nat.Coprime w m →
      ∀ A B : ℤ, IsUnit (A : ZMod m) →
      (B : ZMod r₁) = 0 → (B : ZMod (q₀ * u₁ * Nat.lcm v₁ v₂)) = 0 →
      (B : ZMod q₂) = ((ℓ * (r₁ : ℤ)) : ZMod q₂) →
      ∀ E : ZMod q₀ → Finset (ZMod q₀),
      (∀ r, IsUnit r → ((E r).card : ℝ) ≤ (Int.gcd (q₀ : ℤ) ℓ : ℝ)) →
      (∀ d : ℕ, Nat.Coprime d q₀ → ∀ n : ℤ,
        PrimeGap186.sourceCompatibility (d * r₁) q₀ b₁N b₂N ℓ n =
          if (n : ZMod q₀) ∈ E (d : ZMod q₀) then 1 else 0) →
      let F := incidenceSourceFrequencyBlock J v₁ v₂ m w w₂ Y
      let R₁ := r₁ * q₀ * u₁ * v₁ * q₂
      let R₂ := r₁ * q₀ * u₁ * v₂ * q₂
      let amp : ℕ → ℤ × ℤ → ℂ := fun d h =>
        PrimeGap186.sourcePhiRealFactor ψM M R₁ h.1 (d : ℝ) *
          star (PrimeGap186.sourcePhiRealFactor ψM M R₂ h.2 (d : ℝ))
      let ρ : ℕ → ℝ := fun d => ψD (((d : ℝ) - d₀) / Δ₁)
      (incidenceRawBlockEnergy m w Dmax r₁ q₀ u₁ v₁ v₂ q₂ A B ℓ E ψN N F I
        (incidenceQuotientFrequency w v₁ v₂) amp ρ).re ≤
          ((q₀ : ℝ) * (Int.gcd (q₀ : ℤ) ℓ : ℝ) * (Nat.gcd v₁ v₂ : ℝ) * N) ^ 2 *
            x ^ (-40 * ε)

end PrimeGap182Audit

#print axioms PrimeGap182Audit.IncidenceRawBlockEstimate
