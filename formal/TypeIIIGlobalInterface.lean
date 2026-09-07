import PrimeGaps186
import TypeIIILocal

/-!
# The global Type III target interface

This file defines the exact global analytic proposition for the source assembly.
It does not assert that proposition. The intended proof takes the explicit new
`LocalFourierHypothesis`, the new sigma lower wall, and `108 ω + 2 δ > 1`.

The finite residue family is primitive and coherent. Coherence is retained because
the signed selected-factor reduction uses one common residue before CRT. The sums,
profile sequences, dense-divisibility witnesses, and convolution below are the
actual objects from the public 186 development.
-/

open scoped BigOperators ContDiff
open PrimeGap186

namespace PrimeGap182.TypeIII

noncomputable section

/-- A family of primitive residue classes coming from one integer on this finite set. -/
def FiniteCoherentPrimitiveResidues (Qset : Finset ℕ+) (a : ℕ+ → ℤ) : Prop :=
  (∀ q ∈ Qset, IsUnit (a q : ZMod (q : ℕ))) ∧
    ∃ a₀ : ℤ, ∀ q ∈ Qset, (a q : ZMod (q : ℕ)) = (a₀ : ZMod (q : ℕ))

/-- Exact interface for the new Type III estimate. Its derivation from the explicit
local finite-field Fourier hypothesis is proved in `TypeIIIGlobalEstimate.lean`. -/
def PositiveSmoothTypeIIIGlobalEstimate (omegaExp δ σ : ℝ) : Prop :=
  ∃ εcap : ℝ, 0 < εcap ∧
    ∀ (C E Eα : ℝ) (D : ℕ), 1 ≤ C →
    ∀ ε : ℝ, 0 < ε → ε ≤ εcap →
    let κ : ℝ := ε / 4
    let J : ℕ := Nat.ceil (22 / ε)
    ∀ A : ℝ, 0 < A →
    ∃ K X : ℝ, 0 < K ∧ Real.exp 1 ≤ X ∧
    ∀ x : ℝ, X ≤ x →
    ∀ M N₁ N₂ N₃ : ℝ, 1 ≤ M → 1 ≤ N₁ → 1 ≤ N₂ → 1 ≤ N₃ →
      let N : ℝ := N₁ * N₂ * N₃
      x / C ≤ M * N → M * N ≤ C * x →
      x ^ (1 / 2 + σ - κ) / C ≤ N₁ * N₂ →
      x ^ (1 / 2 + σ - κ) / C ≤ N₁ * N₃ →
      x ^ (1 / 2 + σ - κ) / C ≤ N₂ * N₃ →
      N₁ ≤ C * x ^ (1 / 2 - σ + κ) →
      N₂ ≤ C * x ^ (1 / 2 - σ + κ) →
      N₃ ≤ C * x ^ (1 / 2 - σ + κ) →
    ∀ Y : Set.Ici (1 : ℝ), (Y : ℝ) = x ^ δ →
    ∀ Qset : Finset ℕ+,
      (∀ q ∈ Qset,
        Squarefree (q : ℕ) ∧
        Nonempty (DenseDivisibilityWitness Y 1 (q : ℕ)) ∧
        (q : ℝ) ≤ C * x ^ (1 / 2 + 2 * omegaExp + κ)) →
    ∀ Lα L₁ L₂ L₃ : ℝ, 0 ≤ Lα → 0 ≤ L₁ → 0 ≤ L₂ → 0 ≤ L₃ →
    ∀ α : ℕ →₀ ℂ,
      (∀ n ∈ α.support, M / C ≤ (n : ℝ) ∧ (n : ℝ) ≤ C * M) →
      (∀ n ∈ α.support,
        ‖α n‖ ≤ Lα * ((Nat.divisors n).card : ℝ) ^ D * (Real.log x) ^ Eα) →
    ∀ ψ₁ ψ₂ ψ₃ : ℝ → ℂ,
      ContDiff ℝ ∞ ψ₁ → ContDiff ℝ ∞ ψ₂ → ContDiff ℝ ∞ ψ₃ →
      Function.support ψ₁ ⊆ Set.Icc (1 / C) C →
      Function.support ψ₂ ⊆ Set.Icc (1 / C) C →
      Function.support ψ₃ ⊆ Set.Icc (1 / C) C →
      (∀ r : ℕ, r ≤ J + 2 → ∀ t : ℝ,
        ‖iteratedDeriv r ψ₁ t‖ ≤ L₁ * (Real.log x) ^ E) →
      (∀ r : ℕ, r ≤ J + 2 → ∀ t : ℝ,
        ‖iteratedDeriv r ψ₂ t‖ ≤ L₂ * (Real.log x) ^ E) →
      (∀ r : ℕ, r ≤ J + 2 → ∀ t : ℝ,
        ‖iteratedDeriv r ψ₃ t‖ ≤ L₃ * (Real.log x) ^ E) →
      let β₁ : ℕ →₀ ℂ := positiveCompactProfileSequence ψ₁ C N₁ 0
      let β₂ : ℕ →₀ ℂ := positiveCompactProfileSequence ψ₂ C N₂ 0
      let β₃ : ℕ →₀ ℂ := positiveCompactProfileSequence ψ₃ C N₃ 0
      let f : ℕ →₀ ℂ := finiteConvolution α
        (finiteConvolution β₁ (finiteConvolution β₂ β₃))
      ∀ a : ℕ+ → ℤ, FiniteCoherentPrimitiveResidues Qset a →
        ∑ q ∈ Qset,
          ‖(∑ n ∈ f.support,
              if (n : ZMod (q : ℕ)) = (a q : ZMod (q : ℕ)) then f n else 0) -
            ((q : ℕ).totient : ℂ)⁻¹ *
              (∑ n ∈ f.support, if Nat.Coprime n (q : ℕ) then f n else 0)‖ ≤
          K * (Lα * L₁ * L₂ * L₃) * x / (Real.log x) ^ A

end

end PrimeGap182.TypeIII
