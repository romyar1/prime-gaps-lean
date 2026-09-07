import MixedAuxiliaryCRT182
import MixedAuxiliaryPeriod182

/-!
Uniform marked-bin arithmetic for distinct auxiliary cutoffs. This module
keeps each erased coefficient paired with its own auxiliary coefficient.
-/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186 PrimeGap182.Selberg

namespace PrimeGap182Analytic

theorem finPiFinset_eq_classical {k : ℕ} (t : Fin k → Finset ℕ)
    (dec : DecidableEq (Fin k)) :
    @Fintype.piFinset (Fin k) dec inferInstance (fun _ => ℕ) t =
      @Fintype.piFinset (Fin k) (Classical.typeDecidableEq _) inferInstance (fun _ => ℕ) t := by
  ext r
  simp only [Fintype.mem_piFinset]

def auxiliaryProductValue (h : Fin 39 → ℕ) (i : Fin 39)
    (u : (Fin 1 → ℕ) →₀ ℝ) (z : (Fin 38 → ℕ) →₀ ℝ) (n : ℕ) : ℝ :=
  sampledSelbergRoot u (fun _ => n + h i) *
    sampledSelbergRoot z (fun j => n + h (i.succAbove j))

theorem auxiliaryPeriodCross_product (q : ℕ) (h : Fin 39 → ℕ) (i : Fin 39)
    (u₁ u₂ : (Fin 1 → ℕ) →₀ ℝ) (z₁ z₂ : (Fin 38 → ℕ) →₀ ℝ) :
    (1 / (q : ℝ)) * (∑ n ∈ Finset.range q,
      auxiliaryProductValue h i u₁ z₁ n * auxiliaryProductValue h i u₂ z₂ n) =
      auxiliaryPeriodCross q h i u₁ u₂ z₁ z₂ := by
  unfold auxiliaryPeriodCross
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  dsimp only [auxiliaryProductValue]
  ring

open Classical in
theorem mixed_auxiliary_crt_root_form
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
      ∀ M : ℕ, 0 < M → Nat.Coprime W M →
        (∀ s ∈ u₁.support, Nat.Coprime (s 0) M) →
        (∀ s ∈ u₂.support, Nat.Coprime (s 0) M) →
        (∀ r ∈ z₁.support, Nat.Coprime (∏ j, r j) M) →
        (∀ r ∈ z₂.support, Nat.Coprime (∏ j, r j) M) →
        ∀ b : ℕ,
          |(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
              if Nat.ModEq W n b ∧ M ∣ n + h i then
                auxiliaryProductValue h i u₁ z₁ n * auxiliaryProductValue h i u₂ z₂ n else 0) -
            x / ((W : ℝ) * (M : ℝ)) * auxiliaryPeriodCross q h i u₁ u₂ z₁ z₂| ≤
            2 * (selbergL1 u₁ * selbergL1 z₁) ^ 2 +
              2 * (selbergL1 u₂ * selbergL1 z₂) ^ 2 := by
  intro ρ h W q u₁ u₂ z₁ z₂ hu₁ hu₂ hz₁ hz₂ M hM hWM hu₁M hu₂M hz₁M hz₂M b
  have hc := mixed_auxiliary_marked_interval_period_crt
    (𝓗 := 𝓗) (h𝓗_card := h𝓗_card) i x κ hx hκ u₁ u₂ z₁ z₂
    hu₁ hu₂ hz₁ hz₂ M hM hWM hu₁M hu₂M hz₁M hz₂M b
  rw [← auxiliaryPeriodCross_product]
  simpa only [auxiliaryProductValue, sampledSelbergRoot_fin, Fin.forall_fin_one,
    selbergL1, finPiFinset_eq_classical] using hc

#print axioms mixed_auxiliary_crt_root_form

end PrimeGap182Analytic
