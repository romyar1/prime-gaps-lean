import PrimeGaps186
import TypeIIIGlobalInterface

/-! Exact intermediate analytic interfaces for the new source assembly.
These are propositions about the actual convolution and discrepancies.
The lower-order instances are proved here. The order-three instance is
to be supplied by the incidence proof, rather than by an added axiom. -/

noncomputable section
open scoped BigOperators
open PrimeGap186

namespace PrimeGap182Analytic.Harman

open Classical in
def SourceBilinearEstimate (density : ℕ) («ω» δ σ : ℝ) : Prop :=
  ∀ {ι : Type}, (M N : ℝ → ι → ℝ) → (α β : ℝ → ι → ℕ →₀ ℂ) →
  ∀ (c C W X₀ : ℝ) (k s : ℕ),
    0 < c → 1 ≤ C → 0 ≤ W → Real.exp 1 ≤ X₀ →
    (∀ x : ℝ, X₀ ≤ x → ∀ i : ι,
      x / C ≤ M x i * N x i ∧ M x i * N x i ≤ C * x ∧
      x ^ (1 / 2 - σ) ≤ N x i ∧ N x i ≤ x ^ (1 / 2 : ℝ)) →
    (∀ x : ℝ, X₀ ≤ x → ∀ i : ι,
      (∀ n ∈ (α x i).support,
        c * M x i ≤ (n : ℝ) ∧ (n : ℝ) ≤ C * M x i) ∧
      (∀ n ∈ (β x i).support,
        c * N x i ≤ (n : ℝ) ∧ (n : ℝ) ≤ C * N x i)) →
    (∀ x : ℝ, X₀ ≤ x → ∀ i : ι, ∀ n : ℕ,
      ‖α x i n‖ ≤ W * (n.divisors.card : ℝ) ^ k * (Real.log x) ^ k ∧
      ‖β x i n‖ ≤ W * (n.divisors.card : ℝ) ^ k * (Real.log x) ^ k) →
    (∀ A : ℝ, 0 < A →
      ∃ KSW XSW : ℝ, 0 < KSW ∧ X₀ ≤ XSW ∧
        ∀ x : ℝ, XSW ≤ x → ∀ i : ι,
        ∀ q r a : ℕ, 0 < q → 0 < r → Nat.Coprime a q →
          ‖fullDiscrepancy
              ((β x i).filter (fun n : ℕ => Nat.Coprime n r)) q a‖ ≤
            KSW * ((q * r).divisors.card : ℝ) ^ s * N x i /
              (Real.log x) ^ A) →
    ∀ A : ℝ, 0 < A →
      ∃ K X : ℝ, 0 < K ∧ X₀ ≤ X ∧
        ∀ x : ℝ, X ≤ x → ∀ i : ι,
        ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
        ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
          (∑ q ∈ (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
              q ∣ (∏ p ∈ I, p) ∧
                Nonempty (DenseDivisibilityWitness
                  ⟨max 1 (x ^ δ), by exact le_max_left (1 : ℝ) (x ^ δ)⟩ density q)),
            ‖fullDiscrepancy (finiteConvolution (α x i) (β x i)) q a‖) ≤
              K * x / (Real.log x) ^ A

theorem sourceBilinearEstimate_lower_order (density : ℕ) («ω» δ σ : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ) (hσ : 0 < σ)
    (hI : (density = 1 ∧ 54 * «ω» + 15 * δ + 5 * σ < 1) ∨
      (density = 2 ∧ 56 * «ω» + 16 * δ + 4 * σ < 1))
    (hII : 68 * «ω» + 14 * δ < 1) :
    SourceBilinearEstimate density «ω» δ σ := by
  intro ι M N α β c C W X₀ k s hc hC hW hX₀ hscale hsupp hcoeff hSW
  exact sourceTypeI_II_lowerOrder_dense_uniform_log_saving
    density «ω» δ σ hω hδ hσ hI hII M N α β c C W X₀ k s
    hc hC hW hX₀ hscale hsupp hcoeff hSW

/-- A stronger lower scale bound only restricts the coefficient families. -/
theorem SourceBilinearEstimate.mono_sigma {density : ℕ} {«ω» δ σ σ' : ℝ}
    (h : SourceBilinearEstimate density «ω» δ σ) (hσ : σ' ≤ σ) :
    SourceBilinearEstimate density «ω» δ σ' := by
  intro ι M N α β c C W X₀ k s hc hC hW hX₀ hscale hsupp hcoeff hSW
  apply h M N α β c C W X₀ k s hc hC hW hX₀ _ hsupp hcoeff hSW
  intro x hx i
  have hx1 : 1 ≤ x := (Real.one_le_exp zero_le_one).trans (hX₀.trans hx)
  exact ⟨(hscale x hx i).1, (hscale x hx i).2.1,
    (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)).trans (hscale x hx i).2.2.1,
    (hscale x hx i).2.2.2⟩

end PrimeGap182Analytic.Harman

#print axioms PrimeGap182Analytic.Harman.sourceBilinearEstimate_lower_order
#print axioms PrimeGap182Analytic.Harman.SourceBilinearEstimate.mono_sigma
