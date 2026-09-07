import PrimeGaps186

/-!
# The classical high band on the actual triply dense source moduli

This is the proved public-186 lower-order theorem at density order two,
restricted to the order-three modulus set. There is no local Deligne
premise in this component. It supplies the complementary high-N range
needed when the new incidence argument stops below square-root scale.
-/

noncomputable section

namespace PrimeGap182Audit

open PrimeGap186
open scoped BigOperators

open scoped Classical in
theorem incidenceTripleModuli_subset_double (Y : Set.Ici (1 : ℝ))
    (cutoff : ℕ) (I : Finset ℕ) :
    tripleSourceModuli Y cutoff I ⊆ (Finset.Icc 1 cutoff).filter (fun q =>
      q ∣ (∏ p ∈ I, p) ∧ Nonempty (DenseDivisibilityWitness Y 2 q)) := by
  classical
  intro q hq
  obtain ⟨hcut, hdvd, hdd⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨hcut, hdvd, denseDivisibility_mono_order hdd (by norm_num)⟩

theorem incidenceTypeII_high_band («ω» δ γH : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ) (hγH : γH < 1 / 2)
    (hI : 1 / 4 + 14 * «ω» + 4 * δ < γH)
    (hII : 68 * «ω» + 14 * δ < 1)
    {ι : Type*} (M N : ℝ → ι → ℝ) (α β : ℝ → ι → ℕ →₀ ℂ)
    (c C W X₀ : ℝ) (k s : ℕ)
    (hc : 0 < c) (hCscale : 1 ≤ C) (hW : 0 ≤ W) (hX₀ : Real.exp 1 ≤ X₀)
    (hscale : ∀ x : ℝ, X₀ ≤ x → ∀ i : ι,
      x / C ≤ M x i * N x i ∧ M x i * N x i ≤ C * x ∧
      x ^ γH ≤ N x i ∧ N x i ≤ x ^ (1 / 2 : ℝ))
    (hsupport : ∀ x : ℝ, X₀ ≤ x → ∀ i : ι,
      (∀ n ∈ (α x i).support,
        c * M x i ≤ (n : ℝ) ∧ (n : ℝ) ≤ C * M x i) ∧
      (∀ n ∈ (β x i).support,
        c * N x i ≤ (n : ℝ) ∧ (n : ℝ) ≤ C * N x i))
    (hcoeff : ∀ x : ℝ, X₀ ≤ x → ∀ i : ι, ∀ n : ℕ,
      ‖α x i n‖ ≤ W * (n.divisors.card : ℝ) ^ k * (Real.log x) ^ k ∧
      ‖β x i n‖ ≤ W * (n.divisors.card : ℝ) ^ k * (Real.log x) ^ k)
    (hSW : ∀ A : ℝ, 0 < A →
      ∃ KSW XSW : ℝ, 0 < KSW ∧ X₀ ≤ XSW ∧
        ∀ x : ℝ, XSW ≤ x → ∀ i : ι,
        ∀ q r a : ℕ, 0 < q → 0 < r → Nat.Coprime a q →
          ‖fullDiscrepancy
              ((β x i).filter (fun n : ℕ => Nat.Coprime n r)) q a‖ ≤
            KSW * ((q * r).divisors.card : ℝ) ^ s * N x i /
              (Real.log x) ^ A) :
    ∀ A : ℝ, 0 < A →
      ∃ K X : ℝ, 0 < K ∧ X₀ ≤ X ∧
        ∀ x : ℝ, X ≤ x → ∀ i : ι,
        ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
        ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
          (∑ q ∈ tripleSourceModuli
              ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩
              ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊ I,
            ‖fullDiscrepancy (finiteConvolution (α x i) (β x i)) q a‖) ≤
              K * x / (Real.log x) ^ A := by
  classical
  have hσ : 0 < 1 / 2 - γH := by linarith
  have hI' : 56 * «ω» + 16 * δ + 4 * (1 / 2 - γH) < 1 := by linarith
  have hscale' : ∀ x : ℝ, X₀ ≤ x → ∀ i : ι,
      x / C ≤ M x i * N x i ∧ M x i * N x i ≤ C * x ∧
      x ^ (1 / 2 - (1 / 2 - γH)) ≤ N x i ∧ N x i ≤ x ^ (1 / 2 : ℝ) := by
    simpa only [sub_sub_cancel] using hscale
  have hhigh := sourceTypeI_II_lowerOrder_dense_uniform_log_saving
    2 «ω» δ (1 / 2 - γH) hω hδ hσ (Or.inr ⟨rfl, hI'⟩) hII
    M N α β c C W X₀ k s hc hCscale hW hX₀ hscale' hsupport hcoeff hSW
  intro A hA
  obtain ⟨K, X, hK, hX, hbound⟩ := hhigh A hA
  refine ⟨K, X, hK, hX, ?_⟩
  intro x hx i I hIp a ha
  apply (Finset.sum_le_sum_of_subset_of_nonneg (incidenceTripleModuli_subset_double _ _ _)
    (fun _ _ _ => norm_nonneg _)).trans
  exact hbound x hx i I hIp a ha

end PrimeGap182Audit

#print axioms PrimeGap186.sourceTypeI_II_lowerOrder_dense_uniform_log_saving
#print axioms PrimeGap182Audit.incidenceTripleModuli_subset_double
#print axioms PrimeGap182Audit.incidenceTypeII_high_band
