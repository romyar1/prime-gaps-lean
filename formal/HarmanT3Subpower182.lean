import HarmanT3Distribution182

/-! Subpower-modulus transfer for the literal new T3 source. The retreat
witness consists only of the explicit bilinear and smooth Type III estimates
at slightly larger parameters and their checked geometric inequalities. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

open Classical in
theorem sourceT3_subpower_coherent_log_saving_of_analytic_inputs
    (τ : ℝ) (hτ : 0 < τ) (hτsmall : τ ≤ (1 / 10 ^ 10 : ℝ))
    (j : ℕ) (hj : 1 ≤ j) («ω» δ σdist σIII : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ)
    (hσclass : (1 / 2 : ℝ) - 41361 / 100000 + τ < σdist)
    (hσhalf : σdist < 1 / 2) (hσIIIhi : σIII < 2159 / 25000 - τ)
    (hretreat : ∃ r : ℝ, 0 < r ∧ «ω» + r < 1 / 12 ∧
      PrimeGap182.TypeIII.PositiveSmoothTypeIIIGlobalEstimate («ω» + r) (δ + r) σIII ∧
      (1 / 4 : ℝ) + 7 * («ω» + r) + 2 * (δ + r) < 34941 / 100000 - τ ∧
      SourceBilinearEstimate j («ω» + r) (δ + r) σdist)
    (L0 : ℝ → ℝ) (hL0 : ∀ x : ℝ, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0)) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ Real.exp 100 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ Y : Set.Ici (1 : ℝ), (Y : ℝ) = x ^ δ →
      ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
      ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
        let F : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
          Finsupp.single n (sourceT3 x n : ℂ)
        let Q := (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω») * L0 x⌋₊).filter (fun q =>
          q ∣ (∏ p ∈ I, p) ∧ Nonempty (DenseDivisibilityWitness Y j q))
        (∑ q ∈ Q, ‖fullDiscrepancy F q a‖) ≤ K * x / (Real.log x) ^ A := by
  obtain ⟨r, hr, hωupper, hIII, hsmooth, hbilinear⟩ := hretreat
  obtain ⟨Xr, hXr⟩ := eventually_atTop.mp
    (central_subpower_modulus_family_subset j «ω» δ r hr L0 hL0 hL0sub)
  intro A hA
  obtain ⟨K, Xp, hK, hXp, hp⟩ :=
    sourceT3_selected_dense_log_saving_of_analytic_inputs τ hτ hτsmall j hj
      («ω» + r) (δ + r) (by linarith) hωupper (by linarith)
      σdist σIII hσclass hσhalf hIII hσIIIhi hsmooth hbilinear A hA
  refine ⟨K, max Xp Xr, hK, hXp.trans (le_max_left _ _), ?_⟩
  intro x hx Y hY I hI a ha F Q
  have hxp : Xp ≤ x := (le_max_left _ _).trans hx
  have hxr : Xr ≤ x := (le_max_right _ _).trans hx
  have hsubset := hXr x hxr Y hY I
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun q _ _ => norm_nonneg (fullDiscrepancy F q a))).trans (hp x hxp I hI a ha)

#print axioms sourceT3_subpower_coherent_log_saving_of_analytic_inputs

end PrimeGap182Analytic.Harman
