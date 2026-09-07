import TypeIIIAveragedCoefficients
import TypeIIISharedMatrix

/-!
# Averaging the actual shared Fourier matrix with dependent coefficients

This theorem combines the proved matching multiplier, the exact common-frequency matrix
parameter, and the normalized fourth-moment estimate. Both coefficient vectors may depend
on both outer variables. The sole unproved finite-field input is `LocalFourierHypothesis`.
-/

open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

attribute [local instance] familyProductNeZero

/-- The uniform coefficient estimate for the actual common-frequency shared matrix.
The zero-frequency prime cost is still displayed explicitly, ready for gcd summation. -/
theorem LocalFourierHypothesis.exists_shared_coefficient_estimate
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {ι : Type} [Fintype ι] (q : ι → ℕ) [∀ i, Fact (q i).Prime],
      Pairwise (fun i j => (q i).Coprime (q j)) →
      ∀ (a c A B Ah Ak : ℤ), IsUnit (a : ZMod (∏ i, q i)) →
      ∀ (M R : ℕ), 0 < R → ∀ (W : ℝ), 0 ≤ W →
      ∀ (f : ℕ → ℕ → EuclideanSpace ℂ (IntegerIntervalIndex A M))
        (g : ℕ → ℕ → EuclideanSpace ℂ (IntegerIntervalIndex B M)),
      (∀ x ∈ Finset.range R, ∀ y ∈ Finset.range R, ‖f x y‖ * ‖g x y‖ ≤ W) →
      (∑ x ∈ Finset.range R, ∑ y ∈ Finset.range R,
        ‖matrixCoefficientSum (sharedMatchingMatrix q a c A B M M (Ah + x) (Ak + y))
          (f x y) (g x y)‖) ≤
        K * (4 : ℝ) ^ Fintype.card (ZeroFrequencyPrime q c) *
          ((∏ i : ZeroFrequencyPrime q c, q i.1 : ℕ) : ℝ) * W * (R : ℝ) ^ 2 *
          ((∏ i : NonzeroFrequencyPrime q c, q i.1 : ℕ) : ℝ) ^ ε *
          matrixThreeScale M R ((∏ i : NonzeroFrequencyPrime q c, q i.1 : ℕ) : ℝ) := by
  obtain ⟨K, hK, hbound⟩ := hlocal.exists_matrix_estimate hC hε
  refine ⟨K, hK, ?_⟩
  intro ι _ q _ hcp a c A B Ah Ak ha M R hR W hW f g hfg
  let T : Finset (ℕ × ℕ) := (Finset.range R).product (Finset.range R)
  let L : ℝ := (4 : ℝ) ^ Fintype.card (ZeroFrequencyPrime q c) *
    ((∏ i : ZeroFrequencyPrime q c, q i.1 : ℕ) : ℝ)
  let Kxy (r : ℕ × ℕ) : Matrix (IntegerIntervalIndex A M) (IntegerIntervalIndex B M) ℂ :=
    integerKernelMatrix (fun i : NonzeroFrequencyPrime q c => q i.1)
      (nonzeroFrequencyParameter q a c) A B M M
      ((Ah + r.1 : ℤ) : ZMod (∏ i : NonzeroFrequencyPrime q c, q i.1))
      ((Ak + r.2 : ℤ) : ZMod (∏ i : NonzeroFrequencyPrime q c, q i.1))
  let Mxy (r : ℕ × ℕ) : Matrix (IntegerIntervalIndex A M) (IntegerIntervalIndex B M) ℂ :=
    sharedMatchingMatrix q a c A B M M (Ah + r.1) (Ak + r.2)
  have hcard : T.card = R ^ 2 := by simp [T, pow_two]
  have hT : 0 < T.card := by rw [hcard]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have haux := sum_matrixCoefficients_le_comparison_mean T hT Kxy Mxy
    (fun r => f r.1 r.2) (fun r => g r.1 r.2) hL hW
    (fun r _ => sharedMatchingMatrix_norm_le q a c A B M M (Ah + r.1) (Ak + r.2))
    (fun r hr => hfg r.1 (Finset.mem_product.mp hr).1 r.2 (Finset.mem_product.mp hr).2)
  have haux' :
      (∑ x ∈ Finset.range R, ∑ y ∈ Finset.range R,
        ‖matrixCoefficientSum (sharedMatchingMatrix q a c A B M M (Ah + x) (Ak + y))
          (f x y) (g x y)‖) ≤
        L * W * (R : ℝ) ^ 2 *
          ((∑ x ∈ Finset.range R, ∑ y ∈ Finset.range R,
            ‖integerKernelMatrix (fun i : NonzeroFrequencyPrime q c => q i.1)
              (nonzeroFrequencyParameter q a c) A B M M
              ((Ah + x : ℤ) : ZMod (∏ i : NonzeroFrequencyPrime q c, q i.1))
              ((Ak + y : ℤ) : ZMod (∏ i : NonzeroFrequencyPrime q c, q i.1))‖ ^ 4) /
            (R : ℝ) ^ 2) ^ (1 / 4 : ℝ) := by
    simpa only [T, Kxy, Mxy, Finset.product_eq_sprod, Finset.sum_product,
      Finset.card_product, Finset.card_range, Nat.cast_mul, pow_two] using haux
  have hcp' : Pairwise (fun i j : NonzeroFrequencyPrime q c => (q i.1).Coprime (q j.1)) :=
    fun _ _ hij => hcp (fun heq => hij (Subtype.ext heq))
  have hh := hbound (fun i : NonzeroFrequencyPrime q c => q i.1) hcp'
    (nonzeroFrequencyParameter q a c) (nonzeroFrequencyParameter_ne_zero q hcp a c ha)
    A B Ah Ak M R hR
  apply haux'.trans
  have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ L * W * (R : ℝ) ^ 2 by positivity)
  convert hh' using 1
  dsimp only [L]
  ring

#print axioms LocalFourierHypothesis.exists_shared_coefficient_estimate

end

end PrimeGap182.TypeIII
