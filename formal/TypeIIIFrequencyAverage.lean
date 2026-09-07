import TypeIIISharedAveraging
import TypeIIIFrequencyPartition
import TypeIIIFrequencyScale

/-!
# The completed shared-matrix frequency average

The actual integer-frequency prime partition is identified with `gcd(c,w)`. The three
residual powers are then summed against the full signed-integer decay envelope, at every
positive width. Coefficient vectors may depend on the frequency and both outer variables.
Only the explicitly stated new prime-local Fourier proposition remains a finite-field input.
-/

open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

attribute [local instance] familyProductNeZero

/-- The actual outer sum of the bilinear matrix coefficients at one fixed frequency. -/
def sharedCoefficientMass {ι : Type*} [Fintype ι] (q : ι → ℕ) [∀ i, Fact (q i).Prime]
    (a c A B Ah Ak : ℤ) (M R : ℕ)
    (f : ℕ → ℕ → EuclideanSpace ℂ (IntegerIntervalIndex A M))
    (g : ℕ → ℕ → EuclideanSpace ℂ (IntegerIntervalIndex B M)) : ℝ :=
  ∑ x ∈ Finset.range R, ∑ y ∈ Finset.range R,
    ‖matrixCoefficientSum (sharedMatchingMatrix q a c A B M M (Ah + x) (Ak + y))
      (f x y) (g x y)‖

theorem sharedCoefficientMass_nonneg {ι : Type*} [Fintype ι] (q : ι → ℕ)
    [∀ i, Fact (q i).Prime] (a c A B Ah Ak : ℤ) (M R : ℕ)
    (f : ℕ → ℕ → EuclideanSpace ℂ (IntegerIntervalIndex A M))
    (g : ℕ → ℕ → EuclideanSpace ℂ (IntegerIntervalIndex B M)) :
    0 ≤ sharedCoefficientMass q a c A B Ah Ak M R f g :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))

/-- The fixed-frequency estimate with the actual gcd and the three exact residual powers. -/
theorem LocalFourierHypothesis.exists_shared_mass_gcd_bound
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
      sharedCoefficientMass q a c A B Ah Ak M R f g ≤
        K * W * (R : ℝ) ^ 2 * ((∏ i, q i : ℕ) : ℝ) ^ ε *
          sharedThreeScale M R ((∏ i, q i : ℕ) : ℝ) (Int.gcd c ((∏ i, q i : ℕ) : ℤ)) := by
  obtain ⟨K₁, hK₁, hb₁⟩ := hlocal.exists_shared_coefficient_estimate hC hε
  obtain ⟨K₂, hK₂, hb₂⟩ := exists_frequency_partition_subpower hε
  refine ⟨K₁ * K₂, mul_pos hK₁ hK₂, ?_⟩
  intro ι _ q _ hcp a c A B Ah Ak ha M R hR W hW f g hfg
  have hmain := hb₁ q hcp a c A B Ah Ak ha M R hR W hW f g hfg
  have hpart := hb₂ q hcp c
  let E : ℕ := ∏ i : ZeroFrequencyPrime q c, q i.1
  let P : ℕ := ∏ i : NonzeroFrequencyPrime q c, q i.1
  have hE : (0 : ℝ) < E := by exact_mod_cast (NeZero.pos E)
  have hEP : (E : ℝ) * (P : ℝ) = ((∏ i, q i : ℕ) : ℝ) := by
    exact_mod_cast frequency_partition_product q c
  have he : E = Int.gcd c ((∏ i, q i : ℕ) : ℤ) := zeroFrequency_product_eq_gcd q hcp c
  have hscale : (Int.gcd c ((∏ i, q i : ℕ) : ℤ) : ℝ) * matrixThreeScale M R P =
      sharedThreeScale M R ((∏ i, q i : ℕ) : ℝ) (Int.gcd c ((∏ i, q i : ℕ) : ℤ)) := by
    have hh := mul_matrixThreeScale_eq_sharedThreeScale M R E P hE (Nat.cast_nonneg P)
    rw [hEP, he] at hh
    exact hh
  apply hmain.trans
  calc
    _ = (K₁ * W * (R : ℝ) ^ 2 * matrixThreeScale M R P) *
        ((4 : ℝ) ^ Fintype.card (ZeroFrequencyPrime q c) * (E : ℝ) * (P : ℝ) ^ ε) := by
      dsimp only [E, P]
      ring
    _ ≤ (K₁ * W * (R : ℝ) ^ 2 * matrixThreeScale M R P) *
        (K₂ * ((∏ i, q i : ℕ) : ℝ) ^ ε * (Int.gcd c ((∏ i, q i : ℕ) : ℤ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hpart (mul_nonneg
        (mul_nonneg (mul_nonneg hK₁.le hW) (sq_nonneg _))
        (matrixThreeScale_nonneg (Nat.cast_nonneg M) (Nat.cast_nonneg R) (Nat.cast_nonneg P)))
    _ = _ := by rw [← hscale]; ring

/-- Full integer-frequency summability and bound for the actual shared matrix coefficients.
The positive width may be less than one. The zero frequency is excluded by the decay
weight's definition; it remains a separate analytic term. -/
theorem LocalFourierHypothesis.exists_shared_frequency_tsum_estimate
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    {decay ε : ℝ} (hdecay : 1 < decay) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {ι : Type} [Fintype ι] (q : ι → ℕ) [∀ i, Fact (q i).Prime],
      Pairwise (fun i j => (q i).Coprime (q j)) →
      ∀ (a A B Ah Ak : ℤ), IsUnit (a : ZMod (∏ i, q i)) →
      ∀ (M R : ℕ), 0 < R → ∀ (W κ : ℝ), 0 ≤ W → 0 < κ →
      ∀ (f : ℤ → ℕ → ℕ → EuclideanSpace ℂ (IntegerIntervalIndex A M))
        (g : ℤ → ℕ → ℕ → EuclideanSpace ℂ (IntegerIntervalIndex B M)),
      (∀ c : ℤ, ∀ x ∈ Finset.range R, ∀ y ∈ Finset.range R, ‖f c x y‖ * ‖g c x y‖ ≤ W) →
      Summable (fun c : ℤ => (integerFrequencyDecay κ⁻¹ decay c / κ) *
        sharedCoefficientMass q a c A B Ah Ak M R (f c) (g c)) ∧
      (∑' c : ℤ, (integerFrequencyDecay κ⁻¹ decay c / κ) *
        sharedCoefficientMass q a c A B Ah Ak M R (f c) (g c)) ≤
        K * W * (R : ℝ) ^ 2 * ((∏ i, q i : ℕ) : ℝ) ^ ε *
          matrixThreeScale M R ((∏ i, q i : ℕ) : ℝ) := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨K₁, hK₁, hb₁⟩ := hlocal.exists_shared_mass_gcd_bound hC hhalf
  obtain ⟨K₂, hK₂, hb₂⟩ := exists_sharedThreeScale_frequency_sum hdecay hhalf
  refine ⟨K₁ * K₂, mul_pos hK₁ hK₂, ?_⟩
  intro ι _ q _ hcp a A B Ah Ak ha M R hR W κ hW hκ f g hfg
  let w : ℕ := ∏ i, q i
  let L : ℝ := K₁ * W * (R : ℝ) ^ 2 * (w : ℝ) ^ (ε / 2)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hw : (0 : ℝ) < w := by exact_mod_cast (NeZero.pos w)
  let F (c : ℤ) := (integerFrequencyDecay κ⁻¹ decay c / κ) *
    sharedCoefficientMass q a c A B Ah Ak M R (f c) (g c)
  have hnonneg (c : ℤ) : 0 ≤ F c :=
    mul_nonneg (div_nonneg (integerFrequencyDecay_nonneg (inv_nonneg.mpr hκ.le) decay c) hκ.le)
      (sharedCoefficientMass_nonneg q a c A B Ah Ak M R (f c) (g c))
  have hfinite (S : Finset ℤ) : (∑ c ∈ S, F c) ≤
      (K₁ * K₂) * W * (R : ℝ) ^ 2 * (w : ℝ) ^ ε * matrixThreeScale M R w := by
    calc
      _ ≤ ∑ c ∈ S, L * ((integerFrequencyDecay κ⁻¹ decay c / κ) *
          sharedThreeScale M R w (Int.gcd c (w : ℤ))) := by
        apply Finset.sum_le_sum
        intro c _
        have hh := mul_le_mul_of_nonneg_left
          (hb₁ q hcp a c A B Ah Ak ha M R hR W hW (f c) (g c) (hfg c))
          (div_nonneg (integerFrequencyDecay_nonneg (inv_nonneg.mpr hκ.le) decay c) hκ.le)
        convert hh using 1
        dsimp only [L, w]
        ring
      _ = L * ∑ c ∈ S, (integerFrequencyDecay κ⁻¹ decay c / κ) *
          sharedThreeScale M R w (Int.gcd c (w : ℤ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ L * (K₂ * (w : ℝ) ^ (ε / 2) * matrixThreeScale M R w) :=
        mul_le_mul_of_nonneg_left
          (hb₂ w (NeZero.pos w) κ M R hκ (Nat.cast_nonneg M) (Nat.cast_nonneg R) S) hL
      _ = _ := by
        have he : (w : ℝ) ^ (ε / 2) * (w : ℝ) ^ (ε / 2) = (w : ℝ) ^ ε := by
          rw [← Real.rpow_add hw]
          congr 1
          ring
        dsimp only [L]
        calc
          _ = (K₁ * K₂) * W * (R : ℝ) ^ 2 *
              ((w : ℝ) ^ (ε / 2) * (w : ℝ) ^ (ε / 2)) * matrixThreeScale M R w := by ring
          _ = _ := by rw [he]
  exact ⟨summable_of_sum_le hnonneg hfinite, Real.tsum_le_of_sum_le hnonneg hfinite⟩

#print axioms LocalFourierHypothesis.exists_shared_mass_gcd_bound
#print axioms LocalFourierHypothesis.exists_shared_frequency_tsum_estimate

end

end PrimeGap182.TypeIII
