import TypeIIIOriginalFrequency
import TypeIIIOriginalCompletion

/-!
# The completed nonzero-frequency bound for the actual physical block

The zero-frequency contribution is explicitly subtracted. Every profile, Fourier
coefficient, arithmetic mask, and sum on the left is the original concrete object.
-/

open scoped BigOperators Classical FourierTransform ContDiff

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

attribute [local instance] familyProductNeZero

/-- Finite outer sums can be bounded after completing each full signed inner sum. -/
theorem finite_sum_norm_tsum_le_mass {ι : Type*} (S : Finset ι)
    (F : ℤ → ι → ℂ) (G : ℤ → ℝ) (hG : Summable G)
    (hbound : ∀ c, ∑ i ∈ S, ‖F c i‖ ≤ G c) :
    (∑ i ∈ S, ‖∑' c : ℤ, F c i‖) ≤ ∑' c : ℤ, G c := by
  have hsingle (i : ι) (hi : i ∈ S) : Summable (fun c : ℤ => ‖F c i‖) :=
    Summable.of_nonneg_of_le (fun c => norm_nonneg _) (fun c =>
      (Finset.single_le_sum (fun j _ => norm_nonneg (F c j)) hi).trans (hbound c)) hG
  have hsum : Summable (fun c : ℤ => ∑ i ∈ S, ‖F c i‖) :=
    (hasSum_sum (fun i hi => (hsingle i hi).hasSum)).summable
  calc
    _ ≤ ∑ i ∈ S, ∑' c : ℤ, ‖F c i‖ :=
      Finset.sum_le_sum (fun i hi => norm_tsum_le_tsum_norm (hsingle i hi))
    _ = ∑' c : ℤ, ∑ i ∈ S, ‖F c i‖ :=
      (Summable.tsum_finsetSum hsingle).symm
    _ ≤ _ := Summable.tsum_le_tsum hbound hsum hG

def sharedProfileNonzeroMass (w : ℕ) [NeZero w] (a A B : ℤ) (M R : ℕ)
    (U V : ℕ+) (α : ℕ → ℕ → IntegerIntervalIndex A M → ℂ)
    (β : ℕ → ℕ → IntegerIntervalIndex B M → ℂ)
    (T H t₀ : ℝ) (ψ : ℝ → ℂ) : ℝ :=
  ∑ x ∈ Finset.range R, ∑ y ∈ Finset.range R,
    let u := positiveOuterIndex U x
    let v := positiveOuterIndex V y
    if SharedOuterAdmissible w a u v then
      ‖sharedProfileCoefficientSum u v w a A B M M (α x y) (β x y) T H t₀ ψ -
        normalizedProfileFourier (u * (v * w)) ψ H t₀ 0 *
          sharedOriginalCoefficientSum u v w a 0 A B M M (α x y) (β x y)‖
    else 0

/-- Actual smooth completion plus the new finite-field hypothesis gives the original
physical nonzero-frequency block estimate, uniformly before choosing any modulus. -/
theorem LocalFourierHypothesis.exists_completed_nonzero_block_estimate
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {ι : Type} [Fintype ι] (q : ι → ℕ) [∀ i, Fact (q i).Prime],
      Pairwise (fun i j => (q i).Coprime (q j)) →
      ∀ (a A B : ℤ), IsUnit (a : ZMod (∏ i, q i)) →
      ∀ (M R : ℕ), 0 < R → ∀ (U V : ℕ+) (X L₁ L₂ T L H t₀ κ ρ : ℝ),
      (U : ℝ) + R ≤ X → (V : ℝ) + R ≤ X → 0 ≤ L₁ → 0 ≤ L₂ →
      0 ≤ T → 0 ≤ L → 0 < H → 0 < κ → 0 ≤ ρ →
      (∀ x ∈ Finset.range R, ∀ y ∈ Finset.range R,
        ((positiveOuterIndex U x * (positiveOuterIndex V y * (∏ i, q i)) : ℕ) : ℝ) ≤ κ * H) →
      (∀ x ∈ Finset.range R, ∀ y ∈ Finset.range R,
        κ * H ≤ ρ * ((positiveOuterIndex U x * (positiveOuterIndex V y * (∏ i, q i)) : ℕ) : ℝ)) →
      ∀ (ψ : ℝ → ℂ), ContDiff ℝ ∞ ψ →
      Function.support ψ ⊆ Set.Icc (-T) T →
      (∀ t : ℝ, ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L) →
      ∀ (α : ℕ → ℕ → IntegerIntervalIndex A M → ℂ)
        (β : ℕ → ℕ → IntegerIntervalIndex B M → ℂ),
      (∀ x ∈ Finset.range R, ∀ y ∈ Finset.range R, ∀ m, ‖α x y m‖ ≤ L₁) →
      (∀ x ∈ Finset.range R, ∀ y ∈ Finset.range R, ∀ n, ‖β x y n‖ ≤ L₂) →
      sharedProfileNonzeroMass (∏ i, q i) a A B M R U V α β T H t₀ ψ ≤
        ((8 * T) * L * ρ) * (K * (M : ℝ) * (L₁ * L₂) * X ^ (1 + ε) *
          (R : ℝ) ^ 2 * ((∏ i, q i : ℕ) : ℝ) ^ ε *
            matrixThreeScale M R ((∏ i, q i : ℕ) : ℝ)) := by
  obtain ⟨K, hK, hb⟩ := hlocal.exists_original_frequency_estimate hC
    (show (1 : ℝ) < 2 by norm_num) hε
  refine ⟨K, hK, ?_⟩
  intro ι _ q _ hcp a A B ha M R hR U V X L₁ L₂ T L H t₀ κ ρ
    hUX hVX hL₁ hL₂ hT hL hH hκ hρ hupper hlower ψ hψ hsupport hbound α β hα hβ
  let w : ℕ := ∏ i, q i
  let gain : ℝ := (8 * T) * L * ρ
  let mass (c : ℤ) : ℝ := (integerFrequencyDecay κ⁻¹ 2 c / κ) *
    maskedSharedOriginalMass w a c A B M R U V α β
  obtain ⟨hseries, hestimate⟩ := hb q hcp a A B ha M R hR U V X L₁ L₂ κ
    hUX hVX hL₁ hL₂ hκ (fun _ => α) (fun _ => β) (fun _ => hα) (fun _ => hβ)
  have hgain : 0 ≤ gain := by dsimp only [gain]; positivity
  let term (c : ℤ) (xy : ℕ × ℕ) : ℂ :=
    let u := positiveOuterIndex U xy.1
    let v := positiveOuterIndex V xy.2
    if SharedOuterAdmissible w a u v then
      if c = 0 then 0 else normalizedProfileFourier (u * (v * w)) ψ H t₀ c *
        sharedOriginalCoefficientSum u v w a c A B M M (α xy.1 xy.2) (β xy.1 xy.2)
    else 0
  have hpoint (c : ℤ) : ∑ xy ∈ Finset.range R ×ˢ Finset.range R, ‖term c xy‖ ≤ gain * mass c := by
    rw [Finset.sum_product]
    dsimp only [mass, maskedSharedOriginalMass]
    simp only [Finset.mul_sum, ← mul_assoc]
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.sum_le_sum
    intro y hy
    by_cases had : SharedOuterAdmissible w a (positiveOuterIndex U x) (positiveOuterIndex V y)
    · dsimp only [term]
      rw [ite_eq_left had, ite_eq_left had]
      by_cases hc : c = 0
      · subst c
        simp only [ite_true, norm_zero, integerFrequencyDecay_zero, zero_div, mul_zero, zero_mul,
          le_refl]
      · rw [ite_eq_right hc, norm_mul]
        apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact normalizedProfileFourier_nonzero_bound _ T L H t₀ κ ρ hT hL hH hκ hρ
          (hupper x hx y hy) (hlower x hx y hy) ψ (hψ.of_le (by norm_num))
          hsupport hbound c hc
    · simp only [term, ite_eq_right had, norm_zero, mul_zero, le_refl]
  have hfinite := finite_sum_norm_tsum_le_mass (Finset.range R ×ˢ Finset.range R)
    term (fun c => gain * mass c) (hseries.mul_left gain) hpoint
  have hphysical : (∑ xy ∈ Finset.range R ×ˢ Finset.range R, ‖∑' c : ℤ, term c xy‖) =
      sharedProfileNonzeroMass w a A B M R U V α β T H t₀ ψ := by
    rw [Finset.sum_product]
    unfold sharedProfileNonzeroMass
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    by_cases had : SharedOuterAdmissible w a (positiveOuterIndex U x) (positiveOuterIndex V y)
    · simp only [term, ite_eq_left had]
      have hp := sharedProfileCoefficientSum_poisson (positiveOuterIndex U x)
        (positiveOuterIndex V y) w a A B M M (α x y) (β x y) T H t₀ hT hH ψ hψ hsupport
      rw [hp.2]
      exact congrArg norm (hasSum_ite_sub_hasSum hp.1.hasSum (0 : ℤ)).tsum_eq
    · simp only [term, ite_eq_right had, tsum_zero, norm_zero]
  rw [hphysical, hseries.tsum_mul_left gain] at hfinite
  exact hfinite.trans (mul_le_mul_of_nonneg_left hestimate hgain)

#print axioms finite_sum_norm_tsum_le_mass
#print axioms LocalFourierHypothesis.exists_completed_nonzero_block_estimate

end

end PrimeGap182.TypeIII
