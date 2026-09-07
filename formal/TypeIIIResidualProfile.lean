import TypeIIIResidualTotal
import TypeIIIResidualZeroTotal

/-! The complete actual signed profile blocks, combining the zero and nonzero modes. -/

open scoped BigOperators Classical ContDiff

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

def residualProfileFullMass (w : ℕ) [NeZero w] (a : ℤ) (M R g : ℕ)
    (α β : ℕ → ℕ → IntegerIntervalIndex 1 M → ℂ)
    (T H t₀ : ℝ) (ψ : ℝ → ℂ) : ℝ :=
  let U := residualStart R g
  ∑ x ∈ Finset.range (residualLength R g), ∑ y ∈ Finset.range (residualLength R g),
    let u := positiveOuterIndex U x
    let v := positiveOuterIndex U y
    if SharedOuterAdmissible w a u v then
      ‖sharedProfileCoefficientSum u v w a 1 1 M M (α u v) (β u v) T H t₀ ψ‖
    else 0

theorem residualProfileFullMass_le_split (w : ℕ) [NeZero w] (a : ℤ) (M R g : ℕ)
    (α β : ℕ → ℕ → IntegerIntervalIndex 1 M → ℂ)
    (T H t₀ : ℝ) (ψ : ℝ → ℂ) :
    residualProfileFullMass w a M R g α β T H t₀ ψ ≤
      residualProfileNonzeroMass w a 1 1 M R g α β T H t₀ ψ +
        residualProfileZeroMass w a M R g α β H t₀ ψ := by
  simp only [residualProfileFullMass, residualProfileNonzeroMass, sharedProfileNonzeroMass,
    residualProfileZeroMass, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  by_cases h : SharedOuterAdmissible w a
      (positiveOuterIndex (residualStart R g) x) (positiveOuterIndex (residualStart R g) y)
  · simp only [ite_eq_left h]
    refine (norm_add_le _ _).trans_eq' ?_
    simp only [positiveOuterIndex, PNat.mk_coe, sub_add_cancel]
  · simp only [ite_eq_right h, add_zero, le_refl]

def admissibleResidualProfileMass (a : ℤ) (M R s g : ℕ)
    (α β : ℕ → ℕ → IntegerIntervalIndex 1 M → ℂ)
    (T H t₀ : ℝ) (ψ : ℝ → ℂ) : ℝ :=
  if h : s * g ≠ 0 then
    letI : NeZero (s * g) := ⟨h⟩
    if Squarefree (s * g) ∧ IsUnit (a : ZMod (s * g)) then
      residualProfileFullMass (s * g) a M R g α β T H t₀ ψ
    else 0
  else 0

theorem admissibleResidualProfileMass_nonneg (a : ℤ) (M R s g : ℕ)
    (α β : ℕ → ℕ → IntegerIntervalIndex 1 M → ℂ)
    (T H t₀ : ℝ) (ψ : ℝ → ℂ) :
    0 ≤ admissibleResidualProfileMass a M R s g α β T H t₀ ψ := by
  unfold admissibleResidualProfileMass
  split_ifs
  · unfold residualProfileFullMass
    positivity
  all_goals exact le_rfl

theorem admissibleResidualProfileMass_le_split (a : ℤ) (M R s g : ℕ)
    (α β : ℕ → ℕ → IntegerIntervalIndex 1 M → ℂ)
    (T H t₀ : ℝ) (ψ : ℝ → ℂ) :
    admissibleResidualProfileMass a M R s g α β T H t₀ ψ ≤
      admissibleResidualNonzeroMass a 1 1 M R s g α β T H t₀ ψ +
        admissibleResidualZeroMass a M R s g α β H t₀ ψ := by
  unfold admissibleResidualProfileMass admissibleResidualNonzeroMass admissibleResidualZeroMass
  by_cases hsg : s * g ≠ 0
  · simp only [dite_eq_left hsg]
    let : NeZero (s * g) := ⟨hsg⟩
    split_ifs
    · exact residualProfileFullMass_le_split (s * g) a M R g α β T H t₀ ψ
    · simp only [add_zero, le_refl]
  · simp only [dite_eq_right hsg, add_zero, le_refl]

/-- Actual entire signed residual blocks satisfy the two zero-mode and three nonzero
scales. The only analytic input beyond the proved baseline reductions is the explicit
new finite-field `LocalFourierHypothesis`. -/
theorem LocalFourierHypothesis.exists_residual_profile_total_estimate
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a : ℤ) (M R S : ℕ), 0 < M → 0 < R →
      ∀ (L₁ L₂ T L H t₀ : ℝ), 0 ≤ L₁ → 0 ≤ L₂ → 0 ≤ T → 0 ≤ L → 0 < H →
      ∀ (ψ : ℝ → ℂ), ContDiff ℝ ∞ ψ →
      Function.support ψ ⊆ Set.Icc (-T) T →
      (∀ t : ℝ, ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L) →
      ∀ (α β : ℕ → ℕ → ℕ → ℕ → IntegerIntervalIndex 1 M → ℂ),
      (∀ s ∈ Finset.Icc 1 S, ∀ g ∈ Finset.Icc 1 (2 * R),
        ∀ u ∈ residualRange R g, ∀ v ∈ residualRange R g, ∀ m, ‖α s g u v m‖ ≤ L₁) →
      (∀ s ∈ Finset.Icc 1 S, ∀ g ∈ Finset.Icc 1 (2 * R),
        ∀ u ∈ residualRange R g, ∀ v ∈ residualRange R g, ∀ n, ‖β s g u v n‖ ≤ L₂) →
      (∑ s ∈ Finset.Icc 1 S, ∑ g ∈ Finset.Icc 1 (2 * R),
        (s : ℝ) * admissibleResidualProfileMass a M R s g (α s g) (β s g) T H t₀ ψ) ≤
        K * (T * L) * (L₁ * L₂) *
          (((R : ℝ) * (S : ℝ)) ^ ε * nonzeroSGScale M R S +
            H * (1 + 2 * (S : ℝ) * (R : ℝ)) ^ ε *
              (1 + (M : ℝ) * (2 * (R : ℝ)) ^ 3) ^ ε * zeroSGScale M R S) := by
  obtain ⟨Kn, hKn, hn⟩ := hlocal.exists_residual_nonzero_total_estimate hC hε
  obtain ⟨Kz, hKz, hz⟩ := exists_residual_zero_total_estimate hε
  refine ⟨Kn + Kz, add_pos hKn hKz, ?_⟩
  intro a M R S hM hR L₁ L₂ T L H t₀ hL₁ hL₂ hT hL hH ψ hψ hsupp hbound α β hα hβ
  have hn' := hn a 1 1 M R S (2 * R) hM hR L₁ L₂ T L H t₀ hL₁ hL₂ hT hL hH
    ψ hψ hsupp hbound α β hα hβ
  have hz' := hz a M R S hR L₁ L₂ T L H t₀ hL₁ hL₂ hT hL hH
    ψ (hψ.of_le (by simp)) hsupp hbound α β hα hβ
  let F : ℝ := (T * L) * (L₁ * L₂)
  let A : ℝ := ((R : ℝ) * (S : ℝ)) ^ ε * nonzeroSGScale M R S
  let B : ℝ := H * (1 + 2 * (S : ℝ) * (R : ℝ)) ^ ε *
    (1 + (M : ℝ) * (2 * (R : ℝ)) ^ 3) ^ ε * zeroSGScale M R S
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hA : 0 ≤ A := by dsimp only [A, nonzeroSGScale]; positivity
  have hB : 0 ≤ B := by dsimp only [B, zeroSGScale]; positivity
  calc
    _ ≤ (∑ s ∈ Finset.Icc 1 S, ∑ g ∈ Finset.Icc 1 (2 * R),
        (s : ℝ) * admissibleResidualNonzeroMass a 1 1 M R s g (α s g) (β s g) T H t₀ ψ) +
        (∑ s ∈ Finset.Icc 1 S, ∑ g ∈ Finset.Icc 1 (2 * R),
        (s : ℝ) * admissibleResidualZeroMass a M R s g (α s g) (β s g) H t₀ ψ) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro s _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro g _
      simpa only [mul_add] using mul_le_mul_of_nonneg_left
        (admissibleResidualProfileMass_le_split a M R s g (α s g) (β s g) T H t₀ ψ)
        (Nat.cast_nonneg s)
    _ ≤ _ := by
      apply (add_le_add hn' hz').trans
      change _ ≤ (Kn + Kz) * (T * L) * (L₁ * L₂) * (A + B)
      calc
        _ = Kn * F * A + Kz * F * B := by dsimp only [F, A, B]; ring
        _ ≤ (Kn + Kz) * F * (A + B) := by
          nlinarith [mul_nonneg hKn.le (mul_nonneg hF hB),
            mul_nonneg hKz.le (mul_nonneg hF hA)]
        _ = _ := by dsimp only [F]; ring

#print axioms residualProfileFullMass_le_split
#print axioms LocalFourierHypothesis.exists_residual_profile_total_estimate

end

end PrimeGap182.TypeIII
