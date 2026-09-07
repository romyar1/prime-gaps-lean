import TypeIIIResidualZero
import TypeIIIZeroLoss

/-! The actual zero-frequency correlations summed over every supported shared factor and gcd. -/

open scoped BigOperators Classical ContDiff

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

def zeroSGScale (M R S : ℝ) : ℝ := M * S ^ 2 * R + M ^ 2 * S * R

theorem residual_zero_total_prime_bound (a : ℤ) (M R S : ℕ) (hR : 0 < R)
    (L₁ L₂ T L H t₀ J : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hH : 0 < H) (hJ : 0 ≤ J)
    (hprime : ∀ s ∈ Finset.Icc 1 S, ∀ g ∈ Finset.Icc 1 (2 * R),
      (2 : ℝ) ^ (s * g).primeFactors.card ≤ J)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ 2 ψ)
    (hsupport : Function.support ψ ⊆ Set.Icc (-T) T)
    (hbound : ∀ t : ℝ, ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L)
    (α β : ℕ → ℕ → ℕ → ℕ → IntegerIntervalIndex 1 M → ℂ)
    (hα : ∀ s ∈ Finset.Icc 1 S, ∀ g ∈ Finset.Icc 1 (2 * R),
      ∀ u ∈ residualRange R g, ∀ v ∈ residualRange R g, ∀ m, ‖α s g u v m‖ ≤ L₁)
    (hβ : ∀ s ∈ Finset.Icc 1 S, ∀ g ∈ Finset.Icc 1 (2 * R),
      ∀ u ∈ residualRange R g, ∀ v ∈ residualRange R g, ∀ n, ‖β s g u v n‖ ≤ L₂) :
    (∑ s ∈ Finset.Icc 1 S, ∑ g ∈ Finset.Icc 1 (2 * R),
      (s : ℝ) * admissibleResidualZeroMass a M R s g (α s g) (β s g) H t₀ ψ) ≤
      ((8 * T) * L) * H * (L₁ * L₂) * J *
        (256 * (M : ℝ) * (S : ℝ) ^ 2 * (R : ℝ) +
          32 * (S : ℝ) * (cubicDivisorBound M R : ℝ) * (M : ℝ) ^ 2 * (R : ℝ)) := by
  let F : ℝ := ((8 * T) * L) * H * (L₁ * L₂) * J
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hpoint (s : ℕ) (hs : s ∈ Finset.Icc 1 S) (g : ℕ) (hg : g ∈ Finset.Icc 1 (2 * R)) :
      (s : ℝ) * admissibleResidualZeroMass a M R s g (α s g) (β s g) H t₀ ψ ≤
        F * cubicGcdMass M R s g := by
    apply (admissibleResidualZeroMass_weight_le s g M R
      (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hg).1 hR a
      (α s g) (β s g) L₁ L₂ T L H t₀ hL₁ hL₂ hT hL hH
      (hα s hs g hg) (hβ s hs g hg) ψ hψ hsupport hbound).trans
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hprime s hs g hg)
        (show 0 ≤ ((8 * T) * L) * H * (L₁ * L₂) by positivity))
      (cubicGcdMass_nonneg M R s g)
    dsimp only [F]
    convert! hh using 1
    ring
  calc
    _ ≤ ∑ s ∈ Finset.Icc 1 S, ∑ g ∈ Finset.Icc 1 (2 * R),
        F * cubicGcdMass M R s g :=
      Finset.sum_le_sum (fun s hs => Finset.sum_le_sum (fun g hg => hpoint s hs g hg))
    _ = F * (∑ s ∈ Finset.Icc 1 S, ∑ g ∈ Finset.Icc 1 (2 * R),
        cubicGcdMass M R s g) := by simp only [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (cubicGcdMass_total_le M R S hR) hF

theorem zero_weight_scale_subpower (M R S : ℕ) {ε K : ℝ} (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hτ : (cubicDivisorBound M R : ℝ) ≤ K * (1 + (M : ℝ) * (2 * (R : ℝ)) ^ 3) ^ ε) :
    256 * (M : ℝ) * (S : ℝ) ^ 2 * (R : ℝ) +
        32 * (S : ℝ) * (cubicDivisorBound M R : ℝ) * (M : ℝ) ^ 2 * (R : ℝ) ≤
      256 * (1 + K) * (1 + (M : ℝ) * (2 * (R : ℝ)) ^ 3) ^ ε * zeroSGScale M R S := by
  let V : ℝ := (1 + (M : ℝ) * (2 * (R : ℝ)) ^ 3) ^ ε
  let A : ℝ := (M : ℝ) * (S : ℝ) ^ 2 * (R : ℝ)
  let B : ℝ := (M : ℝ) ^ 2 * (S : ℝ) * (R : ℝ)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hV : 1 ≤ V := Real.one_le_rpow (le_add_of_nonneg_right (by positivity)) hε
  have hV₀ : 0 ≤ V := le_trans (by norm_num) hV
  have hcap : 1 ≤ (1 + K) * V :=
    (mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 1 + K by linarith) hV₀).trans'
      (by simpa only [one_mul] using hV)
  have hτcap : (cubicDivisorBound M R : ℝ) ≤ (1 + K) * V :=
    hτ.trans (mul_le_mul_of_nonneg_right (by linarith) hV₀)
  have hc₁ : A ≤ (1 + K) * V * A := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcap hA
  have hc₂ : 32 * (cubicDivisorBound M R : ℝ) ≤ 256 * ((1 + K) * V) := by
    have hh := mul_le_mul_of_nonneg_left hτcap (by norm_num : (0 : ℝ) ≤ 32)
    have hp : 0 ≤ (1 + K) * V := le_trans (by norm_num) hcap
    linarith
  calc
    _ = 256 * A + (32 * (cubicDivisorBound M R : ℝ)) * B := by dsimp only [A, B]; ring
    _ ≤ 256 * ((1 + K) * V * A) + (256 * ((1 + K) * V)) * B :=
      add_le_add (mul_le_mul_of_nonneg_left hc₁ (by norm_num))
        (mul_le_mul_of_nonneg_right hc₂ hB)
    _ = _ := by dsimp only [A, B, V, zeroSGScale]; ring

/-- Both actual zero-frequency terms have the required polynomially bounded subpower
losses. No finite-field cancellation hypothesis is used in this branch. -/
theorem exists_residual_zero_total_estimate {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a : ℤ) (M R S : ℕ), 0 < R →
      ∀ (L₁ L₂ T L H t₀ : ℝ), 0 ≤ L₁ → 0 ≤ L₂ → 0 ≤ T → 0 ≤ L → 0 < H →
      ∀ (ψ : ℝ → ℂ), ContDiff ℝ 2 ψ →
      Function.support ψ ⊆ Set.Icc (-T) T →
      (∀ t : ℝ, ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L) →
      ∀ (α β : ℕ → ℕ → ℕ → ℕ → IntegerIntervalIndex 1 M → ℂ),
      (∀ s ∈ Finset.Icc 1 S, ∀ g ∈ Finset.Icc 1 (2 * R),
        ∀ u ∈ residualRange R g, ∀ v ∈ residualRange R g, ∀ m, ‖α s g u v m‖ ≤ L₁) →
      (∀ s ∈ Finset.Icc 1 S, ∀ g ∈ Finset.Icc 1 (2 * R),
        ∀ u ∈ residualRange R g, ∀ v ∈ residualRange R g, ∀ n, ‖β s g u v n‖ ≤ L₂) →
      (∑ s ∈ Finset.Icc 1 S, ∑ g ∈ Finset.Icc 1 (2 * R),
        (s : ℝ) * admissibleResidualZeroMass a M R s g (α s g) (β s g) H t₀ ψ) ≤
        K * (T * L) * H * (L₁ * L₂) * (1 + 2 * (S : ℝ) * (R : ℝ)) ^ ε *
          (1 + (M : ℝ) * (2 * (R : ℝ)) ^ 3) ^ ε * zeroSGScale M R S := by
  obtain ⟨Kp, hKp, hp⟩ := exists_zeroFrequency_prime_loss hε
  obtain ⟨Kd, hKd, hd⟩ := exists_cubicDivisorBound_subpower hε
  refine ⟨2048 * Kp * (1 + Kd), by positivity, ?_⟩
  intro a M R S hR L₁ L₂ T L H t₀ hL₁ hL₂ hT hL hH ψ hψ hsupp hbound α β hα hβ
  let P : ℝ := (1 + 2 * (S : ℝ) * (R : ℝ)) ^ ε
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hh := residual_zero_total_prime_bound a M R S hR L₁ L₂ T L H t₀ (Kp * P)
    hL₁ hL₂ hT hL hH (mul_nonneg hKp.le hP) (hp S R)
    ψ hψ hsupp hbound α β hα hβ
  apply hh.trans
  have hb := mul_le_mul_of_nonneg_left
    (zero_weight_scale_subpower M R S hε.le hKd.le (hd M R))
    (show 0 ≤ ((8 * T) * L) * H * (L₁ * L₂) * (Kp * P) by positivity)
  apply hb.trans_eq
  dsimp only [P]
  ring

#print axioms residual_zero_total_prime_bound
#print axioms zero_weight_scale_subpower
#print axioms exists_residual_zero_total_estimate

end

end PrimeGap182.TypeIII
