import TypeIIIPositiveRows
import TypeIIIZeroWeights
import TypeIIIZeroFrequency

/-! The actual zero Fourier coefficient is bounded by its fully summed cubic gcd weight. -/

open scoped BigOperators Classical ContDiff

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem sharedOriginal_zero_weight_le (s g u v M : ℕ)
    [NeZero s] [NeZero g] [NeZero u] [NeZero v]
    (hu : Squarefree u) (hv : Squarefree v) (hw : Squarefree (s * g))
    (huv : u.Coprime v) (huw : u.Coprime (s * g)) (hvw : v.Coprime (s * g))
    (a : ℤ) (ha : IsUnit (a : ZMod (u * (v * (s * g)))))
    (α β : IntegerIntervalIndex 1 M → ℂ) (L₁ L₂ T L H t₀ : ℝ)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hT : 0 ≤ T) (hL : 0 ≤ L) (hH : 0 < H)
    (hα : ∀ m, ‖α m‖ ≤ L₁) (hβ : ∀ n, ‖β n‖ ≤ L₂)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ 2 ψ)
    (hsupport : Function.support ψ ⊆ Set.Icc (-T) T)
    (hbound : ∀ t : ℝ, ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L) :
    (s : ℝ) * ‖normalizedProfileFourier (u * (v * (s * g))) ψ H t₀ 0 *
      sharedOriginalCoefficientSum u v (s * g) a 0 1 1 M M α β‖ ≤
      ((8 * T) * L) * H * (2 : ℝ) ^ (s * g).primeFactors.card * (L₁ * L₂) *
        cubicGcdPairMass M u v s g := by
  let F : ℝ := ((8 * T) * L) * H * (2 : ℝ) ^ (s * g).primeFactors.card * (L₁ * L₂)
  let W (m n : ℕ) : ℝ :=
    ((g : ℝ)⁻¹ * ((u : ℝ)⁻¹ ^ 2) * ((v : ℝ)⁻¹ ^ 2)) *
      (Int.gcd (cubicDifference u v m n) ((s * g : ℕ) : ℤ) : ℝ)
  let ft : ℂ := normalizedProfileFourier (u * (v * (s * g))) ψ H t₀ 0
  let k (m n : IntegerIntervalIndex 1 M) : ℂ :=
    if IsUnit (m.1 : ZMod (u * (s * g))) ∧ IsUnit (n.1 : ZMod (v * (s * g))) then
      α m * sharedInverseFourier u v (s * g) a m.1 n.1 0 * star (β n)
    else 0
  have hpoint (m n : IntegerIntervalIndex 1 M) :
      (s : ℝ) * ‖ft * k m n‖ ≤ F * W m.1.toNat n.1.toNat := by
    by_cases hmn : IsUnit (m.1 : ZMod (u * (s * g))) ∧ IsUnit (n.1 : ZMod (v * (s * g)))
    · dsimp only [k]
      rw [ite_eq_left hmn]
      have hz := zeroFrequency_central_weight s g u v hu hv hw huv huw hvw a m.1 n.1 ha
        hmn.1 hmn.2 T L H t₀ hT hL hH ψ hψ hsupport hbound
      have hcoeff : ‖α m‖ * ‖β n‖ ≤ L₁ * L₂ :=
        mul_le_mul (hα m) (hβ n) (norm_nonneg _) hL₁
      calc
        _ = (‖α m‖ * ‖β n‖) *
            ((s : ℝ) * ‖ft * sharedInverseFourier u v (s * g) a m.1 n.1 0‖) := by
          simp only [norm_mul, norm_star]
          ring
        _ ≤ (L₁ * L₂) * (((8 * T) * L) * (H / (g : ℝ)) *
            (2 : ℝ) ^ (s * g).primeFactors.card *
              (Int.gcd (m.1 * (u : ℤ) ^ 3 - n.1 * (v : ℤ) ^ 3)
                ((s * g : ℕ) : ℤ) : ℝ) / ((u : ℝ) ^ 2 * (v : ℝ) ^ 2)) :=
          mul_le_mul hcoeff hz (by positivity) (mul_nonneg hL₁ hL₂)
        _ = _ := by
          dsimp only [F, W, cubicDifference]
          rw [positiveIntegerInterval_cast_toNat M m, positiveIntegerInterval_cast_toNat M n]
          simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
          ring
    · dsimp only [k]
      rw [ite_eq_right hmn, mul_zero, norm_zero, mul_zero]
      dsimp only [F, W]
      positivity
  calc
    _ = (s : ℝ) * ‖∑ m : IntegerIntervalIndex 1 M, ∑ n : IntegerIntervalIndex 1 M,
        ft * k m n‖ := by
      simp only [sharedOriginalCoefficientSum, ft, k, Finset.mul_sum]
    _ ≤ (s : ℝ) * (∑ m : IntegerIntervalIndex 1 M, ∑ n : IntegerIntervalIndex 1 M,
        ‖ft * k m n‖) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m _ => norm_sum_le _ _))
    _ = ∑ m : IntegerIntervalIndex 1 M, ∑ n : IntegerIntervalIndex 1 M,
        (s : ℝ) * ‖ft * k m n‖ := by simp only [Finset.mul_sum]
    _ ≤ ∑ m : IntegerIntervalIndex 1 M, ∑ n : IntegerIntervalIndex 1 M,
        F * W m.1.toNat n.1.toNat :=
      Finset.sum_le_sum (fun m _ => Finset.sum_le_sum (fun n _ => hpoint m n))
    _ = F * cubicGcdPairMass M u v s g := by
      calc
        _ = ∑ m : IntegerIntervalIndex 1 M, ∑ n ∈ Finset.Icc 1 M,
            F * W m.1.toNat n := by
          apply Finset.sum_congr rfl
          intro m _
          exact sum_positiveIntegerInterval_toNat M (fun n => F * W m.1.toNat n)
        _ = ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M, F * W m n :=
          sum_positiveIntegerInterval_toNat M (fun m => ∑ n ∈ Finset.Icc 1 M, F * W m n)
        _ = _ := by simp only [cubicGcdPairMass, W, Finset.mul_sum]

#print axioms sharedOriginal_zero_weight_le

end

end PrimeGap182.TypeIII
