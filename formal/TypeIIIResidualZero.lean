import TypeIIIZeroCoefficients
import TypeIIIResidualInterval

/-! The actual zero-frequency residual block, on the same intervals as the nonzero part. -/

open scoped BigOperators Classical ContDiff

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem SharedOuterAdmissible.primitive_product {u v w : ℕ} {a : ℤ}
    (h : SharedOuterAdmissible w a u v) (haw : IsUnit (a : ZMod w)) :
    IsUnit (a : ZMod (u * (v * w))) := by
  apply (ZMod.coe_int_isUnit_iff_isCoprime a (u * (v * w))).mpr
  have hu := (ZMod.coe_int_isUnit_iff_isCoprime a u).mp h.left_primitive
  have hv := (ZMod.coe_int_isUnit_iff_isCoprime a v).mp h.right_primitive
  have hw := (ZMod.coe_int_isUnit_iff_isCoprime a w).mp haw
  simpa only [Nat.cast_mul] using hu.mul_left (hv.mul_left hw)

def residualProfileZeroMass (w : ℕ) [NeZero w] (a : ℤ) (M R g : ℕ)
    (α β : ℕ → ℕ → IntegerIntervalIndex 1 M → ℂ)
    (H t₀ : ℝ) (ψ : ℝ → ℂ) : ℝ :=
  let U := residualStart R g
  ∑ x ∈ Finset.range (residualLength R g), ∑ y ∈ Finset.range (residualLength R g),
    let u := positiveOuterIndex U x
    let v := positiveOuterIndex U y
    if SharedOuterAdmissible w a u v then
      ‖normalizedProfileFourier (u * (v * w)) ψ H t₀ 0 *
        sharedOriginalCoefficientSum u v w a 0 1 1 M M (α u v) (β u v)‖
    else 0

theorem residualProfileZeroMass_weight_le (s g M R : ℕ) [NeZero s] [NeZero g]
    (hR : 0 < R) (hw : Squarefree (s * g)) (a : ℤ) (ha : IsUnit (a : ZMod (s * g)))
    (α β : ℕ → ℕ → IntegerIntervalIndex 1 M → ℂ) (L₁ L₂ T L H t₀ : ℝ)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hT : 0 ≤ T) (hL : 0 ≤ L) (hH : 0 < H)
    (hα : ∀ u ∈ residualRange R g, ∀ v ∈ residualRange R g, ∀ m, ‖α u v m‖ ≤ L₁)
    (hβ : ∀ u ∈ residualRange R g, ∀ v ∈ residualRange R g, ∀ n, ‖β u v n‖ ≤ L₂)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ 2 ψ)
    (hsupport : Function.support ψ ⊆ Set.Icc (-T) T)
    (hbound : ∀ t : ℝ, ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L) :
    (s : ℝ) * residualProfileZeroMass (s * g) a M R g α β H t₀ ψ ≤
      ((8 * T) * L) * H * (2 : ℝ) ^ (s * g).primeFactors.card * (L₁ * L₂) *
        cubicGcdMass M R s g := by
  let F : ℝ := ((8 * T) * L) * H * (2 : ℝ) ^ (s * g).primeFactors.card * (L₁ * L₂)
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  let U := residualStart R g
  let N := residualLength R g
  have hg : 0 < g := NeZero.pos g
  have hpair (x : ℕ) (hx : x ∈ Finset.range N) (y : ℕ) (hy : y ∈ Finset.range N) :
      (s : ℝ) * (if SharedOuterAdmissible (s * g) a
          (positiveOuterIndex U x) (positiveOuterIndex U y) then
        ‖normalizedProfileFourier
            (positiveOuterIndex U x * (positiveOuterIndex U y * (s * g))) ψ H t₀ 0 *
          sharedOriginalCoefficientSum (positiveOuterIndex U x) (positiveOuterIndex U y)
            (s * g) a 0 1 1 M M
              (α (positiveOuterIndex U x) (positiveOuterIndex U y))
              (β (positiveOuterIndex U x) (positiveOuterIndex U y))‖ else 0) ≤
        F * (if (positiveOuterIndex U x : ℕ).Coprime (positiveOuterIndex U y) then
          cubicGcdPairMass M (positiveOuterIndex U x) (positiveOuterIndex U y) s g else 0) := by
    let u := positiveOuterIndex U x
    let v := positiveOuterIndex U y
    have hu : (u : ℕ) ∈ residualRange R g := residualStart_add_mem R g x hR hg hx
    have hv : (v : ℕ) ∈ residualRange R g := residualStart_add_mem R g y hR hg hy
    by_cases h : SharedOuterAdmissible (s * g) a u v
    · rw [ite_eq_left h, ite_eq_left h.coprime]
      exact sharedOriginal_zero_weight_le s g u v M
        h.left_squarefree h.right_squarefree hw h.coprime h.left_coprime h.right_coprime
        a (h.primitive_product ha) (α u v) (β u v) L₁ L₂ T L H t₀ hL₁ hL₂ hT hL hH
        (hα u hu v hv) (hβ u hu v hv) ψ hψ hsupport hbound
    · rw [ite_eq_right h, mul_zero]
      apply mul_nonneg hF
      split_ifs
      · unfold cubicGcdPairMass
        positivity
      · exact le_rfl
  have hsum : cubicGcdMass M R s g =
      ∑ x ∈ Finset.range N, ∑ y ∈ Finset.range N,
        if (positiveOuterIndex U x : ℕ).Coprime (positiveOuterIndex U y) then
          cubicGcdPairMass M (positiveOuterIndex U x) (positiveOuterIndex U y) s g else 0 := by
    unfold cubicGcdMass
    rw [sum_residualRange_eq_sum_range R g hR hg]
    apply Finset.sum_congr rfl
    intro x _
    rw [sum_residualRange_eq_sum_range R g hR hg]
    rfl
  rw [hsum]
  simp only [residualProfileZeroMass, Finset.mul_sum]
  exact Finset.sum_le_sum (fun x hx => Finset.sum_le_sum (fun y hy => hpair x hx y hy))

def admissibleResidualZeroMass (a : ℤ) (M R s g : ℕ)
    (α β : ℕ → ℕ → IntegerIntervalIndex 1 M → ℂ)
    (H t₀ : ℝ) (ψ : ℝ → ℂ) : ℝ :=
  if h : s * g ≠ 0 then
    letI : NeZero (s * g) := ⟨h⟩
    if Squarefree (s * g) ∧ IsUnit (a : ZMod (s * g)) then
      residualProfileZeroMass (s * g) a M R g α β H t₀ ψ
    else 0
  else 0

theorem admissibleResidualZeroMass_weight_le (s g M R : ℕ) (hs : 0 < s) (hg : 0 < g)
    (hR : 0 < R) (a : ℤ)
    (α β : ℕ → ℕ → IntegerIntervalIndex 1 M → ℂ) (L₁ L₂ T L H t₀ : ℝ)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hT : 0 ≤ T) (hL : 0 ≤ L) (hH : 0 < H)
    (hα : ∀ u ∈ residualRange R g, ∀ v ∈ residualRange R g, ∀ m, ‖α u v m‖ ≤ L₁)
    (hβ : ∀ u ∈ residualRange R g, ∀ v ∈ residualRange R g, ∀ n, ‖β u v n‖ ≤ L₂)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ 2 ψ)
    (hsupport : Function.support ψ ⊆ Set.Icc (-T) T)
    (hbound : ∀ t : ℝ, ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L) :
    (s : ℝ) * admissibleResidualZeroMass a M R s g α β H t₀ ψ ≤
      ((8 * T) * L) * H * (2 : ℝ) ^ (s * g).primeFactors.card * (L₁ * L₂) *
        cubicGcdMass M R s g := by
  let : NeZero s := ⟨hs.ne'⟩
  let : NeZero g := ⟨hg.ne'⟩
  unfold admissibleResidualZeroMass
  rw [dite_eq_left (mul_ne_zero hs.ne' hg.ne')]
  split_ifs with hgood
  · exact residualProfileZeroMass_weight_le s g M R hR hgood.1 a hgood.2
      α β L₁ L₂ T L H t₀ hL₁ hL₂ hT hL hH hα hβ ψ hψ hsupport hbound
  · rw [mul_zero]
    exact mul_nonneg (by positivity) (cubicGcdMass_nonneg M R s g)

#print axioms SharedOuterAdmissible.primitive_product
#print axioms residualProfileZeroMass_weight_le
#print axioms admissibleResidualZeroMass_weight_le

end

end PrimeGap182.TypeIII
