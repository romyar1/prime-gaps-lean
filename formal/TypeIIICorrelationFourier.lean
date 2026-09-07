import TypeIIIBaselineBridge

/-!
# Exact Fourier algebra for the unpulled Type III correlation

These identities concern the actual finite sums.  No finite-field estimate is
assumed.  In particular, this module does not prove `LocalFourierHypothesis`:
the manuscript's four-cycle uses a nonlinear torus pullback of the correlation.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open scoped BigOperators

variable (p : ℕ) [Fact p.Prime]

private theorem two_pole_sum (a b : ZMod p) (ha : a ≠ 0) :
    (∑ ξ : ZMod p, if ξ ≠ 0 ∧ ξ ≠ -1 then
      ZMod.stdAddChar (a / ξ - b / (ξ + 1)) else 0) =
      ZMod.stdAddChar (-a - b) *
        PrimeGap186.unnormalizedKloosterman2 p (a * b) - 1 := by
  classical
  let e : ZMod p ≃ ZMod p :=
    (Equiv.inv (ZMod p)).trans ((Equiv.addRight 1).trans (Equiv.mulLeft₀ a ha))
  have he (ξ : ZMod p) : e ξ = a * (ξ⁻¹ + 1) := rfl
  have he0 : e 0 = a := by simp [he]
  have he1 : e (-1) = 0 := by simp [he]
  have hφ : ZMod.stdAddChar (a + a * b / a - a - b) = (1 : ℂ) := by
    have hh : a + a * b / a - a - b = 0 := by field_simp; ring
    rw [hh, AddChar.map_zero_eq_one]
  have hs :
      (∑ ξ : ZMod p, if ξ ≠ 0 ∧ ξ ≠ -1 then
        ZMod.stdAddChar (a / ξ - b / (ξ + 1)) else 0) =
      ∑ y : ZMod p, if y ≠ 0 ∧ y ≠ a then
        ZMod.stdAddChar (y + a * b / y - a - b) else 0 := by
    refine Fintype.sum_equiv e _ _ ?_
    intro ξ
    have h0 : e ξ = 0 ↔ ξ = -1 := by
      rw [← he1, e.injective.eq_iff]
    have h1 : e ξ = a ↔ ξ = 0 := by
      rw [← he0, e.injective.eq_iff]
    by_cases hξ : ξ = 0
    · subst ξ
      simp [he0]
    by_cases hξ1 : ξ = -1
    · subst ξ
      simp [he1]
    rw [ite_eq_left ⟨hξ, hξ1⟩, ite_eq_left ⟨fun h => hξ1 (h0.mp h), fun h => hξ (h1.mp h)⟩]
    congr 1
    rw [he]
    have hx1 : ξ + 1 ≠ 0 := by
      intro hx
      apply hξ1
      linear_combination hx
    rw [show ξ⁻¹ + 1 = (ξ + 1) / ξ by field_simp; ring]
    field_simp [ha, hξ, hx1]
    ring
  rw [hs]
  have hi (y : ZMod p) :
      (if y ≠ 0 ∧ y ≠ a then
        ZMod.stdAddChar (y + a * b / y - a - b) else 0) =
      (if y ≠ 0 then ZMod.stdAddChar (y + a * b / y - a - b) else 0) -
        (if y = a then (1 : ℂ) else 0) := by
    by_cases hy : y = a
    · subst y
      rw [ite_eq_right (by simp), ite_eq_left ha, hφ, ite_eq_left rfl, sub_self]
    by_cases hy0 : y = 0
    · subst y
      simp only [ne_eq, not_true_eq_false, false_and, ite_false, sub_zero,
        ite_eq_right (Ne.symm ha)]
    · rw [ite_eq_left ⟨hy0, hy⟩, ite_eq_left hy0, ite_eq_right hy, sub_zero]
  simp_rw [hi]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← PrimeGap186.sum_units_eq_sum_ite]
  congr 1
  unfold PrimeGap186.unnormalizedKloosterman2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- Exact nonzero additive twist of a pair of ordinary Kloosterman sums. -/
theorem kl2_unit_pair_twist_one (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∑ x : (ZMod p)ˣ,
      PrimeGap186.unnormalizedKloosterman2 p (a * (x : ZMod p)) *
        PrimeGap186.unnormalizedKloosterman2 p (b * (x : ZMod p)) *
          ZMod.stdAddChar (x : ZMod p)) =
      (p : ℂ) * ZMod.stdAddChar (-a - b) *
        PrimeGap186.unnormalizedKloosterman2 p (a * b) - p - 1 := by
  classical
  have hp : (p : ℂ) ≠ 0 := NeZero.ne _
  have h := PrimeGap186.dft_pairing_twist p
    (fun x => PrimeGap186.unnormalizedKloosterman2 p (a * x))
    (fun x => PrimeGap186.unnormalizedKloosterman2 p (b * x)) 1
  simp only [one_mul, PrimeGap186.unnormalizedKloosterman2_star] at h
  simp_rw [PrimeGap186.unnormalizedKloosterman2_scaled_dft p a _ ha,
    PrimeGap186.unnormalizedKloosterman2_scaled_dft p b _ hb] at h
  have hs :
      (∑ ξ : ZMod p,
        (if ξ = 0 then 0 else (p : ℂ) * ZMod.stdAddChar (a / ξ)) *
          star (if ξ + 1 = 0 then 0 else (p : ℂ) * ZMod.stdAddChar (b / (ξ + 1)))) =
      (p : ℂ) ^ 2 *
        ∑ ξ : ZMod p, if ξ ≠ 0 ∧ ξ ≠ -1 then
          ZMod.stdAddChar (a / ξ - b / (ξ + 1)) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ξ _
    by_cases hξ : ξ = 0
    · simp [hξ]
    by_cases hξ1 : ξ = -1
    · simp [hξ1]
    have hx1 : ξ + 1 ≠ 0 := by
      intro hx
      apply hξ1
      linear_combination hx
    rw [ite_eq_right hξ, ite_eq_right hx1, ite_eq_left ⟨hξ, hξ1⟩]
    simp only [star_mul, star_natCast, PrimeGap186.star_stdAddChar]
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  rw [hs, two_pole_sum p a b ha] at h
  rw [PrimeGap186.sum_units_eq_sum_sub_zero p (fun x : ZMod p =>
    PrimeGap186.unnormalizedKloosterman2 p (a * x) *
      PrimeGap186.unnormalizedKloosterman2 p (b * x) * ZMod.stdAddChar x)]
  simp only [mul_zero, PrimeGap186.unnormalizedKloosterman2_zero,
    AddChar.map_zero_eq_one, neg_mul_neg, mul_one]
  rw [h]
  field_simp

private theorem kl3_scaled_positive_fourier (c a : ZMod p) (hc : c ≠ 0) :
    (∑ x : ZMod p, kl3 p (c * x) * ZMod.stdAddChar (a * x)) =
      if a = 0 then 0 else PrimeGap186.unnormalizedKloosterman2 p (-c / a) := by
  classical
  calc
    _ = ZMod.dft (fun x => PrimeGap186.normalizedKloosterman3 p (c * x)) (-a) := by
      simp only [ZMod.dft_apply, smul_eq_mul, kl3_eq_baseline]
      apply Finset.sum_congr rfl
      intro x _
      rw [mul_comm]
      congr 2
      ring
    _ = _ := by
      rw [PrimeGap186.normalizedKloosterman3_scaled_dft p c (-a) hc]
      simp only [neg_eq_zero, div_neg, neg_div]

private theorem kl3_star_scaled_positive_fourier (c b : ZMod p) (hc : c ≠ 0) :
    (∑ x : ZMod p, star (kl3 p (c * x)) * ZMod.stdAddChar (b * x)) =
      if b = 0 then 0 else PrimeGap186.unnormalizedKloosterman2 p (c / b) := by
  classical
  calc
    _ = star (∑ x : ZMod p, kl3 p (c * x) * ZMod.stdAddChar ((-b) * x)) := by
      simp only [star_sum, star_mul, PrimeGap186.star_stdAddChar]
      apply Finset.sum_congr rfl
      intro x _
      rw [mul_comm]
      congr 2
      ring
    _ = _ := by
      rw [kl3_scaled_positive_fourier p c (-b) hc]
      by_cases hb : b = 0
      · simp [hb]
      · rw [ite_eq_right (neg_ne_zero.mpr hb), ite_eq_right hb, neg_div_neg_eq,
          PrimeGap186.unnormalizedKloosterman2_star]

/-- The exact positive Fourier transform of the actual correlation, before
the manuscript's nonlinear torus substitution. -/
theorem correlation_two_variable_fourier (a b : ZMod p) :
    fourier₂ p (fun A B => correlation p A B 1) a b =
      if a = 0 ∨ b = 0 then 0 else
        (p : ℂ) * ZMod.stdAddChar ((1 : ZMod p) / a - 1 / b) *
          PrimeGap186.unnormalizedKloosterman2 p (-1 / (a * b)) - p - 1 := by
  classical
  have he : fourier₂ p (fun A B => correlation p A B 1) a b =
      ∑ h : (ZMod p)ˣ, ZMod.stdAddChar (h : ZMod p) *
        (∑ A : ZMod p, kl3 p ((h : ZMod p) * A) * ZMod.stdAddChar (a * A)) *
        (∑ B : ZMod p, star (kl3 p ((h : ZMod p) * B)) * ZMod.stdAddChar (b * B)) := by
    simp only [fourier₂, correlation, one_mul, Finset.sum_mul]
    rw [Finset.sum_comm_cycle]
    apply Finset.sum_congr rfl
    intro h _
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro B _
    rw [AddChar.map_add_eq_mul, mul_comm A (h : ZMod p), mul_comm B (h : ZMod p)]
    ring
  rw [he]
  simp_rw [kl3_scaled_positive_fourier p _ _ (Units.ne_zero _),
    kl3_star_scaled_positive_fourier p _ _ (Units.ne_zero _)]
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [ite_eq_right (not_or.mpr ⟨ha, hb⟩)]
  simp only [ite_eq_right ha, ite_eq_right hb]
  calc
    _ = ∑ h : (ZMod p)ˣ,
        PrimeGap186.unnormalizedKloosterman2 p ((-a⁻¹) * (h : ZMod p)) *
          PrimeGap186.unnormalizedKloosterman2 p (b⁻¹ * (h : ZMod p)) *
            ZMod.stdAddChar (h : ZMod p) := by
      apply Finset.sum_congr rfl
      intro h _
      have h₁ : -(h : ZMod p) / a = (-a⁻¹) * (h : ZMod p) := by ring
      have h₂ : (h : ZMod p) / b = b⁻¹ * (h : ZMod p) := by ring
      rw [h₁, h₂]
      ring
    _ = _ := by
      rw [kl2_unit_pair_twist_one p (-a⁻¹) b⁻¹
        (neg_ne_zero.mpr (inv_ne_zero ha)) (inv_ne_zero hb)]
      simp only [neg_neg, one_div, neg_div, neg_mul, mul_inv_rev]
      rw [mul_comm b⁻¹ a⁻¹]

/-- The scalar toric phase which occurs after additive Fourier expansion of
the four pulled-back correlations.  This is an actual finite sum. -/
def toricPhaseFourier (A B h k : ZMod p) : ℂ :=
  ∑ x : (ZMod p)ˣ, ∑ y : (ZMod p)ˣ,
    ZMod.stdAddChar
      (A * (y : ZMod p) / (x : ZMod p) ^ 2 +
        B * (x : ZMod p) / (y : ZMod p) ^ 2 + h * (x : ZMod p) + k * (y : ZMod p))

private theorem reciprocal_linear_sum (u v : ZMod p) :
    (∑ t : (ZMod p)ˣ, ZMod.stdAddChar (u / (t : ZMod p) + v * (t : ZMod p))) =
      if v = 0 then (if u = 0 then (p : ℂ) - 1 else -1)
      else PrimeGap186.unnormalizedKloosterman2 p (u * v) := by
  classical
  by_cases hv : v = 0
  · subst v
    simp only [zero_mul, add_zero, ite_true]
    exact PrimeGap186.stdAddChar_sum_units_div p u
  rw [ite_eq_right hv]
  unfold PrimeGap186.unnormalizedKloosterman2
  refine Fintype.sum_equiv (Equiv.mulLeft (Units.mk0 v hv)) _ _ ?_
  intro t
  simp only [Equiv.coe_mulLeft, Units.val_mul, Units.val_mk0]
  congr 1
  field_simp
  ring

/-- Radial summation reduces the residual two-variable toric phase to a
Kloosterman sum composed with a Laurent polynomial having exponents ±1, ±2.
The degenerate radial coefficients are retained exactly. -/
theorem toricPhaseFourier_radial (A B h k : ZMod p) :
    toricPhaseFourier p A B h k =
      ∑ z : (ZMod p)ˣ,
        if h + k * (z : ZMod p) = 0 then
          (if A * (z : ZMod p) + B / (z : ZMod p) ^ 2 = 0 then (p : ℂ) - 1 else -1)
        else PrimeGap186.unnormalizedKloosterman2 p
          (A * k * (z : ZMod p) ^ 2 + A * h * (z : ZMod p) +
            B * k / (z : ZMod p) + B * h / (z : ZMod p) ^ 2) := by
  classical
  have he : toricPhaseFourier p A B h k =
      ∑ t : (ZMod p)ˣ, ∑ z : (ZMod p)ˣ,
        ZMod.stdAddChar
          ((A * (z : ZMod p) + B / (z : ZMod p) ^ 2) / (t : ZMod p) +
            (h + k * (z : ZMod p)) * (t : ZMod p)) := by
    unfold toricPhaseFourier
    apply Finset.sum_congr rfl
    intro t _
    symm
    refine Fintype.sum_equiv (Equiv.mulLeft t) _ _ ?_
    intro z
    simp only [Equiv.coe_mulLeft, Units.val_mul]
    congr 1
    field_simp
    ring
  rw [he, Finset.sum_comm]
  simp_rw [reciprocal_linear_sum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : h + k * (z : ZMod p) = 0
  · rw [ite_eq_left hz, ite_eq_left hz]
  rw [ite_eq_right hz, ite_eq_right hz]
  congr 1
  field_simp
  ring

#print axioms kl2_unit_pair_twist_one
#print axioms correlation_two_variable_fourier
#print axioms toricPhaseFourier_radial

end PrimeGap182.TypeIII
