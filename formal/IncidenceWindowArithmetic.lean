import IncidenceSquarefreeCompletion

/-!
# Uniform constants in the incidence smooth-window estimate

Only elementary subpower divisor estimates from the baseline are used here.
The scale bound is uniform also when either positive window width is below one.
-/

noncomputable section

namespace PrimeGap182Audit

open scoped BigOperators

def incidenceWindowScale (η : ℝ) (q : ℕ) (E₁ E₂ : ℝ) : ℝ :=
  E₁ * E₂ + (q : ℝ) ^ ((3 : ℝ) / 2 + η) +
    (q : ℝ) ^ ((1 : ℝ) / 2 + η) * (E₁ + E₂)

theorem incidence_prime_divisor_subpower (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, q ≠ 0 →
      (8 : ℝ) ^ q.primeFactors.card * (q.divisors.card : ℝ) ≤ C * (q : ℝ) ^ η := by
  obtain ⟨C, hC, hc⟩ := PrimeGap186.exists_primeFactors_power_bound
    (by norm_num : (1 : ℝ) ≤ 8) (show 0 < η / 2 by positivity)
  obtain ⟨D, hD, hd⟩ := PrimeGap186.exists_card_divisors_bound
    (show 0 < η / 2 by positivity)
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro q hq
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  calc
    _ ≤ (C * (q : ℝ) ^ (η / 2)) * (D * (q : ℝ) ^ (η / 2)) :=
      mul_le_mul (hc q hq) (hd q hq) (Nat.cast_nonneg _) (by positivity)
    _ = (C * D) * (q : ℝ) ^ (η / 2 + η / 2) := by
      rw [Real.rpow_add hq0]
      ring
    _ = _ := by congr 2; ring

theorem incidence_rpow_half (q η : ℝ) (hq : 0 < q) :
    q ^ η * Real.sqrt q = q ^ ((1 : ℝ) / 2 + η) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hq]
  congr 1
  ring

theorem incidence_rpow_three_half (q η : ℝ) (hq : 0 < q) :
    q ^ η * q * Real.sqrt q = q ^ ((3 : ℝ) / 2 + η) := by
  calc
    _ = q ^ η * q ^ (1 : ℝ) * q ^ ((1 : ℝ) / 2) := by
      rw [Real.rpow_one, Real.sqrt_eq_rpow]
    _ = _ := by
      rw [← Real.rpow_add hq, ← Real.rpow_add hq]
      congr 1
      ring

theorem incidenceWindowScale_nonneg (η : ℝ) (q : ℕ) (E₁ E₂ : ℝ)
    (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) : 0 ≤ incidenceWindowScale η q E₁ E₂ := by
  unfold incidenceWindowScale
  positivity

theorem incidenceWindowScale_mass (η : ℝ) (hη : 0 < η) (q : ℕ) (hq : q ≠ 0)
    (E₁ E₂ : ℝ) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) :
    (2 + 4 * E₁) * (2 + 4 * E₂) ≤ 16 * incidenceWindowScale η q E₁ E₂ := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
  have hbig : 1 ≤ (q : ℝ) ^ ((3 : ℝ) / 2 + η) :=
    Real.one_le_rpow hq1 (by positivity)
  have hsmall : 1 ≤ (q : ℝ) ^ ((1 : ℝ) / 2 + η) :=
    Real.one_le_rpow hq1 (by positivity)
  have hlinear := mul_le_mul_of_nonneg_right hsmall (add_nonneg hE₁ hE₂)
  unfold incidenceWindowScale
  nlinarith

set_option maxHeartbeats 600000 in
theorem incidenceWindowScale_error (η : ℝ) (q : ℕ) (hq : q ≠ 0)
    (C K₁ K₂ E₁ E₂ : ℝ) (hC : 0 ≤ C) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hE₁ : 0 < E₁) (hE₂ : 0 < E₂)
    (hsub : (8 : ℝ) ^ q.primeFactors.card * (q.divisors.card : ℝ) ≤ C * (q : ℝ) ^ η) :
    ((q : ℝ) ^ 2)⁻¹ * ((8 : ℝ) ^ q.primeFactors.card * (q : ℝ) * Real.sqrt (q : ℝ)) *
      ((K₁ * E₁) * (K₂ * E₂)) * (q.divisors.card : ℝ) *
      (8 / ((E₁ / q) * (E₂ / q)) + 4 / (E₂ / q) + 2 / (E₁ / q)) ≤
        (8 * K₁ * K₂ * C) * incidenceWindowScale η q E₁ E₂ := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  let B : ℝ := (8 : ℝ) ^ q.primeFactors.card * (q.divisors.card : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have heq : ((q : ℝ) ^ 2)⁻¹ *
      ((8 : ℝ) ^ q.primeFactors.card * (q : ℝ) * Real.sqrt (q : ℝ)) *
      ((K₁ * E₁) * (K₂ * E₂)) * (q.divisors.card : ℝ) *
      (8 / ((E₁ / q) * (E₂ / q)) + 4 / (E₂ / q) + 2 / (E₁ / q)) =
      (K₁ * K₂) * B * (8 * (q : ℝ) * Real.sqrt (q : ℝ) +
        4 * E₁ * Real.sqrt (q : ℝ) + 2 * E₂ * Real.sqrt (q : ℝ)) := by
    dsimp [B]
    field_simp [hq0.ne', hE₁.ne', hE₂.ne']
  rw [heq]
  calc
    _ ≤ (K₁ * K₂) * B * (8 * ((q : ℝ) * Real.sqrt (q : ℝ) +
        Real.sqrt (q : ℝ) * (E₁ + E₂))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg hK₁ hK₂) hB)
      nlinarith [Real.sqrt_nonneg (q : ℝ)]
    _ = (8 * K₁ * K₂) * B * ((q : ℝ) * Real.sqrt (q : ℝ) +
        Real.sqrt (q : ℝ) * (E₁ + E₂)) := by ring
    _ ≤ (8 * K₁ * K₂) * (C * (q : ℝ) ^ η) * ((q : ℝ) * Real.sqrt (q : ℝ) +
        Real.sqrt (q : ℝ) * (E₁ + E₂)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hsub (by positivity)
    _ = (8 * K₁ * K₂ * C) * ((q : ℝ) ^ ((3 : ℝ) / 2 + η) +
        (q : ℝ) ^ ((1 : ℝ) / 2 + η) * (E₁ + E₂)) := by
      rw [← incidence_rpow_three_half _ _ hq0, ← incidence_rpow_half _ _ hq0]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      unfold incidenceWindowScale
      linarith [mul_nonneg hE₁.le hE₂.le]

#print axioms incidence_prime_divisor_subpower
#print axioms incidenceWindowScale_mass
#print axioms incidenceWindowScale_error

end PrimeGap182Audit
