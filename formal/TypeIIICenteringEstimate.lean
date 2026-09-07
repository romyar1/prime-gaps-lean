import TypeIIICorrelationGram

/-!
# The acceptable error from subtracting row-pair means

The elementary estimate here bounds the difference between a rectangle
product and the product of its centered row pairs. It will be applied to
the actual correlation matrix and transported through the determinant-three
torus map. No estimate for the remaining centered four-cycle is asserted.
-/

noncomputable section

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

section FiniteArrays

variable {I J : Type*}

/-- The literal error from removing one constant from both row-pair factors. -/
def rowCenteringError (P : I → J → ℂ) (μ : I → ℂ) (e : J ≃ J)
    (i : I) (j : J) : ℂ :=
  P i j * star (P i (e j)) -
    (P i j - μ i) * star (P i (e j) - μ i)

theorem rowCenteringError_eq (P : I → J → ℂ) (μ : I → ℂ)
    (e : J ≃ J) (i : I) (j : J) :
    rowCenteringError P μ e i j =
      μ i * star (P i (e j)) + P i j * star (μ i) - μ i * star (μ i) := by
  simp only [rowCenteringError, star_sub]
  ring

theorem rowCenteringError_norm_le (P : I → J → ℂ) (μ : I → ℂ)
    (e : J ≃ J) (i : I) (j : J) :
    ‖rowCenteringError P μ e i j‖ ≤
      ‖μ i‖ * ‖P i j‖ + ‖μ i‖ * ‖P i (e j)‖ + ‖μ i‖ ^ 2 := by
  rw [rowCenteringError_eq]
  calc
    _ ≤ ‖μ i * star (P i (e j)) + P i j * star (μ i)‖ +
        ‖μ i * star (μ i)‖ := norm_sub_le _ _
    _ ≤ (‖μ i * star (P i (e j))‖ + ‖P i j * star (μ i)‖) +
        ‖μ i * star (μ i)‖ := add_le_add (norm_add_le _ _) le_rfl
    _ = _ := by simp only [norm_mul, norm_star]; ring

/-- An entire row costs at most three times its mass bound times its mean. -/
theorem rowCenteringError_row_mass_le [Fintype J] (P : I → J → ℂ) (μ : I → ℂ)
    (e : J ≃ J) (i : I) (B : ℝ)
    (hP : (∑ j : J, ‖P i j‖) ≤ B)
    (hμ : (Fintype.card J : ℝ) * ‖μ i‖ ≤ B) :
    (∑ j : J, ‖rowCenteringError P μ e i j‖) ≤ 3 * B * ‖μ i‖ := by
  have he : (∑ j : J, ‖P i (e j)‖) = ∑ j : J, ‖P i j‖ :=
    Equiv.sum_comp e (fun j => ‖P i j‖)
  calc
    _ ≤ ∑ j : J, (‖μ i‖ * ‖P i j‖ + ‖μ i‖ * ‖P i (e j)‖ + ‖μ i‖ ^ 2) :=
      Finset.sum_le_sum (fun j _ => rowCenteringError_norm_le P μ e i j)
    _ = ‖μ i‖ * (∑ j : J, ‖P i j‖) + ‖μ i‖ * (∑ j : J, ‖P i j‖) +
        (Fintype.card J : ℝ) * ‖μ i‖ ^ 2 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, he,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 3 * B * ‖μ i‖ := by
      have h₁ := mul_le_mul_of_nonneg_left hP (norm_nonneg (μ i))
      have h₂ := mul_le_mul_of_nonneg_right hμ (norm_nonneg (μ i))
      nlinarith

/-- A sum of the actual centering errors, before a bounded-fiber pullback. -/
theorem rowCenteringError_total_mass_le [Fintype I] [Fintype J]
    (P : I → J → ℂ) (μ : I → ℂ)
    (e : J ≃ J) (B M : ℝ) (hB : 0 ≤ B)
    (hP : ∀ i, (∑ j : J, ‖P i j‖) ≤ B)
    (hμ : ∀ i, (Fintype.card J : ℝ) * ‖μ i‖ ≤ B)
    (hM : (∑ i : I, ‖μ i‖) ≤ M) :
    (∑ i : I, ∑ j : J, ‖rowCenteringError P μ e i j‖) ≤ 3 * B * M := by
  calc
    _ ≤ ∑ i : I, 3 * B * ‖μ i‖ :=
      Finset.sum_le_sum (fun i _ => rowCenteringError_row_mass_le P μ e i B (hP i) (hμ i))
    _ = 3 * B * ∑ i : I, ‖μ i‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hM (by positivity)

end FiniteArrays

theorem correlationGramKappa_le_seven_quarters (p : ℕ) [Fact p.Prime] :
    correlationGramKappa p ≤ (7 : ℝ) / 4 := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp
  norm_num at hinv
  have hsq : ((p : ℝ)⁻¹) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr (Nat.cast_nonneg p)) hinv 2
  unfold correlationGramKappa
  linarith

#print axioms rowCenteringError
#print axioms rowCenteringError_eq
#print axioms rowCenteringError_norm_le
#print axioms rowCenteringError_row_mass_le
#print axioms rowCenteringError_total_mass_le
#print axioms correlationGramKappa_le_seven_quarters

end PrimeGap182.TypeIII
