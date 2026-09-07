import IncidenceSourceCoefficients

/-!
# Summing the source divisor sectors without discarding short coefficients

The nonzero-mode contribution uses the actual pointwise coefficient
bound and the short dyadic support. The area and row contributions use
the total coefficient energy. The divisor multiplicity and harmonic
mass remain explicit.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

theorem incidenceSourceFrequencyBlock_card_le (J : Finset ℤ)
    (v₁ v₂ m w₁ w₂ : ℕ) (Y : ℤ) :
    (incidenceSourceFrequencyBlock J v₁ v₂ m w₁ w₂ Y).card ≤ J.card ^ 2 := by
  apply (Finset.card_filter_le _ _).trans
  apply (Finset.card_filter_le _ _).trans
  simp [Finset.product_eq_sprod, pow_two]

theorem incidenceSourceSector_card_le (J : Finset ℤ)
    (v₁ v₂ m w₁ w₂ : ℕ) (Y : ℤ) (t : ℕ) :
    (incidenceDividedCoefficientSet (incidenceSourceQuotientSet J v₁ v₂ m w₁ w₂ Y)
      (t * w₂)).card ≤ J.card ^ 2 := by
  apply (incidenceDividedCoefficientSet_card _ _).trans
  apply Finset.card_image_le.trans
  exact incidenceSourceFrequencyBlock_card_le J v₁ v₂ m w₁ w₂ Y

theorem incidenceSectorCoefficients_point_energy (S : Finset ℤ) (t w₂ : ℕ)
    (ht : 0 < t) (hw₂ : 0 < w₂) (Λ B : ℝ) (hΛ : 0 < Λ)
    (hS : ∀ l ∈ S, Λ ≤ |(l : ℝ)| ∧ |(l : ℝ)| ≤ 2 * Λ)
    (coeff : ℤ → ℂ) (_hB : 0 ≤ B) (hcoeff : ∀ l ∈ S, ‖coeff l‖ ≤ B) :
    (∑ a ∈ incidenceDividedCoefficientSet S (t * w₂),
      ‖coeff (((t * w₂ : ℕ) : ℤ) * a)‖ ^ 2) ≤
        6 * (Λ / (w₂ : ℝ)) * B ^ 2 / (t : ℝ) := by
  have htw : 0 < t * w₂ := mul_pos ht hw₂
  have hcard := incidenceIntegerDyadic_card (incidenceDividedCoefficientSet S (t * w₂))
    (Λ / (t * w₂ : ℕ)) (by positivity)
    (fun a ha => incidenceDividedCoefficient_dyadic S (t * w₂) htw Λ hS a ha)
  calc
    _ ≤ ∑ _a ∈ incidenceDividedCoefficientSet S (t * w₂), B ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      exact pow_le_pow_left₀ (norm_nonneg _)
        (hcoeff _ ((incidenceDividedCoefficientSet_mem S (t * w₂) htw.ne' a).mp ha)) 2
    _ = ((incidenceDividedCoefficientSet S (t * w₂)).card : ℝ) * B ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (6 * (Λ / (t * w₂ : ℕ))) * B ^ 2 :=
      mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = _ := by push_cast; ring

theorem incidenceFarey_small_density (A : Finset ℤ) (U V q C τ : ℝ)
    (_hU : 0 ≤ U) (hV : 0 ≤ V) (hq : 0 < q) (_hC : 0 ≤ C) (hτ : 0 ≤ τ)
    (hdensity : U * V ≤ q) (hcard : (A.card : ℝ) ≤ C * V) :
    (1 + 8 * U * V / q) * ((A.card : ℝ) + 8 * V * τ) ≤
      9 * (C + 8 * τ) * V := by
  have hfirst : 1 + 8 * U * V / q ≤ 9 := by
    have hrat : 8 * U * V / q ≤ 8 := (div_le_iff₀ hq).mpr (by nlinarith only [hdensity])
    linarith
  calc
    _ ≤ 9 * (C * V + 8 * V * τ) :=
      mul_le_mul hfirst (add_le_add hcard le_rfl) (by positivity) (by norm_num)
    _ = _ := by ring

theorem incidenceFarey_density_factor (A : Finset ℤ) (U V q C τ Ddensity : ℝ)
    (hV : 0 ≤ V) (hq : 0 < q) (hτ : 0 ≤ τ) (hDdensity : 1 ≤ Ddensity)
    (hdensity : U * V ≤ Ddensity * q) (hcard : (A.card : ℝ) ≤ C * V) :
    (1 + 8 * U * V / q) * ((A.card : ℝ) + 8 * V * τ) ≤
      9 * Ddensity * (C + 8 * τ) * V := by
  have hfirst : 1 + 8 * U * V / q ≤ 9 * Ddensity := by
    have hrat : 8 * U * V / q ≤ 8 * Ddensity :=
      (div_le_iff₀ hq).mpr (by nlinarith only [hdensity])
    linarith
  calc
    _ ≤ (9 * Ddensity) * (C * V + 8 * V * τ) :=
      mul_le_mul hfirst (add_le_add hcard le_rfl) (by positivity) (by positivity)
    _ = _ := by ring

theorem incidenceSectorEnergy_linear_sum (T : Finset ℕ) (ht : ∀ t ∈ T, 0 < t)
    (E : ℕ → ℝ) (hE : ∀ t ∈ T, 0 ≤ E t)
    (Etotal P α β γ δ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ)
    (htotal : (∑ t ∈ T, E t) ≤ Etotal)
    (hpoint : ∀ t ∈ T, E t ≤ P / (t : ℝ)) :
    (∑ t ∈ T, (α / (t : ℝ) + β + γ / (t : ℝ) + δ) * E t) ≤
      (α + γ + δ) * Etotal + β * P * ∑ t ∈ T, (t : ℝ)⁻¹ := by
  calc
    _ ≤ ∑ t ∈ T, ((α + γ + δ) * E t + β * (P / (t : ℝ))) := by
      apply Finset.sum_le_sum
      intro t htT
      have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht t htT
      have hαt : α / (t : ℝ) ≤ α := div_le_self hα ht1
      have hγt : γ / (t : ℝ) ≤ γ := div_le_self hγ ht1
      have hmain := mul_le_mul_of_nonneg_right (add_le_add hαt hγt) (hE t htT)
      have hosc := mul_le_mul_of_nonneg_left (hpoint t htT) hβ
      nlinarith only [hmain, hosc]
    _ = (α + γ + δ) * (∑ t ∈ T, E t) + β * P * ∑ t ∈ T, (t : ℝ)⁻¹ := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, div_eq_mul_inv]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left htotal (add_nonneg (add_nonneg hα hγ) hδ)) le_rfl

theorem incidenceSectorWindow_sum_le (T : Finset ℕ) (ht : ∀ t ∈ T, 0 < t)
    (S : Finset ℤ) (w₂ : ℕ) (hw₂ : 0 < w₂)
    (Λ Ebase esc V q B E₀ C τcoeff τD Ddensity η : ℝ) (J : ℕ)
    (hΛ : 0 < Λ) (hEbase : 0 ≤ Ebase) (hesc : 0 ≤ esc) (hV : 0 ≤ V) (hq : 0 < q)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hτcoeff : 0 ≤ τcoeff) (hτD : 0 ≤ τD)
    (hDdensity : 1 ≤ Ddensity)
    (hS : ∀ l ∈ S, Λ ≤ |(l : ℝ)| ∧ |(l : ℝ)| ≤ 2 * Λ)
    (hdivisors : ∀ l ∈ S, (l.natAbs.divisors.card : ℝ) ≤ τcoeff)
    (coeff : ℤ → ℂ) (hcoeff : ∀ l ∈ S, ‖coeff l‖ ≤ B)
    (henergy : (∑ l ∈ S, ‖coeff l‖ ^ 2) ≤ E₀)
    (hdensity : ∀ t ∈ T, (Λ / ((t * w₂ : ℕ) : ℝ)) * V ≤ Ddensity * q)
    (hcard : ∀ t ∈ T, ((incidenceDividedCoefficientSet S (t * w₂)).card : ℝ) ≤ C * V) :
    (∑ t ∈ T,
      (2 * (Ebase / (t : ℝ)) * esc + (J : ℝ) * q ^ (3 / 2 + η) +
        q ^ (1 / 2 + η) * ((J : ℝ) * (Ebase / (t : ℝ)) + 2 * esc)) *
      ((1 + 8 * (Λ / ((t * w₂ : ℕ) : ℝ)) * V / q) *
        (((incidenceDividedCoefficientSet S (t * w₂)).card : ℝ) + 8 * V * τD)) *
      ∑ a ∈ incidenceDividedCoefficientSet S (t * w₂),
        ‖coeff (((t * w₂ : ℕ) : ℤ) * a)‖ ^ 2) ≤
      9 * Ddensity * (C + 8 * τD) * V *
        ((2 * Ebase * esc + q ^ (1 / 2 + η) * J * Ebase +
          q ^ (1 / 2 + η) * (2 * esc)) * (τcoeff * E₀) +
          ((J : ℝ) * q ^ (3 / 2 + η)) * (6 * (Λ / (w₂ : ℝ)) * B ^ 2) *
            ∑ t ∈ T, (t : ℝ)⁻¹) := by
  let E (t : ℕ) : ℝ := ∑ a ∈ incidenceDividedCoefficientSet S (t * w₂),
    ‖coeff (((t * w₂ : ℕ) : ℤ) * a)‖ ^ 2
  have hE (t : ℕ) : 0 ≤ E t := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hS0 : ∀ l ∈ S, l ≠ 0 := by
    intro l hl hz
    have hh := (hS l hl).1
    simp only [hz, Int.cast_zero, abs_zero] at hh
    exact hΛ.not_ge hh
  have htotal : (∑ t ∈ T, E t) ≤ τcoeff * E₀ :=
    (incidenceSectorCoefficients_energy_sum T S w₂ coeff τcoeff hS0 hdivisors).trans
      (mul_le_mul_of_nonneg_left henergy hτcoeff)
  have hpoint (t : ℕ) (htT : t ∈ T) : E t ≤
      (6 * (Λ / (w₂ : ℝ)) * B ^ 2) / (t : ℝ) :=
    incidenceSectorCoefficients_point_energy S t w₂ (ht t htT) hw₂ Λ B hΛ hS coeff hB hcoeff
  have hsum := incidenceSectorEnergy_linear_sum T ht E (fun t _ => hE t)
    (τcoeff * E₀) (6 * (Λ / (w₂ : ℝ)) * B ^ 2)
    (2 * Ebase * esc) ((J : ℝ) * q ^ (3 / 2 + η))
    (q ^ (1 / 2 + η) * J * Ebase) (q ^ (1 / 2 + η) * (2 * esc))
    (by positivity) (by positivity) (by positivity) (by positivity) htotal hpoint
  calc
    _ ≤ ∑ t ∈ T,
        (9 * Ddensity * (C + 8 * τD) * V *
          ((2 * Ebase * esc / (t : ℝ) + (J : ℝ) * q ^ (3 / 2 + η) +
            q ^ (1 / 2 + η) * J * Ebase / (t : ℝ) +
            q ^ (1 / 2 + η) * (2 * esc)) * E t)) := by
      apply Finset.sum_le_sum
      intro t htT
      have htR : 0 < (t : ℝ) := by exact_mod_cast ht t htT
      have hf := incidenceFarey_density_factor (incidenceDividedCoefficientSet S (t * w₂))
        (Λ / ((t * w₂ : ℕ) : ℝ)) V q C τD Ddensity hV hq hτD hDdensity
        (hdensity t htT) (hcard t htT)
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hf
          (show 0 ≤ 2 * (Ebase / (t : ℝ)) * esc + (J : ℝ) * q ^ (3 / 2 + η) +
            q ^ (1 / 2 + η) * ((J : ℝ) * (Ebase / (t : ℝ)) + 2 * esc) by positivity)) (hE t)
      convert hh using 1
      dsimp only [E]
      ring
    _ = 9 * Ddensity * (C + 8 * τD) * V *
        ∑ t ∈ T,
          (2 * Ebase * esc / (t : ℝ) + (J : ℝ) * q ^ (3 / 2 + η) +
            q ^ (1 / 2 + η) * J * Ebase / (t : ℝ) +
            q ^ (1 / 2 + η) * (2 * esc)) * E t := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceSourceFrequencyBlock_card_le
#print axioms PrimeGap182Audit.incidenceSourceSector_card_le
#print axioms PrimeGap182Audit.incidenceSectorCoefficients_point_energy
#print axioms PrimeGap182Audit.incidenceFarey_small_density
#print axioms PrimeGap182Audit.incidenceFarey_density_factor
#print axioms PrimeGap182Audit.incidenceSectorEnergy_linear_sum
#print axioms PrimeGap182Audit.incidenceSectorWindow_sum_le
