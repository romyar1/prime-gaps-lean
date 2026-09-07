import IncidenceSourceNormalization

/-!
# The coefficient correction retains favorable common-factor powers

The actual public source fiber count has the extra factor q₀. Retaining
its square uniformly multiplies all four normalized contributions by
q₀². The corrected lower modulus scale also permits a density factor
q₀ in the Farey bound. The final four bounds retain both corrections,
with favorable common-factor powers still present in every denominator.
-/

noncomputable section

namespace PrimeGap182Audit.IncidenceSourceEnvelope

variable {x «ω» δ γ L Z A M N H q₀ v₀ w₁ Δ₁ Δ m : ℝ}
variable (h : IncidenceSourceEnvelope x «ω» δ γ L Z A M N H q₀ v₀ w₁ Δ₁ Δ m)

include h

theorem corrected_mean_bound :
    q₀ ^ 2 * (Δ₁ * H ^ 2 / (q₀ ^ 3 * w₁ * v₀ * N)) ≤
      1 / (q₀ ^ 3 * w₁ * v₀ * Z) := by
  have hq : q₀ ≠ 0 := ne_of_gt (zero_lt_one.trans_le h.hq₀)
  apply (mul_le_mul_of_nonneg_left h.mean_bound (sq_nonneg q₀)).trans_eq
  field_simp

theorem corrected_oscillatory_bound :
    q₀ ^ 2 * (x ^ (2 * δ) * m ^ (3 / 2 : ℝ) * H ^ 2 /
      (q₀ ^ (5 / 2 : ℝ) * v₀ * N * Δ)) ≤
      L ^ 16 * Z ^ (5 / 2 : ℝ) * x ^ (3 / 2 + 40 * «ω» + 16 * δ - 5 * γ) /
        (q₀ ^ 4 * v₀ ^ (5 / 2 : ℝ)) := by
  have hq : q₀ ≠ 0 := ne_of_gt (zero_lt_one.trans_le h.hq₀)
  apply (mul_le_mul_of_nonneg_left h.oscillatory_bound (sq_nonneg q₀)).trans_eq
  field_simp

theorem corrected_row_two_bound :
    q₀ ^ 2 * (Real.sqrt m * H ^ 2 / (q₀ ^ (5 / 2 : ℝ) * v₀ * N)) ≤
      L ^ 6 * Real.sqrt Z * x ^ (1 / 2 + 16 * «ω» + 5 * δ - 2 * γ) /
        (q₀ ^ 3 * v₀ ^ (3 / 2 : ℝ)) := by
  have hq : q₀ ≠ 0 := ne_of_gt (zero_lt_one.trans_le h.hq₀)
  apply (mul_le_mul_of_nonneg_left h.row_two_bound (sq_nonneg q₀)).trans_eq
  field_simp

theorem corrected_row_one_bound :
    q₀ ^ 2 * (x ^ δ * Real.sqrt m * H ^ 2 / (q₀ ^ (7 / 2 : ℝ) * v₀ * N)) ≤
      L ^ 6 * Real.sqrt Z * x ^ (1 / 2 + 16 * «ω» + 6 * δ - 2 * γ) /
        (q₀ ^ 4 * v₀ ^ (3 / 2 : ℝ)) := by
  have hq : q₀ ≠ 0 := ne_of_gt (zero_lt_one.trans_le h.hq₀)
  apply (mul_le_mul_of_nonneg_left h.row_one_bound (sq_nonneg q₀)).trans_eq
  field_simp

theorem fully_corrected_mean_bound :
    q₀ ^ 3 * (Δ₁ * H ^ 2 / (q₀ ^ 3 * w₁ * v₀ * N)) ≤
      1 / (q₀ ^ 2 * w₁ * v₀ * Z) := by
  have hq : q₀ ≠ 0 := ne_of_gt (zero_lt_one.trans_le h.hq₀)
  apply (mul_le_mul_of_nonneg_left h.mean_bound
    (pow_nonneg (zero_le_one.trans h.hq₀) 3)).trans_eq
  field_simp

theorem fully_corrected_oscillatory_bound :
    q₀ ^ 3 * (x ^ (2 * δ) * m ^ (3 / 2 : ℝ) * H ^ 2 /
      (q₀ ^ (5 / 2 : ℝ) * v₀ * N * Δ)) ≤
      L ^ 16 * Z ^ (5 / 2 : ℝ) * x ^ (3 / 2 + 40 * «ω» + 16 * δ - 5 * γ) /
        (q₀ ^ 3 * v₀ ^ (5 / 2 : ℝ)) := by
  have hq : q₀ ≠ 0 := ne_of_gt (zero_lt_one.trans_le h.hq₀)
  apply (mul_le_mul_of_nonneg_left h.oscillatory_bound
    (pow_nonneg (zero_le_one.trans h.hq₀) 3)).trans_eq
  field_simp

theorem fully_corrected_row_two_bound :
    q₀ ^ 3 * (Real.sqrt m * H ^ 2 / (q₀ ^ (5 / 2 : ℝ) * v₀ * N)) ≤
      L ^ 6 * Real.sqrt Z * x ^ (1 / 2 + 16 * «ω» + 5 * δ - 2 * γ) /
        (q₀ ^ 2 * v₀ ^ (3 / 2 : ℝ)) := by
  have hq : q₀ ≠ 0 := ne_of_gt (zero_lt_one.trans_le h.hq₀)
  apply (mul_le_mul_of_nonneg_left h.row_two_bound
    (pow_nonneg (zero_le_one.trans h.hq₀) 3)).trans_eq
  field_simp

theorem fully_corrected_row_one_bound :
    q₀ ^ 3 * (x ^ δ * Real.sqrt m * H ^ 2 / (q₀ ^ (7 / 2 : ℝ) * v₀ * N)) ≤
      L ^ 6 * Real.sqrt Z * x ^ (1 / 2 + 16 * «ω» + 6 * δ - 2 * γ) /
        (q₀ ^ 3 * v₀ ^ (3 / 2 : ℝ)) := by
  have hq : q₀ ≠ 0 := ne_of_gt (zero_lt_one.trans_le h.hq₀)
  apply (mul_le_mul_of_nonneg_left h.row_one_bound
    (pow_nonneg (zero_le_one.trans h.hq₀) 3)).trans_eq
  field_simp

end PrimeGap182Audit.IncidenceSourceEnvelope

#print axioms PrimeGap182Audit.IncidenceSourceEnvelope.corrected_mean_bound
#print axioms PrimeGap182Audit.IncidenceSourceEnvelope.corrected_oscillatory_bound
#print axioms PrimeGap182Audit.IncidenceSourceEnvelope.corrected_row_two_bound
#print axioms PrimeGap182Audit.IncidenceSourceEnvelope.corrected_row_one_bound
#print axioms PrimeGap182Audit.IncidenceSourceEnvelope.fully_corrected_mean_bound
#print axioms PrimeGap182Audit.IncidenceSourceEnvelope.fully_corrected_oscillatory_bound
#print axioms PrimeGap182Audit.IncidenceSourceEnvelope.fully_corrected_row_two_bound
#print axioms PrimeGap182Audit.IncidenceSourceEnvelope.fully_corrected_row_one_bound
