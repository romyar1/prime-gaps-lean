import TypeIIICorrelationGram

/-!
# Exact row means of the actual Type III correlation

The product of a correlation row and a multiplicatively translated row has
an explicit unit-column average.  The Gram identity bounds its absolute
row sum by `p²`.  For distinct rows the total absolute mass of the means is
at most `2 κ p`, using the exact second moment of the raw rank-two sums.
Every assertion concerns the actual finite sums; no character-sum estimate
or local Fourier hypothesis is used.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open scoped BigOperators Classical

variable (p : ℕ) [Fact p.Prime]

/-- A row product of the actual correlation, before its column average. -/
def correlationRowPair (a A B : (ZMod p)ˣ) : ℂ :=
  correlationUnitMatrix p A B * star (correlationUnitMatrix p (a * A) B)

/-- The exact unit-column average, whose denominator is the number `p-1`
of unit columns. -/
def correlationRowMean (a A : (ZMod p)ˣ) : ℂ :=
  ((p : ℂ) - 1)⁻¹ * ∑ B : (ZMod p)ˣ, correlationRowPair p a A B

theorem correlation_units_card_real :
    (Fintype.card (ZMod p)ˣ : ℝ) = (p : ℝ) - 1 := by
  rw [ZMod.card_units, Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one]

theorem correlation_units_card_complex :
    (Fintype.card (ZMod p)ˣ : ℂ) = (p : ℂ) - 1 := by
  rw [ZMod.card_units, Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one]

theorem correlation_unit_count_pos : 0 < (p : ℝ) - 1 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  linarith

theorem correlation_unit_count_norm : ‖(p : ℂ) - 1‖ = (p : ℝ) - 1 := by
  have he : (p : ℂ) - 1 = (((p : ℝ) - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (correlation_unit_count_pos p)]

/-- Exact squared norm of one actual correlation row. -/
theorem correlation_row_norm_sq (A : (ZMod p)ˣ) :
    (∑ B : (ZMod p)ˣ, ‖correlationUnitMatrix p A B‖ ^ 2) =
      (p : ℝ) ^ 2 - correlationGramKappa p * ((p : ℝ) + ‖correlationGramVector p A‖ ^ 2) := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_add]
  simp_rw [gram_complex_norm_sq]
  simp only [Complex.ofReal_pow, Complex.ofReal_natCast]
  simpa only [correlationUnitMatrix, ite_true] using correlation_gram_entry p A A

/-- Every actual correlation row has squared norm at most `p²`. -/
theorem correlation_row_norm_sq_le (A : (ZMod p)ˣ) :
    (∑ B : (ZMod p)ˣ, ‖correlationUnitMatrix p A B‖ ^ 2) ≤ (p : ℝ) ^ 2 := by
  rw [correlation_row_norm_sq]
  exact sub_le_self _ (mul_nonneg (correlationGramKappa_nonneg p)
    (add_nonneg (Nat.cast_nonneg p) (sq_nonneg _)))

/-- The absolute unit-column sum of a row product is at most `p²`. -/
theorem correlationRowPair_abs_sum_le (a A : (ZMod p)ˣ) :
    (∑ B : (ZMod p)ˣ, ‖correlationRowPair p a A B‖) ≤ (p : ℝ) ^ 2 := by
  simp only [correlationRowPair, norm_mul, norm_star]
  have hab :
      (∑ B : (ZMod p)ˣ,
        2 * (‖correlationUnitMatrix p A B‖ * ‖correlationUnitMatrix p (a * A) B‖)) ≤
      ∑ B : (ZMod p)ˣ,
        (‖correlationUnitMatrix p A B‖ ^ 2 + ‖correlationUnitMatrix p (a * A) B‖ ^ 2) := by
    apply Finset.sum_le_sum
    intro B _
    nlinarith [sq_nonneg (‖correlationUnitMatrix p A B‖ -
      ‖correlationUnitMatrix p (a * A) B‖)]
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hab
  have hA := correlation_row_norm_sq_le p A
  have haA := correlation_row_norm_sq_le p (a * A)
  linarith

/-- Multiplying the norm of the mean by the exact unit count cancels
the averaging denominator. -/
theorem correlationRowMean_norm_mul (a A : (ZMod p)ˣ) :
    ((p : ℝ) - 1) * ‖correlationRowMean p a A‖ =
      ‖∑ B : (ZMod p)ˣ, correlationRowPair p a A B‖ := by
  rw [correlationRowMean, norm_mul, norm_inv, correlation_unit_count_norm,
    ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (correlation_unit_count_pos p)), one_mul]

/-- The pointwise mean bound holds for every row translation. -/
theorem correlationRowMean_norm_mul_le (a A : (ZMod p)ˣ) :
    ((p : ℝ) - 1) * ‖correlationRowMean p a A‖ ≤ (p : ℝ) ^ 2 := by
  rw [correlationRowMean_norm_mul]
  exact (norm_sum_le _ _).trans (correlationRowPair_abs_sum_le p a A)

/-- A nontrivial row translation gives the exact rank-two expression for
the column mean. -/
theorem correlationRowMean_eq_of_ne_one (a A : (ZMod p)ˣ) (ha : a ≠ 1) :
    correlationRowMean p a A =
      -(correlationGramKappa p : ℂ) / ((p : ℂ) - 1) *
        ((p : ℂ) + correlationGramVector p A * star (correlationGramVector p (a * A))) := by
  have hAA : A ≠ a * A := by
    intro h
    apply ha
    have hm : a * A = 1 * A := by simpa only [one_mul] using h.symm
    exact mul_right_cancel hm
  unfold correlationRowMean correlationRowPair correlationUnitMatrix
  rw [correlation_gram_entry, ite_eq_right hAA]
  ring

/-- The raw rank-two sum has unit first moment one, including the exact
subtraction of its value at zero. -/
theorem correlation_rawKl2_first_moment :
    (∑ A : (ZMod p)ˣ, PrimeGap186.unnormalizedKloosterman2 p (-(A : ZMod p))) = 1 := by
  have hfull : (∑ x : ZMod p, PrimeGap186.unnormalizedKloosterman2 p (-x)) = 0 := by
    have h := PrimeGap186.unnormalizedKloosterman2_scaled_dft p (-1) 0
      (neg_ne_zero.mpr one_ne_zero)
    simpa only [ZMod.dft_apply, neg_one_mul, zero_mul, mul_zero, neg_zero,
      AddChar.map_zero_eq_one, smul_eq_mul, one_mul, ite_true] using h
  rw [PrimeGap186.sum_units_eq_sum_sub_zero p
    (fun x : ZMod p => PrimeGap186.unnormalizedKloosterman2 p (-x)), hfull]
  simp only [neg_zero, PrimeGap186.unnormalizedKloosterman2_zero, zero_sub, neg_neg]

/-- The exact energy of the vector in the Gram correction. -/
theorem correlationGramVector_sum_norm_sq :
    (∑ A : (ZMod p)ˣ, ‖correlationGramVector p A‖ ^ 2) =
      (p : ℝ) * ((p : ℝ) - 1) - correlationGramKappa p := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hsecond :
      (∑ A : (ZMod p)ˣ,
        PrimeGap186.unnormalizedKloosterman2 p (-(A : ZMod p)) *
          star (PrimeGap186.unnormalizedKloosterman2 p (-(A : ZMod p)))) =
        (p : ℂ) ^ 2 - (p : ℂ) - 1 := by
    simpa only [neg_one_mul, ite_true] using
      PrimeGap186.unnormalizedKloosterman2_unit_correlation p (-1) (-1)
        (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)
  have hpoint (A : (ZMod p)ˣ) :
      correlationGramVector p A * star (correlationGramVector p A) =
        PrimeGap186.unnormalizedKloosterman2 p (-(A : ZMod p)) *
          star (PrimeGap186.unnormalizedKloosterman2 p (-(A : ZMod p))) -
        (p : ℂ)⁻¹ * PrimeGap186.unnormalizedKloosterman2 p (-(A : ZMod p)) -
        (p : ℂ)⁻¹ * star (PrimeGap186.unnormalizedKloosterman2 p (-(A : ZMod p))) +
        ((p : ℂ)⁻¹) ^ 2 := by
    simp only [correlationGramVector, star_sub, star_inv₀, star_natCast]
    ring
  have he :
      (∑ A : (ZMod p)ˣ, correlationGramVector p A * star (correlationGramVector p A)) =
        (p : ℂ) * ((p : ℂ) - 1) - (correlationGramKappa p : ℂ) := by
    simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [← Finset.mul_sum, ← star_sum, correlation_rawKl2_first_moment,
      hsecond, star_one, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      correlation_units_card_complex, correlationGramKappa,
      Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_inv,
      Complex.ofReal_pow, Complex.ofReal_natCast]
    field_simp; ring
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one]
  simp_rw [gram_complex_norm_sq]
  simp only [Complex.ofReal_natCast]
  exact he

/-- The useful upper bound keeps the exact `p(p-1)` normalization. -/
theorem correlationGramVector_sum_norm_sq_le :
    (∑ A : (ZMod p)ˣ, ‖correlationGramVector p A‖ ^ 2) ≤ (p : ℝ) * ((p : ℝ) - 1) := by
  rw [correlationGramVector_sum_norm_sq]
  exact sub_le_self _ (correlationGramKappa_nonneg p)

/-- Multiplicative translation preserves vector energy, so the mixed
absolute product has the same energy bound. -/
theorem correlationGramVector_pair_norm_sum_le (a : (ZMod p)ˣ) :
    (∑ A : (ZMod p)ˣ, ‖correlationGramVector p A‖ * ‖correlationGramVector p (a * A)‖) ≤
      (p : ℝ) * ((p : ℝ) - 1) := by
  have hperm :
      (∑ A : (ZMod p)ˣ, ‖correlationGramVector p (a * A)‖ ^ 2) =
        ∑ A : (ZMod p)ˣ, ‖correlationGramVector p A‖ ^ 2 :=
    Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun _ => rfl)
  have hab :
      (∑ A : (ZMod p)ˣ,
        2 * (‖correlationGramVector p A‖ * ‖correlationGramVector p (a * A)‖)) ≤
      ∑ A : (ZMod p)ˣ,
        (‖correlationGramVector p A‖ ^ 2 + ‖correlationGramVector p (a * A)‖ ^ 2) := by
    apply Finset.sum_le_sum
    intro A _
    nlinarith [sq_nonneg (‖correlationGramVector p A‖ - ‖correlationGramVector p (a * A)‖)]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, hperm] at hab
  have hbound := correlationGramVector_sum_norm_sq_le p
  linarith

/-- A pointwise estimate for a distinct-row mean using its exact rank-two
formula; no pointwise rank-two estimate enters. -/
theorem correlationRowMean_norm_le_of_ne_one (a A : (ZMod p)ˣ) (ha : a ≠ 1) :
    ‖correlationRowMean p a A‖ ≤
      correlationGramKappa p / ((p : ℝ) - 1) *
        ((p : ℝ) + ‖correlationGramVector p A‖ * ‖correlationGramVector p (a * A)‖) := by
  have hcoef : ‖-(correlationGramKappa p : ℂ) / ((p : ℂ) - 1)‖ =
      correlationGramKappa p / ((p : ℝ) - 1) := by
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (correlationGramKappa_nonneg p), correlation_unit_count_norm]
  rw [correlationRowMean_eq_of_ne_one p a A ha, norm_mul, hcoef]
  apply mul_le_mul_of_nonneg_left _
    (div_nonneg (correlationGramKappa_nonneg p) (le_of_lt (correlation_unit_count_pos p)))
  simpa only [norm_natCast, norm_mul, norm_star] using
    norm_add_le (p : ℂ) (correlationGramVector p A * star (correlationGramVector p (a * A)))

/-- For a nontrivial row translation, the total absolute mass of all row
means is at most `2 κ p`. -/
theorem correlationRowMean_sum_norm_le (a : (ZMod p)ˣ) (ha : a ≠ 1) :
    (∑ A : (ZMod p)ˣ, ‖correlationRowMean p a A‖) ≤
      2 * correlationGramKappa p * (p : ℝ) := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (ZMod p)ˣ))
    (fun A _ => correlationRowMean_norm_le_of_ne_one p a A ha)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, correlation_units_card_real] at hsum
  calc
    _ ≤ correlationGramKappa p / ((p : ℝ) - 1) *
        (((p : ℝ) - 1) * (p : ℝ) +
          ∑ A : (ZMod p)ˣ, ‖correlationGramVector p A‖ * ‖correlationGramVector p (a * A)‖) := hsum
    _ ≤ correlationGramKappa p / ((p : ℝ) - 1) *
        (((p : ℝ) - 1) * (p : ℝ) + (p : ℝ) * ((p : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (correlationGramVector_pair_norm_sum_le p a))
        (div_nonneg (correlationGramKappa_nonneg p) (le_of_lt (correlation_unit_count_pos p)))
    _ = _ := by
      field_simp [ne_of_gt (correlation_unit_count_pos p)]; ring

#print axioms correlationRowPair
#print axioms correlationRowMean
#print axioms correlation_units_card_real
#print axioms correlation_units_card_complex
#print axioms correlation_unit_count_pos
#print axioms correlation_unit_count_norm
#print axioms correlation_row_norm_sq
#print axioms correlation_row_norm_sq_le
#print axioms correlationRowPair_abs_sum_le
#print axioms correlationRowMean_norm_mul
#print axioms correlationRowMean_norm_mul_le
#print axioms correlationRowMean_eq_of_ne_one
#print axioms correlation_rawKl2_first_moment
#print axioms correlationGramVector_sum_norm_sq
#print axioms correlationGramVector_sum_norm_sq_le
#print axioms correlationGramVector_pair_norm_sum_le
#print axioms correlationRowMean_norm_le_of_ne_one
#print axioms correlationRowMean_sum_norm_le

end PrimeGap182.TypeIII
