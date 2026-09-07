import TypeIIIFourIndexSum

/-! Explicit real inequalities for the three powers in the Type III matrix estimate. -/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

/-- Repeated-index completion controls the diagonal cycles without a pointwise Deligne bound. -/
theorem squarefreeCompletionShape_diagonal_le {S : ℝ} (hS : 0 ≤ S) (R : ℕ) :
    squarefreeCompletionShape S S R R ≤
      2 * S ^ 3 * (1 + Real.log S) ^ 2 + 8 * (R : ℝ) ^ 2 * S ^ 2 := by
  have hcross : 4 * (R : ℝ) * S ^ 2 * (1 + Real.log S) * Real.sqrt S ≤
      S ^ 3 * (1 + Real.log S) ^ 2 + 4 * (R : ℝ) ^ 2 * S ^ 2 := by
    calc
      _ = 2 * (S * Real.sqrt S * (1 + Real.log S)) * (2 * R * S) := by ring
      _ ≤ (S * Real.sqrt S * (1 + Real.log S)) ^ 2 + (2 * (R : ℝ) * S) ^ 2 := by
        nlinarith [sq_nonneg (S * Real.sqrt S * (1 + Real.log S) - 2 * R * S)]
      _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hS]; ring
  unfold squarefreeCompletionShape
  rw [Real.sqrt_mul hS, ← sq, Real.sq_sqrt hS]
  nlinarith only [hcross]

/-- The mixed completion term is absorbed uniformly for all positive moduli and all R. -/
theorem matrix_middle_term_absorption {R S : ℝ} (hS : 1 ≤ S) :
    R * S ^ 2 ≤ S ^ 3 + R ^ 2 * S * Real.sqrt S := by
  have hs0 : 0 ≤ S := zero_le_one.trans hS
  have hroot : 1 ≤ Real.sqrt S := Real.one_le_sqrt.mpr hS
  calc
    _ = S * (R * S) := by ring
    _ ≤ S * (S ^ 2 + R ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hs0
      nlinarith [sq_nonneg (S - R)]
    _ = S ^ 3 + R ^ 2 * S := by ring
    _ ≤ _ := by
      exact add_le_add le_rfl
        (le_mul_of_one_le_right (mul_nonneg (sq_nonneg R) hs0) hroot)

/-- The raw rectangular fourth-moment bound, specialized to square index ranges, has the
three expected monomials with a completely explicit constant. -/
theorem matrix_raw_bound_le_three_terms
    {S T : ℝ} (hS : 1 ≤ S) (hT : 1 ≤ T) (M R : ℕ) :
    ((M : ℝ) * (M : ℝ) ^ 2 + (M : ℝ) ^ 2 * (M : ℝ)) *
        squarefreeCompletionShape S S R R +
      (M : ℝ) ^ 2 * (M : ℝ) ^ 2 *
        (S ^ 3 * (1 + Real.log S) ^ 2 +
          4 * T ^ 2 * (2 * ((R : ℝ) + R) * S ^ 2 * (1 + Real.log S) +
            4 * R * R * S * Real.sqrt S)) ≤
      64 * T ^ 2 * (1 + Real.log S) ^ 2 *
        ((R : ℝ) ^ 2 * (M : ℝ) ^ 3 * S ^ 2 +
          (M : ℝ) ^ 4 * S ^ 3 + (R : ℝ) ^ 2 * (M : ℝ) ^ 4 * S * Real.sqrt S) := by
  let L := 1 + Real.log S
  have hs0 : 0 ≤ S := zero_le_one.trans hS
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hS]
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hTone : 1 ≤ T ^ 2 := by nlinarith
  have hLone : 1 ≤ L ^ 2 := le_trans hL hLsq
  have hbig : 1 ≤ T ^ 2 * L ^ 2 := one_le_mul_of_one_le_of_one_le hTone hLone
  have hM : (M : ℝ) ^ 3 ≤ (M : ℝ) ^ 4 := by
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · norm_num
    · have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
      simpa only [pow_succ] using le_mul_of_one_le_right (pow_nonneg (Nat.cast_nonneg M) 3) hm1
  have hd := squarefreeCompletionShape_diagonal_le hs0 R
  have hmixed := matrix_middle_term_absorption (R := (R : ℝ)) hS
  calc
    _ ≤ 2 * (M : ℝ) ^ 3 * (2 * S ^ 3 * L ^ 2 + 8 * (R : ℝ) ^ 2 * S ^ 2) +
        (M : ℝ) ^ 4 *
          (S ^ 3 * L ^ 2 + 16 * T ^ 2 * ((R : ℝ) * S ^ 2 * L) +
            16 * T ^ 2 * (R : ℝ) ^ 2 * S * Real.sqrt S) := by
      have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2 * (M : ℝ) ^ 3 by positivity)
      dsimp only [L] at hh ⊢
      nlinarith only [hh]
    _ = 16 * (R : ℝ) ^ 2 * (M : ℝ) ^ 3 * S ^ 2 +
        4 * (M : ℝ) ^ 3 * S ^ 3 * L ^ 2 + (M : ℝ) ^ 4 * S ^ 3 * L ^ 2 +
        16 * T ^ 2 * (M : ℝ) ^ 4 * L * ((R : ℝ) * S ^ 2) +
        16 * T ^ 2 * (R : ℝ) ^ 2 * (M : ℝ) ^ 4 * S * Real.sqrt S := by ring
    _ ≤ 16 * T ^ 2 * L ^ 2 * ((R : ℝ) ^ 2 * (M : ℝ) ^ 3 * S ^ 2) +
        4 * T ^ 2 * L ^ 2 * ((M : ℝ) ^ 4 * S ^ 3) +
        T ^ 2 * L ^ 2 * ((M : ℝ) ^ 4 * S ^ 3) +
        16 * T ^ 2 * L ^ 2 * (M : ℝ) ^ 4 * (S ^ 3 + (R : ℝ) ^ 2 * S * Real.sqrt S) +
        16 * T ^ 2 * L ^ 2 * ((R : ℝ) ^ 2 * (M : ℝ) ^ 4 * S * Real.sqrt S) := by
      apply add_le_add
      · apply add_le_add
        · apply add_le_add
          · apply add_le_add
            · nlinarith [mul_le_mul_of_nonneg_right hbig
                (show 0 ≤ 16 * (R : ℝ) ^ 2 * (M : ℝ) ^ 3 * S ^ 2 by positivity)]
            · have hm' := mul_le_mul_of_nonneg_right hM (show 0 ≤ 4 * S ^ 3 * L ^ 2 by positivity)
              have ht' := mul_le_mul_of_nonneg_right hTone
                (show 0 ≤ 4 * (M : ℝ) ^ 4 * S ^ 3 * L ^ 2 by positivity)
              nlinarith only [hm', ht']
          · have ht' := mul_le_mul_of_nonneg_right hTone
              (show 0 ≤ (M : ℝ) ^ 4 * S ^ 3 * L ^ 2 by positivity)
            nlinarith only [ht']
        · have hm' := mul_le_mul_of_nonneg_left hmixed
            (show 0 ≤ 16 * T ^ 2 * (M : ℝ) ^ 4 * L by positivity)
          have hl' := mul_le_mul_of_nonneg_right hLsq
            (show 0 ≤ 16 * T ^ 2 * (M : ℝ) ^ 4 *
              (S ^ 3 + (R : ℝ) ^ 2 * S * Real.sqrt S) by positivity)
          nlinarith only [hm', hl']
      · have hl' := mul_le_mul_of_nonneg_right hLone
          (show 0 ≤ 16 * T ^ 2 * (R : ℝ) ^ 2 * (M : ℝ) ^ 4 * S * Real.sqrt S by positivity)
        nlinarith only [hl']
    _ ≤ _ := by
      dsimp only [L]
      nlinarith [mul_nonneg (show 0 ≤ T ^ 2 * (1 + Real.log S) ^ 2 by positivity)
        (show 0 ≤ (R : ℝ) ^ 2 * (M : ℝ) ^ 3 * S ^ 2 by positivity),
        mul_nonneg (show 0 ≤ T ^ 2 * (1 + Real.log S) ^ 2 by positivity)
          (show 0 ≤ (M : ℝ) ^ 4 * S ^ 3 by positivity),
        mul_nonneg (show 0 ≤ T ^ 2 * (1 + Real.log S) ^ 2 by positivity)
          (show 0 ≤ (R : ℝ) ^ 2 * (M : ℝ) ^ 4 * S * Real.sqrt S by positivity)]

#print axioms squarefreeCompletionShape_diagonal_le
#print axioms matrix_middle_term_absorption
#print axioms matrix_raw_bound_le_three_terms

end

end PrimeGap182.TypeIII
