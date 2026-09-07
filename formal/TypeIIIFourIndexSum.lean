import TypeIIIIntegerGCD

/-! Elementary finite-sum bounds used in the actual Type III matrix fourth moment. -/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

/-- A nonnegative constant over unequal pairs is bounded by the full four-index count. -/
theorem four_index_offdiag_const_le {m n : Type*} [DecidableEq m] [DecidableEq n]
    (U : Finset m) (V : Finset n) {K : ℝ} (hK : 0 ≤ K) :
    (∑ i ∈ U, ∑ _i' ∈ U.erase i, ∑ j ∈ V, ∑ _j' ∈ V.erase j, K) ≤
      (U.card : ℝ) ^ 2 * (V.card : ℝ) ^ 2 * K := by
  calc
    _ ≤ ∑ i ∈ U, ∑ i' ∈ U, ∑ j ∈ V, ∑ j' ∈ V, K := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ ∑ i' ∈ U.erase i, ∑ j ∈ V, ∑ j' ∈ V, K := by
          apply Finset.sum_le_sum
          intro i' hi'
          apply Finset.sum_le_sum
          intro j hj
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset j V)
            (fun _ _ _ => hK)
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i U)
          (fun _ _ _ => Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => hK)))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- Equal rows or columns contribute only three free indices.  The remaining term is
exactly the sum over pairs of unequal integer indices. -/
theorem four_index_sum_le_diagonal_and_offdiag
    {m n : Type*} [DecidableEq m] [DecidableEq n]
    (U : Finset m) (V : Finset n) (f : m → m → n → n → ℝ) {D : ℝ}
    (hD : 0 ≤ D)
    (hdiag : ∀ i ∈ U, ∀ i' ∈ U, ∀ j ∈ V, ∀ j' ∈ V,
      i = i' ∨ j = j' → f i i' j j' ≤ D) :
    (∑ i ∈ U, ∑ i' ∈ U, ∑ j ∈ V, ∑ j' ∈ V, f i i' j j') ≤
      ((U.card : ℝ) * (V.card : ℝ) ^ 2 + (U.card : ℝ) ^ 2 * (V.card : ℝ)) * D +
        ∑ i ∈ U, ∑ i' ∈ U.erase i, ∑ j ∈ V, ∑ j' ∈ V.erase j, f i i' j j' := by
  have hrow (i : m) (hi : i ∈ U) :
      (∑ i' ∈ U, ∑ j ∈ V, ∑ j' ∈ V, f i i' j j') ≤
        (V.card : ℝ) ^ 2 * D + ∑ i' ∈ U.erase i, ∑ j ∈ V, ∑ j' ∈ V, f i i' j j' := by
    have heq := Finset.sum_erase_add (s := U)
      (fun i' => ∑ j ∈ V, ∑ j' ∈ V, f i i' j j') hi
    have hd : (∑ j ∈ V, ∑ j' ∈ V, f i i j j') ≤ (V.card : ℝ) ^ 2 * D := by
      calc
        _ ≤ ∑ _j ∈ V, ∑ _j' ∈ V, D := by
          apply Finset.sum_le_sum
          intro j hj
          exact Finset.sum_le_sum (fun j' hj' => hdiag i hi i hi j hj j' hj' (Or.inl rfl))
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
    linarith
  have hcol (i i' : m) (hi : i ∈ U) (hi' : i' ∈ U) :
      (∑ j ∈ V, ∑ j' ∈ V, f i i' j j') ≤
        (V.card : ℝ) * D + ∑ j ∈ V, ∑ j' ∈ V.erase j, f i i' j j' := by
    calc
      _ ≤ ∑ j ∈ V, (D + ∑ j' ∈ V.erase j, f i i' j j') := by
        apply Finset.sum_le_sum
        intro j hj
        have heq := Finset.sum_erase_add (s := V) (fun j' => f i i' j j') hj
        have hd := hdiag i hi i' hi' j hj j hj (Or.inr rfl)
        linarith
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ ∑ i ∈ U, ((V.card : ℝ) ^ 2 * D +
        ∑ i' ∈ U.erase i, ∑ j ∈ V, ∑ j' ∈ V, f i i' j j') :=
      Finset.sum_le_sum (fun i hi => hrow i hi)
    _ ≤ ∑ i ∈ U, ((V.card : ℝ) ^ 2 * D +
        ∑ i' ∈ U.erase i, ((V.card : ℝ) * D +
          ∑ j ∈ V, ∑ j' ∈ V.erase j, f i i' j j')) := by
      apply Finset.sum_le_sum
      intro i hi
      apply add_le_add_right
      exact Finset.sum_le_sum (fun i' hi' => hcol i i' hi (Finset.mem_of_mem_erase hi'))
    _ ≤ ∑ i ∈ U, ((V.card : ℝ) ^ 2 * D +
        (∑ _i' ∈ U, (V.card : ℝ) * D) +
          ∑ i' ∈ U.erase i, ∑ j ∈ V, ∑ j' ∈ V.erase j, f i i' j j') := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.sum_add_distrib]
      have hc : (∑ _i' ∈ U.erase i, (V.card : ℝ) * D) ≤
          ∑ _i' ∈ U, (V.card : ℝ) * D :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i U)
          (fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) hD)
      linarith
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      ring

/-- The explicit completion majorant is affine in the square-root gcd. -/
theorem squarefreeCompletionShape_eq_affine_sqrt {S G : ℝ} (hS : 0 ≤ S)
    (Nh Nk : ℕ) :
    squarefreeCompletionShape S G Nh Nk =
      S ^ 3 * (1 + Real.log S) ^ 2 +
        (2 * ((Nh : ℝ) + Nk) * S ^ 2 * (1 + Real.log S) +
          4 * Nh * Nk * S * Real.sqrt S) * Real.sqrt G := by
  unfold squarefreeCompletionShape
  rw [Real.sqrt_mul hS]
  ring

/-- The actual four-index sum of the completion majorant over unequal row and column
indices, with the discriminant gcd internally averaged. -/
theorem interval_offdiag_completionShape_sum
    (s N M : ℕ) (hs : 0 < s) (A B : ℤ) (Nh Nk : ℕ) :
    (∑ i ∈ Finset.Ico A (A + N), ∑ i' ∈ (Finset.Ico A (A + N)).erase i,
      ∑ j ∈ Finset.Ico B (B + M), ∑ j' ∈ (Finset.Ico B (B + M)).erase j,
        squarefreeCompletionShape s (Int.gcd ((i - i') * (j - j')) (s : ℤ)) Nh Nk) ≤
      (N : ℝ) ^ 2 * (M : ℝ) ^ 2 *
        ((s : ℝ) ^ 3 * (1 + Real.log s) ^ 2 +
          4 * (s.divisors.card : ℝ) ^ 2 *
            (2 * ((Nh : ℝ) + Nk) * (s : ℝ) ^ 2 * (1 + Real.log s) +
              4 * Nh * Nk * s * Real.sqrt s)) := by
  let U := Finset.Ico A (A + N)
  let V := Finset.Ico B (B + M)
  let a := (s : ℝ) ^ 3 * (1 + Real.log s) ^ 2
  let b := 2 * ((Nh : ℝ) + Nk) * (s : ℝ) ^ 2 * (1 + Real.log s) +
    4 * Nh * Nk * s * Real.sqrt s
  have hlog : 0 ≤ Real.log (s : ℝ) := Real.log_nonneg (by exact_mod_cast hs)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hcount := four_index_offdiag_const_le U V ha
  simp only [U, V, Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast] at hcount
  have hgcd := interval_four_index_sqrt_gcd_offdiag s N M hs A B
  calc
    _ = (∑ i ∈ U, ∑ i' ∈ U.erase i, ∑ j ∈ V, ∑ j' ∈ V.erase j, a) +
        b * (∑ i ∈ U, ∑ i' ∈ U.erase i, ∑ j ∈ V, ∑ j' ∈ V.erase j,
          Real.sqrt (Int.gcd ((i - i') * (j - j')) (s : ℤ) : ℝ)) := by
      dsimp only [a, b, U, V]
      simp only [squarefreeCompletionShape_eq_affine_sqrt (Nat.cast_nonneg s),
        Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ (N : ℝ) ^ 2 * (M : ℝ) ^ 2 * a +
        b * (4 * (N : ℝ) ^ 2 * (M : ℝ) ^ 2 * (s.divisors.card : ℝ) ^ 2) :=
      add_le_add hcount (mul_le_mul_of_nonneg_left hgcd hb)
    _ = _ := by dsimp [a, b]; ring

#print axioms four_index_sum_le_diagonal_and_offdiag
#print axioms interval_offdiag_completionShape_sum

end

end PrimeGap182.TypeIII
