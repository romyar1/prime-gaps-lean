import SharpPairBins182

/-!
The pointwise marked-pair majorant for a full signed radial sum. Auxiliary
sieves may vary with both pair bin and radial block. All radial cross terms
remain inside the square.
-/

noncomputable section
open scoped BigOperators
open PrimeGap186

namespace PrimeGap182Analytic

theorem sharpDefect_radial_auxiliary_square {J : Type*} (blocks : Finset J)
    (x a t : ℝ) (hx : 1 < x) (ha : 2 / 5 < a) (ht : t < 2 / 5)
    (n : ℕ) (hxn : x ≤ (n : ℝ))
    (L : Fin 1024 → J → ℝ) (C : J → ℝ)
    (hL : SharpExceptional x a n → ∀ j, ∀ b ∈ blocks, L j b = 1) :
    sharpDefect x a n * (∑ b ∈ blocks, C b) ^ 2 ≤ ∑ j : Fin 1024,
      pairHinge t (pairBinRight (1 - 2 * a) a j) *
        ∑ pq ∈ markedPrimePairBin x (1 - 2 * a) a
          (pairBinLeft (1 - 2 * a) a j) (pairBinRight (1 - 2 * a) a j),
          if pq.1 * pq.2 ∣ n then (∑ b ∈ blocks, L j b * C b) ^ 2 else 0 := by
  classical
  by_cases hex : SharpExceptional x a n
  · have h := sharpDefect_bin_auxiliary_square x a t hx ha ht n hxn
      (fun _ => 1) (∑ b ∈ blocks, C b) (fun _ _ => rfl)
    have hs (j : Fin 1024) : (∑ b ∈ blocks, L j b * C b) = ∑ b ∈ blocks, C b := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [hL hex j b hb, one_mul]
    simpa only [hs, one_mul] using h
  · simp only [sharpDefect, ite_eq_right hex, zero_mul]
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (pairHinge_nonneg t _ ht)
    apply Finset.sum_nonneg
    intro pq _
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl

theorem sharp182_radial_auxiliary_square {J : Type*} (blocks : Finset J)
    (x : ℝ) (hx : 1 < x) (n : ℕ) (hxn : x ≤ (n : ℝ))
    (L : Fin 1024 → J → ℝ) (C : J → ℝ)
    (hL : SharpExceptional x (41361 / 100000) n → ∀ j, ∀ b ∈ blocks, L j b = 1) :
    sharpDefect x (41361 / 100000) n * (∑ b ∈ blocks, C b) ^ 2 ≤ ∑ j : Fin 1024,
      pairHinge (19 / 50) (pairBinRight (8639 / 50000) (41361 / 100000) j) *
        ∑ pq ∈ markedPrimePairBin x (8639 / 50000) (41361 / 100000)
          (pairBinLeft (8639 / 50000) (41361 / 100000) j)
          (pairBinRight (8639 / 50000) (41361 / 100000) j),
          if pq.1 * pq.2 ∣ n then (∑ b ∈ blocks, L j b * C b) ^ 2 else 0 := by
  have h := sharpDefect_radial_auxiliary_square blocks x (41361 / 100000) (19 / 50)
    hx (by norm_num) (by norm_num) n hxn L C hL
  norm_num only [show (1 : ℝ) - 2 * (41361 / 100000) = 8639 / 50000 by norm_num] at h
  exact h

#print axioms sharpDefect_radial_auxiliary_square
#print axioms sharp182_radial_auxiliary_square

end PrimeGap182Analytic
