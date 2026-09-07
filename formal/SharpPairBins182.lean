import PairPartition182
import PairDensity182

/-!
# The sharp defect in the actual unordered pair bins

This module connects the five-prime defect to the exact prime-divisor carrier,
then to its disjoint 1024 bins. The auxiliary-square statement preserves an
arbitrary signed value C: it is applied to the full sum before any square.
Its auxiliary values must equal one on the actual exceptional support.
-/

noncomputable section
open scoped BigOperators
open PrimeGap186

namespace PrimeGap182Analytic

def unorderedPair (pq : ℕ × ℕ) : Finset ℕ := {pq.1, pq.2}

theorem unorderedPair_injective_on_ordered (U : Finset (ℕ × ℕ))
    (hU : ∀ pq ∈ U, pq.1 < pq.2) : Set.InjOn unorderedPair U := by
  intro pq hpq rs hrs he
  have hs : ({pq.1, pq.2} : Set ℕ) = {rs.1, rs.2} := by
    simpa only [unorderedPair, Finset.coe_pair] using
      congrArg (fun s : Finset ℕ => (s : Set ℕ)) he
  rcases Set.pair_eq_pair_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext h1 h2
  · have h := hU pq hpq
    rw [h1, h2] at h
    exact False.elim ((not_lt_of_gt (hU rs hrs)) h)

theorem sharpPairCarrier_subset_marked_image (x a : ℝ) (n : ℕ) (hn : 0 < n) :
    sharpPairCarrier x a n ⊆
      (markedPairCarrier x (1 - 2 * a) a n).image unorderedPair := by
  classical
  intro s hs
  obtain ⟨hcard, hrough, hprod⟩ := Finset.mem_filter.mp hs
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hcard
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hcard
  have hpMem := hsub (Finset.mem_insert_self p {q})
  have hqMem := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self q))
  have hp := Nat.prime_of_mem_primeFactors hpMem
  have hq := Nat.prime_of_mem_primeFactors hqMem
  have hpn := Nat.dvd_of_mem_primeFactors hpMem
  have hqn := Nat.dvd_of_mem_primeFactors hqMem
  have hcop : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr
    (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))
  have hpqn : p * q ∣ n := hcop.mul_dvd_of_dvd_of_dvd hpn hqn
  have hpR := hrough p (Finset.mem_insert_self p {q})
  have hqR := hrough q (Finset.mem_insert_of_mem (Finset.mem_singleton_self q))
  have hpqR : ((p * q : ℕ) : ℝ) < x ^ a := by
    simpa only [Finset.prod_pair hpq] using hprod
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · apply Finset.mem_image.mpr
    refine ⟨(p, q), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩,
      hlt, hpqn, hpR.le, hqR.le, hpqR⟩, rfl⟩
    · exact Nat.mem_primesLE.mpr ⟨Nat.le_of_dvd hn hpn, hp⟩
    · exact Nat.mem_primesLE.mpr ⟨Nat.le_of_dvd hn hqn, hq⟩
  · apply Finset.mem_image.mpr
    refine ⟨(q, p), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩,
      hgt, ?_, hqR.le, hpR.le, ?_⟩, ?_⟩
    · exact Nat.mem_primesLE.mpr ⟨Nat.le_of_dvd hn hqn, hq⟩
    · exact Nat.mem_primesLE.mpr ⟨Nat.le_of_dvd hn hpn, hp⟩
    · simpa only [mul_comm] using hpqn
    · simpa only [mul_comm] using hpqR
    · exact Finset.pair_comm q p

theorem sharpDefect_le_markedPairCarrier (x a t : ℝ) (hx : 1 < x)
    (ht : t < 2 / 5) (n : ℕ) (hxn : x ≤ (n : ℝ)) :
    sharpDefect x a n ≤ ∑ pq ∈ markedPairCarrier x (1 - 2 * a) a n,
      pairHinge t (Real.logb x ((pq.1 * pq.2 : ℕ) : ℝ)) := by
  classical
  have hn : 0 < n := Nat.cast_pos.mp ((zero_lt_one.trans hx).trans_le hxn)
  let U := markedPairCarrier x (1 - 2 * a) a n
  have hU (pq : ℕ × ℕ) (hpq : pq ∈ U) : pq.1 < pq.2 :=
    (Finset.mem_filter.mp hpq).2.1
  have hsub := sharpPairCarrier_subset_marked_image x a n hn
  have hbound := Finset.sum_le_sum_of_subset_of_nonneg
    (f := arithmeticPairWeight x t) hsub
    (fun s _ _ => pairHinge_nonneg t _ ht)
  have heq : (∑ s ∈ U.image unorderedPair, arithmeticPairWeight x t s) =
      ∑ pq ∈ U, pairHinge t (Real.logb x ((pq.1 * pq.2 : ℕ) : ℝ)) := by
    rw [Finset.sum_image (unorderedPair_injective_on_ordered U hU)]
    apply Finset.sum_congr rfl
    intro pq hpq
    simp only [arithmeticPairWeight, unorderedPair, Finset.prod_pair (ne_of_lt (hU pq hpq))]
  rw [heq] at hbound
  exact (sharpDefect_le_arithmetic_pair_majorant x a t hx ht n hxn).trans hbound

theorem sharpDefect_le_weighted_bin_card (x a t : ℝ) (hx : 1 < x)
    (ha : 2 / 5 < a) (ht : t < 2 / 5) (n : ℕ) (hxn : x ≤ (n : ℝ)) :
    sharpDefect x a n ≤ ∑ j : Fin 1024,
      pairHinge t (pairBinRight (1 - 2 * a) a j) *
        ((markedDivisorPairBin x (1 - 2 * a) a j n).card : ℝ) := by
  classical
  have hn : 0 < n := Nat.cast_pos.mp ((zero_lt_one.trans hx).trans_le hxn)
  have hgap : 2 * (1 - 2 * a) < a := by linarith
  have hbound := sharpDefect_le_markedPairCarrier x a t hx ht n hxn
  rw [markedPairCarrier_weighted_partition x (1 - 2 * a) a hx hgap n hn] at hbound
  apply hbound.trans
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ ∑ _pq ∈ markedDivisorPairBin x (1 - 2 * a) a j n,
        pairHinge t (pairBinRight (1 - 2 * a) a j) := by
      apply Finset.sum_le_sum
      intro pq hpq
      have hbin := (Finset.mem_filter.mp hpq).1
      have hupper := (Finset.mem_filter.mp hbin).2.2.2.2.2.1
      exact PrimeGap182.pairHinge_monotone t ht hupper
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The auxiliary roots are allowed to depend on the pair bin. Their exact
value on the exceptional support is the only extra pointwise premise. -/
theorem sharpDefect_bin_auxiliary_square (x a t : ℝ) (hx : 1 < x)
    (ha : 2 / 5 < a) (ht : t < 2 / 5) (n : ℕ) (hxn : x ≤ (n : ℝ))
    (L : Fin 1024 → ℝ) (C : ℝ)
    (hL : SharpExceptional x a n → ∀ j, L j = 1) :
    sharpDefect x a n * C ^ 2 ≤ ∑ j : Fin 1024,
      pairHinge t (pairBinRight (1 - 2 * a) a j) *
        ∑ pq ∈ markedPrimePairBin x (1 - 2 * a) a
          (pairBinLeft (1 - 2 * a) a j) (pairBinRight (1 - 2 * a) a j),
          if pq.1 * pq.2 ∣ n then (L j * C) ^ 2 else 0 := by
  classical
  by_cases hex : SharpExceptional x a n
  · have h := mul_le_mul_of_nonneg_right
      (sharpDefect_le_weighted_bin_card x a t hx ha ht n hxn) (sq_nonneg C)
    apply h.trans_eq
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [hL hex j, one_mul, ← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, markedDivisorPairBin]
    ring
  · simp only [sharpDefect, ite_eq_right hex, zero_mul]
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (pairHinge_nonneg t _ ht)
    exact Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

#print axioms unorderedPair_injective_on_ordered
#print axioms sharpPairCarrier_subset_marked_image
#print axioms sharpDefect_le_markedPairCarrier
#print axioms sharpDefect_le_weighted_bin_card
#print axioms sharpDefect_bin_auxiliary_square

end PrimeGap182Analytic
