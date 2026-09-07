import HarmanResidualSplit182

/-! Exact product geometry of the new five-prime source regions. Every
eligible pair belongs to the central Type II range for sufficiently
large x, and every repeated tuple has a square divisor in the stated
prime band. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

theorem eventually_sourceFive_envelope :
    ∀ᶠ x : ℝ in atTop, 1 < x ∧ 2 * x ≤ x ^ ((10001 : ℝ) / 10000) := by
  have h := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 10000)
  filter_upwards [eventually_gt_atTop (1 : ℝ), h.eventually_gt_atTop 2] with x hx hh
  have hx0 : 0 < x := zero_lt_one.trans hx
  have heq : x ^ ((10001 : ℝ) / 10000) = x * x ^ ((1 : ℝ) / 10000) := by
    rw [show (10001 : ℝ) / 10000 = 1 + (1 : ℝ) / 10000 by norm_num,
      Real.rpow_add hx0, Real.rpow_one]
  exact ⟨hx, by rw [heq]; nlinarith only [hh, hx0]⟩

theorem sourceFive_log_geometry {x : ℝ} (hx : 1 < x)
    (he : 2 * x ≤ x ^ ((10001 : ℝ) / 10000)) {n : ℕ}
    (hnx : (n : ℝ) ≤ 2 * x) {j : Fin 2} {p : Fin 5 → ℕ}
    (hp : p ∈ sourceFiveTuples x n j) :
    (∀ i, (8639 : ℝ) / 50000 ≤ Real.logb x (p i : ℝ) ∧
      Real.logb x (p i : ℝ) < (31 : ℝ) / 100) ∧
    (∀ i k : Fin 5, i < k →
      Real.logb x (p i : ℝ) + Real.logb x (p k : ℝ) < (58639 : ℝ) / 100000) := by
  obtain ⟨hpr, hprod, ho⟩ := sourceFiveTuples_mem.mp hp
  have hlo := sourceFiveOrder_rough hx j p hpr ho
  have hl (i : Fin 5) : (8639 : ℝ) / 50000 ≤ Real.logb x (p i : ℝ) :=
    (Real.le_logb_iff_rpow_le hx (Nat.cast_pos.mpr (hpr i).pos)).mpr (hlo i)
  have hnpos : 0 < n := hprod ▸ Finset.prod_pos (fun i _ => (hpr i).pos)
  have hs : (∑ i, Real.logb x (p i : ℝ)) ≤ (10001 : ℝ) / 10000 := by
    rw [← Real.logb_prod Finset.univ (fun i : Fin 5 => (p i : ℝ))
      (fun i _ => (Nat.cast_pos.mpr (hpr i).pos).ne'), ← Nat.cast_prod, hprod]
    exact (Real.logb_le_iff_le_rpow hx (Nat.cast_pos.mpr hnpos)).mpr (hnx.trans he)
  simp only [Fin.sum_univ_five] at hs
  have h0 := hl 0
  have h1 := hl 1
  have h2 := hl 2
  have h3 := hl 3
  have h4 := hl 4
  constructor
  · intro i
    refine ⟨hl i, ?_⟩
    fin_cases i <;> dsimp <;> linarith only [hs, h0, h1, h2, h3, h4]
  · intro i k hik
    fin_cases i <;> fin_cases k <;> norm_num at hik
    all_goals dsimp; linarith only [hs, h0, h1, h2, h3, h4]

theorem sourceFive_prime_band {x : ℝ} (hx : 1 < x)
    (he : 2 * x ≤ x ^ ((10001 : ℝ) / 10000)) {n : ℕ}
    (hnx : (n : ℝ) ≤ 2 * x) {j : Fin 2} {p : Fin 5 → ℕ}
    (hp : p ∈ sourceFiveTuples x n j) :
    ∀ i, x ^ ((8639 : ℝ) / 50000) ≤ (p i : ℝ) ∧ (p i : ℝ) < x ^ ((31 : ℝ) / 100) := by
  have hpr := (sourceFiveTuples_mem.mp hp).1
  have hg := (sourceFive_log_geometry hx he hnx hp).1
  intro i
  exact ⟨(Real.le_logb_iff_rpow_le hx (Nat.cast_pos.mpr (hpr i).pos)).mp (hg i).1,
    (Real.logb_lt_iff_lt_rpow hx (Nat.cast_pos.mpr (hpr i).pos)).mp (hg i).2⟩

theorem sourceFiveEligible_central_pair {x : ℝ} (hx : 1 < x)
    (he : 2 * x ≤ x ^ ((10001 : ℝ) / 10000)) {n : ℕ}
    (hnx : (n : ℝ) ≤ 2 * x) {j : Fin 2} {p : Fin 5 → ℕ}
    (hp : p ∈ sourceFiveEligible x n j) :
    ∃ i k : Fin 5, i < k ∧
      x ^ ((41361 : ℝ) / 100000) ≤ (p i : ℝ) * (p k : ℝ) ∧
      (p i : ℝ) * (p k : ℝ) < x ^ ((58639 : ℝ) / 100000) := by
  obtain ⟨hpS, _, i, k, hik, hlo⟩ := sourceFiveEligible_mem.mp hp
  have hpr := (sourceFiveTuples_mem.mp hpS).1
  have hg := (sourceFive_log_geometry hx he hnx hpS).2 i k hik
  refine ⟨i, k, hik, hlo, ?_⟩
  apply (Real.logb_lt_iff_lt_rpow hx
    (mul_pos (Nat.cast_pos.mpr (hpr i).pos) (Nat.cast_pos.mpr (hpr k).pos))).mp
  simpa only [Real.logb_mul (Nat.cast_pos.mpr (hpr i).pos).ne'
    (Nat.cast_pos.mpr (hpr k).pos).ne'] using hg

theorem sourceFiveCollision_square {x : ℝ} (hx : 1 < x)
    (he : 2 * x ≤ x ^ ((10001 : ℝ) / 10000)) {n : ℕ}
    (hnx : (n : ℝ) ≤ 2 * x) {j : Fin 2} {p : Fin 5 → ℕ}
    (hp : p ∈ sourceFiveCollision x n j) :
    ∃ r : ℕ, r.Prime ∧ x ^ ((8639 : ℝ) / 50000) ≤ (r : ℝ) ∧
      (r : ℝ) < x ^ ((31 : ℝ) / 100) ∧ r ^ 2 ∣ n := by
  classical
  obtain ⟨hpS, hni⟩ := Finset.mem_filter.mp hp
  obtain ⟨i, k, heq, hik⟩ := Function.not_injective_iff.mp hni
  obtain ⟨hpr, hprod, _⟩ := sourceFiveTuples_mem.mp hpS
  obtain ⟨hlo, hhi⟩ := sourceFive_prime_band hx he hnx hpS i
  refine ⟨p i, hpr i, hlo, hhi, ?_⟩
  have hd := Finset.prod_dvd_prod_of_subset {i, k} Finset.univ p (Finset.subset_univ _)
  simpa only [Finset.prod_pair hik, ← heq, ← pow_two, hprod] using hd

theorem sourceFive_card_le_divisor_power (x : ℝ) (n : ℕ) (j : Fin 2) :
    (sourceFiveTuples x n j).card ≤ n.divisors.card ^ 5 := by
  classical
  have hsub : sourceFiveTuples x n j ⊆ Fintype.piFinset (fun _ : Fin 5 => n.divisors) := by
    intro p hp
    obtain ⟨hpr, hprod, _⟩ := sourceFiveTuples_mem.mp hp
    have hn : n ≠ 0 := (hprod ▸ Finset.prod_pos (fun i _ => (hpr i).pos)).ne'
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Nat.mem_divisors.mpr ⟨hprod ▸ Finset.dvd_prod_of_mem p (Finset.mem_univ i), hn⟩
  simpa only [Fintype.card_piFinset_const, Fintype.card_fin] using Finset.card_le_card hsub

theorem sourceFiveCollision_card_le_divisor_power (x : ℝ) (n : ℕ) (j : Fin 2) :
    (sourceFiveCollision x n j).card ≤ n.divisors.card ^ 5 :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans (sourceFive_card_le_divisor_power x n j)

#print axioms sourceFiveEligible_central_pair
#print axioms sourceFiveCollision_square
#print axioms sourceFiveCollision_card_le_divisor_power

end PrimeGap182Analytic.Harman
