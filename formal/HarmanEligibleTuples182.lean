import HarmanEligibleCuts182
import HarmanCollision182

/-! Exact finite pushforward of the source tuples into the arithmetic
coefficient sequence. The same identity covers eligible tuples and the
sharp residual by changing only the actual tuple filter. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

def sourceFivePrimeBand (x : ℝ) : Finset ℕ :=
  (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
    ⌊x ^ ((31 : ℝ) / 100)⌋₊).filter Nat.Prime

def sourceFivePrimeCarrier (x : ℝ) : Finset (Fin 5 → ℕ) :=
  Fintype.piFinset (fun _ : Fin 5 => sourceFivePrimeBand x)

theorem sourceFivePrimeCarrier_spec {x : ℝ} (hx : 0 < x)
    {p : Fin 5 → ℕ} (hp : p ∈ sourceFivePrimeCarrier x) (i : Fin 5) :
    (p i).Prime ∧ x ^ ((8639 : ℝ) / 50000) ≤ (p i : ℝ) ∧
      (p i : ℝ) ≤ x ^ ((31 : ℝ) / 100) := by
  have hh := Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)
  refine ⟨hh.2, Nat.ceil_le.mp (Finset.mem_Icc.mp hh.1).1, ?_⟩
  exact (Nat.cast_le.mpr (Finset.mem_Icc.mp hh.1).2).trans
    (Nat.floor_le (Real.rpow_nonneg hx.le _))

theorem sourceFive_mem_primeCarrier {x : ℝ} (hx : 1 < x)
    (he : 2 * x ≤ x ^ ((10001 : ℝ) / 10000)) {n : ℕ}
    (hnx : (n : ℝ) ≤ 2 * x) {j : Fin 2} {p : Fin 5 → ℕ}
    (hp : p ∈ sourceFiveTuples x n j) : p ∈ sourceFivePrimeCarrier x := by
  have hpr := (sourceFiveTuples_mem.mp hp).1
  have hb := sourceFive_prime_band hx he hnx hp
  apply Fintype.mem_piFinset.mpr
  intro i
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨Nat.ceil_le.mpr (hb i).1, Nat.le_floor (hb i).2.le⟩, hpr i⟩

open Classical in
theorem sourceFive_filteredSequence_eq_tuple_sum {x : ℝ} (hx : 1 < x)
    (he : 2 * x ≤ x ^ ((10001 : ℝ) / 10000)) (j : Fin 2)
    (R : (Fin 5 → ℕ) → Prop) :
    (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
      Finsupp.single n (((sourceFiveTuples x n j).filter R).card : ℂ)) =
    ∑ p ∈ sourceFivePrimeCarrier x, Finsupp.single (∏ i, p i)
      (if (∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧
          sourceFiveOrder x j p ∧ R p then (1 : ℂ) else 0) := by
  let N := Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊
  let T := sourceFivePrimeCarrier x
  have hfilter (n : ℕ) (hn : n ∈ N) :
      (sourceFiveTuples x n j).filter R =
        T.filter (fun p => (∏ i, p i) = n ∧ sourceFiveOrder x j p ∧ R p) := by
    have hnx : (n : ℝ) ≤ 2 * x :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le (by positivity))
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, hR⟩
      obtain ⟨_, hprod, ho⟩ := sourceFiveTuples_mem.mp hp
      exact ⟨sourceFive_mem_primeCarrier hx he hnx hp, hprod, ho, hR⟩
    · rintro ⟨hp, hprod, ho, hR⟩
      exact ⟨sourceFiveTuples_mem.mpr ⟨fun i =>
        (sourceFivePrimeCarrier_spec (zero_lt_one.trans hx) hp i).1, hprod, ho⟩, hR⟩
  ext n
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
  by_cases hn : n ∈ N
  · rw [ite_eq_left hn, hfilter n hn, Finset.natCast_card_filter]
    apply Finset.sum_congr rfl
    intro p _hp
    by_cases hpn : (∏ i, p i) = n
    · have hn' : n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ := hn
      simp only [hpn, hn', ite_true, true_and]
    · simp only [hpn, ite_false, false_and]
  · rw [ite_eq_right hn]
    symm
    apply Finset.sum_eq_zero
    intro p _hp
    by_cases hpn : (∏ i, p i) = n
    · have hn' : n ∉ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ := hn
      simp only [hpn, hn', ite_true, ite_false, false_and]
    · simp only [hpn, ite_false]

open Classical in
theorem sourceFiveEligibleSequence_eq_tuple_sum {x : ℝ} (hx : 1 < x)
    (he : 2 * x ≤ x ^ ((10001 : ℝ) / 10000)) (j : Fin 2) :
    sourceFiveEligibleSequence x j (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊) =
      ∑ p ∈ sourceFivePrimeCarrier x, Finsupp.single (∏ i, p i)
        (if sourceFiveEligiblePredicate x j p then (1 : ℂ) else 0) := by
  convert sourceFive_filteredSequence_eq_tuple_sum hx he j
      (fun p => Function.Injective p ∧ ¬ fivePairCaps x p) using 1
  · unfold sourceFiveEligibleSequence
    apply Finset.sum_congr rfl
    intro n _hn
    have hs : sourceFiveEligible x n j = (sourceFiveTuples x n j).filter
        (fun p => Function.Injective p ∧ ¬ fivePairCaps x p) := by
      ext p
      simp only [sourceFiveEligible, Finset.mem_filter]
    rw [hs]
    congr
  · apply Finset.sum_congr rfl
    intro p _hp
    unfold sourceFiveEligiblePredicate
    congr

theorem sourceFiveEligiblePredicate_central {x : ℝ} (hx : 1 < x)
    (he : 2 * x ≤ x ^ ((10001 : ℝ) / 10000)) (j : Fin 2)
    (p : Fin 5 → ℕ) (hp : p ∈ sourceFivePrimeCarrier x)
    (hC : sourceFiveEligiblePredicate x j p) :
    (∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧
      ∃ S : Finset (Fin 5), (S.card = 2 ∨ S.card = 3) ∧
        x ^ ((41361 : ℝ) / 100000) ≤ ((∏ i ∈ S, p i : ℕ) : ℝ) ∧
        ((∏ i ∈ S, p i : ℕ) : ℝ) ≤ x ^ ((58639 : ℝ) / 100000) := by
  classical
  obtain ⟨hc, ho, hi, hn⟩ := hC
  have hpS : p ∈ sourceFiveEligible x (∏ i, p i) j := by
    apply Finset.mem_filter.mpr
    exact ⟨sourceFiveTuples_mem.mpr ⟨fun i =>
      (sourceFivePrimeCarrier_spec (zero_lt_one.trans hx) hp i).1, rfl, ho⟩, hi, hn⟩
  have hprod : ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x :=
    (Nat.cast_le.mpr (Finset.mem_Icc.mp hc).2).trans (Nat.floor_le (by positivity))
  obtain ⟨i, k, hik, hlo, hhi⟩ := sourceFiveEligible_central_pair hx he hprod hpS
  refine ⟨hc, {i, k}, Or.inl (Finset.card_pair (ne_of_lt hik)), ?_, ?_⟩
  · simpa only [Finset.prod_pair (ne_of_lt hik), Nat.cast_mul] using hlo
  · simpa only [Finset.prod_pair (ne_of_lt hik), Nat.cast_mul] using hhi.le

#print axioms sourceFive_filteredSequence_eq_tuple_sum
#print axioms sourceFiveEligibleSequence_eq_tuple_sum
#print axioms sourceFiveEligiblePredicate_central

end PrimeGap182Analytic.Harman
