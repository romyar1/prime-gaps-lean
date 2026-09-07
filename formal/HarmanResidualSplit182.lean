import HarmanFivePrime182
import SharpBuchstab182

/-! The two literal five-prime sources split into the sharp residual,
distinct tuples with an eligible pair, and tuples with a repeated prime.
This is an exact identity at each integer in [x,2x]. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

def sourceFiveOrder (x : ℝ) (j : Fin 2) (p : Fin 5 → ℕ) : Prop :=
  if j = 0 then
    (8639 : ℝ) / 50000 ≤ Real.logb x (p 3 : ℝ) ∧
    Real.logb x (p 3 : ℝ) < Real.logb x (p 2 : ℝ) ∧
    Real.logb x (p 2 : ℝ) < Real.logb x (p 1 : ℝ) ∧
    Real.logb x (p 1 : ℝ) < Real.logb x (p 0 : ℝ) ∧
    Real.logb x (p 0 : ℝ) < (41361 : ℝ) / 100000 ∧
    Real.logb x (p 0 : ℝ) + Real.logb x (p 1 : ℝ) < (41361 : ℝ) / 100000 ∧
    (p 3 : ℝ) ≤ (p 4 : ℝ)
  else
    [p 0, p 1, p 2] ∈ siftedPrimeTuples x (5 : Fin 6) ∧
    x ^ ((8639 : ℝ) / 50000) ≤ (p 3 : ℝ) ∧ (p 3 : ℝ) ≤ (p 4 : ℝ)

def fivePairCaps (x : ℝ) (p : Fin 5 → ℕ) : Prop :=
  ∀ i k : Fin 5, i < k → (p i : ℝ) * (p k : ℝ) < x ^ ((41361 : ℝ) / 100000)

open Classical in
def sourceFiveTuples (x : ℝ) (n : ℕ) (j : Fin 2) : Finset (Fin 5 → ℕ) :=
  (Fintype.piFinset (fun _ : Fin 5 => Nat.primesLE n)).filter
    (fun p => (∏ i, p i) = n ∧ sourceFiveOrder x j p)

open Classical in
def sourceFiveEligible (x : ℝ) (n : ℕ) (j : Fin 2) : Finset (Fin 5 → ℕ) :=
  (sourceFiveTuples x n j).filter (fun p => Function.Injective p ∧ ¬ fivePairCaps x p)

open Classical in
def sourceFiveCollision (x : ℝ) (n : ℕ) (j : Fin 2) : Finset (Fin 5 → ℕ) :=
  (sourceFiveTuples x n j).filter (fun p => ¬ Function.Injective p)

theorem sourceFiveTuples_mem {x : ℝ} {n : ℕ} {j : Fin 2} {p : Fin 5 → ℕ} :
    p ∈ sourceFiveTuples x n j ↔
      (∀ i, (p i).Prime) ∧ (∏ i, p i) = n ∧ sourceFiveOrder x j p := by
  classical
  simp only [sourceFiveTuples, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hp, hn, ho⟩
    exact ⟨fun i => Nat.prime_of_mem_primesLE (hp i), hn, ho⟩
  · rintro ⟨hp, hn, ho⟩
    refine ⟨?_, hn, ho⟩
    intro i
    apply Nat.mem_primesLE.mpr
    refine ⟨?_, hp i⟩
    have hnpos : 0 < n := hn ▸ Finset.prod_pos (fun k _ => (hp k).pos)
    exact Nat.le_of_dvd hnpos (hn ▸ Finset.dvd_prod_of_mem p (Finset.mem_univ i))

private theorem prime_log_lt_iff {x : ℝ} (hx : 1 < x) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) :
    Real.logb x (p : ℝ) < Real.logb x (q : ℝ) ↔ p < q := by
  rw [lt_iff_not_ge, Real.logb_le_logb hx (Nat.cast_pos.mpr hq.pos)
    (Nat.cast_pos.mpr hp.pos), Nat.cast_le, not_le]

theorem sourceFiveOrder_rough {x : ℝ} (hx : 1 < x) (j : Fin 2)
    (p : Fin 5 → ℕ) (hp : ∀ i, (p i).Prime) (ho : sourceFiveOrder x j p) :
    ∀ i, x ^ ((8639 : ℝ) / 50000) ≤ (p i : ℝ) := by
  have hlo (i : Fin 5) (h : (8639 : ℝ) / 50000 ≤ Real.logb x (p i : ℝ)) :
      x ^ ((8639 : ℝ) / 50000) ≤ (p i : ℝ) :=
    (Real.le_logb_iff_rpow_le hx (Nat.cast_pos.mpr (hp i).pos)).mp h
  fin_cases j
  · simp only [sourceFiveOrder] at ho
    obtain ⟨h3, h32, h21, h10, _, _, h34⟩ := ho
    intro i
    fin_cases i
    · exact hlo 0 (by linarith only [h3, h32, h21, h10])
    · exact hlo 1 (by linarith only [h3, h32, h21])
    · exact hlo 2 (by linarith only [h3, h32])
    · exact hlo 3 h3
    · exact (hlo 3 h3).trans h34
  · simp only [sourceFiveOrder] at ho
    obtain ⟨hm, h3, h34⟩ := ho
    have ht := (mem_siftedPrimeTuples_iff x hx (5 : Fin 6) [p 0, p 1, p 2]).mp hm
    dsimp only at ht
    obtain ⟨_, _, _, h1, h10, _, h12, _, _⟩ := ht
    intro i
    fin_cases i
    · exact hlo 0 (by linarith only [h1, h10])
    · exact hlo 1 h1
    · exact hlo 2 (by linarith only [h1, h12])
    · exact h3
    · exact h3.trans h34

theorem sourceFiveOrder_of_sharp {x : ℝ} (hx : 1 < x) (j : Fin 2)
    (p : Fin 5 → ℕ) (hp : ∀ i, (p i).Prime)
    (hprod : x ≤ (∏ i, (p i : ℝ))) (hc : fivePairCaps x p)
    (ho : sharpResidualOrder j p) : sourceFiveOrder x j p := by
  have hsum := five_prime_log_sum x hx p hp rfl (by simpa only [Nat.cast_prod] using hprod)
  have hpair := five_prime_log_pair x ((41361 : ℝ) / 100000) hx p hp hc
  have hg := five_pair_bounds_geometry ((41361 : ℝ) / 100000)
    (fun i => Real.logb x (p i : ℝ)) hsum hpair
  have hlo (i : Fin 5) : (8639 : ℝ) / 50000 ≤ Real.logb x (p i : ℝ) := by
    have hh := (hg i).1
    linarith only [hh]
  have hhi (i : Fin 5) : Real.logb x (p i : ℝ) < (23698 : ℝ) / 100000 := by
    have hh := (hg i).2
    linarith only [hh]
  have hlog (i k : Fin 5) := prime_log_lt_iff hx (hp i) (hp k)
  fin_cases j
  · simp only [sourceFiveOrder, sharpResidualOrder] at ho ⊢
    exact ⟨hlo 3, (hlog 3 2).mpr ho.1, (hlog 2 1).mpr ho.2.1,
      (hlog 1 0).mpr ho.2.2.1, (hhi 0).trans (by norm_num),
      hpair 0 1 (by decide), Nat.cast_le.mpr ho.2.2.2.le⟩
  · simp only [sourceFiveOrder, sharpResidualOrder] at ho ⊢
    refine ⟨?_, (Real.le_logb_iff_rpow_le hx (Nat.cast_pos.mpr (hp 3).pos)).mp (hlo 3),
      Nat.cast_le.mpr ho.2.2.le⟩
    apply (mem_siftedPrimeTuples_iff x hx (5 : Fin 6) [p 0, p 1, p 2]).mpr
    dsimp only
    refine ⟨hp 0, hp 1, hp 2, hlo 1, (hlog 1 0).mpr ho.1,
      (hhi 0).trans (by norm_num), ((hlog 1 2).mpr ho.2.1).le,
      hpair 1 2 (by decide), ?_⟩
    convert hhi 0 using 1
    norm_num

theorem sharpResidualOrder_of_source {x : ℝ} (hx : 1 < x) (j : Fin 2)
    (p : Fin 5 → ℕ) (hp : ∀ i, (p i).Prime)
    (hi : Function.Injective p) (ho : sourceFiveOrder x j p) : sharpResidualOrder j p := by
  have hlog (i k : Fin 5) := prime_log_lt_iff hx (hp i) (hp k)
  have hne (i k : Fin 5) (hik : i ≠ k) : p i ≠ p k := fun h => hik (hi h)
  fin_cases j
  · simp only [sourceFiveOrder, sharpResidualOrder] at ho ⊢
    exact ⟨(hlog 3 2).mp ho.2.1, (hlog 2 1).mp ho.2.2.1,
      (hlog 1 0).mp ho.2.2.2.1,
      lt_of_le_of_ne (Nat.cast_le.mp ho.2.2.2.2.2.2) (hne 3 4 (by decide))⟩
  · simp only [sourceFiveOrder, sharpResidualOrder] at ho ⊢
    have ht := (mem_siftedPrimeTuples_iff x hx (5 : Fin 6) [p 0, p 1, p 2]).mp ho.1
    dsimp only at ht
    obtain ⟨_, _, _, _, h10, _, h12, _, _⟩ := ht
    have h12' : p 1 ≤ p 2 := by
      exact Nat.cast_le.mp ((Real.logb_le_logb hx
        (Nat.cast_pos.mpr (hp 1).pos) (Nat.cast_pos.mpr (hp 2).pos)).mp h12)
    exact ⟨(hlog 1 0).mp h10, lt_of_le_of_ne h12' (hne 1 2 (by decide)),
      lt_of_le_of_ne (Nat.cast_le.mp ho.2.2) (hne 3 4 (by decide))⟩

open Classical in
theorem sharpResidualTuples_eq_source_filter {x : ℝ} (hx : 1 < x)
    (n : ℕ) (hxn : x ≤ (n : ℝ)) (j : Fin 2) :
    sharpResidualTuples x (41361 / 100000) n j =
      (sourceFiveTuples x n j).filter (fun p => Function.Injective p ∧ fivePairCaps x p) := by
  classical
  ext p
  simp only [sharpResidualTuples_mem, Finset.mem_filter, sourceFiveTuples_mem]
  constructor
  · rintro ⟨hp, hi, hn, hc, ho⟩
    have hprod : x ≤ ∏ i, (p i : ℝ) := by simpa only [← Nat.cast_prod, hn] using hxn
    exact ⟨⟨hp, hn, sourceFiveOrder_of_sharp hx j p hp hprod hc ho⟩, hi, hc⟩
  · rintro ⟨⟨hp, hn, ho⟩, hi, hc⟩
    exact ⟨hp, hi, hn, hc, sharpResidualOrder_of_source hx j p hp hi ho⟩

theorem sourceFiveEligible_mem {x : ℝ} {n : ℕ} {j : Fin 2} {p : Fin 5 → ℕ} :
    p ∈ sourceFiveEligible x n j ↔ p ∈ sourceFiveTuples x n j ∧ Function.Injective p ∧
      ∃ i k : Fin 5, i < k ∧ x ^ ((41361 : ℝ) / 100000) ≤ (p i : ℝ) * (p k : ℝ) := by
  classical
  simp only [sourceFiveEligible, Finset.mem_filter, fivePairCaps, not_forall,
    not_lt, exists_prop]

theorem sourceFive_card_split {x : ℝ} (hx : 1 < x) (n : ℕ)
    (hxn : x ≤ (n : ℝ)) (j : Fin 2) :
    (sourceFiveTuples x n j).card = (sharpResidualTuples x (41361 / 100000) n j).card +
      (sourceFiveEligible x n j).card + (sourceFiveCollision x n j).card := by
  classical
  rw [sharpResidualTuples_eq_source_filter hx n hxn j]
  have h1 := Finset.card_filter_add_card_filter_not (s := sourceFiveTuples x n j)
    (p := fun p => Function.Injective p)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (sourceFiveTuples x n j).filter (fun p => Function.Injective p))
    (p := fivePairCaps x)
  simp only [Finset.filter_filter] at h2
  change (sourceFiveTuples x n j).card = _ + _ + _
  dsimp only [sourceFiveEligible, sourceFiveCollision]
  omega

theorem sourceFiveTuples_card_source {x : ℝ} (hx : 1 < x)
    (hg : 2 * x < x ^ (6 * ((8639 : ℝ) / 50000)))
    (n : ℕ) (hxn : x ≤ (n : ℝ)) (hnx : (n : ℝ) ≤ 2 * x) (j : Fin 2) :
    ((sourceFiveTuples x n j).card : ℝ) = if j = 0 then sourceT5 x n else sourceU3 x n := by
  classical
  fin_cases j
  · change ((sourceFiveTuples x n 0).card : ℝ) = sourceT5 x n
    rw [sourceT5_eq_five hx hg hxn hnx]
    simp [sourceFiveTuples, sourceFiveOrder, Finset.sum_boole]
  · change ((sourceFiveTuples x n 1).card : ℝ) = sourceU3 x n
    rw [sourceU3_eq_five_prime_sum x hx n]
    simp [sourceFiveTuples, sourceFiveOrder, Finset.sum_boole]

theorem sharp_residual_source_difference {x : ℝ} (hx : 1 < x)
    (hg : 2 * x < x ^ (6 * ((8639 : ℝ) / 50000)))
    (n : ℕ) (hxn : x ≤ (n : ℝ)) (hnx : (n : ℝ) ≤ 2 * x) (j : Fin 2) :
    (if j = 0 then sourceT5 x n else sourceU3 x n) - sharpResidualCount x j n =
      (sourceFiveEligible x n j).card + (sourceFiveCollision x n j).card := by
  rw [← sourceFiveTuples_card_source hx hg n hxn hnx j, sourceFive_card_split hx n hxn j]
  simp only [Nat.cast_add, sharpResidualCount]
  ring

#print axioms sourceFiveOrder_rough
#print axioms sharpResidualTuples_eq_source_filter
#print axioms sourceFive_card_split
#print axioms sharp_residual_source_difference

end PrimeGap182Analytic.Harman
