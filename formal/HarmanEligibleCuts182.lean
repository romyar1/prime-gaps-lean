import HarmanResidualGeometry182

/-! Exact Boolean description of the actual eligible five-prime tuples.
The 32 cuts consist of nineteen directed coordinate comparisons, all ten
unordered pair caps, the two product endpoints, and the U3 coordinate cap.
The omitted comparison p₀ < p₁ is false on both source regions. No choice
of an eligible pair is made, so a tuple with several eligible pairs is
counted exactly once. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

def eligibleOrderPairs : Finset (Fin 5 × Fin 5) :=
  Finset.univ.filter (fun ik => ik.1 ≠ ik.2 ∧ ik ≠ (0, 1))

theorem eligibleOrderPairs_card : eligibleOrderPairs.card = 19 := by decide

def eligibleOrderCut (ik : Fin 5 × Fin 5) : MinorantMonomialCut :=
  ⟨{ik.1}, {ik.2}, 1, false, true⟩

def eligiblePairCut (x : ℝ) (ik : Fin 5 × Fin 5) : MinorantMonomialCut :=
  ⟨{ik.1, ik.2}, ∅, x ^ ((41361 : ℝ) / 100000), false, true⟩

open Classical in
def sourceFiveEligibleMonomialCuts (x : ℝ) : Finset MinorantMonomialCut :=
  (eligibleOrderPairs.image eligibleOrderCut ∪ fivePairs.image (eligiblePairCut x)) ∪
    {⟨Finset.univ, ∅, x, true, false⟩,
      ⟨Finset.univ, ∅, 2 * x, false, false⟩,
      ⟨{0}, ∅, x ^ ((23698 : ℝ) / 100000), false, true⟩}

theorem sourceFiveEligibleMonomialCuts_card_le (x : ℝ) :
    (sourceFiveEligibleMonomialCuts x).card ≤ 32 := by
  classical
  calc
    _ ≤ (eligibleOrderPairs.image eligibleOrderCut ∪
        fivePairs.image (eligiblePairCut x)).card + 3 :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_le_three _)
    _ ≤ (eligibleOrderPairs.card + fivePairs.card) + 3 := by
      exact Nat.add_le_add_right ((Finset.card_union_le _ _).trans
        (Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le))) _
    _ = 32 := by rw [eligibleOrderPairs_card, fivePairs_card]

theorem sourceFiveEligibleMonomialCuts_data (x : ℝ) (hx : 0 < x)
    (d : MinorantMonomialCut) (hd : d ∈ sourceFiveEligibleMonomialCuts x) :
    d.numerator.Nonempty ∧ Disjoint d.numerator d.denominator ∧
      d.numerator.card + d.denominator.card ≤ 5 ∧ 0 < d.threshold := by
  classical
  simp only [sourceFiveEligibleMonomialCuts, Finset.mem_union] at hd
  rcases hd with (hd | hd) | hd
  · obtain ⟨ik, hik, rfl⟩ := Finset.mem_image.mp hd
    have hne := (Finset.mem_filter.mp hik).2.1
    simp [eligibleOrderCut, hne]
  · obtain ⟨ik, hik, rfl⟩ := Finset.mem_image.mp hd
    have hne := ne_of_lt ((mem_fivePairs _ _).mp hik)
    simp [eligiblePairCut, Finset.card_pair hne, Real.rpow_pos_of_pos hx]
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl <;>
      norm_num [Finset.card_fin] <;> positivity

def eligibleCutTest (d : MinorantMonomialCut) (p : Fin 5 → ℕ) : Prop :=
  if d.lower then
    if d.strict then d.threshold < d.value p else d.threshold ≤ d.value p
  else if d.strict then d.value p < d.threshold else d.value p ≤ d.threshold

def sourceFiveEligiblePredicate (x : ℝ) (j : Fin 2) (p : Fin 5 → ℕ) : Prop :=
  (∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧ sourceFiveOrder x j p ∧
    Function.Injective p ∧ ¬ fivePairCaps x p

def sourceFiveSharpPredicate (x : ℝ) (j : Fin 2) (p : Fin 5 → ℕ) : Prop :=
  (∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧ sourceFiveOrder x j p ∧
    Function.Injective p ∧ fivePairCaps x p

private theorem sourceFiveOrder_physical {x : ℝ} (hx : 1 < x)
    (j : Fin 2) (p : Fin 5 → ℕ) (hp : ∀ i, (p i).Prime)
    (hlo : ∀ i, x ^ ((8639 : ℝ) / 50000) ≤ (p i : ℝ))
    (hhi : ∀ i, (p i : ℝ) ≤ x ^ ((31 : ℝ) / 100)) :
    sourceFiveOrder x j p ↔
      if j = 0 then
        p 3 < p 2 ∧ p 2 < p 1 ∧ p 1 < p 0 ∧
          (p 0 : ℝ) * p 1 < x ^ ((41361 : ℝ) / 100000) ∧ p 3 ≤ p 4
      else
        p 1 < p 0 ∧ p 1 ≤ p 2 ∧
          (p 1 : ℝ) * p 2 < x ^ ((41361 : ℝ) / 100000) ∧
          (p 0 : ℝ) < x ^ ((23698 : ℝ) / 100000) ∧ p 3 ≤ p 4 := by
  have hpos (i : Fin 5) : 0 < (p i : ℝ) := Nat.cast_pos.mpr (hp i).pos
  have hloglo (i : Fin 5) : (8639 : ℝ) / 50000 ≤ Real.logb x (p i : ℝ) :=
    (Real.le_logb_iff_rpow_le hx (hpos i)).mpr (hlo i)
  have hloghi (i : Fin 5) : Real.logb x (p i : ℝ) < (41361 : ℝ) / 100000 := by
    apply (Real.logb_lt_iff_lt_rpow hx (hpos i)).mpr
    exact (hhi i).trans_lt (Real.rpow_lt_rpow_of_exponent_lt hx (by norm_num))
  have hlt (i k : Fin 5) :
      (Real.logb x (p i : ℝ) < Real.logb x (p k : ℝ)) ↔ p i < p k := by
    rw [Real.logb_lt_logb_iff hx (hpos i) (hpos k), Nat.cast_lt]
  have hle (i k : Fin 5) :
      (Real.logb x (p i : ℝ) ≤ Real.logb x (p k : ℝ)) ↔ p i ≤ p k := by
    rw [Real.logb_le_logb hx (hpos i) (hpos k), Nat.cast_le]
  have hpair (i k : Fin 5) :
      Real.logb x (p i : ℝ) + Real.logb x (p k : ℝ) < (41361 : ℝ) / 100000 ↔
        (p i : ℝ) * p k < x ^ ((41361 : ℝ) / 100000) := by
    rw [← Real.logb_mul (hpos i).ne' (hpos k).ne',
      Real.logb_lt_iff_lt_rpow hx (mul_pos (hpos i) (hpos k))]
  by_cases hj : j = 0
  · simp only [sourceFiveOrder, hj, ite_true, hloglo, true_and, hlt, hloghi, hpair,
      Nat.cast_le]
  · simp only [sourceFiveOrder, hj, ite_false]
    have hm := mem_siftedPrimeTuples_iff x hx (5 : Fin 6) [p 0, p 1, p 2]
    change ([p 0, p 1, p 2] ∈ siftedPrimeTuples x (5 : Fin 6) ↔
      (p 0).Prime ∧ (p 1).Prime ∧ (p 2).Prime ∧
      (8639 : ℝ) / 50000 ≤ Real.logb x (p 1 : ℝ) ∧
      Real.logb x (p 1 : ℝ) < Real.logb x (p 0 : ℝ) ∧
      Real.logb x (p 0 : ℝ) < (41361 : ℝ) / 100000 ∧
      Real.logb x (p 1 : ℝ) ≤ Real.logb x (p 2 : ℝ) ∧
      Real.logb x (p 1 : ℝ) + Real.logb x (p 2 : ℝ) < (41361 : ℝ) / 100000 ∧
      Real.logb x (p 0 : ℝ) < 1 - (34941 : ℝ) / 100000 - 41361 / 100000) at hm
    rw [hm]
    have hz : 1 - (34941 : ℝ) / 100000 - 41361 / 100000 = 23698 / 100000 := by
      norm_num
    simp only [hp, hloglo, hloghi, hlo, true_and, hlt, hle, hpair, hz,
      Real.logb_lt_iff_lt_rpow hx (hpos 0), Nat.cast_le]
    tauto

theorem sourceFiveEligibleMonomialCuts_boolean_components (x : ℝ) (hx : 1 < x)
    (j : Fin 2) (p q : Fin 5 → ℕ)
    (hp : ∀ i, (p i).Prime) (hq : ∀ i, (q i).Prime)
    (hplo : ∀ i, x ^ ((8639 : ℝ) / 50000) ≤ (p i : ℝ))
    (hqlo : ∀ i, x ^ ((8639 : ℝ) / 50000) ≤ (q i : ℝ))
    (hphi : ∀ i, (p i : ℝ) ≤ x ^ ((31 : ℝ) / 100))
    (hqhi : ∀ i, (q i : ℝ) ≤ x ^ ((31 : ℝ) / 100))
    (htests : ∀ d ∈ sourceFiveEligibleMonomialCuts x,
      eligibleCutTest d p ↔ eligibleCutTest d q) :
    (((∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧
        sourceFiveOrder x j p ∧ Function.Injective p) ↔
      ((∏ i, q i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧
        sourceFiveOrder x j q ∧ Function.Injective q)) ∧
      (fivePairCaps x p ↔ fivePairCaps x q) := by
  classical
  have hposp (i : Fin 5) : 0 < (p i : ℝ) := Nat.cast_pos.mpr (hp i).pos
  have hposq (i : Fin 5) : 0 < (q i : ℝ) := Nat.cast_pos.mpr (hq i).pos
  have horder (i k : Fin 5) (hik : i ≠ k) (hex : (i, k) ≠ (0, 1)) :
      p i < p k ↔ q i < q k := by
    have hm : eligibleOrderCut (i, k) ∈ sourceFiveEligibleMonomialCuts x := by
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨(i, k), by simp [eligibleOrderPairs, hik, hex], rfl⟩
    have ht := htests _ hm
    simpa only [eligibleCutTest, eligibleOrderCut, MinorantMonomialCut.value,
      Bool.false_eq_true, ite_true, ite_false, Finset.prod_singleton,
      div_lt_one (hposp k), div_lt_one (hposq k), Nat.cast_lt] using ht
  have hpair (i k : Fin 5) (hik : i < k) :
      (p i : ℝ) * p k < x ^ ((41361 : ℝ) / 100000) ↔
        (q i : ℝ) * q k < x ^ ((41361 : ℝ) / 100000) := by
    have hm : eligiblePairCut x (i, k) ∈ sourceFiveEligibleMonomialCuts x := by
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(i, k), (mem_fivePairs _ _).mpr hik, rfl⟩
    simpa only [eligibleCutTest, eligiblePairCut, MinorantMonomialCut.value,
      Bool.false_eq_true, ite_true, ite_false, Finset.prod_pair (ne_of_lt hik),
      Finset.prod_empty, div_one] using htests _ hm
  have hz : (p 0 : ℝ) < x ^ ((23698 : ℝ) / 100000) ↔
      (q 0 : ℝ) < x ^ ((23698 : ℝ) / 100000) := by
    have hm : (⟨{0}, ∅, x ^ ((23698 : ℝ) / 100000), false, true⟩ :
        MinorantMonomialCut) ∈ sourceFiveEligibleMonomialCuts x := by
      apply Finset.mem_union_right
      simp
    simpa only [eligibleCutTest, MinorantMonomialCut.value, Bool.false_eq_true,
      ite_true, ite_false, Finset.prod_singleton, Finset.prod_empty, div_one]
      using htests _ hm
  have hcarrier : ((∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊) ↔
      ((∏ i, q i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊) := by
    have hmlo : (⟨Finset.univ, ∅, x, true, false⟩ : MinorantMonomialCut) ∈
        sourceFiveEligibleMonomialCuts x := Finset.mem_union_right _ (by simp)
    have hmhi : (⟨Finset.univ, ∅, 2 * x, false, false⟩ : MinorantMonomialCut) ∈
        sourceFiveEligibleMonomialCuts x := Finset.mem_union_right _ (by simp)
    have hlow := htests _ hmlo
    have hhigh := htests _ hmhi
    simp only [eligibleCutTest, MinorantMonomialCut.value, Bool.false_eq_true,
      ite_true, ite_false, Finset.prod_empty, div_one] at hlow hhigh
    rw [Finset.mem_Icc, Finset.mem_Icc, Nat.ceil_le, Nat.ceil_le,
      Nat.le_floor_iff (by positivity : 0 ≤ 2 * x),
      Nat.le_floor_iff (by positivity : 0 ≤ 2 * x)]
    simp only [Nat.cast_prod]
    exact and_congr hlow hhigh
  have hsource : sourceFiveOrder x j p ↔ sourceFiveOrder x j q := by
    rw [sourceFiveOrder_physical hx j p hp hplo hphi,
      sourceFiveOrder_physical hx j q hq hqlo hqhi]
    have h32 := horder 3 2 (by decide) (by decide)
    have h21 := horder 2 1 (by decide) (by decide)
    have h10 := horder 1 0 (by decide) (by decide)
    have h43 := horder 4 3 (by decide) (by decide)
    have h34 : p 3 ≤ p 4 ↔ q 3 ≤ q 4 := by simpa only [not_lt] using not_congr h43
    have h12 : p 1 ≤ p 2 ↔ q 1 ≤ q 2 := by simpa only [not_lt] using not_congr h21
    by_cases hj : j = 0
    · simp only [hj, ite_true]
      exact and_congr h32 (and_congr h21 (and_congr h10
        (and_congr (hpair 0 1 (by decide)) h34)))
    · simp only [hj, ite_false]
      exact and_congr h10 (and_congr h12 (and_congr (hpair 1 2 (by decide))
        (and_congr hz h34)))
  have hcaps : fivePairCaps x p ↔ fivePairCaps x q :=
    forall_congr' fun i => forall_congr' fun k => imp_congr_right fun hik => hpair i k hik
  have h10of (r : Fin 5 → ℕ) (hr : ∀ i, (r i).Prime)
      (hrlo : ∀ i, x ^ ((8639 : ℝ) / 50000) ≤ (r i : ℝ))
      (hrhi : ∀ i, (r i : ℝ) ≤ x ^ ((31 : ℝ) / 100))
      (hs : sourceFiveOrder x j r) : r 1 < r 0 := by
    rw [sourceFiveOrder_physical hx j r hr hrlo hrhi] at hs
    split_ifs at hs
    · exact hs.2.2.1
    · exact hs.1
  have hinjective (hs : sourceFiveOrder x j p) (hsq : sourceFiveOrder x j q) :
      Function.Injective p ↔ Function.Injective q := by
    have hp10 := h10of p hp hplo hphi hs
    have hq10 := h10of q hq hqlo hqhi hsq
    have hall (i k : Fin 5) : p i < p k ↔ q i < q k := by
      by_cases hik : i = k
      · subst k; simp
      by_cases hex : (i, k) = (0, 1)
      · have hi : i = 0 := congrArg Prod.fst hex
        have hk : k = 1 := congrArg Prod.snd hex
        subst i; subst k
        exact iff_of_false (not_lt_of_ge hp10.le) (not_lt_of_ge hq10.le)
      exact horder i k hik hex
    have heq (i k : Fin 5) : p i = p k ↔ q i = q k := by
      rw [le_antisymm_iff, le_antisymm_iff, ← not_lt, ← not_lt, ← not_lt, ← not_lt]
      exact and_congr (not_congr (hall k i)) (not_congr (hall i k))
    constructor
    · intro hi i k he
      exact hi ((heq i k).mpr he)
    · intro hi i k he
      exact hi ((heq i k).mp he)
  refine ⟨?_, hcaps⟩
  constructor
  · rintro ⟨hc, hs, hi⟩
    have hsq := hsource.mp hs
    exact ⟨hcarrier.mp hc, hsq, (hinjective hs hsq).mp hi⟩
  · rintro ⟨hc, hs, hi⟩
    have hsp := hsource.mpr hs
    exact ⟨hcarrier.mpr hc, hsp, (hinjective hsp hs).mpr hi⟩

theorem sourceFiveEligibleMonomialCuts_boolean (x : ℝ) (hx : 1 < x)
    (j : Fin 2) (p q : Fin 5 → ℕ)
    (hp : ∀ i, (p i).Prime) (hq : ∀ i, (q i).Prime)
    (hplo : ∀ i, x ^ ((8639 : ℝ) / 50000) ≤ (p i : ℝ))
    (hqlo : ∀ i, x ^ ((8639 : ℝ) / 50000) ≤ (q i : ℝ))
    (hphi : ∀ i, (p i : ℝ) ≤ x ^ ((31 : ℝ) / 100))
    (hqhi : ∀ i, (q i : ℝ) ≤ x ^ ((31 : ℝ) / 100))
    (htests : ∀ d ∈ sourceFiveEligibleMonomialCuts x,
      eligibleCutTest d p ↔ eligibleCutTest d q) :
    sourceFiveEligiblePredicate x j p ↔ sourceFiveEligiblePredicate x j q := by
  obtain ⟨hd, hc⟩ := sourceFiveEligibleMonomialCuts_boolean_components x hx j p q
    hp hq hplo hqlo hphi hqhi htests
  simpa only [sourceFiveEligiblePredicate, and_assoc] using and_congr hd (not_congr hc)

theorem sourceFiveSharpMonomialCuts_boolean (x : ℝ) (hx : 1 < x)
    (j : Fin 2) (p q : Fin 5 → ℕ)
    (hp : ∀ i, (p i).Prime) (hq : ∀ i, (q i).Prime)
    (hplo : ∀ i, x ^ ((8639 : ℝ) / 50000) ≤ (p i : ℝ))
    (hqlo : ∀ i, x ^ ((8639 : ℝ) / 50000) ≤ (q i : ℝ))
    (hphi : ∀ i, (p i : ℝ) ≤ x ^ ((31 : ℝ) / 100))
    (hqhi : ∀ i, (q i : ℝ) ≤ x ^ ((31 : ℝ) / 100))
    (htests : ∀ d ∈ sourceFiveEligibleMonomialCuts x,
      eligibleCutTest d p ↔ eligibleCutTest d q) :
    sourceFiveSharpPredicate x j p ↔ sourceFiveSharpPredicate x j q := by
  obtain ⟨hd, hc⟩ := sourceFiveEligibleMonomialCuts_boolean_components x hx j p q
    hp hq hplo hqlo hphi hqhi htests
  simpa only [sourceFiveSharpPredicate, and_assoc] using and_congr hd hc

#print axioms sourceFiveEligibleMonomialCuts_card_le
#print axioms sourceFiveEligibleMonomialCuts_data
#print axioms sourceFiveEligibleMonomialCuts_boolean
#print axioms sourceFiveSharpMonomialCuts_boolean

end PrimeGap182Analytic.Harman
