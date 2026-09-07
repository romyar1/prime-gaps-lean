import PrimeGaps186

/-! Elementary progression bounds for coefficients supported on large
square divisors. These estimates use the literal square-divisor support
and primitive residues; no distribution theorem is an input. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186 Classical

namespace PrimeGap182Analytic

private theorem squareCRT_ite_classical {α : Sort*} (p : Prop) (d : Decidable p) (a b : α) :
    @ite α p d a b = @ite α p (Classical.propDecidable p) a b := by
  have hd : d = Classical.propDecidable p := Subsingleton.elim _ _
  cases hd
  rfl

private theorem squareCRT_filter_classical {α : Type*} (p : α → Prop) (d : DecidablePred p)
    (s : Finset α) :
    @Finset.filter α p d s = @Finset.filter α p (fun a => Classical.propDecidable (p a)) s := by
  have hd : d = (fun a => Classical.propDecidable (p a)) := Subsingleton.elim _ _
  cases hd
  rfl

theorem multiplier_progression_count_le (q a m M : ℕ) (ha : Nat.Coprime a q) :
    ({t ∈ Finset.Icc 1 M | Nat.ModEq q (m * t) a}.card : ℝ) ≤
      (M : ℝ) / (q : ℝ) + 1 := by
  classical
  have hcard : {t ∈ Finset.Icc 1 M | Nat.ModEq q (m * t) a}.card ≤ M / q + 1 := by
    calc
      _ ≤ (Finset.Icc 0 (M / q)).card := by
        apply Finset.card_le_card_of_injOn (fun t : ℕ => t / q)
        · intro t ht
          exact Finset.mem_Icc.mpr ⟨Nat.zero_le _,
            Nat.div_le_div_right (Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1).2⟩
        · intro t ht u hu heq
          have htmod := (Finset.mem_filter.mp ht).2
          have humod := (Finset.mem_filter.mp hu).2
          have hmt : Nat.Coprime (m * t) q := htmod.gcd_eq.trans ha
          exact Nat.ext_div_modEq heq (Nat.ModEq.cancel_left_of_coprime
            hmt.coprime_mul_right.symm (htmod.trans humod.symm))
      _ = M / q + 1 := by simp
  calc
    _ ≤ ((M / q + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ _ := by
      push_cast
      linarith only [Nat.cast_div_le (m := M) (n := q) (α := ℝ)]

theorem square_progression_count_le (N p q a : ℕ) (hp : 0 < p)
    (ha : Nat.Coprime a q) :
    ({n ∈ Finset.Icc 1 N | p ^ 2 ∣ n ∧ Nat.ModEq q n a}.card : ℝ) ≤
      (N : ℝ) / (p : ℝ) ^ 2 / (q : ℝ) + 1 := by
  classical
  have hp2 : 0 < p ^ 2 := pow_pos hp 2
  have hsub : {n ∈ Finset.Icc 1 N | p ^ 2 ∣ n ∧ Nat.ModEq q n a}.card ≤
      {t ∈ Finset.Icc 1 (N / p ^ 2) | Nat.ModEq q (p ^ 2 * t) a}.card := by
    apply Finset.card_le_card_of_injOn (fun n : ℕ => n / p ^ 2)
    · intro n hn
      obtain ⟨hnI, hdiv, hmod⟩ := Finset.mem_filter.mp hn
      have heq : p ^ 2 * (n / p ^ 2) = n := Nat.mul_div_cancel' hdiv
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_,
        Nat.div_le_div_right (Finset.mem_Icc.mp hnI).2⟩, ?_⟩
      · have hnpos := (Finset.mem_Icc.mp hnI).1
        have hpos : 0 < n / p ^ 2 := by
          by_contra hh
          have hz : n / p ^ 2 = 0 := Nat.eq_zero_of_not_pos hh
          simp only [hz, mul_zero] at heq
          omega
        exact hpos
      · simpa only [heq] using hmod
    · intro n hn k hk heq
      have hn' := Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2.1
      have hk' := Nat.mul_div_cancel' (Finset.mem_filter.mp hk).2.1
      exact hn'.symm.trans ((congrArg (fun t => p ^ 2 * t) heq).trans hk')
  calc
    _ ≤ ({t ∈ Finset.Icc 1 (N / p ^ 2) | Nat.ModEq q (p ^ 2 * t) a}.card : ℝ) := by
      exact_mod_cast hsub
    _ ≤ ((N / p ^ 2 : ℕ) : ℝ) / (q : ℝ) + 1 :=
      multiplier_progression_count_le q a (p ^ 2) (N / p ^ 2) ha
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg q)
      have hh := (Nat.cast_div_le (m := N) (n := p ^ 2) (α := ℝ))
      rw [Nat.cast_pow] at hh
      exact hh

theorem square_divisor_count_le (N p : ℕ) (hp : 0 < p) :
    ({n ∈ Finset.Icc 1 N | p ^ 2 ∣ n}.card : ℝ) ≤ (N : ℝ) / (p : ℝ) ^ 2 + 1 := by
  simpa only [Nat.ModEq, Nat.mod_one, and_true, Nat.cast_one, div_one] using
    square_progression_count_le N p 1 0 hp (by decide)

open Classical in
theorem square_supported_mask_mass_le (N : ℕ) (D : Finset ℕ) (U : ℝ) (hU : 0 ≤ U)
    (e : ℕ → ℂ) (hb : ∀ n ∈ Finset.Icc 1 N, ‖e n‖ ≤ U)
    (hs : ∀ n ∈ Finset.Icc 1 N, e n ≠ 0 → ∃ p ∈ D, p ^ 2 ∣ n)
    (c : ℕ → Prop) :
    (∑ n ∈ Finset.Icc 1 N, if c n then ‖e n‖ else 0) ≤
      U * ∑ p ∈ D, ({n ∈ Finset.Icc 1 N | p ^ 2 ∣ n ∧ c n}.card : ℝ) := by
  have hg (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      ‖e n‖ ≤ U * ∑ p ∈ D, if p ^ 2 ∣ n then (1 : ℝ) else 0 := by
    by_cases he : e n = 0
    · rw [he, norm_zero]
      positivity
    · obtain ⟨p, hp, hdiv⟩ := hs n hn he
      have hh : (1 : ℝ) ≤ ∑ p ∈ D, if p ^ 2 ∣ n then (1 : ℝ) else 0 := by
        rw [Finset.sum_boole]
        exact_mod_cast Finset.one_le_card.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hdiv⟩⟩
      exact (hb n hn).trans (le_mul_of_one_le_right hU hh)
  calc
    _ = ∑ n ∈ (Finset.Icc 1 N).filter c, ‖e n‖ := (Finset.sum_filter _ _).symm
    _ ≤ ∑ n ∈ (Finset.Icc 1 N).filter c,
        U * ∑ p ∈ D, if p ^ 2 ∣ n then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun n hn => hg n (Finset.mem_filter.mp hn).1)
    _ = U * ∑ p ∈ D, ({n ∈ Finset.Icc 1 N | p ^ 2 ∣ n ∧ c n}.card : ℝ) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      simp only [Finset.sum_boole, Finset.filter_filter, and_comm]

theorem square_supported_fullDiscrepancy_le
    (N : ℕ) (D : Finset ℕ) (hD : ∀ p ∈ D, 0 < p) (U : ℝ) (hU : 0 ≤ U)
    (e : ℕ → ℂ) (hb : ∀ n ∈ Finset.Icc 1 N, ‖e n‖ ≤ U)
    (hs : ∀ n ∈ Finset.Icc 1 N, e n ≠ 0 → ∃ p ∈ D, p ^ 2 ∣ n)
    (q a : ℕ) (hq : 0 < q) (ha : Nat.Coprime a q) :
    ‖fullDiscrepancy (∑ n ∈ Finset.Icc 1 N, Finsupp.single n (e n)) q a‖ ≤
      2 * U * ((N : ℝ) / (q.totient : ℝ) *
        (∑ p ∈ D, (1 : ℝ) / (p : ℝ) ^ 2) + D.card) := by
  classical
  let T : ℝ := ∑ p ∈ D, (1 : ℝ) / (p : ℝ) ^ 2
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφq : (q.totient : ℝ) ≤ q := Nat.cast_le.mpr (Nat.totient_le q)
  have hprogress :
      ‖∑ n ∈ Finset.Icc 1 N, if n % q = a % q then e n else 0‖ ≤
        U * ((N : ℝ) / q * T + D.card) := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 N, if Nat.ModEq q n a then ‖e n‖ else 0 := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro n _
        by_cases h : n % q = a % q <;> simp only [Nat.ModEq, h, ↓reduceIte, norm_zero, le_refl]
      _ ≤ U * ∑ p ∈ D,
          ({n ∈ Finset.Icc 1 N | p ^ 2 ∣ n ∧ Nat.ModEq q n a}.card : ℝ) :=
        by simpa only [squareCRT_ite_classical, squareCRT_filter_classical] using
          square_supported_mask_mass_le N D U hU e hb hs (fun n => Nat.ModEq q n a)
      _ ≤ U * ∑ p ∈ D, ((N : ℝ) / (p : ℝ) ^ 2 / q + 1) := by
        apply mul_le_mul_of_nonneg_left _ hU
        exact Finset.sum_le_sum (fun p hp => square_progression_count_le N p q a (hD p hp) ha)
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, T]
        rw [Finset.mul_sum]
        congr 2
        exact Finset.sum_congr rfl (fun p _ => by ring)
  have hmass : (∑ n ∈ Finset.Icc 1 N, ‖e n‖) ≤ U * ((N : ℝ) * T + D.card) := by
    calc
      _ ≤ U * ∑ p ∈ D, ({n ∈ Finset.Icc 1 N | p ^ 2 ∣ n}.card : ℝ) := by
        simpa only [ite_true, and_true] using square_supported_mask_mass_le N D U hU e hb hs (fun _ => True)
      _ ≤ U * ∑ p ∈ D, ((N : ℝ) / (p : ℝ) ^ 2 + 1) := by
        apply mul_le_mul_of_nonneg_left _ hU
        exact Finset.sum_le_sum (fun p hp => square_divisor_count_le N p (hD p hp))
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, T]
        rw [Finset.mul_sum]
        congr 2
        exact Finset.sum_congr rfl (fun p _ => by ring)
  have hreduced :
      ‖∑ n ∈ Finset.Icc 1 N, if Nat.Coprime n q then e n else 0‖ ≤ U * ((N : ℝ) * T + D.card) := by
    apply (norm_sum_le _ _).trans
    apply le_trans _ hmass
    apply Finset.sum_le_sum
    intro n _
    split_ifs <;> simp only [norm_zero, norm_nonneg, le_refl]
  rw [fullDiscrepancy_sample, Finset.sum_sub_distrib, ← Finset.sum_div]
  have hraw := norm_sub_le_of_le hprogress (show
    ‖(∑ n ∈ Finset.Icc 1 N, if Nat.Coprime n q then e n else 0) / (q.totient : ℂ)‖ ≤
      (U * ((N : ℝ) * T + D.card)) / (q.totient : ℝ) by
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right hreduced (Nat.cast_nonneg _))
  have hfirst : (N : ℝ) / q * T ≤ (N : ℝ) / (q.totient : ℝ) * T :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (Nat.cast_nonneg N)
      (zero_lt_one.trans_le hφ) hφq) hT
  have hlast : (D.card : ℝ) / (q.totient : ℝ) ≤ D.card := div_le_self (Nat.cast_nonneg _) hφ
  have hright : U * ((N : ℝ) * T + D.card) / (q.totient : ℝ) =
      U * ((N : ℝ) / (q.totient : ℝ) * T + (D.card : ℝ) / (q.totient : ℝ)) := by ring
  rw [hright] at hraw
  have hfirst' := mul_le_mul_of_nonneg_left hfirst hU
  have hlast' := mul_le_mul_of_nonneg_left hlast hU
  change _ ≤ 2 * U * ((N : ℝ) / (q.totient : ℝ) * T + D.card)
  linarith only [hraw, hfirst', hlast']

theorem square_supported_band_fullDiscrepancy_le
    (N r P : ℕ) (hr : 2 ≤ r) (D : Finset ℕ) (hD : D ⊆ Finset.Icc r P)
    (U : ℝ) (hU : 0 ≤ U) (e : ℕ → ℂ)
    (hb : ∀ n ∈ Finset.Icc 1 N, ‖e n‖ ≤ U)
    (hs : ∀ n ∈ Finset.Icc 1 N, e n ≠ 0 → ∃ p ∈ D, p ^ 2 ∣ n)
    (q a : ℕ) (hq : 0 < q) (ha : Nat.Coprime a q) :
    ‖fullDiscrepancy (∑ n ∈ Finset.Icc 1 N, Finsupp.single n (e n)) q a‖ ≤
      2 * U * ((N : ℝ) / ((r - 1 : ℕ) : ℝ) / (q.totient : ℝ) + P) := by
  have hpos : ∀ p ∈ D, 0 < p := fun p hp => lt_of_lt_of_le (by omega) (Finset.mem_Icc.mp (hD hp)).1
  have ht : (∑ p ∈ D, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1 / ((r - 1 : ℕ) : ℝ) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hD (fun _ _ _ => by positivity)).trans
      (sum_Icc_inv_sq_le P r hr)
  have hc : D.card ≤ P := by
    have hh : D ⊆ Finset.Icc 1 P := fun p hp => Finset.mem_Icc.mpr
      ⟨(by omega : 1 ≤ r).trans (Finset.mem_Icc.mp (hD hp)).1, (Finset.mem_Icc.mp (hD hp)).2⟩
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hh
  apply (square_supported_fullDiscrepancy_le N D hpos U hU e hb hs q a hq ha).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg zero_le_two hU)
  have hh := add_le_add (mul_le_mul_of_nonneg_left ht
    (div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg q.totient))) (Nat.cast_le.mpr hc)
  convert hh using 1
  ring

#print axioms multiplier_progression_count_le
#print axioms square_supported_fullDiscrepancy_le
#print axioms square_supported_band_fullDiscrepancy_le

end PrimeGap182Analytic
