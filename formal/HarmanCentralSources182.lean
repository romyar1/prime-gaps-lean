import HarmanSourceGeometry182

/-! Actual prime tuple and compact support identities for the new central,
large-first and T4-U1 sources. Four-prime boxes use the valid .9 upper band;
five-prime boxes use .31, because the former .24 band is too narrow.
All identities refer to the literal arithmetic sources of HarmanBuchstab182.
Adapted from Apache-2.0 PrimeGaps186 at the checked source hash. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

theorem source_large_first_power_gates :
    ∀ᶠ x : ℝ in atTop, 3 < x ∧
      2 * x < x ^ (3 * ((41361 : ℝ) / 100000)) ∧
      Real.sqrt (3 * x) < x ^ ((58639 : ℝ) / 100000) ∧
      2 * x ^ ((58639 : ℝ) / 100000) ≤ x ^ ((9 : ℝ) / 10) := by
  have hc := tendsto_rpow_atTop (by norm_num :
    (0 : ℝ) < 3 * (41361 / 100000) - 1)
  have hs := tendsto_rpow_atTop (by norm_num :
    (0 : ℝ) < 2 * (58639 / 100000) - 1)
  have hu := tendsto_rpow_atTop (by norm_num :
    (0 : ℝ) < 9 / 10 - 58639 / 100000)
  filter_upwards [eventually_gt_atTop (3 : ℝ), hc.eventually_gt_atTop 2,
    hs.eventually_gt_atTop 3, hu.eventually_ge_atTop 2] with x hx hcx hsx hux
  have hx0 : 0 < x := by linarith
  have hmul (r : ℝ) : x * x ^ (r - 1) = x ^ r := by
    conv_lhs => lhs; rw [← Real.rpow_one x]
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  refine ⟨hx, ?_, ?_, ?_⟩
  · calc
      2 * x < x * x ^ (3 * (41361 / 100000) - 1) := by nlinarith
      _ = _ := hmul _
  · apply (Real.sqrt_lt' (Real.rpow_pos_of_pos hx0 _)).mpr
    calc
      3 * x < x * x ^ (2 * (58639 / 100000) - 1) := by nlinarith
      _ = x ^ (2 * (58639 / 100000)) := hmul _
      _ = (x ^ ((58639 : ℝ) / 100000)) ^ (2 : ℕ) := by
        rw [← Real.rpow_mul_natCast hx0.le]
        congr 1
        ring
  · calc
      2 * x ^ ((58639 : ℝ) / 100000) ≤
          x ^ ((58639 : ℝ) / 100000) * x ^ ((9 : ℝ) / 10 - 58639 / 100000) := by
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left hux (Real.rpow_nonneg hx0.le ((58639 : ℝ) / 100000))
      _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring

open Classical in
theorem sourceLargeFirst_eq_two_primes {x : ℝ} (hx : 3 < x)
    (hcube : 2 * x < x ^ (3 * ((41361 : ℝ) / 100000)))
    (n : ℕ) (hnlo : x ≤ (n : ℝ)) (hnhi : (n : ℝ) ≤ 2 * x) :
    sourceLargeFirst x n =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin 2 => Nat.primesLE n),
        if (∏ i, p i) = n ∧ x ^ ((41361 : ℝ) / 100000) ≤ (p 0 : ℝ) ∧
          (p 0 : ℝ) < Real.sqrt (3 * x) ∧ p 0 ≤ p 1 then (1 : ℝ) else 0 := by
  have hx0 : 0 < x := by linarith
  have hn0 : n ≠ 0 := by intro h; simp only [h, Nat.cast_zero] at hnlo; linarith
  have hsqrt : Real.sqrt (3 * x) < x :=
    (Real.sqrt_lt' hx0).mpr (by nlinarith)
  have hrough (d : ℕ × ℕ) (hd : d ∈ n.divisorsAntidiagonal)
      (hcut : d.1.Prime ∧ x ^ ((41361 : ℝ) / 100000) ≤ (d.1 : ℝ) ∧
        (d.1 : ℝ) < Real.sqrt (3 * x)) :
      roughWeight (d.1 : ℝ) d.2 = if d.2.Prime ∧ d.1 ≤ d.2 then 1 else 0 := by
    have hprod : d.1 * d.2 = n := (Nat.mem_divisorsAntidiagonal.mp hd).1
    have hr0 : d.2 ≠ 0 := by intro h; simp only [h, mul_zero] at hprod; exact hn0 hprod.symm
    have hr1 : d.2 ≠ 1 := by
      intro h
      have hp : d.1 = n := by simpa only [h, mul_one] using hprod
      have := hcut.2.2.trans hsqrt
      rw [hp] at this
      exact (not_lt_of_ge hnlo) this
    rw [roughWeight_eq_ite_minFac _ hr0 hr1]
    by_cases hp : d.2.Prime
    · rw [hp.minFac_eq]
      simp only [hp, true_and, Nat.cast_le]
    · have hnot : ¬ (d.1 : ℝ) ≤ (d.2.minFac : ℝ) := by
        intro hmin
        have hsq : (d.2.minFac : ℝ) ^ 2 ≤ (d.2 : ℝ) := by
          exact_mod_cast Nat.minFac_sq_le_self (Nat.pos_of_ne_zero hr0) hp
        have hpsq : (d.1 : ℝ) ^ 2 ≤ (d.2 : ℝ) :=
          (pow_le_pow_left₀ (Nat.cast_nonneg _) hmin 2).trans hsq
        have hcube' : (d.1 : ℝ) ^ 3 ≤ (n : ℝ) := by
          calc
            (d.1 : ℝ) ^ 3 = (d.1 : ℝ) * (d.1 : ℝ) ^ 2 := by ring
            _ ≤ (d.1 : ℝ) * (d.2 : ℝ) :=
              mul_le_mul_of_nonneg_left hpsq (Nat.cast_nonneg _)
            _ = _ := by exact_mod_cast hprod
        have hg : x ^ (3 * ((41361 : ℝ) / 100000)) ≤ (d.1 : ℝ) ^ 3 := by
          calc
            _ = (x ^ ((41361 : ℝ) / 100000)) ^ (3 : ℕ) := by
              rw [← Real.rpow_mul_natCast hx0.le]
              congr 1
              ring
            _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hx0.le _) hcut.2.1 3
        exact (not_le_of_gt hcube) (hg.trans (hcube'.trans hnhi))
      simp only [hp, false_and, ite_false, ite_eq_right hnot]
  let w (p : Fin 2 → ℕ) : ℝ :=
    if x ^ ((41361 : ℝ) / 100000) ≤ (p 0 : ℝ) ∧
      (p 0 : ℝ) < Real.sqrt (3 * x) ∧ p 0 ≤ p 1 then 1 else 0
  calc
    sourceLargeFirst x n = ∑ d ∈ n.divisorsAntidiagonal,
        if d.1.Prime ∧ d.2.Prime then w ![d.1, d.2] else 0 := by
      change (∑ d ∈ n.divisorsAntidiagonal, _) = _
      apply Finset.sum_congr rfl
      intro d hd
      change (if d.1.Prime ∧ x ^ ((41361 : ℝ) / 100000) ≤ (d.1 : ℝ) ∧
          (d.1 : ℝ) < Real.sqrt (3 * x) then roughWeight (d.1 : ℝ) d.2 else 0) =
        (if d.1.Prime ∧ d.2.Prime then
          if x ^ ((41361 : ℝ) / 100000) ≤ (d.1 : ℝ) ∧
            (d.1 : ℝ) < Real.sqrt (3 * x) ∧ d.1 ≤ d.2 then 1 else 0 else 0)
      by_cases hcut : d.1.Prime ∧ x ^ ((41361 : ℝ) / 100000) ≤ (d.1 : ℝ) ∧
          (d.1 : ℝ) < Real.sqrt (3 * x)
      · rw [ite_eq_left hcut, hrough d hd hcut]
        by_cases hr : d.2.Prime <;> by_cases hord : d.1 ≤ d.2 <;>
          simp only [hcut.1, hcut.2.1, hcut.2.2, hr, hord, true_and, false_and,
            ite_true, ite_false]
      · rw [ite_eq_right hcut]
        split_ifs with hprime hbound
        · exact False.elim (hcut ⟨hprime.1, hbound.1, hbound.2.1⟩)
        · rfl
        · rfl
    _ = _ := by
      rw [sum_two_prime_divisorsAntidiagonal]
      apply Finset.sum_congr rfl
      intro p _hp
      dsimp only [w]
      split_ifs <;> simp_all only [and_self, not_true_eq_false, false_and]

open Classical in
theorem sourceLargeFirst_eventually_compact_central :
    ∀ᶠ x : ℝ in atTop,
      let P := (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
        ⌊x ^ ((9 : ℝ) / 10)⌋₊).filter Nat.Prime
      let T := Fintype.piFinset (fun _ : Fin 2 => P)
      (∀ n : ℕ, x ≤ (n : ℝ) → (n : ℝ) ≤ 2 * x →
        sourceLargeFirst x n = ∑ p ∈ T,
          if (∏ i, p i) = n ∧ x ^ ((41361 : ℝ) / 100000) ≤ (p 0 : ℝ) ∧
            (p 0 : ℝ) < Real.sqrt (3 * x) ∧ p 0 ≤ p 1 then (1 : ℝ) else 0) ∧
      (∀ p ∈ T, x ^ ((41361 : ℝ) / 100000) ≤ (p 0 : ℝ) →
        (p 0 : ℝ) < Real.sqrt (3 * x) →
        ∃ S : Finset (Fin 2), S.Nonempty ∧ S ≠ Finset.univ ∧
          x ^ ((41361 : ℝ) / 100000) ≤ ((∏ i ∈ S, p i : ℕ) : ℝ) ∧
          ((∏ i ∈ S, p i : ℕ) : ℝ) ≤ x ^ ((58639 : ℝ) / 100000)) := by
  filter_upwards [source_large_first_power_gates] with x hx
  intro P T
  have hx1 : 1 < x := by linarith [hx.1]
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hab : x ^ ((41361 : ℝ) / 100000) * x ^ ((58639 : ℝ) / 100000) = x := by
    rw [← Real.rpow_add hx0]
    norm_num
  have halow : x ^ ((8639 : ℝ) / 50000) ≤ x ^ ((41361 : ℝ) / 100000) :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
  have hcompact (p : Fin 2 → ℕ) (hprime : ∀ i, (p i).Prime)
      (hprod : ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x)
      (hlo : x ^ ((41361 : ℝ) / 100000) ≤ (p 0 : ℝ)) (horder : p 0 ≤ p 1) : p ∈ T := by
    have hlo1 := hlo.trans (Nat.cast_le.mpr horder)
    have hproduct : (p 0 : ℝ) * (p 1 : ℝ) ≤ 2 * x := by
      simpa only [Fin.prod_univ_two, Nat.cast_mul] using hprod
    have ha0 : 0 < x ^ ((41361 : ℝ) / 100000) := Real.rpow_pos_of_pos hx0 _
    have hupper (i : Fin 2) : (p i : ℝ) ≤ 2 * x ^ ((58639 : ℝ) / 100000) := by
      fin_cases i
      · change (p 0 : ℝ) ≤ 2 * x ^ ((58639 : ℝ) / 100000)
        apply (mul_le_mul_iff_right₀ ha0).mp
        have hm := mul_le_mul_of_nonneg_left hlo1 (Nat.cast_nonneg (p 0))
        nlinarith
      · change (p 1 : ℝ) ≤ 2 * x ^ ((58639 : ℝ) / 100000)
        apply (mul_le_mul_iff_right₀ ha0).mp
        have hm := mul_le_mul_of_nonneg_right hlo (Nat.cast_nonneg (p 1))
        nlinarith
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr ?_,
      (Nat.le_floor_iff (Real.rpow_nonneg hx0.le _)).mpr ((hupper i).trans hx.2.2.2)⟩,
      hprime i⟩
    fin_cases i
    · exact halow.trans hlo
    · exact halow.trans hlo1
  constructor
  · intro n hnlo hnhi
    rw [sourceLargeFirst_eq_two_primes hx.1 hx.2.1 n hnlo hnhi]
    symm
    apply Finset.sum_subset
    · intro p hp
      apply Fintype.mem_piFinset.mpr
      intro i
      obtain ⟨hpi, hpprime⟩ := Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)
      apply Nat.mem_primesLE.mpr
      refine ⟨?_, hpprime⟩
      have hpupper := (Nat.le_floor_iff (Real.rpow_nonneg hx0.le _)).mp
        (Finset.mem_Icc.mp hpi).2
      have hxupper : x ^ ((9 : ℝ) / 10) ≤ x := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num : (9 : ℝ) / 10 ≤ 1)
      exact_mod_cast hpupper.trans (hxupper.trans hnlo)
    · intro p hp hpnot
      apply ite_eq_right
      intro hcut
      have hprime (i : Fin 2) := Nat.prime_of_mem_primesLE (Fintype.mem_piFinset.mp hp i)
      have hprod : ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x := by rw [hcut.1]; exact hnhi
      exact hpnot (hcompact p hprime hprod hcut.2.1 hcut.2.2.2)
  · intro p _hp hlo hhi
    refine ⟨{0}, Finset.singleton_nonempty 0, ?_, ?_, ?_⟩
    · intro h
      have hm : (1 : Fin 2) ∈ ({0} : Finset (Fin 2)) := by rw [h]; exact Finset.mem_univ _
      norm_num at hm
    · simpa only [Finset.prod_singleton] using hlo
    · simpa only [Finset.prod_singleton] using (hhi.trans hx.2.2.1).le

open Classical in
theorem sourceLargeFirst_eventually_finsupp :
    ∀ᶠ x : ℝ in atTop,
      let P := (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
        ⌊x ^ ((9 : ℝ) / 10)⌋₊).filter Nat.Prime
      let T := Fintype.piFinset (fun _ : Fin 2 => P)
      let C (p : Fin 2 → ℕ) : Prop :=
        x ≤ ((∏ i, p i : ℕ) : ℝ) ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x ∧
          x ^ ((41361 : ℝ) / 100000) ≤ (p 0 : ℝ) ∧
          (p 0 : ℝ) < Real.sqrt (3 * x) ∧ p 0 ≤ p 1
      (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
        Finsupp.single n (sourceLargeFirst x n : ℂ)) =
        ∑ p ∈ T, Finsupp.single (∏ i, p i) (if C p then (1 : ℂ) else 0) := by
  filter_upwards [sourceLargeFirst_eventually_compact_central,
    eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro P T C
  let I := Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊
  let D (p : Fin 2 → ℕ) : Prop := x ^ ((41361 : ℝ) / 100000) ≤ (p 0 : ℝ) ∧
    (p 0 : ℝ) < Real.sqrt (3 * x) ∧ p 0 ≤ p 1
  have hband (p : Fin 2 → ℕ) :
      (∏ i, p i) ∈ I ↔ x ≤ ((∏ i, p i : ℕ) : ℝ) ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x := by
    simp only [I, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff (by linarith : 0 ≤ 2 * x)]
  have hpoint (n : ℕ) (hn : n ∈ I) :
      (sourceLargeFirst x n : ℂ) =
        ∑ p ∈ T, if (∏ i, p i) = n ∧ D p then (1 : ℂ) else 0 := by
    have hlo := Nat.ceil_le.mp (Finset.mem_Icc.mp hn).1
    have hhi := (Nat.le_floor_iff (by linarith : 0 ≤ 2 * x)).mp (Finset.mem_Icc.mp hn).2
    have h := congrArg Complex.ofReal ((hx.1) n hlo hhi)
    simpa only [Complex.ofReal_sum, apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using h
  calc
    _ = ∑ n ∈ I, ∑ p ∈ T,
        Finsupp.single n (if (∏ i, p i) = n ∧ D p then (1 : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hpoint n hn, Finsupp.single_finsetSum]
    _ = ∑ p ∈ T, ∑ n ∈ I,
        Finsupp.single n (if (∏ i, p i) = n ∧ D p then (1 : ℂ) else 0) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hd : D p
      · by_cases hp : (∏ i, p i) ∈ I
        · have hc : C p := ⟨(hband p).mp hp |>.1, (hband p).mp hp |>.2, hd⟩
          rw [ite_eq_left hc]
          rw [Finset.sum_eq_single_of_mem (∏ i, p i) hp]
          · rw [ite_eq_left ⟨rfl, hd⟩]
          · intro n _hn hne
            rw [ite_eq_right (fun h => hne h.1.symm), Finsupp.single_zero]
        · have hc : ¬ C p := fun h => hp ((hband p).mpr ⟨h.1, h.2.1⟩)
          rw [ite_eq_right hc, Finsupp.single_zero]
          apply Finset.sum_eq_zero
          intro n hn
          have hnot : ¬ ((∏ i, p i) = n ∧ D p) := by
            intro h
            apply hp
            rw [h.1]
            exact hn
          rw [ite_eq_right hnot, Finsupp.single_zero]
      · have hc : ¬ C p := fun h => hd h.2.2
        rw [ite_eq_right hc, Finsupp.single_zero]
        apply Finset.sum_eq_zero
        intro n _hn
        rw [ite_eq_right (fun h => hd h.2), Finsupp.single_zero]

open Classical in
theorem sourceLargeFirst_small_monomial_representation (x : ℝ) (hx : 0 < x) :
    ∃ M : Finset (MinorantSmallMonomialCut 2), M.card ≤ 32 ∧
      (∀ d ∈ M, d.numerator.Nonempty ∧ Disjoint d.numerator d.denominator ∧
        d.numerator.card + d.denominator.card ≤ 2 ∧ 0 < d.threshold) ∧
      ∀ p q : Fin 2 → ℕ, (∀ i, 0 < p i) → (∀ i, 0 < q i) →
      (∀ d ∈ M,
        (if d.lower then
          if d.strict then d.threshold < d.value p else d.threshold ≤ d.value p
        else if d.strict then d.value p < d.threshold else d.value p ≤ d.threshold) ↔
        (if d.lower then
          if d.strict then d.threshold < d.value q else d.threshold ≤ d.value q
        else if d.strict then d.value q < d.threshold else d.value q ≤ d.threshold)) →
      ((x ≤ ((∏ i, p i : ℕ) : ℝ) ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x ∧
          x ^ ((41361 : ℝ) / 100000) ≤ (p 0 : ℝ) ∧
          (p 0 : ℝ) < Real.sqrt (3 * x) ∧ p 0 ≤ p 1) ↔
        (x ≤ ((∏ i, q i : ℕ) : ℝ) ∧ ((∏ i, q i : ℕ) : ℝ) ≤ 2 * x ∧
          x ^ ((41361 : ℝ) / 100000) ≤ (q 0 : ℝ) ∧
          (q 0 : ℝ) < Real.sqrt (3 * x) ∧ q 0 ≤ q 1)) := by
  let d : Fin 5 → MinorantSmallMonomialCut 2 :=
    ![⟨Finset.univ, ∅, x, true, false⟩,
      ⟨Finset.univ, ∅, 2 * x, false, false⟩,
      ⟨{0}, ∅, x ^ ((41361 : ℝ) / 100000), true, false⟩,
      ⟨{0}, ∅, Real.sqrt (3 * x), false, true⟩,
      ⟨{0}, {1}, 1, false, false⟩]
  let M := Finset.univ.image d
  have hmem (i : Fin 5) : d i ∈ M := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hcard : M.card ≤ 32 := by
    calc
      M.card ≤ (Finset.univ : Finset (Fin 5)).card := Finset.card_image_le
      _ ≤ 32 := by norm_num
  refine ⟨M, hcard, ?_, ?_⟩
  · intro e he
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp he
    fin_cases i <;> norm_num [d, Finset.disjoint_left] <;> positivity
  · intro p q hp hq htest
    have h0 := htest (d 0) (hmem 0)
    have h1 := htest (d 1) (hmem 1)
    have h2 := htest (d 2) (hmem 2)
    have h3 := htest (d 3) (hmem 3)
    have h4 := htest (d 4) (hmem 4)
    change (x ≤ (d 0).value p) ↔ (x ≤ (d 0).value q) at h0
    change ((d 1).value p ≤ 2 * x) ↔ ((d 1).value q ≤ 2 * x) at h1
    change (x ^ ((41361 : ℝ) / 100000) ≤ (d 2).value p) ↔
      (x ^ ((41361 : ℝ) / 100000) ≤ (d 2).value q) at h2
    change ((d 3).value p < Real.sqrt (3 * x)) ↔
      ((d 3).value q < Real.sqrt (3 * x)) at h3
    change ((d 4).value p ≤ 1) ↔ ((d 4).value q ≤ 1) at h4
    have hv0 (r : Fin 2 → ℕ) : (d 0).value r = ((∏ i, r i : ℕ) : ℝ) := by
      simp [d, MinorantSmallMonomialCut.value]
    have hv1 (r : Fin 2 → ℕ) : (d 1).value r = ((∏ i, r i : ℕ) : ℝ) := by
      simp [d, MinorantSmallMonomialCut.value]
    have hv2 (r : Fin 2 → ℕ) : (d 2).value r = (r 0 : ℝ) := by
      change (∏ i ∈ ({0} : Finset (Fin 2)), (r i : ℝ)) /
        (∏ i ∈ (∅ : Finset (Fin 2)), (r i : ℝ)) = (r 0 : ℝ)
      simp only [Finset.prod_singleton, Finset.prod_empty, div_one]
    have hv3 (r : Fin 2 → ℕ) : (d 3).value r = (r 0 : ℝ) := by
      change (∏ i ∈ ({0} : Finset (Fin 2)), (r i : ℝ)) /
        (∏ i ∈ (∅ : Finset (Fin 2)), (r i : ℝ)) = (r 0 : ℝ)
      simp only [Finset.prod_singleton, Finset.prod_empty, div_one]
    have hv4 (r : Fin 2 → ℕ) : (d 4).value r = (r 0 : ℝ) / (r 1 : ℝ) := by
      change (∏ i ∈ ({0} : Finset (Fin 2)), (r i : ℝ)) /
        (∏ i ∈ ({1} : Finset (Fin 2)), (r i : ℝ)) = (r 0 : ℝ) / (r 1 : ℝ)
      simp only [Finset.prod_singleton]
    rw [hv0 p, hv0 q] at h0
    rw [hv1 p, hv1 q] at h1
    rw [hv2 p, hv2 q] at h2
    rw [hv3 p, hv3 q] at h3
    rw [hv4 p, hv4 q, div_le_one (Nat.cast_pos.mpr (hp 1)),
      div_le_one (Nat.cast_pos.mpr (hq 1)), Nat.cast_le, Nat.cast_le] at h4
    exact and_congr h0 (and_congr h1 (and_congr h2 (and_congr h3 h4)))

theorem sourceCentralPair_eventually_residual_bounds :
    ∃ X : ℝ, 3 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      ∀ n p q m : ℕ, p.Prime → q.Prime → p * (q * m) = n →
      x ≤ (n : ℝ) → (n : ℝ) ≤ 2 * x →
      (8639 : ℝ) / 50000 ≤ Real.logb x (q : ℝ) →
      Real.logb x (q : ℝ) < Real.logb x (p : ℝ) →
      Real.logb x (p : ℝ) < (41361 : ℝ) / 100000 →
      (41361 : ℝ) / 100000 ≤ Real.logb x (p : ℝ) + Real.logb x (q : ℝ) →
      Real.logb x (p : ℝ) + Real.logb x (q : ℝ) ≤ (58639 : ℝ) / 100000 →
        q ≤ m ∧ (m : ℝ) < (q : ℝ) ^ (4 : ℕ) ∧
        x ^ ((41361 : ℝ) / 100000) ≤ (p : ℝ) * q ∧
        (p : ℝ) * q ≤ x ^ ((58639 : ℝ) / 100000) ∧
        x ^ ((8639 : ℝ) / 50000) ≤ (q : ℝ) ∧ q < p ∧
        (p : ℝ) < x ^ ((41361 : ℝ) / 100000) := by
  have hlarge : ∀ᶠ x : ℝ in atTop,
      2 < x ^ (4 * ((8639 : ℝ) / 50000) - (58639 : ℝ) / 100000) :=
    (tendsto_rpow_atTop (by norm_num :
      (0 : ℝ) < 4 * ((8639 : ℝ) / 50000) - (58639 : ℝ) / 100000)).eventually_gt_atTop 2
  obtain ⟨X, hX⟩ := hlarge.exists_forall_of_atTop
  refine ⟨max 3 X, le_max_left _ _, ?_⟩
  intro x hx n p q m hp hq hprod hxn hnx hqlo hqp hpa hsumlo hsumhi
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hp0 : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hq0 : 0 < (q : ℝ) := Nat.cast_pos.mpr hq.pos
  have hprodR : (p : ℝ) * q * m = n := by
    exact_mod_cast (mul_assoc p q m).trans hprod
  have hpairlo : x ^ ((41361 : ℝ) / 100000) ≤ (p : ℝ) * q :=
    (Real.le_logb_iff_rpow_le hx1 (mul_pos hp0 hq0)).mp (by
      rw [Real.logb_mul hp0.ne' hq0.ne']
      exact hsumlo)
  have hpairhi : (p : ℝ) * q ≤ x ^ ((58639 : ℝ) / 100000) :=
    (Real.logb_le_iff_le_rpow hx1 (mul_pos hp0 hq0)).mp (by
      rw [Real.logb_mul hp0.ne' hq0.ne']
      exact hsumhi)
  have hqpow : x ^ ((8639 : ℝ) / 50000) ≤ (q : ℝ) :=
    (Real.le_logb_iff_rpow_le hx1 hq0).mp hqlo
  have hqpR : (q : ℝ) < p := (Real.logb_lt_logb_iff hx1 hq0 hp0).mp hqp
  have hppow : (p : ℝ) < x ^ ((41361 : ℝ) / 100000) :=
    (Real.logb_lt_iff_lt_rpow hx1 hp0).mp hpa
  have hunit : x ^ ((58639 : ℝ) / 100000) * x ^ ((41361 : ℝ) / 100000) = x := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hmlower : x ^ ((41361 : ℝ) / 100000) ≤ (m : ℝ) := by
    apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hx0 ((58639 : ℝ) / 100000))).mp
    calc
      x ^ ((58639 : ℝ) / 100000) * x ^ ((41361 : ℝ) / 100000) = x := hunit
      _ ≤ (n : ℝ) := hxn
      _ = (p : ℝ) * q * m := hprodR.symm
      _ ≤ x ^ ((58639 : ℝ) / 100000) * m :=
        mul_le_mul_of_nonneg_right hpairhi (Nat.cast_nonneg m)
  have hmupper : (m : ℝ) ≤ 2 * x ^ ((58639 : ℝ) / 100000) := by
    apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hx0 ((41361 : ℝ) / 100000))).mp
    calc
      x ^ ((41361 : ℝ) / 100000) * m ≤ (p : ℝ) * q * m :=
        mul_le_mul_of_nonneg_right hpairlo (Nat.cast_nonneg m)
      _ = (n : ℝ) := hprodR
      _ ≤ 2 * x := hnx
      _ = x ^ ((41361 : ℝ) / 100000) * (2 * x ^ ((58639 : ℝ) / 100000)) := by
        calc
          2 * x = 2 * (x ^ ((58639 : ℝ) / 100000) *
              x ^ ((41361 : ℝ) / 100000)) := congrArg (fun z : ℝ => 2 * z) hunit.symm
          _ = _ := by ring
  have hfour : 2 * x ^ ((58639 : ℝ) / 100000) <
      x ^ (4 * ((8639 : ℝ) / 50000)) := by
    calc
      _ < x ^ (4 * ((8639 : ℝ) / 50000) - (58639 : ℝ) / 100000) *
          x ^ ((58639 : ℝ) / 100000) :=
        mul_lt_mul_of_pos_right (hX x ((le_max_right _ _).trans hx))
          (Real.rpow_pos_of_pos hx0 _)
      _ = _ := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring
  have hqfour : x ^ (4 * ((8639 : ℝ) / 50000)) ≤ (q : ℝ) ^ (4 : ℕ) := by
    calc
      _ = (x ^ ((8639 : ℝ) / 50000)) ^ (4 : ℕ) := by
        rw [← Real.rpow_mul_natCast hx0.le]
        congr 1
        norm_num
      _ ≤ (q : ℝ) ^ (4 : ℕ) :=
        pow_le_pow_left₀ (Real.rpow_nonneg hx0.le _) hqpow 4
  exact ⟨Nat.cast_le.mp ((hqpR.trans hppow).le.trans hmlower),
    hmupper.trans_lt (hfour.trans_le hqfour), hpairlo, hpairhi, hqpow,
    Nat.cast_lt.mp hqpR, hppow⟩

open Classical in
theorem sourceCentralPair_eventually_eq_expanded_antidiagonal :
    ∃ X : ℝ, 3 ≤ X ∧ ∀ x : ℝ, X ≤ x → ∀ n : ℕ,
      x ≤ (n : ℝ) → (n : ℝ) ≤ 2 * x →
      let α (p : ℕ) : ℝ := Real.logb x (p : ℝ)
      let C (p q : ℕ) : Prop :=
        (8639 : ℝ) / 50000 ≤ α q ∧ α q < α p ∧
        α p < (41361 : ℝ) / 100000 ∧
        (41361 : ℝ) / 100000 ≤ α p + α q ∧ α p + α q ≤ (58639 : ℝ) / 100000
      sourceCentralPair x n =
        ∑ d ∈ n.divisorsAntidiagonal, ∑ e ∈ d.2.divisorsAntidiagonal,
          if d.1.Prime ∧ e.1.Prime ∧ C d.1 e.1 then
            (if e.2.Prime ∧ e.1 ≤ e.2 then (1 : ℝ) else 0) +
            (∑ f ∈ e.2.divisorsAntidiagonal,
              if f.1.Prime ∧ f.2.Prime ∧ e.1 ≤ f.1 ∧ f.1 ≤ f.2 then 1 else 0) +
            (∑ f ∈ e.2.divisorsAntidiagonal, ∑ g ∈ f.2.divisorsAntidiagonal,
              if f.1.Prime ∧ g.1.Prime ∧ g.2.Prime ∧
                e.1 ≤ f.1 ∧ f.1 ≤ g.1 ∧ g.1 ≤ g.2 then 1 else 0)
          else 0 := by
  obtain ⟨X, hX, hresidual⟩ := sourceCentralPair_eventually_residual_bounds
  refine ⟨X, hX, ?_⟩
  intro x hx n hxn hnx α C
  change (∑ d ∈ n.divisorsAntidiagonal, ∑ e ∈ d.2.divisorsAntidiagonal,
    if d.1.Prime ∧ e.1.Prime ∧ C d.1 e.1 then roughWeight (e.1 : ℝ) e.2 else 0) = _
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  by_cases hc : d.1.Prime ∧ e.1.Prime ∧ C d.1 e.1
  · rw [ite_eq_left hc, ite_eq_left hc]
    obtain ⟨hp, hq, hqlo, hqp, hpa, hsumlo, hsumhi⟩ := hc
    have hprod : d.1 * (e.1 * e.2) = n := by
      rw [(Nat.mem_divisorsAntidiagonal.mp he).1]
      exact (Nat.mem_divisorsAntidiagonal.mp hd).1
    obtain ⟨hqm, hmfour, _⟩ :=
      hresidual x hx n d.1 e.1 e.2 hp hq hprod hxn hnx hqlo hqp hpa hsumlo hsumhi
    have hqone : (1 : ℝ) < e.1 := by exact_mod_cast hq.one_lt
    simpa only [Nat.cast_le, and_iff_left hqm] using
      roughWeight_eq_prime_add_ordered_two_three (e.1 : ℝ) e.2 hqone
        (Nat.cast_le.mpr hqm) hmfour
  · rw [ite_eq_right hc, ite_eq_right hc]

theorem prime_tuple_eventually_mem_common_power_band
    (k : ℕ) (β : ℝ)
    (hgap : 1 < (k : ℝ) * ((8639 : ℝ) / 50000) + β) :
    ∃ X : ℝ, 3 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      ∀ p : Fin (k + 1) → ℕ, (∀ i, (p i).Prime) →
      (∀ i, x ^ ((8639 : ℝ) / 50000) ≤ (p i : ℝ)) →
      ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x →
      ∀ i, p i ∈ (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊ ⌊x ^ β⌋₊).filter Nat.Prime := by
  classical
  let γ : ℝ := (k : ℝ) * ((8639 : ℝ) / 50000) + β - 1
  have hγ : 0 < γ := sub_pos.mpr hgap
  obtain ⟨X, hX⟩ :=
    ((tendsto_rpow_atTop hγ).eventually_ge_atTop (2 : ℝ)).exists_forall_of_atTop
  refine ⟨max 3 X, le_max_left _ _, ?_⟩
  intro x hx p hp hlo hprod i
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hrest : (x ^ ((8639 : ℝ) / 50000)) ^ k ≤
      ∏ j : Fin k, (p (i.succAbove j) : ℝ) := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Finset.prod_le_prod (s := (Finset.univ : Finset (Fin k)))
        (fun _ _ => Real.rpow_nonneg hx0.le ((8639 : ℝ) / 50000))
        (fun j _ => hlo (i.succAbove j))
  have hpower : (x ^ ((8639 : ℝ) / 50000)) ^ k * x ^ β = x ^ γ * x := by
    calc
      _ = x ^ (((8639 : ℝ) / 50000) * (k : ℝ) + β) := by
        rw [← Real.rpow_mul_natCast hx0.le, ← Real.rpow_add hx0]
      _ = x ^ (γ + 1) := by congr 1; dsimp only [γ]; ring
      _ = x ^ γ * x := by rw [Real.rpow_add hx0, Real.rpow_one]
  have hupper : (p i : ℝ) ≤ x ^ β := by
    apply (mul_le_mul_iff_right₀ (pow_pos
      (Real.rpow_pos_of_pos hx0 ((8639 : ℝ) / 50000)) k)).mp
    calc
      (x ^ ((8639 : ℝ) / 50000)) ^ k * (p i : ℝ) ≤
          (∏ j : Fin k, (p (i.succAbove j) : ℝ)) * p i :=
        mul_le_mul_of_nonneg_right hrest (Nat.cast_nonneg _)
      _ = ∏ j : Fin (k + 1), (p j : ℝ) := by
        rw [Fin.prod_univ_succAbove (fun j => (p j : ℝ)) i]
        ring
      _ ≤ 2 * x := by simpa only [Nat.cast_prod] using hprod
      _ ≤ x ^ γ * x := mul_le_mul_of_nonneg_right
        (hX x ((le_max_right _ _).trans hx)) hx0.le
      _ = (x ^ ((8639 : ℝ) / 50000)) ^ k * x ^ β := hpower.symm
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨Nat.ceil_le.mpr (hlo i), Nat.le_floor hupper⟩, hp i⟩

open Classical in
theorem sourceCentralPair_eventually_finsupp :
    ∃ X : ℝ, 3 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      let α (p : ℕ) : ℝ := Real.logb x (p : ℝ)
      let C (p q : ℕ) : Prop :=
        (8639 : ℝ) / 50000 ≤ α q ∧ α q < α p ∧
        α p < (41361 : ℝ) / 100000 ∧
        (41361 : ℝ) / 100000 ≤ α p + α q ∧ α p + α q ≤ (58639 : ℝ) / 100000
      let Ps := (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
        ⌊x ^ ((9 : ℝ) / 10)⌋₊).filter Nat.Prime
      let Pf := (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
        ⌊x ^ ((31 : ℝ) / 100)⌋₊).filter Nat.Prime
      (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
        Finsupp.single n (sourceCentralPair x n : ℂ)) =
      (∑ p ∈ Fintype.piFinset (fun _ : Fin 3 => Ps),
        Finsupp.single (∏ i, p i)
          (if x ≤ ((∏ i, p i : ℕ) : ℝ) ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x ∧
            C (p 0) (p 1) ∧ p 1 ≤ p 2 then (1 : ℂ) else 0)) +
      (∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => Ps),
        Finsupp.single (∏ i, p i)
          (if x ≤ ((∏ i, p i : ℕ) : ℝ) ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x ∧
            C (p 0) (p 1) ∧ p 1 ≤ p 2 ∧ p 2 ≤ p 3 then (1 : ℂ) else 0)) +
      (∑ p ∈ Fintype.piFinset (fun _ : Fin 5 => Pf),
        Finsupp.single (∏ i, p i)
          (if x ≤ ((∏ i, p i : ℕ) : ℝ) ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x ∧
            C (p 0) (p 1) ∧ p 1 ≤ p 2 ∧ p 2 ≤ p 3 ∧ p 3 ≤ p 4 then (1 : ℂ) else 0)) := by
  obtain ⟨Xr, hXr, hsource⟩ := sourceCentralPair_eventually_eq_expanded_antidiagonal
  obtain ⟨X3, _hX3, hc3⟩ :=
    prime_tuple_eventually_mem_common_power_band 2 (9 / 10) (by norm_num)
  obtain ⟨X4, _hX4, hc4⟩ :=
    prime_tuple_eventually_mem_common_power_band 3 (9 / 10) (by norm_num)
  obtain ⟨X5, _hX5, hc5⟩ :=
    prime_tuple_eventually_mem_common_power_band 4 (31 / 100) (by norm_num)
  refine ⟨max (max Xr X3) (max X4 X5),
    hXr.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro x hx α C Ps Pf
  have hxr : Xr ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hx3 : X3 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx4 : X4 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx5 : X5 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx1 : 1 < x := (by norm_num : (1 : ℝ) < 3).trans_le (hXr.trans hxr)
  have hx2 : 0 ≤ 2 * x := by linarith
  let N : Finset ℕ := Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊
  let w3 (p : Fin 3 → ℕ) : ℝ := if C (p 0) (p 1) ∧ p 1 ≤ p 2 then 1 else 0
  let w4 (p : Fin 4 → ℕ) : ℝ :=
    if C (p 0) (p 1) ∧ p 1 ≤ p 2 ∧ p 2 ≤ p 3 then 1 else 0
  let w5 (p : Fin 5 → ℕ) : ℝ :=
    if C (p 0) (p 1) ∧ p 1 ≤ p 2 ∧ p 2 ≤ p 3 ∧ p 3 ≤ p 4 then 1 else 0
  let f3 : ℕ →₀ ℂ := ∑ n ∈ N, Finsupp.single n
    (∑ p ∈ Fintype.piFinset (fun _ : Fin 3 => Nat.primesLE n),
      if (∏ i, p i) = n then (w3 p : ℂ) else 0)
  let f4 : ℕ →₀ ℂ := ∑ n ∈ N, Finsupp.single n
    (∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => Nat.primesLE n),
      if (∏ i, p i) = n then (w4 p : ℂ) else 0)
  let f5 : ℕ →₀ ℂ := ∑ n ∈ N, Finsupp.single n
    (∑ p ∈ Fintype.piFinset (fun _ : Fin 5 => Nat.primesLE n),
      if (∏ i, p i) = n then (w5 p : ℂ) else 0)
  have hpi {n : ℕ} (t : Fin n → Finset ℕ) (dec : DecidableEq (Fin n)) :
      @Fintype.piFinset (Fin n) dec _ (fun _ => ℕ) t =
        @Fintype.piFinset (Fin n) (Classical.typeDecidableEq _) _ (fun _ => ℕ) t := by
    ext r
    simp only [Fintype.mem_piFinset]
  have hite {V : Type} (p : Prop) (dec : Decidable p) (z w : V) :
      @ite V p dec z w = @ite V p (Classical.propDecidable p) z w :=
    @ite_cond_congr V p p dec (Classical.propDecidable p) z w rfl
  have handite {V : Type} (p q : Prop) (dec : Decidable (p ∧ q)) (z w : V) :
      @ite V (p ∧ q) dec z w = if p then (if q then z else w) else w := by
    by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
  have hpoint (n : ℕ) (hn : n ∈ N) :
      (sourceCentralPair x n : ℂ) =
      (∑ p ∈ Fintype.piFinset (fun _ : Fin 3 => Nat.primesLE n),
        if (∏ i, p i) = n then (w3 p : ℂ) else 0) +
      (∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => Nat.primesLE n),
        if (∏ i, p i) = n then (w4 p : ℂ) else 0) +
      (∑ p ∈ Fintype.piFinset (fun _ : Fin 5 => Nat.primesLE n),
        if (∏ i, p i) = n then (w5 p : ℂ) else 0) := by
    have hnlo : x ≤ (n : ℝ) := Nat.ceil_le.mp (Finset.mem_Icc.mp hn).1
    have hnhi : (n : ℝ) ≤ 2 * x :=
      (Nat.le_floor_iff hx2).mp (Finset.mem_Icc.mp hn).2
    have hsrc := hsource x hxr n hnlo hnhi
    have hreindex := centralPair_expanded_antidiagonal_eq_prime_tuples n C
    simp only [hite] at hsrc hreindex
    have hreal := hsrc.trans hreindex
    have hcast := congrArg Complex.ofReal hreal
    simpa only [Complex.ofReal_add, Complex.ofReal_sum, apply_ite Complex.ofReal,
      Complex.ofReal_zero, Complex.ofReal_one, w3, w4, w5, handite, hpi, hite] using hcast
  have hsplit : (∑ n ∈ N, Finsupp.single n (sourceCentralPair x n : ℂ)) =
      f3 + f4 + f5 := by
    dsimp only [f3, f4, f5]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    simp_rw [← Finsupp.single_add]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hpoint n hn]
  have hcompact3 (p : Fin 3 → ℕ) (hp : ∀ i, (p i).Prime)
      (hprod : (∏ i, p i) ∈ N) (hne : (w3 p : ℂ) ≠ 0) : ∀ i, p i ∈ Ps := by
    have hw : C (p 0) (p 1) ∧ p 1 ≤ p 2 :=
      (ite_ne_right_iff.mp (Complex.ofReal_ne_zero.mp hne)).1
    have hqpow : x ^ ((8639 : ℝ) / 50000) ≤ (p 1 : ℝ) :=
      (Real.le_logb_iff_rpow_le hx1 (Nat.cast_pos.mpr (hp 1).pos)).mp hw.1.1
    have hppow : x ^ ((8639 : ℝ) / 50000) ≤ (p 0 : ℝ) :=
      hqpow.trans ((Real.logb_lt_logb_iff hx1
        (Nat.cast_pos.mpr (hp 1).pos) (Nat.cast_pos.mpr (hp 0).pos)).mp hw.1.2.1).le
    have hlo : ∀ i : Fin 3, x ^ ((8639 : ℝ) / 50000) ≤ (p i : ℝ) := by
      intro i
      fin_cases i
      · exact hppow
      · exact hqpow
      · exact hqpow.trans (Nat.cast_le.mpr hw.2)
    exact hc3 x hx3 p hp hlo
      ((Nat.le_floor_iff hx2).mp (Finset.mem_Icc.mp hprod).2)
  have hf3 : f3 =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin 3 => Ps),
        Finsupp.single (∏ i, p i)
          (if (∏ i, p i) ∈ N then (w3 p : ℂ) else 0) :=
    prime_tuple_closed_sample_eq_compact 3 ⌈x⌉₊ ⌊2 * x⌋₊ Ps
      (fun _ hp => (Finset.mem_filter.mp hp).2) (fun p => (w3 p : ℂ)) hcompact3
  have hcompact4 (p : Fin 4 → ℕ) (hp : ∀ i, (p i).Prime)
      (hprod : (∏ i, p i) ∈ N) (hne : (w4 p : ℂ) ≠ 0) : ∀ i, p i ∈ Ps := by
    have hw : C (p 0) (p 1) ∧ p 1 ≤ p 2 ∧ p 2 ≤ p 3 :=
      (ite_ne_right_iff.mp (Complex.ofReal_ne_zero.mp hne)).1
    have hqpow : x ^ ((8639 : ℝ) / 50000) ≤ (p 1 : ℝ) :=
      (Real.le_logb_iff_rpow_le hx1 (Nat.cast_pos.mpr (hp 1).pos)).mp hw.1.1
    have hppow : x ^ ((8639 : ℝ) / 50000) ≤ (p 0 : ℝ) :=
      hqpow.trans ((Real.logb_lt_logb_iff hx1
        (Nat.cast_pos.mpr (hp 1).pos) (Nat.cast_pos.mpr (hp 0).pos)).mp hw.1.2.1).le
    have hlo : ∀ i : Fin 4, x ^ ((8639 : ℝ) / 50000) ≤ (p i : ℝ) := by
      intro i
      fin_cases i
      · exact hppow
      · exact hqpow
      · exact hqpow.trans (Nat.cast_le.mpr hw.2.1)
      · exact hqpow.trans (Nat.cast_le.mpr (hw.2.1.trans hw.2.2))
    exact hc4 x hx4 p hp hlo
      ((Nat.le_floor_iff hx2).mp (Finset.mem_Icc.mp hprod).2)
  have hf4 : f4 =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => Ps),
        Finsupp.single (∏ i, p i)
          (if (∏ i, p i) ∈ N then (w4 p : ℂ) else 0) :=
    prime_tuple_closed_sample_eq_compact 4 ⌈x⌉₊ ⌊2 * x⌋₊ Ps
      (fun _ hp => (Finset.mem_filter.mp hp).2) (fun p => (w4 p : ℂ)) hcompact4
  have hcompact5 (p : Fin 5 → ℕ) (hp : ∀ i, (p i).Prime)
      (hprod : (∏ i, p i) ∈ N) (hne : (w5 p : ℂ) ≠ 0) : ∀ i, p i ∈ Pf := by
    have hw : C (p 0) (p 1) ∧ p 1 ≤ p 2 ∧ p 2 ≤ p 3 ∧ p 3 ≤ p 4 :=
      (ite_ne_right_iff.mp (Complex.ofReal_ne_zero.mp hne)).1
    have hqpow : x ^ ((8639 : ℝ) / 50000) ≤ (p 1 : ℝ) :=
      (Real.le_logb_iff_rpow_le hx1 (Nat.cast_pos.mpr (hp 1).pos)).mp hw.1.1
    have hppow : x ^ ((8639 : ℝ) / 50000) ≤ (p 0 : ℝ) :=
      hqpow.trans ((Real.logb_lt_logb_iff hx1
        (Nat.cast_pos.mpr (hp 1).pos) (Nat.cast_pos.mpr (hp 0).pos)).mp hw.1.2.1).le
    have hlo : ∀ i : Fin 5, x ^ ((8639 : ℝ) / 50000) ≤ (p i : ℝ) := by
      intro i
      fin_cases i
      · exact hppow
      · exact hqpow
      · exact hqpow.trans (Nat.cast_le.mpr hw.2.1)
      · exact hqpow.trans (Nat.cast_le.mpr (hw.2.1.trans hw.2.2.1))
      · exact hqpow.trans (Nat.cast_le.mpr (hw.2.1.trans (hw.2.2.1.trans hw.2.2.2)))
    exact hc5 x hx5 p hp hlo
      ((Nat.le_floor_iff hx2).mp (Finset.mem_Icc.mp hprod).2)
  have hf5 : f5 =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin 5 => Pf),
        Finsupp.single (∏ i, p i)
          (if (∏ i, p i) ∈ N then (w5 p : ℂ) else 0) :=
    prime_tuple_closed_sample_eq_compact 5 ⌈x⌉₊ ⌊2 * x⌋₊ Pf
      (fun _ hp => (Finset.mem_filter.mp hp).2) (fun p => (w5 p : ℂ)) hcompact5
  change (∑ n ∈ N, Finsupp.single n (sourceCentralPair x n : ℂ)) = _
  rw [hsplit, hf3, hf4, hf5]
  simp only [N, w3, w4, w5, Finset.mem_Icc, Nat.ceil_le,
    Nat.le_floor_iff hx2, apply_ite Complex.ofReal, Complex.ofReal_one,
    Complex.ofReal_zero, ite_and]

open Classical in
theorem sourceCentralPair_five_monomial_representation_wide (x : ℝ) (hx : 1 < x) :
    ∃ M : Finset MinorantMonomialCut, M.card ≤ 32 ∧
      (∀ d ∈ M, d.numerator.Nonempty ∧ Disjoint d.numerator d.denominator ∧
        d.numerator.card + d.denominator.card ≤ 5 ∧ 0 < d.threshold) ∧
      let P := (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
        ⌊x ^ ((31 : ℝ) / 100)⌋₊).filter Nat.Prime
      let T := Fintype.piFinset (fun _ : Fin 5 => P)
      let α (p : ℕ) : ℝ := Real.logb x (p : ℝ)
      let C (p : Fin 5 → ℕ) : Prop :=
        x ≤ ((∏ i, p i : ℕ) : ℝ) ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x ∧
        (8639 : ℝ) / 50000 ≤ α (p 1) ∧ α (p 1) < α (p 0) ∧
        α (p 0) < (41361 : ℝ) / 100000 ∧
        (41361 : ℝ) / 100000 ≤ α (p 0) + α (p 1) ∧
        α (p 0) + α (p 1) ≤ (58639 : ℝ) / 100000 ∧
        p 1 ≤ p 2 ∧ p 2 ≤ p 3 ∧ p 3 ≤ p 4
      ∀ p ∈ T, ∀ q ∈ T,
        (∀ d ∈ M,
          (if d.lower then
            if d.strict then d.threshold < d.value p else d.threshold ≤ d.value p
          else if d.strict then d.value p < d.threshold else d.value p ≤ d.threshold) ↔
          (if d.lower then
            if d.strict then d.threshold < d.value q else d.threshold ≤ d.value q
          else if d.strict then d.value q < d.threshold else d.value q ≤ d.threshold)) →
        (C p ↔ C q) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  let M : Finset MinorantMonomialCut :=
    {⟨Finset.univ, ∅, x, true, false⟩,
      ⟨Finset.univ, ∅, 2 * x, false, false⟩,
      ⟨{1}, ∅, x ^ ((8639 : ℝ) / 50000), true, false⟩,
      ⟨{1}, {0}, 1, false, true⟩,
      ⟨{0}, ∅, x ^ ((41361 : ℝ) / 100000), false, true⟩} ∪
    {⟨{0, 1}, ∅, x ^ ((41361 : ℝ) / 100000), true, false⟩,
      ⟨{0, 1}, ∅, x ^ ((58639 : ℝ) / 100000), false, false⟩,
      ⟨{1}, {2}, 1, false, false⟩,
      ⟨{2}, {3}, 1, false, false⟩,
      ⟨{3}, {4}, 1, false, false⟩}
  have hMcard : M.card ≤ 32 :=
    (Finset.card_union_le _ _).trans
      ((Nat.add_le_add Finset.card_le_five Finset.card_le_five).trans (by decide))
  have hMdata (d : MinorantMonomialCut) (hd : d ∈ M) :
      d.numerator.Nonempty ∧ Disjoint d.numerator d.denominator ∧
        d.numerator.card + d.denominator.card ≤ 5 ∧ 0 < d.threshold := by
    simp only [M, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with (rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [Finset.card_fin, Finset.disjoint_left] <;>
        first | positivity | decide
  refine ⟨M, hMcard, hMdata, ?_⟩
  intro P T α C
  have hpos (p : Fin 5 → ℕ) (hp : p ∈ T) (i : Fin 5) : 0 < (p i : ℝ) :=
    Nat.cast_pos.mpr (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)).2.pos
  have hCeq (p : Fin 5 → ℕ) (hp : p ∈ T) : C p ↔
      ∀ d ∈ M,
        if d.lower then
          if d.strict then d.threshold < d.value p else d.threshold ≤ d.value p
        else if d.strict then d.value p < d.threshold else d.value p ≤ d.threshold := by
    have hlow : ((8639 : ℝ) / 50000 ≤ α (p 1)) ↔
        x ^ ((8639 : ℝ) / 50000) ≤ (p 1 : ℝ) :=
      Real.le_logb_iff_rpow_le hx (hpos p hp 1)
    have horder : (α (p 1) < α (p 0)) ↔ (p 1 : ℝ) / p 0 < 1 := by
      dsimp only [α]
      rw [Real.logb_lt_logb_iff hx (hpos p hp 1) (hpos p hp 0),
        div_lt_one (hpos p hp 0)]
    have htop : (α (p 0) < (41361 : ℝ) / 100000) ↔
        (p 0 : ℝ) < x ^ ((41361 : ℝ) / 100000) :=
      Real.logb_lt_iff_lt_rpow hx (hpos p hp 0)
    have hpairlo : ((41361 : ℝ) / 100000 ≤ α (p 0) + α (p 1)) ↔
        x ^ ((41361 : ℝ) / 100000) ≤ (p 0 : ℝ) * p 1 := by
      dsimp only [α]
      rw [← Real.logb_mul (hpos p hp 0).ne' (hpos p hp 1).ne',
        Real.le_logb_iff_rpow_le hx (mul_pos (hpos p hp 0) (hpos p hp 1))]
    have hpairhi : (α (p 0) + α (p 1) ≤ (58639 : ℝ) / 100000) ↔
        (p 0 : ℝ) * p 1 ≤ x ^ ((58639 : ℝ) / 100000) := by
      dsimp only [α]
      rw [← Real.logb_mul (hpos p hp 0).ne' (hpos p hp 1).ne',
        Real.logb_le_iff_le_rpow hx (mul_pos (hpos p hp 0) (hpos p hp 1))]
    have hnatorder (i k : Fin 5) : (p i ≤ p k) ↔ (p i : ℝ) / p k ≤ 1 := by
      rw [div_le_one (hpos p hp k)]
      exact Nat.cast_le.symm
    simp only [C, hlow, horder, htop, hpairlo, hpairhi, hnatorder, Nat.cast_prod]
    suffices h :
        ((x ≤ (∏ i, (p i : ℝ))) ∧
        ((∏ i, (p i : ℝ)) ≤ 2 * x) ∧
        (x ^ ((8639 : ℝ) / 50000) ≤ (p 1 : ℝ)) ∧
        ((p 1 : ℝ) / p 0 < 1) ∧
        ((p 0 : ℝ) < x ^ ((41361 : ℝ) / 100000)) ∧
        (x ^ ((41361 : ℝ) / 100000) ≤ (p 0 : ℝ) * p 1) ∧
        ((p 0 : ℝ) * p 1 ≤ x ^ ((58639 : ℝ) / 100000)) ∧
        ((p 1 : ℝ) / p 2 ≤ 1) ∧
        ((p 2 : ℝ) / p 3 ≤ 1) ∧
        ((p 3 : ℝ) / p 4 ≤ 1)) ↔
        ((x ^ ((41361 : ℝ) / 100000) ≤ (p 0 : ℝ) * p 1) ∧
        ((p 0 : ℝ) * p 1 ≤ x ^ ((58639 : ℝ) / 100000)) ∧
        ((p 1 : ℝ) / p 2 ≤ 1) ∧
        ((p 2 : ℝ) / p 3 ≤ 1) ∧
        (x ≤ (∏ i, (p i : ℝ))) ∧
        ((∏ i, (p i : ℝ)) ≤ 2 * x) ∧
        (x ^ ((8639 : ℝ) / 50000) ≤ (p 1 : ℝ)) ∧
        ((p 1 : ℝ) / p 0 < 1) ∧
        ((p 0 : ℝ) < x ^ ((41361 : ℝ) / 100000)) ∧
        ((p 3 : ℝ) / p 4 ≤ 1)) by
      simpa [M, MinorantMonomialCut.value] using h
    constructor
    · rintro ⟨ha, hb, hc, hd, he, hf, hg, hh, hi, hj⟩
      exact ⟨hf, hg, hh, hi, ha, hb, hc, hd, he, hj⟩
    · rintro ⟨hf, hg, hh, hi, ha, hb, hc, hd, he, hj⟩
      exact ⟨ha, hb, hc, hd, he, hf, hg, hh, hi, hj⟩
  intro p hp q hq hbits
  rw [hCeq p hp, hCeq q hq]
  constructor
  · intro h d hd
    exact (hbits d hd).mp (h d hd)
  · intro h d hd
    exact (hbits d hd).mpr (h d hd)

open Classical in
noncomputable def sourceT4ExponentMask (α : Fin 4 → ℝ) : Bool :=
  decide ((8639 : ℝ) / 50000 ≤ α 2 ∧ α 2 < α 1 ∧ α 1 < α 0 ∧
    α 0 < (41361 : ℝ) / 100000 ∧ (58639 : ℝ) / 100000 < α 0 + α 1 ∧
    α 1 < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000 ∧ α 2 ≤ α 3)

open Classical in
/--
The Boolean test for the four-exponent `U1` region. Its inequalities involve coordinates `1`,
`2`, and `3`; coordinate `0` is unrestricted by this mask.
-/
noncomputable def sourceU1ExponentMask (α : Fin 4 → ℝ) : Bool :=
  decide ((8639 : ℝ) / 50000 ≤ α 2 ∧ α 2 < α 1 ∧ α 1 < (41361 : ℝ) / 100000 ∧
    α 2 + α 3 < (41361 : ℝ) / 100000 ∧
    α 1 < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000 ∧ α 2 ≤ α 3)

open Classical in
theorem sum_four_prime_divisorsAntidiagonal {A : Type*} [AddCommMonoid A]
    (n : ℕ) (w : (Fin 4 → ℕ) → A) :
    (∑ a ∈ n.divisorsAntidiagonal, ∑ b ∈ a.2.divisorsAntidiagonal,
      ∑ c ∈ b.2.divisorsAntidiagonal,
        if a.1.Prime ∧ b.1.Prime ∧ c.1.Prime ∧ c.2.Prime then
          w ![a.1, b.1, c.1, c.2] else 0) =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => Nat.primesLE n),
        if (∏ i, p i) = n then w p else 0 := by
  let S : Finset (Σ _ : ℕ × ℕ, Σ _ : ℕ × ℕ, ℕ × ℕ) :=
    (n.divisorsAntidiagonal.sigma (fun a =>
      a.2.divisorsAntidiagonal.sigma (fun b => b.2.divisorsAntidiagonal))).filter
        (fun v => v.1.1.Prime ∧ v.2.1.1.Prime ∧ v.2.2.1.Prime ∧ v.2.2.2.Prime)
  let T : Finset (Fin 4 → ℕ) :=
    (Fintype.piFinset (fun _ : Fin 4 => Nat.primesLE n)).filter (fun p => ∏ i, p i = n)
  let f : (Σ _ : ℕ × ℕ, Σ _ : ℕ × ℕ, ℕ × ℕ) → Fin 4 → ℕ :=
    fun v => ![v.1.1, v.2.1.1, v.2.2.1, v.2.2.2]
  calc
    _ = ∑ v ∈ S, w (f v) := by
      simp only [S, f, Finset.sum_filter, Finset.sum_sigma]
    _ = ∑ p ∈ T, w p := by
      refine Finset.sum_bij (fun v _ => f v) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro v hv
        obtain ⟨hvs, hp, hq, hr, hs⟩ := Finset.mem_filter.mp hv
        obtain ⟨ha, hbc⟩ := Finset.mem_sigma.mp hvs
        obtain ⟨hb, hc⟩ := Finset.mem_sigma.mp hbc
        have hproduct : ∏ i, f v i = n := by
          rw [Fin.prod_univ_four]
          change v.1.1 * v.2.1.1 * v.2.2.1 * v.2.2.2 = n
          rw [Nat.mul_assoc, Nat.mul_assoc, (Nat.mem_divisorsAntidiagonal.mp hc).1,
            (Nat.mem_divisorsAntidiagonal.mp hb).1, (Nat.mem_divisorsAntidiagonal.mp ha).1]
        have hprime (i : Fin 4) : (f v i).Prime := by
          fin_cases i
          · simpa [f] using hp
          · simpa [f] using hq
          · simpa [f] using hr
          · simpa [f] using hs
        apply Finset.mem_filter.mpr
        refine ⟨Fintype.mem_piFinset.mpr (fun i => ?_), hproduct⟩
        apply Nat.mem_primesLE.mpr
        refine ⟨Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisorsAntidiagonal.mp ha).2) ?_,
          hprime i⟩
        rw [← hproduct]
        exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      · intro v hv u hu heq
        have h0 : v.1.1 = u.1.1 := congrArg (fun p : Fin 4 → ℕ => p 0) heq
        have h1 : v.2.1.1 = u.2.1.1 := congrArg (fun p : Fin 4 → ℕ => p 1) heq
        have h2 : v.2.2.1 = u.2.2.1 := congrArg (fun p : Fin 4 → ℕ => p 2) heq
        have h3 : v.2.2.2 = u.2.2.2 := congrArg (fun p : Fin 4 → ℕ => p 3) heq
        obtain ⟨_, hvt⟩ := Finset.mem_sigma.mp (Finset.mem_filter.mp hv).1
        obtain ⟨hvb, hvc⟩ := Finset.mem_sigma.mp hvt
        obtain ⟨_, hut⟩ := Finset.mem_sigma.mp (Finset.mem_filter.mp hu).1
        obtain ⟨hub, huc⟩ := Finset.mem_sigma.mp hut
        have hb : v.2.1.2 = u.2.1.2 := by
          rw [← (Nat.mem_divisorsAntidiagonal.mp hvc).1,
            ← (Nat.mem_divisorsAntidiagonal.mp huc).1, h2, h3]
        have ha : v.1.2 = u.1.2 := by
          rw [← (Nat.mem_divisorsAntidiagonal.mp hvb).1,
            ← (Nat.mem_divisorsAntidiagonal.mp hub).1, h1, hb]
        exact Sigma.ext (Prod.ext h0 ha)
          (heq_of_eq (Sigma.ext (Prod.ext h1 hb) (heq_of_eq (Prod.ext h2 h3))))
      · intro p hp
        obtain ⟨hpp, hpn⟩ := Finset.mem_filter.mp hp
        have hprime (i : Fin 4) := Nat.prime_of_mem_primesLE (Fintype.mem_piFinset.mp hpp i)
        have hn : n ≠ 0 := by
          rw [← hpn]
          exact Finset.prod_ne_zero_iff.mpr (fun i _ => (hprime i).ne_zero)
        have hprod : p 0 * (p 1 * (p 2 * p 3)) = n := by
          simpa only [Fin.prod_univ_four, Nat.mul_assoc] using hpn
        let v : Σ _ : ℕ × ℕ, Σ _ : ℕ × ℕ, ℕ × ℕ :=
          ⟨(p 0, p 1 * (p 2 * p 3)), ⟨(p 1, p 2 * p 3), (p 2, p 3)⟩⟩
        have hv : v ∈ S := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_sigma.mpr ⟨?_, Finset.mem_sigma.mpr ⟨?_, ?_⟩⟩,
            hprime 0, hprime 1, hprime 2, hprime 3⟩
          · exact Nat.mem_divisorsAntidiagonal.mpr ⟨hprod, hn⟩
          · exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl,
              mul_ne_zero (hprime 1).ne_zero (mul_ne_zero (hprime 2).ne_zero (hprime 3).ne_zero)⟩
          · exact Nat.mem_divisorsAntidiagonal.mpr
              ⟨rfl, mul_ne_zero (hprime 2).ne_zero (hprime 3).ne_zero⟩
        refine ⟨v, hv, ?_⟩
        funext i
        fin_cases i <;> simp [f, v]
    _ = _ := by simp only [T, Finset.sum_filter]

open Classical in
theorem sum_four_prime_divisorsAntidiagonal_residual_first
    {A : Type*} [AddCommMonoid A] (n : ℕ) (w : (Fin 4 → ℕ) → A) :
    (∑ a ∈ n.divisorsAntidiagonal, ∑ b ∈ a.2.divisorsAntidiagonal,
      ∑ c ∈ b.2.divisorsAntidiagonal,
        if a.1.Prime ∧ b.1.Prime ∧ c.1.Prime ∧ c.2.Prime then
          w ![c.2, a.1, b.1, c.1] else 0) =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => Nat.primesLE n),
        if (∏ i, p i) = n then w p else 0 := by
  let f : (Fin 4 → ℕ) → Fin 4 → ℕ := fun p => ![p 3, p 0, p 1, p 2]
  have hstart :
      (∑ a ∈ n.divisorsAntidiagonal, ∑ b ∈ a.2.divisorsAntidiagonal,
        ∑ c ∈ b.2.divisorsAntidiagonal,
          if a.1.Prime ∧ b.1.Prime ∧ c.1.Prime ∧ c.2.Prime then
            w ![c.2, a.1, b.1, c.1] else 0) =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => Nat.primesLE n),
        if (∏ i, p i) = n then w (f p) else 0 := by
    simpa [f] using sum_four_prime_divisorsAntidiagonal n (fun p => w (f p))
  rw [hstart]
  refine Finset.sum_bij (fun p _ => f p) ?_ ?_ ?_ ?_
  · intro p hp
    apply Fintype.mem_piFinset.mpr
    intro i
    fin_cases i
    · simpa [f] using Fintype.mem_piFinset.mp hp 3
    · simpa [f] using Fintype.mem_piFinset.mp hp 0
    · simpa [f] using Fintype.mem_piFinset.mp hp 1
    · simpa [f] using Fintype.mem_piFinset.mp hp 2
  · intro p _ q _ hpq
    funext i
    fin_cases i
    · exact congrArg (fun p : Fin 4 → ℕ => p 1) hpq
    · exact congrArg (fun p : Fin 4 → ℕ => p 2) hpq
    · exact congrArg (fun p : Fin 4 → ℕ => p 3) hpq
    · exact congrArg (fun p : Fin 4 → ℕ => p 0) hpq
  · intro p hp
    refine ⟨![p 1, p 2, p 3, p 0], ?_, ?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      fin_cases i
      · simpa using Fintype.mem_piFinset.mp hp 1
      · simpa using Fintype.mem_piFinset.mp hp 2
      · simpa using Fintype.mem_piFinset.mp hp 3
      · simpa using Fintype.mem_piFinset.mp hp 0
    · funext i
      fin_cases i <;> simp [f]
  · intro p _
    have hprod : (∏ i, f p i) = ∏ i, p i := by
      simp only [Fin.prod_univ_four]
      change p 3 * p 0 * p 1 * p 2 = p 0 * p 1 * p 2 * p 3
      ac_rfl
    rw [hprod]

open Classical in
theorem sourceU1_eq_four_prime_tuple_sum (x : ℝ) (hx : 1 < x) (n : ℕ) :
    sourceU1 x n =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => Nat.primesLE n),
        if (∏ i, p i) = n then
          (if sourceU1ExponentMask (fun i => Real.logb x (p i : ℝ)) then (1 : ℝ) else 0)
        else 0 := by
  have hshape (ps : List ℕ) (hps : ps ∈ siftedPrimeTuples x (5 : Fin 6)) :
      ∃ p q r : ℕ, ps = [p, q, r] := by
    have hm := (mem_siftedPrimeTuples_iff x hx (5 : Fin 6) ps).mp hps
    rcases ps with _ | ⟨p, _ | ⟨q, _ | ⟨r, _ | ⟨s, ss⟩⟩⟩⟩ <;> simp at hm ⊢
  have hstart := sum_triple_list_divisorsAntidiagonal (siftedPrimeTuples x (5 : Fin 6))
    hshape (fun _ r => if r.Prime then (1 : ℝ) else 0) n
  change sourceU1 x n = _ at hstart
  rw [hstart, ← sum_four_prime_divisorsAntidiagonal_residual_first n
    (fun p => if sourceU1ExponentMask (fun i => Real.logb x (p i : ℝ)) then 1 else 0)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have hm := mem_siftedPrimeTuples_iff x hx (5 : Fin 6) [a.1, b.1, c.1]
  dsimp only at hm
  simp only [hm]
  simp [sourceU1ExponentMask, ← ite_and, and_assoc, and_left_comm, and_comm]

open Classical in
theorem sourceT4_eventually_eq_four_prime_tuple_sum :
    ∃ X : ℝ, 3 ≤ X ∧ ∀ x : ℝ, X ≤ x → ∀ n : ℕ,
      x ≤ (n : ℝ) → (n : ℝ) ≤ 2 * x →
      sourceT4 x n =
        ∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => Nat.primesLE n),
          if (∏ i, p i) = n then
            (if sourceT4ExponentMask (fun i => Real.logb x (p i : ℝ)) then (1 : ℝ) else 0)
          else 0 := by
  obtain ⟨X, hX, hres⟩ := sourceT4_eventually_residual_prime
  refine ⟨X, hX, ?_⟩
  intro x hx n hnlo hnhi
  have hxOne : 1 < x := (by norm_num : (1 : ℝ) < 3).trans_le (hX.trans hx)
  rw [← sum_four_prime_divisorsAntidiagonal n
    (fun p => if sourceT4ExponentMask (fun i => Real.logb x (p i : ℝ)) then 1 else 0)]
  change (∑ a ∈ n.divisorsAntidiagonal, ∑ b ∈ a.2.divisorsAntidiagonal,
    ∑ c ∈ b.2.divisorsAntidiagonal, _) = _
  refine Finset.sum_congr rfl (fun a ha => ?_)
  refine Finset.sum_congr rfl (fun b hb => ?_)
  refine Finset.sum_congr rfl (fun c hc => ?_)
  let α (p : ℕ) : ℝ := Real.logb x (p : ℝ)
  let P : Prop := a.1.Prime ∧ b.1.Prime ∧ c.1.Prime ∧
    (8639 : ℝ) / 50000 ≤ α c.1 ∧ α c.1 < α b.1 ∧ α b.1 < α a.1 ∧
    α a.1 < (41361 : ℝ) / 100000 ∧ (58639 : ℝ) / 100000 < α a.1 + α b.1 ∧
    α b.1 < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000
  change (if P then roughWeight (c.1 : ℝ) c.2 else 0) =
    if a.1.Prime ∧ b.1.Prime ∧ c.1.Prime ∧ c.2.Prime then
      (if sourceT4ExponentMask ![α a.1, α b.1, α c.1, α c.2] then 1 else 0) else 0
  by_cases hP : P
  · rw [ite_eq_left hP]
    obtain ⟨hp, hq, hr, hξ, hrq, hqp, hpa, hpq, hζ⟩ := hP
    by_cases hs : c.2.Prime
    · have horder : α c.1 ≤ α c.2 ↔ (c.1 : ℝ) ≤ (c.2 : ℝ) :=
        Real.logb_le_logb hxOne (Nat.cast_pos.mpr hr.pos) (Nat.cast_pos.mpr hs.pos)
      have hm : sourceT4ExponentMask ![α a.1, α b.1, α c.1, α c.2] =
          decide ((c.1 : ℝ) ≤ (c.2 : ℝ)) := by
        simp [sourceT4ExponentMask, hξ, hrq, hqp, hpa, hpq, hζ, horder]
      rw [ite_eq_left ⟨hp, hq, hr, hs⟩, hm]
      rw [roughWeight_eq_ite_minFac (c.1 : ℝ) hs.ne_zero hs.ne_one, hs.minFac_eq]
      simp
    · rw [ite_eq_right (fun h => hs h.2.2.2)]
      by_contra hrough
      have hn : n = a.1 * b.1 * c.1 * c.2 := by
        symm
        rw [Nat.mul_assoc, Nat.mul_assoc, (Nat.mem_divisorsAntidiagonal.mp hc).1,
          (Nat.mem_divisorsAntidiagonal.mp hb).1, (Nat.mem_divisorsAntidiagonal.mp ha).1]
      exact hs ((hres x hx n a.1 b.1 c.1 c.2 hnlo hnhi hn
        hp hq hr hξ hrq hqp hpa hpq hζ hrough).1)
  · rw [ite_eq_right hP]
    by_cases hprime : a.1.Prime ∧ b.1.Prime ∧ c.1.Prime ∧ c.2.Prime
    · rw [ite_eq_left hprime]
      symm
      apply ite_eq_right
      intro hm
      have hcuts : (8639 : ℝ) / 50000 ≤ α c.1 ∧ α c.1 < α b.1 ∧
          α b.1 < α a.1 ∧ α a.1 < (41361 : ℝ) / 100000 ∧
          (58639 : ℝ) / 100000 < α a.1 + α b.1 ∧
          α b.1 < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000 ∧ α c.1 ≤ α c.2 := by
        unfold sourceT4ExponentMask at hm
        simpa using of_decide_eq_true hm
      exact hP ⟨hprime.1, hprime.2.1, hprime.2.2.1, hcuts.1, hcuts.2.1,
        hcuts.2.2.1, hcuts.2.2.2.1, hcuts.2.2.2.2.1, hcuts.2.2.2.2.2.1⟩
    · rw [ite_eq_right hprime]

open Classical in
theorem sourceT4_sub_sourceU1_eventually_central_tuple_sum :
    ∃ X : ℝ, 3 ≤ X ∧ ∀ x : ℝ, X ≤ x → ∀ n : ℕ,
      x ≤ (n : ℝ) → (n : ℝ) ≤ 2 * x →
      let α : (Fin 4 → ℕ) → Fin 4 → ℝ := fun p i => Real.logb x (p i : ℝ)
      let w : (Fin 4 → ℕ) → ℝ := fun p =>
        (if sourceT4ExponentMask (α p) then 1 else 0) -
          (if sourceU1ExponentMask (α p) then 1 else 0)
      sourceT4 x n - sourceU1 x n =
        (∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => Nat.primesLE n),
          if (∏ i, p i) = n then w p else 0) ∧
      (∀ p : Fin 4 → ℕ, |w p| ≤ 1) ∧
      ∀ p ∈ Fintype.piFinset (fun _ : Fin 4 => Nat.primesLE n),
        (∏ i, p i) = n → w p ≠ 0 →
        (∀ i, (8639 : ℝ) / 50000 ≤ α p i) ∧
        ∃ S : Finset (Fin 4), S.Nonempty ∧ S ≠ Finset.univ ∧
          (41361 : ℝ) / 100000 ≤ ∑ i ∈ S, α p i ∧
            (∑ i ∈ S, α p i) ≤ (58639 : ℝ) / 100000 := by
  obtain ⟨X, hX, hT4⟩ := sourceT4_eventually_eq_four_prime_tuple_sum
  let Y : ℝ := max X (Real.exp ((10 : ℝ) ^ 10 * Real.log 2))
  refine ⟨Y, hX.trans (le_max_left _ _), ?_⟩
  intro x hx n hnlo hnhi α w
  have hxX : X ≤ x := (le_max_left _ _).trans hx
  have hxOne : 1 < x := (by norm_num : (1 : ℝ) < 3).trans_le (hX.trans hxX)
  have hxPos : 0 < x := zero_lt_one.trans hxOne
  have hlogx : 0 < Real.log x := Real.log_pos hxOne
  have hlogLarge : (10 : ℝ) ^ 10 * Real.log 2 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hxPos).mpr ((le_max_right _ _).trans hx)
  have hsmall : Real.logb x 2 ≤ (1 / 10 ^ 10 : ℝ) := by
    apply (div_le_iff₀ hlogx).mpr
    nlinarith only [hlogLarge]
  refine ⟨?_, ?_, ?_⟩
  · rw [hT4 x hxX n hnlo hnhi, sourceU1_eq_four_prime_tuple_sum x hxOne,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hp : (∏ i, p i) = n <;> simp only [hp, ite_true, ite_false, w, α, sub_zero]
  · intro p
    dsimp only [w]
    cases sourceT4ExponentMask (α p) <;> cases sourceU1ExponentMask (α p) <;> norm_num
  · intro p hp hprod hw
    have hprime (i : Fin 4) := Nat.prime_of_mem_primesLE (Fintype.mem_piFinset.mp hp i)
    have hnonneg (i : Fin 4) : 0 ≤ α p i :=
      Real.logb_nonneg hxOne (by exact_mod_cast (hprime i).one_le)
    have hsum : (∑ i, α p i) = Real.logb x (n : ℝ) := by
      rw [← hprod, Nat.cast_prod]
      exact (Real.logb_prod Finset.univ _
        (fun i _ => (Nat.cast_pos.mpr (hprime i).pos).ne')).symm
    have hslo : 1 ≤ ∑ i, α p i := by
      rw [hsum]
      have h := Real.logb_le_logb_of_le hxOne hxPos hnlo
      simpa only [Real.logb_self_eq_one hxOne] using h
    have hshi : (∑ i, α p i) ≤ 1 + (1 / 10 ^ 10 : ℝ) := by
      rw [hsum]
      have h := Real.logb_le_logb_of_le hxOne (hxPos.trans_le hnlo) hnhi
      rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) hxPos.ne',
        Real.logb_self_eq_one hxOne] at h
      linarith only [h, hsmall]
    apply minorant_t4_sub_u1_typeII_support (α p) hnonneg hslo hshi
    simpa only [w, sourceT4ExponentMask, sourceU1ExponentMask, decide_eq_true_eq] using hw

open Classical in
theorem sourceT4U1_eventually_compact_tuple_geometry :
    ∃ X : ℝ, 3 ≤ X ∧ ∀ x : ℝ, X ≤ x → ∀ p : Fin 4 → ℕ,
      (∀ i, (p i).Prime) →
      (∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ →
      let α : Fin 4 → ℝ := fun i => Real.logb x (p i : ℝ)
      ((if sourceT4ExponentMask α then (1 : ℝ) else 0) -
        (if sourceU1ExponentMask α then 1 else 0)) ≠ 0 →
      (∀ i, p i ∈ (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
        ⌊x ^ ((9 : ℝ) / 10)⌋₊).filter Nat.Prime) ∧
      ∃ S : Finset (Fin 4), S.Nonempty ∧ S ≠ Finset.univ ∧
        x ^ ((41361 : ℝ) / 100000) ≤ ((∏ i ∈ S, p i : ℕ) : ℝ) ∧
        ((∏ i ∈ S, p i : ℕ) : ℝ) ≤ x ^ ((58639 : ℝ) / 100000) := by
  obtain ⟨X₀, hX₀, hsource⟩ := sourceT4_sub_sourceU1_eventually_central_tuple_sum
  refine ⟨max X₀ (Real.exp (100 * Real.log 2)), hX₀.trans (le_max_left _ _), ?_⟩
  intro x hx p hp hprod α hw
  have hxX : X₀ ≤ x := (le_max_left _ _).trans hx
  have hx1 : 1 < x := (by norm_num : (1 : ℝ) < 3).trans_le (hX₀.trans hxX)
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hp0 (i : Fin 4) : 0 < (p i : ℝ) := Nat.cast_pos.mpr (hp i).pos
  have hpn : 0 < ∏ i, p i := Finset.prod_pos (fun i _ => (hp i).pos)
  have hpN : p ∈ Fintype.piFinset (fun _ : Fin 4 => Nat.primesLE (∏ i, p i)) := by
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Nat.mem_primesLE.mpr ⟨Nat.le_of_dvd hpn
      (Finset.dvd_prod_of_mem p (Finset.mem_univ i)), hp i⟩
  have hnlo : x ≤ ((∏ i, p i : ℕ) : ℝ) :=
    Nat.le_of_ceil_le (Finset.mem_Icc.mp hprod).1
  have hnhi : ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x :=
    (Nat.cast_le.mpr (Finset.mem_Icc.mp hprod).2).trans (Nat.floor_le (by positivity))
  obtain ⟨hlow, S, hS, hSproper, hSlo, hShi⟩ :=
    (hsource x hxX (∏ i, p i) hnlo hnhi).2.2 p hpN rfl hw
  have hsum : (∑ i, α i) = Real.logb x ((∏ i, p i : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
    exact (Real.logb_prod Finset.univ _ (fun i _ => (hp0 i).ne')).symm
  have hlogLarge : 100 * Real.log 2 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hx0).mpr ((le_max_right _ _).trans hx)
  have hsmall : Real.logb x 2 ≤ (1 / 100 : ℝ) := by
    apply (div_le_iff₀ hlogx).mpr
    nlinarith only [hlogLarge]
  have htotal : (∑ i, α i) ≤ 1 + (1 / 100 : ℝ) := by
    rw [hsum]
    have h := Real.logb_le_logb_of_le hx1 (by exact_mod_cast hpn) hnhi
    rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne',
      Real.logb_self_eq_one hx1] at h
    linarith only [h, hsmall]
  have hupper (i : Fin 4) : α i ≤ (9 : ℝ) / 10 := by
    have h0 := hlow 0
    have h1 := hlow 1
    have h2 := hlow 2
    have h3 := hlow 3
    change (8639 : ℝ) / 50000 ≤ α 0 at h0
    change (8639 : ℝ) / 50000 ≤ α 1 at h1
    change (8639 : ℝ) / 50000 ≤ α 2 at h2
    change (8639 : ℝ) / 50000 ≤ α 3 at h3
    rw [Fin.sum_univ_four] at htotal
    fin_cases i
    · change α 0 ≤ (9 : ℝ) / 10
      linarith
    · change α 1 ≤ (9 : ℝ) / 10
      linarith
    · change α 2 ≤ (9 : ℝ) / 10
      linarith
    · change α 3 ≤ (9 : ℝ) / 10
      linarith
  have hSpos : 0 < ((∏ i ∈ S, p i : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => (hp i).pos)
  refine ⟨?_, S, hS, hSproper, ?_, ?_⟩
  · intro i
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hp i⟩
    · apply Nat.ceil_le.mpr
      exact (Real.le_logb_iff_rpow_le hx1 (hp0 i)).mp (hlow i)
    · apply Nat.le_floor
      exact (Real.logb_le_iff_le_rpow hx1 (hp0 i)).mp (hupper i)
  · have hlogprod : Real.logb x ((∏ i ∈ S, p i : ℕ) : ℝ) = ∑ i ∈ S, α i := by
      rw [Nat.cast_prod]
      exact Real.logb_prod S _ (fun i _ => (hp0 i).ne')
    apply (Real.le_logb_iff_rpow_le hx1 hSpos).mp
    rw [hlogprod]
    exact hSlo
  · have hlogprod : Real.logb x ((∏ i ∈ S, p i : ℕ) : ℝ) = ∑ i ∈ S, α i := by
      rw [Nat.cast_prod]
      exact Real.logb_prod S _ (fun i _ => (hp0 i).ne')
    apply (Real.logb_le_iff_le_rpow hx1 hSpos).mp
    rw [hlogprod]
    exact hShi

open Classical in
theorem sourceT4_sub_sourceU1_eventually_four_prime_finsupp :
    ∃ X : ℝ, 3 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      let P := (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
        ⌊x ^ ((9 : ℝ) / 10)⌋₊).filter Nat.Prime
      let T := Fintype.piFinset (fun _ : Fin 4 => P)
      let α : (Fin 4 → ℕ) → Fin 4 → ℝ := fun p i => Real.logb x (p i : ℝ)
      let w : (Fin 4 → ℕ) → ℝ := fun p =>
        (if sourceT4ExponentMask (α p) then 1 else 0) -
          (if sourceU1ExponentMask (α p) then 1 else 0)
      (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
        Finsupp.single n ((sourceT4 x n - sourceU1 x n : ℝ) : ℂ)) =
      ∑ p ∈ T, Finsupp.single (∏ i, p i)
        (if (∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ then (w p : ℂ) else 0) := by
  obtain ⟨X₁, hX₁, hsource⟩ := sourceT4_sub_sourceU1_eventually_central_tuple_sum
  obtain ⟨X₂, _hX₂, hcompact⟩ := sourceT4U1_eventually_compact_tuple_geometry
  refine ⟨max X₁ X₂, hX₁.trans (le_max_left _ _), ?_⟩
  intro x hx P T α w
  have hx₁ : X₁ ≤ x := (le_max_left _ _).trans hx
  have hx₂ : X₂ ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := (by norm_num : (0 : ℝ) < 3).trans_le (hX₁.trans hx₁)
  let N := Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊
  have hprime (p : Fin 4 → ℕ) (hp : p ∈ T) (i : Fin 4) : (p i).Prime :=
    (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)).2
  ext n
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
  by_cases hn : n ∈ N
  · have hnlo : x ≤ (n : ℝ) := Nat.le_of_ceil_le (Finset.mem_Icc.mp hn).1
    have hnhi : (n : ℝ) ≤ 2 * x :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le (by positivity))
    have hs := (hsource x hx₁ n hnlo hnhi).1
    have hcast : ((sourceT4 x n - sourceU1 x n : ℝ) : ℂ) =
        ∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => Nat.primesLE n),
          if (∏ i, p i) = n then (w p : ℂ) else 0 := by
      rw [hs, Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hpn : (∏ i, p i) = n
      · simp only [ite_eq_left hpn]
        rfl
      · simp only [ite_eq_right hpn, Complex.ofReal_zero]
    rw [ite_eq_left hn, hcast]
    have heq :
        (∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => Nat.primesLE n),
          if (∏ i, p i) = n then (w p : ℂ) else 0) =
        ∑ p ∈ T, if (∏ i, p i) = n then (w p : ℂ) else 0 := by
      apply Finset.sum_congr_of_eq_on_inter
      · intro p hp hpT
        by_cases hpn : (∏ i, p i) = n
        · by_cases hw : w p = 0
          · simp only [ite_eq_left hpn, hw, Complex.ofReal_zero]
          · exfalso
            apply hpT
            apply Fintype.mem_piFinset.mpr
            exact (hcompact x hx₂ p
              (fun i => Nat.prime_of_mem_primesLE (Fintype.mem_piFinset.mp hp i))
              (by simpa only [hpn] using hn) hw).1
        · exact ite_eq_right hpn
      · intro p hp hpN
        by_cases hpn : (∏ i, p i) = n
        · exfalso
          apply hpN
          apply Fintype.mem_piFinset.mpr
          intro i
          apply Nat.mem_primesLE.mpr
          refine ⟨Nat.le_of_dvd (by
            rw [← hpn]
            exact Finset.prod_pos (fun i _ => (hprime p hp i).pos)) ?_, hprime p hp i⟩
          rw [← hpn]
          exact Finset.dvd_prod_of_mem p (Finset.mem_univ i)
        · exact ite_eq_right hpn
      · intro _ _ _
        rfl
    rw [heq]
    apply Finset.sum_congr rfl
    intro p _hp
    by_cases hpn : (∏ i, p i) = n
    · have hm : (∏ i, p i) ∈ N := by simpa only [hpn] using hn
      dsimp only [N] at hm
      simp only [ite_eq_left hpn, ite_eq_left hm]
    · simp only [ite_eq_right hpn]
  · rw [ite_eq_right hn]
    symm
    apply Finset.sum_eq_zero
    intro p _hp
    by_cases hpn : (∏ i, p i) = n
    · have hm : (∏ i, p i) ∉ N := by simpa only [hpn] using hn
      dsimp only [N] at hm
      simp only [ite_eq_left hpn, ite_eq_right hm]
    · simp only [ite_eq_right hpn]

open Classical in
/--
The combined collection of multiplicative boundary cuts needed for the `T4` and `U1` regions,
including the total-product window `[x, 2 * x]`. The collection supplies their boundaries rather
than defining either region by a single conjunction.
-/
noncomputable def sourceT4U1MonomialCuts (x : ℝ) : Finset (MinorantSmallMonomialCut 4) :=
  {⟨Finset.univ, ∅, x, true, false⟩,
    ⟨Finset.univ, ∅, 2 * x, false, false⟩,
    ⟨{2}, ∅, x ^ ((8639 : ℝ) / 50000), true, false⟩,
    ⟨{2}, {1}, 1, false, true⟩,
    ⟨{1}, {0}, 1, false, true⟩,
    ⟨{0}, ∅, x ^ ((41361 : ℝ) / 100000), false, true⟩} ∪
  {⟨{0, 1}, ∅, x ^ ((58639 : ℝ) / 100000), true, true⟩,
    ⟨{1}, ∅, x ^ (1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000), false, true⟩,
    ⟨{2}, {3}, 1, false, false⟩,
    ⟨{1}, ∅, x ^ ((41361 : ℝ) / 100000), false, true⟩,
    ⟨{2, 3}, ∅, x ^ ((41361 : ℝ) / 100000), false, true⟩}

theorem sourceT4U1MonomialCuts_card_le (x : ℝ) :
    (sourceT4U1MonomialCuts x).card ≤ 32 := by
  classical
  unfold sourceT4U1MonomialCuts
  exact (Finset.card_union_le _ _).trans
    ((Nat.add_le_add Finset.card_le_six Finset.card_le_five).trans (by decide))

theorem sourceT4U1MonomialCuts_data (x : ℝ) (hx : 0 < x)
    (d : (MinorantSmallMonomialCut 4)) (hd : d ∈ sourceT4U1MonomialCuts x) :
    d.numerator.Nonempty ∧ Disjoint d.numerator d.denominator ∧
      d.numerator.card + d.denominator.card ≤ 4 ∧ 0 < d.threshold := by
  classical
  simp only [sourceT4U1MonomialCuts, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with (rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl | rfl | rfl) <;>
      norm_num [Finset.card_fin, Finset.disjoint_left] <;>
        first | positivity | decide | exact ⟨Finset.card_le_univ _, by positivity⟩

open Classical in
theorem sourceT4U1MonomialCuts_boolean (x : ℝ) (hx : 1 < x)
    (p q : Fin 4 → ℕ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (htests : ∀ d ∈ sourceT4U1MonomialCuts x,
      (if d.lower then
        if d.strict then d.threshold < d.value p else d.threshold ≤ d.value p
      else if d.strict then d.value p < d.threshold else d.value p ≤ d.threshold) ↔
      (if d.lower then
        if d.strict then d.threshold < d.value q else d.threshold ≤ d.value q
      else if d.strict then d.value q < d.threshold else d.value q ≤ d.threshold)) :
    (((∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧
        sourceT4ExponentMask (fun i => Real.logb x (p i : ℝ)) = true ∧
        sourceU1ExponentMask (fun i => Real.logb x (p i : ℝ)) = false) ↔
      ((∏ i, q i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧
        sourceT4ExponentMask (fun i => Real.logb x (q i : ℝ)) = true ∧
        sourceU1ExponentMask (fun i => Real.logb x (q i : ℝ)) = false)) ∧
    (((∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧
        sourceU1ExponentMask (fun i => Real.logb x (p i : ℝ)) = true ∧
        sourceT4ExponentMask (fun i => Real.logb x (p i : ℝ)) = false) ↔
      ((∏ i, q i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧
        sourceU1ExponentMask (fun i => Real.logb x (q i : ℝ)) = true ∧
        sourceT4ExponentMask (fun i => Real.logb x (q i : ℝ)) = false)) := by
  have hmask (r : Fin 4 → ℕ) (hr : ∀ i, 0 < r i) :
      (sourceT4ExponentMask (fun i => Real.logb x (r i : ℝ)) = true ↔
        x ^ ((8639 : ℝ) / 50000) ≤ (r 2 : ℝ) ∧
          (r 2 : ℝ) / r 1 < 1 ∧ (r 1 : ℝ) / r 0 < 1 ∧
          (r 0 : ℝ) < x ^ ((41361 : ℝ) / 100000) ∧
          x ^ ((58639 : ℝ) / 100000) < (r 0 : ℝ) * r 1 ∧
          (r 1 : ℝ) < x ^ (1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000) ∧
          (r 2 : ℝ) / r 3 ≤ 1) ∧
      (sourceU1ExponentMask (fun i => Real.logb x (r i : ℝ)) = true ↔
        x ^ ((8639 : ℝ) / 50000) ≤ (r 2 : ℝ) ∧
          (r 2 : ℝ) / r 1 < 1 ∧ (r 1 : ℝ) < x ^ ((41361 : ℝ) / 100000) ∧
          (r 2 : ℝ) * r 3 < x ^ ((41361 : ℝ) / 100000) ∧
          (r 1 : ℝ) < x ^ (1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000) ∧
          (r 2 : ℝ) / r 3 ≤ 1) := by
    have hpos (i : Fin 4) : 0 < (r i : ℝ) := by exact_mod_cast hr i
    have horder (i k : Fin 4) :
        (Real.logb x (r i : ℝ) < Real.logb x (r k : ℝ) ↔ (r i : ℝ) / r k < 1) ∧
        (Real.logb x (r i : ℝ) ≤ Real.logb x (r k : ℝ) ↔ (r i : ℝ) / r k ≤ 1) := by
      rw [Real.logb_lt_logb_iff hx (hpos i) (hpos k),
        Real.logb_le_logb hx (hpos i) (hpos k),
        div_lt_one (hpos k), div_le_one (hpos k)]
      exact ⟨Iff.rfl, Iff.rfl⟩
    have hlow (i : Fin 4) (t : ℝ) :
        t ≤ Real.logb x (r i : ℝ) ↔ x ^ t ≤ (r i : ℝ) :=
      Real.le_logb_iff_rpow_le hx (hpos i)
    have hlt (i : Fin 4) (t : ℝ) :
        Real.logb x (r i : ℝ) < t ↔ (r i : ℝ) < x ^ t :=
      Real.logb_lt_iff_lt_rpow hx (hpos i)
    have hpairlt (i k : Fin 4) (t : ℝ) :
        Real.logb x (r i : ℝ) + Real.logb x (r k : ℝ) < t ↔
          (r i : ℝ) * r k < x ^ t := by
      rw [← Real.logb_mul (hpos i).ne' (hpos k).ne',
        Real.logb_lt_iff_lt_rpow hx (mul_pos (hpos i) (hpos k))]
    have hpairgt (i k : Fin 4) (t : ℝ) :
        t < Real.logb x (r i : ℝ) + Real.logb x (r k : ℝ) ↔
          x ^ t < (r i : ℝ) * r k := by
      rw [← Real.logb_mul (hpos i).ne' (hpos k).ne',
        Real.lt_logb_iff_rpow_lt hx (mul_pos (hpos i) (hpos k))]
    constructor
    · simp only [sourceT4ExponentMask, decide_eq_true_eq]
      rw [(horder 2 1).1, (horder 1 0).1, (horder 2 3).2]
      simp only [hlow, hlt, hpairgt]
    · simp only [sourceU1ExponentMask, decide_eq_true_eq]
      rw [(horder 2 1).1, (horder 2 3).2]
      simp only [hlow, hlt, hpairlt]
  have hcarrier (r : Fin 4 → ℕ) :
      (∏ i, r i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ↔
        x ≤ ∏ i, (r i : ℝ) ∧ (∏ i, (r i : ℝ)) ≤ 2 * x := by
    rw [Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff (by positivity)]
    push_cast
    rfl
  simp only [sourceT4U1MonomialCuts, Finset.forall_mem_union,
    Finset.forall_mem_insert, Finset.mem_singleton, forall_eq] at htests
  obtain ⟨⟨hlo, hhi, hxi, h21, h10, h0a⟩, h01, h1z, h23, h1a, h23a⟩ := htests
  simp only [MinorantSmallMonomialCut.value, Bool.false_eq_true, ite_true, ite_false,
    Finset.prod_empty, Finset.prod_singleton, div_one,
    Finset.prod_pair (by decide : (0 : Fin 4) ≠ 1),
    Finset.prod_pair (by decide : (2 : Fin 4) ≠ 3)] at hlo hhi hxi h21 h10 h0a h01 h1z h23 h1a h23a
  have hc : ((∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊) ↔
      ((∏ i, q i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊) := by
    rw [hcarrier p, hcarrier q]
    exact and_congr hlo hhi
  have hT : sourceT4ExponentMask (fun i => Real.logb x (p i : ℝ)) =
      sourceT4ExponentMask (fun i => Real.logb x (q i : ℝ)) := by
    apply Bool.eq_iff_iff.mpr
    rw [(hmask p hp).1, (hmask q hq).1]
    exact and_congr hxi (and_congr h21 (and_congr h10
      (and_congr h0a (and_congr h01 (and_congr h1z h23)))))
  have hU : sourceU1ExponentMask (fun i => Real.logb x (p i : ℝ)) =
      sourceU1ExponentMask (fun i => Real.logb x (q i : ℝ)) := by
    apply Bool.eq_iff_iff.mpr
    rw [(hmask p hp).2, (hmask q hq).2]
    exact and_congr hxi (and_congr h21 (and_congr h1a
      (and_congr h23a (and_congr h1z h23))))
  constructor <;> rw [hT, hU] <;> exact and_congr hc Iff.rfl

open Classical in
theorem sourceT4U1_tuple_discrepancy_split
    (x : ℝ) (T : Finset (Fin 4 → ℕ)) (N : Finset ℕ) (q a : ℕ) :
    fullDiscrepancy (∑ p ∈ T, Finsupp.single (∏ i, p i)
      (if (∏ i, p i) ∈ N then
        (((if sourceT4ExponentMask (fun i => Real.logb x (p i : ℝ)) then (1 : ℝ) else 0) -
          (if sourceU1ExponentMask (fun i => Real.logb x (p i : ℝ)) then 1 else 0) : ℝ) : ℂ)
      else 0)) q a =
    fullDiscrepancy (∑ p ∈ T, Finsupp.single (∏ i, p i)
      (@ite ℂ ((∏ i, p i) ∈ N ∧
        sourceT4ExponentMask (fun i => Real.logb x (p i : ℝ)) = true ∧
        sourceU1ExponentMask (fun i => Real.logb x (p i : ℝ)) = false)
        (Classical.propDecidable _) 1 0)) q a -
    fullDiscrepancy (∑ p ∈ T, Finsupp.single (∏ i, p i)
      (@ite ℂ ((∏ i, p i) ∈ N ∧
        sourceU1ExponentMask (fun i => Real.logb x (p i : ℝ)) = true ∧
        sourceT4ExponentMask (fun i => Real.logb x (p i : ℝ)) = false)
        (Classical.propDecidable _) 1 0)) q a := by
  simp only [fullDiscrepancy_indexed_sample, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hn : (∏ i, p i) ∈ N
  · simp only [hn, ite_true, true_and]
    cases sourceT4ExponentMask (fun i => Real.logb x (p i : ℝ)) <;>
      cases sourceU1ExponentMask (fun i => Real.logb x (p i : ℝ)) <;> norm_num
  · simp [hn]

#print axioms sourceLargeFirst_eventually_finsupp
#print axioms sourceCentralPair_eventually_finsupp
#print axioms sourceCentralPair_five_monomial_representation_wide
#print axioms sourceT4_sub_sourceU1_eventually_central_tuple_sum
#print axioms sourceT4_sub_sourceU1_eventually_four_prime_finsupp
#print axioms sourceT4U1MonomialCuts_boolean

end PrimeGap182Analytic.Harman
