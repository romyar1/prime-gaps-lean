import HarmanBuchstab182

/-! Actual five-prime tuple identities for T5 and U3 at the new cutoffs.
Adapted from Apache-2.0 PrimeGaps186, with the source hash checked by
scripts/build_harman_five_prime.py. The residual prime argument uses the
actual inequality 6 * .17278 > 1 and retains [x,2x] exactly. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

theorem exceptional_residual_prime {x : ℝ} (hx : 1 < x)
    (hg : 2 * x < x ^ (6 * ((8639 : ℝ) / 50000)))
    {n : ℕ} (hlo : x ≤ (n : ℝ)) (hhi : (n : ℝ) ≤ 2 * x)
    (p : Fin 4 → ℕ) (hp : ∀ i, (p i).Prime) (r : ℕ)
    (heq : (∏ i, p i) * r = n)
    (h0 : ((8639 : ℝ) / 50000) ≤ Real.logb x (p 3 : ℝ))
    (h32 : Real.logb x (p 3 : ℝ) < Real.logb x (p 2 : ℝ))
    (h21 : Real.logb x (p 2 : ℝ) < Real.logb x (p 1 : ℝ))
    (h10 : Real.logb x (p 1 : ℝ) < Real.logb x (p 0 : ℝ))
    (hs : Real.logb x (p 0 : ℝ) + Real.logb x (p 1 : ℝ) < (41361 : ℝ) / 100000)
    (hr : r ≠ 0 ∧ ∀ q ∈ r.primeFactors, (p 3 : ℝ) ≤ (q : ℝ)) :
    r.Prime ∧ (p 3 : ℝ) ≤ (r : ℝ) := by
  classical
  have hx0 : 0 < x := by linarith
  have hpos (i : Fin 4) : 0 < (p i : ℝ) := Nat.cast_pos.mpr (hp i).pos
  have hlow : ∀ i : Fin 4, x ^ ((8639 : ℝ) / 50000) ≤ (p i : ℝ) := by
    intro i
    apply (Real.le_logb_iff_rpow_le hx (hpos i)).mp
    fin_cases i
    · change (8639 : ℝ) / 50000 ≤ Real.logb x (p 0 : ℝ)
      linarith
    · change (8639 : ℝ) / 50000 ≤ Real.logb x (p 1 : ℝ)
      linarith
    · change (8639 : ℝ) / 50000 ≤ Real.logb x (p 2 : ℝ)
      linarith
    · change (8639 : ℝ) / 50000 ≤ Real.logb x (p 3 : ℝ)
      exact h0
  have hn0 : 0 < (n : ℝ) := hx0.trans_le hlo
  have hrone : r ≠ 1 := by
    intro hr1
    have heqp : (∏ i, p i) = n := by simpa [hr1] using heq
    have hl : Real.logb x (n : ℝ) < 2 * ((41361 : ℝ) / 100000) := by
      rw [← heqp, Nat.cast_prod,
        Real.logb_prod Finset.univ (fun i : Fin 4 => (p i : ℝ))
          (fun i _ => (hpos i).ne')]
      simp only [Fin.sum_univ_four]
      linarith
    have hlt : (n : ℝ) < x ^ (2 * ((41361 : ℝ) / 100000)) :=
      (Real.logb_lt_iff_lt_rpow hx hn0).mp hl
    have hlx : x ^ (2 * ((41361 : ℝ) / 100000)) < x := by
      simpa using Real.rpow_lt_rpow_of_exponent_lt hx
        (by norm_num : (2 * ((41361 : ℝ) / 100000)) < 1)
    exact (not_lt_of_ge hlo) (hlt.trans hlx)
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr.1
  have hrp : r.Prime := by
    by_contra hnp
    have hm := Nat.minFac_sq_le_self hrpos hnp
    have hmprime := Nat.minFac_prime hrone
    have hmem : r.minFac ∈ r.primeFactors :=
      (Nat.mem_primeFactors_of_ne_zero hr.1).mpr ⟨hmprime, Nat.minFac_dvd r⟩
    have hmlo := hr.2 (Nat.minFac r) hmem
    have hrlo : (x ^ ((8639 : ℝ) / 50000)) ^ 2 ≤ (r : ℝ) := by
      have hmin : x ^ ((8639 : ℝ) / 50000) ≤ (r.minFac : ℝ) := (hlow 3).trans hmlo
      have hsquare : (r.minFac : ℝ) ^ 2 ≤ (r : ℝ) := by exact_mod_cast hm
      exact (pow_le_pow_left₀ (by positivity) hmin 2).trans hsquare
    have hfour : (x ^ ((8639 : ℝ) / 50000)) ^ 4 ≤ (∏ i, (p i : ℝ)) := by
      simpa using (Finset.prod_le_prod (s := Finset.univ)
        (f := fun _ : Fin 4 => x ^ ((8639 : ℝ) / 50000))
        (g := fun i : Fin 4 => (p i : ℝ)) (by intro i hi; positivity)
        (fun i hi => hlow i))
    have hh : x ^ (6 * ((8639 : ℝ) / 50000)) ≤ (n : ℝ) := by
      have hm' := mul_le_mul hfour hrlo (by positivity) (by positivity)
      rw [← Nat.cast_prod, ← Nat.cast_mul, heq] at hm'
      have hxp : (x ^ ((8639 : ℝ) / 50000)) ^ (6 : ℕ) =
          x ^ (6 * ((8639 : ℝ) / 50000)) := by
        rw [← Real.rpow_mul_natCast hx0.le _ 6]
        norm_num [mul_comm]
      simpa only [← hxp, ← pow_add, show 4 + 2 = 6 from rfl] using hm'
    linarith
  have hrle : (p 3 : ℝ) ≤ (r : ℝ) := by
    simpa only using hr.2 r (hrp.mem_primeFactors_self)
  exact ⟨hrp, hrle⟩

open Classical in
theorem sourceU3_eq_five_prime_sum (x : ℝ) (hx : 1 < x) (n : ℕ) :
    sourceU3 x n =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin 5 => Nat.primesLE n),
        if (∏ i, p i) = n ∧ [p 0, p 1, p 2] ∈ siftedPrimeTuples x (5 : Fin 6) ∧
            x ^ ((8639 : ℝ) / 50000) ≤ (p 3 : ℝ) ∧ p 3 ≤ p 4
        then 1 else 0 := by
  let F := siftedPrimeTuples x (5 : Fin 6)
  let z : ℝ := x ^ ((8639 : ℝ) / 50000)
  let S : Finset (Σ _ : List ℕ × (ℕ × ℕ), ℕ × ℕ) :=
    ((F.product n.divisorsAntidiagonal).sigma
      (fun u => u.2.2.divisorsAntidiagonal)).filter
      (fun t => t.1.2.1 = t.1.1.prod ∧ t.2.1.Prime ∧ t.2.2.Prime ∧
        z ≤ (t.2.1 : ℝ) ∧ t.2.1 ≤ t.2.2)
  let T := (Fintype.piFinset (fun _ : Fin 5 => Nat.primesLE n)).filter
    (fun p => (∏ i, p i) = n ∧ [p 0, p 1, p 2] ∈ F ∧
      z ≤ (p 3 : ℝ) ∧ p 3 ≤ p 4)
  let f : (Fin 5 → ℕ) → (Σ _ : List ℕ × (ℕ × ℕ), ℕ × ℕ) := fun p =>
    ⟨([p 0, p 1, p 2], (p 0 * p 1 * p 2, p 3 * p 4)), (p 3, p 4)⟩
  have hprod (p : Fin 5 → ℕ) :
      (∏ i, p i) = (p 0 * p 1 * p 2) * (p 3 * p 4) := by
    simp only [Fin.prod_univ_succ]
    change p 0 * (p 1 * (p 2 * (p 3 * (p 4 * 1)))) =
      (p 0 * p 1 * p 2) * (p 3 * p 4)
    ring
  have hshape (ps : List ℕ) (hps : ps ∈ F) : ∃ a b c : ℕ, ps = [a, b, c] := by
    have hm := (mem_siftedPrimeTuples_iff x hx (5 : Fin 6) ps).mp hps
    dsimp only at hm
    rcases ps with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, ds⟩⟩⟩⟩
    · exact False.elim hm
    · exact False.elim hm
    · exact False.elim hm
    · exact ⟨a, b, c, rfl⟩
    · exact False.elim hm
  have hsum : (∑ p ∈ T, (1 : ℝ)) = ∑ t ∈ S, (1 : ℝ) := by
    refine Finset.sum_bij (fun p _ => f p) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro p hp
      obtain ⟨hpP, hpN, hpF, hpz, hp34⟩ := Finset.mem_filter.mp hp
      have hprime (i : Fin 5) : (p i).Prime :=
        Nat.prime_of_mem_primesLE ((Fintype.mem_piFinset.mp hpP) i)
      have hn0 : n ≠ 0 := by
        rw [← hpN]
        exact Finset.prod_ne_zero_iff.mpr (fun i _ => (hprime i).ne_zero)
      have hpN' : (p 0 * p 1 * p 2) * (p 3 * p 4) = n :=
        (hprod p).symm.trans hpN
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sigma.mpr ⟨Finset.mem_product.mpr ⟨hpF, ?_⟩, ?_⟩, ?_⟩
      · exact Nat.mem_divisorsAntidiagonal.mpr ⟨hpN', hn0⟩
      · exact Nat.mem_divisorsAntidiagonal.mpr
          ⟨rfl, mul_ne_zero (hprime 3).ne_zero (hprime 4).ne_zero⟩
      · refine ⟨?_, hprime 3, hprime 4, hpz, hp34⟩
        simp only [f, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    · intro p _hp q _hq heq
      have hhead : [p 0, p 1, p 2] = [q 0, q 1, q 2] :=
        congrArg (fun t : Σ _ : List ℕ × (ℕ × ℕ), ℕ × ℕ => t.1.1) heq
      simp only [List.cons.injEq, and_true] at hhead
      have h3 : p 3 = q 3 :=
        congrArg (fun t : Σ _ : List ℕ × (ℕ × ℕ), ℕ × ℕ => t.2.1) heq
      have h4 : p 4 = q 4 :=
        congrArg (fun t : Σ _ : List ℕ × (ℕ × ℕ), ℕ × ℕ => t.2.2) heq
      funext i
      fin_cases i
      · exact hhead.1
      · exact hhead.2.1
      · exact hhead.2.2
      · exact h3
      · exact h4
    · intro t ht
      obtain ⟨htS, htprod, ht3, ht4, htz, ht34⟩ := Finset.mem_filter.mp ht
      obtain ⟨htP, hte⟩ := Finset.mem_sigma.mp htS
      obtain ⟨htF, htd⟩ := Finset.mem_product.mp htP
      obtain ⟨a, b, c, hlist⟩ := hshape t.1.1 htF
      have hmem := (mem_siftedPrimeTuples_iff x hx (5 : Fin 6) t.1.1).mp htF
      rw [hlist] at hmem
      dsimp only at hmem
      have htd1 : t.1.2.1 = a * b * c := by
        simpa only [hlist, List.prod_cons, List.prod_nil, mul_one, mul_assoc] using htprod
      let p : Fin 5 → ℕ := ![a, b, c, t.2.1, t.2.2]
      have hprime : ∀ i, (p i).Prime := by
        intro i
        fin_cases i
        · exact hmem.1
        · exact hmem.2.1
        · exact hmem.2.2.1
        · exact ht3
        · exact ht4
      have hpN : (∏ i, p i) = n := by
        rw [hprod]
        change (a * b * c) * (t.2.1 * t.2.2) = n
        rw [(Nat.mem_divisorsAntidiagonal.mp hte).1, ← htd1]
        exact (Nat.mem_divisorsAntidiagonal.mp htd).1
      have hpP : p ∈ Fintype.piFinset (fun _ : Fin 5 => Nat.primesLE n) := by
        apply Fintype.mem_piFinset.mpr
        intro i
        apply Nat.mem_primesLE.mpr
        refine ⟨?_, hprime i⟩
        apply Nat.le_of_dvd (Nat.pos_of_ne_zero
          (Nat.mem_divisorsAntidiagonal.mp htd).2)
        rw [← hpN]
        exact Finset.dvd_prod_of_mem p (Finset.mem_univ i)
      have hpT : p ∈ T := by
        apply Finset.mem_filter.mpr
        refine ⟨hpP, hpN, ?_, htz, ht34⟩
        change [a, b, c] ∈ F
        simpa only [hlist] using htF
      refine ⟨p, hpT, ?_⟩
      apply Sigma.ext
      · exact Prod.ext hlist.symm
          (Prod.ext htd1.symm (Nat.mem_divisorsAntidiagonal.mp hte).1)
      · exact heq_of_eq rfl
  calc
    sourceU3 x n = ∑ t ∈ S, (1 : ℝ) := by
      simp only [sourceU3, ArithmeticFunction.coe_mk, S, Finset.sum_filter,
        Finset.sum_sigma, Finset.product_eq_sprod, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro ps _hps
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases heq : d.1 = ps.prod
      · simp only [z, ite_and, ite_eq_left heq]
      · simp only [ite_and, ite_eq_right heq, Finset.sum_const_zero]
    _ = ∑ p ∈ T, (1 : ℝ) := hsum.symm
    _ = _ := by simp only [T, F, z, Finset.sum_filter]

theorem sourceT5_eq_five {x : ℝ} (hx : 1 < x)
    (hg : 2 * x < x ^ (6 * ((8639 : ℝ) / 50000)))
    {n : ℕ} (hlo : x ≤ (n : ℝ)) (hhi : (n : ℝ) ≤ 2 * x) :
    sourceT5 x n =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin 5 => Nat.primesLE n),
        if (∏ i, p i) = n ∧
            (8639 : ℝ) / 50000 ≤ Real.logb x (p 3 : ℝ) ∧
            Real.logb x (p 3 : ℝ) < Real.logb x (p 2 : ℝ) ∧
            Real.logb x (p 2 : ℝ) < Real.logb x (p 1 : ℝ) ∧
            Real.logb x (p 1 : ℝ) < Real.logb x (p 0 : ℝ) ∧
            Real.logb x (p 0 : ℝ) < (41361 : ℝ) / 100000 ∧
            Real.logb x (p 0 : ℝ) + Real.logb x (p 1 : ℝ) < (41361 : ℝ) / 100000 ∧
            (p 3 : ℝ) ≤ (p 4 : ℝ)
        then (1 : ℝ) else 0 := by
  classical
  let C (p : Fin 5 → ℕ) : Prop :=
    (8639 : ℝ) / 50000 ≤ Real.logb x (p 3 : ℝ) ∧
      Real.logb x (p 3 : ℝ) < Real.logb x (p 2 : ℝ) ∧
      Real.logb x (p 2 : ℝ) < Real.logb x (p 1 : ℝ) ∧
      Real.logb x (p 1 : ℝ) < Real.logb x (p 0 : ℝ) ∧
      Real.logb x (p 0 : ℝ) < (41361 : ℝ) / 100000 ∧
      Real.logb x (p 0 : ℝ) + Real.logb x (p 1 : ℝ) < (41361 : ℝ) / 100000
  have hsource : sourceT5 x n =
      ∑ p ∈ Nat.finMulAntidiag 5 n,
        if (p 0).Prime ∧ (p 1).Prime ∧ (p 2).Prime ∧ (p 3).Prime ∧ C p
        then roughWeight (p 3 : ℝ) (p 4) else 0 := by
    rw [← sum_four_divisorsAntidiagonal]
    simp only [sourceT5, ArithmeticFunction.coe_mk, C, Matrix.cons_val]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    apply Finset.sum_congr rfl
    intro g _
    exact if_congr Iff.rfl rfl rfl
  rw [hsource]
  calc
    _ = ∑ p ∈ Nat.finMulAntidiag 5 n,
        if (∀ i, (p i).Prime) ∧ C p ∧ (p 3 : ℝ) ≤ (p 4 : ℝ)
        then (1 : ℝ) else 0 := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      by_cases h : (p 0).Prime ∧ (p 1).Prime ∧ (p 2).Prime ∧ (p 3).Prime ∧ C p
      · rcases h with ⟨h0, h1, h2, h3, hc⟩
        have hrough :
            (p 4 ≠ 0 ∧ ∀ q ∈ (p 4).primeFactors, (p 3 : ℝ) ≤ (q : ℝ)) ↔
              (p 4).Prime ∧ (p 3 : ℝ) ≤ (p 4 : ℝ) := by
          constructor
          · intro hr
            apply exceptional_residual_prime hx hg hlo hhi
              ![p 0, p 1, p 2, p 3] (by intro i; fin_cases i <;> assumption) (p 4)
              ?_ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.2 hr
            simpa only [Fin.prod_univ_four, Fin.prod_univ_five, Matrix.cons_val] using
              (Nat.mem_finMulAntidiag.mp hp).1
          · rintro ⟨hr, hle⟩
            refine ⟨hr.ne_zero, ?_⟩
            simpa only [hr.primeFactors, Finset.mem_singleton, forall_eq] using hle
        have hprime : (∀ i : Fin 5, (p i).Prime) ↔ (p 4).Prime := by
          refine ⟨fun h => h 4, ?_⟩
          intro h4 i
          fin_cases i <;> assumption
        simp only [h0, h1, h2, h3, hc, and_self, ite_true, roughWeight, ArithmeticFunction.coe_mk,
          hrough, hprime, true_and]
      · have hnot : ¬ ((∀ i, (p i).Prime) ∧ C p ∧ (p 3 : ℝ) ≤ (p 4 : ℝ)) := by
          rintro ⟨hp, hc, _⟩
          exact h ⟨hp 0, hp 1, hp 2, hp 3, hc⟩
        rw [ite_eq_right h, ite_eq_right hnot]
    _ = ∑ p ∈ (Nat.finMulAntidiag 5 n).filter (fun p => ∀ i, (p i).Prime),
        if C p ∧ (p 3 : ℝ) ≤ (p 4 : ℝ) then (1 : ℝ) else 0 := by
      simp only [Finset.sum_filter, ite_and]
    _ = _ := by
      rw [prime_finMulAntidiag_eq_filter]
      simp only [Finset.sum_filter, ite_and, C]

#print axioms exceptional_residual_prime
#print axioms sourceU3_eq_five_prime_sum
#print axioms sourceT5_eq_five

end PrimeGap182Analytic.Harman
