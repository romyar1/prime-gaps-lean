import HarmanBuchstab182

/-! Uniform interval and coprimality-filtered Siegel--Walfisz bounds for
the six actual short Harman coefficients at the new cutoffs. The prime,
Mobius, ordered-pair/triple identities and coefficient norms are proved.
Only already proved general analytic lemmas from the public development
are reused. Adapted from Apache-2.0 PrimeGaps186 at the checked source hash. -/

noncomputable section
open scoped BigOperators Topology ContDiff
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

theorem sifted_short_sixth_primeFactors_coefficient_eq
    (x : ℝ) (hx : 1 < x) (n : ℕ) :
    let z : ℝ := x ^ ((8639 : ℝ) / 50000)
    let H : ℝ := x ^ ((41361 : ℝ) / 100000)
    let S : ℝ := x ^ (1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000)
    (∑ ps ∈ siftedPrimeTuples x (5 : Fin 6), ∑ d ∈ n.divisorsAntidiagonal,
      if d.1 = ps.prod then smallPrimeMobius z d.2 else 0) =
    ((∑ p2 ∈ n.primeFactors, ∑ p3 ∈ n.primeFactors, ∑ p4 ∈ n.primeFactors,
      if p2 * p3 * p4 ∣ n ∧ z ≤ (p3 : ℝ) ∧ p3 < p2 ∧ (p2 : ℝ) < H ∧
          p3 ≤ p4 ∧ ((p3 * p4 : ℕ) : ℝ) < H ∧ (p2 : ℝ) < S ∧
          n / (p2 * p3 * p4) ∈ Nat.smoothNumbers (Nat.ceil z)
      then ArithmeticFunction.moebius (n / (p2 * p3 * p4)) else 0 : ℤ) : ℝ) := by
  intro z H S
  by_cases hn : n = 0
  · subst n
    simp
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hz : 1 < z := Real.one_lt_rpow hx (by norm_num)
  have htriple (p q r : ℕ) : [p, q, r] ∈ siftedPrimeTuples x (5 : Fin 6) ↔
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ z ≤ (q : ℝ) ∧ q < p ∧
        (p : ℝ) < H ∧ q ≤ r ∧ ((q * r : ℕ) : ℝ) < H ∧ (p : ℝ) < S := by
    have hmem := mem_siftedPrimeTuples_iff x hx (5 : Fin 6) [p, q, r]
    dsimp only at hmem
    rw [hmem]
    apply and_congr_right
    intro hp
    apply and_congr_right
    intro hq
    apply and_congr_right
    intro hr
    have hp0 : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
    have hq0 : 0 < (q : ℝ) := Nat.cast_pos.mpr hq.pos
    have hr0 : 0 < (r : ℝ) := Nat.cast_pos.mpr hr.pos
    have hlo : (8639 : ℝ) / 50000 ≤ Real.logb x (q : ℝ) ↔ z ≤ (q : ℝ) :=
      Real.le_logb_iff_rpow_le hx hq0
    have hord : Real.logb x (q : ℝ) < Real.logb x (p : ℝ) ↔ q < p := by
      simpa only [Nat.cast_lt] using Real.logb_lt_logb_iff hx hq0 hp0
    have hHcut : Real.logb x (p : ℝ) < (41361 : ℝ) / 100000 ↔ (p : ℝ) < H :=
      Real.logb_lt_iff_lt_rpow hx hp0
    have hweak : Real.logb x (q : ℝ) ≤ Real.logb x (r : ℝ) ↔ q ≤ r := by
      simpa only [Nat.cast_le] using Real.logb_le_logb hx hq0 hr0
    have hprodcut :
        Real.logb x (q : ℝ) + Real.logb x (r : ℝ) < (41361 : ℝ) / 100000 ↔
          ((q * r : ℕ) : ℝ) < H := by
      simp only [H, Nat.cast_mul]
      rw [← Real.logb_mul hq0.ne' hr0.ne',
        Real.logb_lt_iff_lt_rpow hx (mul_pos hq0 hr0)]
    have hScut :
        Real.logb x (p : ℝ) < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000 ↔
          (p : ℝ) < S := Real.logb_lt_iff_lt_rpow hx hp0
    exact and_congr hlo (and_congr hord
      (and_congr hHcut (and_congr hweak (and_congr hprodcut hScut))))
  have hshape (ps : List ℕ) (hps : ps ∈ siftedPrimeTuples x (5 : Fin 6)) :
      ∃ p q r : ℕ, ps = [p, q, r] := by
    have hmem := (mem_siftedPrimeTuples_iff x hx (5 : Fin 6) ps).mp hps
    rcases ps with _ | ⟨p, _ | ⟨q, _ | ⟨r, _ | ⟨s, ss⟩⟩⟩⟩ <;>
      simp at hmem ⊢
  have hsmall (d : ℕ) (hd : d ≠ 0) :
      smallPrimeMobius z d =
        ((if d ∈ Nat.smoothNumbers (Nat.ceil z) then ArithmeticFunction.moebius d
          else 0 : ℤ) : ℝ) := by
    have hceil : 0 < Nat.ceil z := Nat.ceil_pos.mpr (zero_lt_one.trans hz)
    have hcut : ((max 1 (d.primeFactors.sup id) : ℕ) : ℝ) < z ↔
        d ∈ Nat.smoothNumbers (Nat.ceil z) := by
      rw [← Nat.lt_ceil, max_lt_iff, Finset.sup_lt_iff hceil]
      simp only [id_eq, Nat.lt_ceil, Nat.cast_one, hz, true_and]
      constructor
      · intro h
        apply Nat.mem_smoothNumbers'.mpr
        intro p hp hpd
        exact Nat.lt_ceil.mpr (h p (hp.mem_primeFactors hpd hd))
      · intro h p hp
        exact Nat.lt_ceil.mp ((Nat.mem_smoothNumbers'.mp h) p
          (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
    change (if ((max 1 (d.primeFactors.sup id) : ℕ) : ℝ) < z then
      (ArithmeticFunction.moebius d : ℝ) else 0) = _
    simp only [hcut]
    by_cases hs : d ∈ Nat.smoothNumbers (Nat.ceil z)
    · simp only [eq_true hs, ite_true]
    · simp only [eq_false hs, ite_false, Int.cast_zero]
  let D : Finset (List ℕ × (ℕ × ℕ)) :=
    ((siftedPrimeTuples x (5 : Fin 6)).product n.divisorsAntidiagonal).filter
      (fun u => u.2.1 = u.1.prod)
  let V : Finset (ℕ × (ℕ × ℕ)) :=
    (n.primeFactors.product (n.primeFactors.product n.primeFactors)).filter
      (fun v => [v.1, v.2.1, v.2.2] ∈ siftedPrimeTuples x (5 : Fin 6) ∧
        v.1 * v.2.1 * v.2.2 ∣ n)
  let f : (ℕ × (ℕ × ℕ)) → List ℕ × (ℕ × ℕ) := fun v =>
    ([v.1, v.2.1, v.2.2], (v.1 * v.2.1 * v.2.2, n / (v.1 * v.2.1 * v.2.2)))
  calc
    _ = ∑ u ∈ D, smallPrimeMobius z u.2.2 := by
      simpa only [D, Finset.sum_filter, Finset.product_eq_sprod] using
        (Finset.sum_product (siftedPrimeTuples x (5 : Fin 6)) n.divisorsAntidiagonal
          (fun u : List ℕ × (ℕ × ℕ) =>
            if u.2.1 = u.1.prod then smallPrimeMobius z u.2.2 else 0)).symm
    _ = ∑ v ∈ V, smallPrimeMobius z (n / (v.1 * v.2.1 * v.2.2)) := by
      symm
      refine Finset.sum_bij (fun v _ => f v) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro v hv
        obtain ⟨_hvP, htuple, hdiv⟩ := Finset.mem_filter.mp hv
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨htuple, ?_⟩, ?_⟩
        · exact Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.mul_div_cancel' hdiv, hn⟩
        · simp only [f, List.prod_cons, List.prod_nil, mul_one, Nat.mul_assoc]
      · intro v _hv w _hw heq
        have hlist : [v.1, v.2.1, v.2.2] = [w.1, w.2.1, w.2.2] :=
          congrArg Prod.fst heq
        simp only [List.cons.injEq, and_true] at hlist
        exact Prod.ext hlist.1 (Prod.ext hlist.2.1 hlist.2.2)
      · intro u hu
        obtain ⟨huD, hproduct⟩ := Finset.mem_filter.mp hu
        obtain ⟨hps, hd⟩ := Finset.mem_product.mp huD
        obtain ⟨p, q, r, hpshape⟩ := hshape u.1 hps
        have htuple : [p, q, r] ∈ siftedPrimeTuples x (5 : Fin 6) := by
          simpa only [hpshape] using hps
        obtain ⟨hp, hq, hr, _hcuts⟩ := (htriple p q r).mp htuple
        have hprod : u.2.1 = p * q * r := by
          simpa only [hpshape, List.prod_cons, List.prod_nil, mul_one, Nat.mul_assoc]
            using hproduct
        have htotal : (p * q * r) * u.2.2 = n := by
          simpa only [hprod] using (Nat.mem_divisorsAntidiagonal.mp hd).1
        have hdiv : p * q * r ∣ n := ⟨u.2.2, htotal.symm⟩
        have hprod0 : 0 < p * q * r := Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos
        have hquot : n / (p * q * r) = u.2.2 := by
          rw [← htotal, Nat.mul_div_cancel_left _ hprod0]
        have hpdiv : p ∣ p * q * r := ⟨q * r, by ring⟩
        have hqdiv : q ∣ p * q * r := ⟨p * r, by ring⟩
        have hrdiv : r ∣ p * q * r := ⟨p * q, by ring⟩
        let v : ℕ × (ℕ × ℕ) := (p, (q, r))
        have hv : v ∈ V := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_product.mpr
            ⟨Nat.mem_primeFactors.mpr ⟨hp, hpdiv.trans hdiv, hn⟩,
              Finset.mem_product.mpr
                ⟨Nat.mem_primeFactors.mpr ⟨hq, hqdiv.trans hdiv, hn⟩,
                  Nat.mem_primeFactors.mpr ⟨hr, hrdiv.trans hdiv, hn⟩⟩⟩,
            htuple, hdiv⟩
        refine ⟨v, hv, ?_⟩
        exact Prod.ext hpshape.symm (Prod.ext hprod.symm hquot)
    _ = ((∑ v ∈ V,
        if n / (v.1 * v.2.1 * v.2.2) ∈ Nat.smoothNumbers (Nat.ceil z)
        then ArithmeticFunction.moebius (n / (v.1 * v.2.1 * v.2.2)) else 0 : ℤ) : ℝ) := by
      rw [Int.cast_sum]
      apply Finset.sum_congr rfl
      intro v hv
      obtain ⟨hvP, _htuple, hdiv⟩ := Finset.mem_filter.mp hv
      obtain ⟨hp, hqr⟩ := Finset.mem_product.mp hvP
      obtain ⟨hq, hr⟩ := Finset.mem_product.mp hqr
      have hprod0 : 0 < v.1 * v.2.1 * v.2.2 :=
        Nat.mul_pos (Nat.mul_pos (Nat.prime_of_mem_primeFactors hp).pos
          (Nat.prime_of_mem_primeFactors hq).pos) (Nat.prime_of_mem_primeFactors hr).pos
      exact hsmall _ (Nat.div_pos (Nat.le_of_dvd hn0 hdiv) hprod0).ne'
    _ = _ := by
      apply congrArg (fun t : ℤ => (t : ℝ))
      simp only [V, Finset.sum_filter, Finset.product_eq_sprod]
      rw [Finset.sum_product n.primeFactors (n.primeFactors ×ˢ n.primeFactors)
        (fun v : ℕ × (ℕ × ℕ) =>
          if [v.1, v.2.1, v.2.2] ∈ siftedPrimeTuples x (5 : Fin 6) ∧
              v.1 * v.2.1 * v.2.2 ∣ n then
            if n / (v.1 * v.2.1 * v.2.2) ∈ Nat.smoothNumbers (Nat.ceil z)
            then ArithmeticFunction.moebius (n / (v.1 * v.2.1 * v.2.2)) else 0
          else 0)]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_product n.primeFactors n.primeFactors
        (fun qr : ℕ × ℕ =>
          if [p, qr.1, qr.2] ∈ siftedPrimeTuples x (5 : Fin 6) ∧ p * qr.1 * qr.2 ∣ n then
            if n / (p * qr.1 * qr.2) ∈ Nat.smoothNumbers (Nat.ceil z)
            then ArithmeticFunction.moebius (n / (p * qr.1 * qr.2)) else 0
          else 0)]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro r hr
      have hp' := Nat.prime_of_mem_primeFactors hp
      have hq' := Nat.prime_of_mem_primeFactors hq
      have hr' := Nat.prime_of_mem_primeFactors hr
      have hcondition :
          (([p, q, r] ∈ siftedPrimeTuples x (5 : Fin 6) ∧ p * q * r ∣ n) ∧
            n / (p * q * r) ∈ Nat.smoothNumbers (Nat.ceil z)) ↔
          p * q * r ∣ n ∧ z ≤ (q : ℝ) ∧ q < p ∧ (p : ℝ) < H ∧
            q ≤ r ∧ ((q * r : ℕ) : ℝ) < H ∧ (p : ℝ) < S ∧
            n / (p * q * r) ∈ Nat.smoothNumbers (Nat.ceil z) := by
        rw [htriple]
        simp only [eq_true hp', eq_true hq', eq_true hr', true_and]
        constructor
        · rintro ⟨⟨⟨hzq, hqp, hpH, hqr, hqrH, hpS⟩, hdiv⟩, hs⟩
          exact ⟨hdiv, hzq, hqp, hpH, hqr, hqrH, hpS, hs⟩
        · rintro ⟨hdiv, hzq, hqp, hpH, hqr, hqrH, hpS, hs⟩
          exact ⟨⟨⟨hzq, hqp, hpH, hqr, hqrH, hpS⟩, hdiv⟩, hs⟩
      simp only [← ite_and, hcondition]

open Classical in
theorem sifted_short_sixth_raw_norm_le (x : ℝ) (hx : 1 < x) (n : ℕ) :
    ‖((∑ ps ∈ siftedPrimeTuples x (5 : Fin 6), ∑ d ∈ n.divisorsAntidiagonal,
      if d.1 = ps.prod then smallPrimeMobius (x ^ ((8639 : ℝ) / 50000)) d.2
      else 0 : ℝ) : ℂ)‖ ≤ (n.divisors.card : ℝ) ^ 3 := by
  let z := x ^ ((8639 : ℝ) / 50000)
  let H := x ^ ((41361 : ℝ) / 100000)
  let S := x ^ (1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000)
  have hz : 1 < z := Real.one_lt_rpow hx (by norm_num)
  have hb := theta6_a0_norm_le_divisor_cube n z H S (n : ℝ)
  simp only [eq_true hz, le_refl, true_and, ite_true] at hb
  have hs := congrArg (fun t : ℝ => (t : ℂ))
    (sifted_short_sixth_primeFactors_coefficient_eq x hx n)
  simp only [Complex.ofReal_intCast] at hs
  rw [hs]
  simpa only [Int.cast_sum, apply_ite (fun t : ℤ => (t : ℂ)), Int.cast_zero] using hb

open Classical in
theorem sifted_short_one_prime_coefficient_eq
    (x : ℝ) (hx : 1 < x) (n : ℕ) :
    (∑ ps ∈ siftedPrimeTuples x (1 : Fin 6), ∑ d ∈ n.divisorsAntidiagonal,
      if d.1 = ps.prod then smallPrimeMobius (x ^ ((8639 : ℝ) / 50000)) d.2 else 0) =
    ∑ d ∈ n.divisorsAntidiagonal,
      if Nat.Prime d.1 ∧ x ^ ((8639 : ℝ) / 50000) ≤ (d.1 : ℝ) ∧
          (d.1 : ℝ) < x ^ ((41361 : ℝ) / 100000)
      then smallPrimeMobius (x ^ ((8639 : ℝ) / 50000)) d.2 else 0 := by
  rw [theta2_prime_tuples_eq x hx,
    Finset.sum_image List.singleton_injective.injOn]
  simp only [List.prod_cons, List.prod_nil, Nat.mul_one]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_filter, Nat.mem_primesBelow, Nat.lt_ceil,
    and_left_comm, and_comm]

open Classical in
theorem sifted_short_one_prime_unit_row
    (z H : ℝ) (hH : 0 < H) (p m : ℕ) (hm : 0 < m) :
    let U0 : ℝ := ((Nat.ceil H - 1 : ℕ) : ℝ)
    ((∑ bb ∈ m.divisorsAntidiagonal, ∑ cc ∈ bb.2.divisorsAntidiagonal,
      if Nat.Prime p ∧ z ≤ (p : ℝ) ∧ bb.1 = 1 ∧ bb.1 ≤ p ∧
          cc.1 = 1 ∧ cc.1 ≤ p ∧
          ((max 1 (cc.2.primeFactors.sup id) : ℕ) : ℝ) < z ∧
          True ∧ 0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ U0
      then ArithmeticFunction.moebius cc.2 else 0 : ℤ) : ℝ) =
    if Nat.Prime p ∧ z ≤ (p : ℝ) ∧ (p : ℝ) < H
    then smallPrimeMobius z m else 0 := by
  intro U0
  have hupper : (p : ℝ) ≤ U0 ↔ (p : ℝ) < H := by
    dsimp only [U0]
    rw [Nat.cast_le, Nat.le_sub_one_iff_lt (Nat.ceil_pos.mpr hH), Nat.lt_ceil]
  have hunit : (1, m) ∈ m.divisorsAntidiagonal :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul _, hm.ne'⟩
  rw [Finset.sum_eq_single_of_mem (1, m) hunit]
  · simp only
    rw [Finset.sum_eq_single_of_mem (1, m) hunit]
    · simp only
      have hguard :
          (Nat.Prime p ∧ z ≤ (p : ℝ) ∧ True ∧ 1 ≤ p ∧ True ∧ 1 ≤ p ∧
            ((max 1 (m.primeFactors.sup id) : ℕ) : ℝ) < z ∧
            True ∧ 0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ U0) ↔
          (Nat.Prime p ∧ z ≤ (p : ℝ) ∧ (p : ℝ) < H) ∧
            ((max 1 (m.primeFactors.sup id) : ℕ) : ℝ) < z := by
        have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
        constructor
        · rintro ⟨hp, hz, _h1, _hp1, _h2, _hp2, hmz, _h3, _hp0, hpU⟩
          exact ⟨⟨hp, hz, hupper.mp hpU⟩, hmz⟩
        · rintro ⟨⟨hp, hz, hpH⟩, hmz⟩
          exact ⟨hp, hz, True.intro, hp.one_lt.le, True.intro, hp.one_lt.le,
            hmz, True.intro, hp0, hupper.mpr hpH⟩
      simp only [hguard, smallPrimeMobius, ArithmeticFunction.coe_mk,
        apply_ite (fun t : ℤ => (t : ℝ)), Int.cast_zero, ← ite_and]
    · intro cc hcc hne
      apply ite_eq_right
      intro h
      have hc1 : cc.1 = 1 := h.2.2.2.2.1
      have hc2 : cc.2 = m := by
        simpa only [hc1, one_mul] using (Nat.mem_divisorsAntidiagonal.mp hcc).1
      exact hne (Prod.ext hc1 hc2)
  · intro bb hbb hne
    apply Finset.sum_eq_zero
    intro cc _hcc
    apply ite_eq_right
    intro h
    have hb1 : bb.1 = 1 := h.2.2.1
    have hb2 : bb.2 = m := by
      simpa only [hb1, one_mul] using (Nat.mem_divisorsAntidiagonal.mp hbb).1
    exact hne (Prod.ext hb1 hb2)

open Classical in
theorem sifted_short_one_prime_named_coefficient_eq
    (x : ℝ) (hx : 1 < x) (n : ℕ) :
    let z := x ^ ((8639 : ℝ) / 50000)
    let H := x ^ ((41361 : ℝ) / 100000)
    let U0 : ℝ := ((Nat.ceil H - 1 : ℕ) : ℝ)
    let Q0 : ℤ :=
      ∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
        ∑ cc ∈ bb.2.divisorsAntidiagonal,
          if Nat.Prime aa.1 ∧ z ≤ (aa.1 : ℝ) ∧ bb.1 = 1 ∧ bb.1 ≤ aa.1 ∧
              cc.1 = 1 ∧ cc.1 ≤ aa.1 ∧
              ((max 1 (cc.2.primeFactors.sup id) : ℕ) : ℝ) < z ∧
              True ∧ 0 ≤ (aa.1 : ℝ) ∧ (aa.1 : ℝ) ≤ U0
          then ArithmeticFunction.moebius cc.2 else 0
    (∑ ps ∈ siftedPrimeTuples x (1 : Fin 6), ∑ d ∈ n.divisorsAntidiagonal,
      if d.1 = ps.prod then smallPrimeMobius z d.2 else 0) = (Q0 : ℝ) := by
  intro z H U0 Q0
  rw [sifted_short_one_prime_coefficient_eq x hx]
  simp only [Q0, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simpa only [Int.cast_sum] using
    (sifted_short_one_prime_unit_row z H
      (Real.rpow_pos_of_pos (zero_lt_one.trans hx) _) d.1 d.2
      (Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hd))).symm

open Classical in
theorem sifted_short_one_prime_all_moduli_siegelWalfisz
    (ε T c C A : ℝ) (hε : 0 < ε) (hT : 0 < T) (hc : 0 < c)
    (hC : 0 < C) (hA : 0 < A) :
    ∃ K X0 : ℝ, 0 < K ∧ Real.exp 1 ≤ X0 ∧
      ∀ x : ℝ, X0 ≤ x → ∀ N : ℝ, x ^ ε ≤ N → N ≤ x ^ C →
      ∀ nlo nhi : ℝ, c * N ≤ nlo →
      ∀ q : ℕ, 0 < q → ∀ r0 : ℕ, 0 < r0 →
      ∀ a : ℕ, Nat.Coprime a q →
      let z := x ^ ((8639 : ℝ) / 50000)
      let M0 := x ^ (1 - (34941 : ℝ) / 100000)
      let S0 : ℕ → ℝ := fun n =>
        if (n : ℝ) ≤ M0 then
          ∑ ps ∈ siftedPrimeTuples x (1 : Fin 6), ∑ d ∈ n.divisorsAntidiagonal,
            if d.1 = ps.prod then smallPrimeMobius z d.2 else 0
        else 0
      ‖fullDiscrepancy
        (∑ n ∈ Finset.Icc 1 (Nat.floor (T * N)), Finsupp.single n
          (if nlo ≤ (n : ℝ) ∧ (n : ℝ) ≤ nhi ∧ Nat.Coprime n r0
           then (S0 n : ℂ) else 0)) q a‖ ≤
        K * ((q * r0).divisors.card : ℝ) * N / (Real.log x) ^ A := by
  obtain ⟨K, X0, hK, hX0, hbound⟩ :=
    harmanA0_named_all_moduli_siegelWalfisz ε T c C A hε hT hc hC hA
  refine ⟨K, X0, hK, hX0, ?_⟩
  intro x hx N hNL hNU nlo nhi hlo q hq r0 hr0 a ha z M0 S0
  have hx1 : 1 < x :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le (hX0.trans hx)
  have hz : 0 < z := Real.rpow_pos_of_pos (zero_lt_one.trans hx1) _
  let H := x ^ ((41361 : ℝ) / 100000)
  let U0 : ℝ := ((Nat.ceil H - 1 : ℕ) : ℝ)
  let Q0 : ℕ → ℤ := fun n =>
    ∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
      ∑ cc ∈ bb.2.divisorsAntidiagonal,
        if Nat.Prime aa.1 ∧ z ≤ (aa.1 : ℝ) ∧ bb.1 = 1 ∧ bb.1 ≤ aa.1 ∧
            cc.1 = 1 ∧ cc.1 ≤ aa.1 ∧
            ((max 1 (cc.2.primeFactors.sup id) : ℕ) : ℝ) < z ∧
            True ∧ 0 ≤ (aa.1 : ℝ) ∧ (aa.1 : ℝ) ≤ U0
        then ArithmeticFunction.moebius cc.2 else 0
  have hcoeff (n : ℕ) : (Q0 n : ℂ) =
      ((∑ ps ∈ siftedPrimeTuples x (1 : Fin 6), ∑ d ∈ n.divisorsAntidiagonal,
        if d.1 = ps.prod then smallPrimeMobius z d.2 else 0 : ℝ) : ℂ) := by
    have hs := congrArg (fun t : ℝ => (t : ℂ))
      (sifted_short_one_prime_named_coefficient_eq x hx1 n)
    simpa only [Complex.ofReal_intCast] using hs.symm
  have hb := hbound x hx N hNL hNU (0 : Fin 2) (0 : Fin 2)
    (fun _ _ _ => True) (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => U0)
    z M0 nlo nhi hz hlo false q hq r0 hr0 a ha
  dsimp only at hb
  simp only [ite_true,
    ite_eq_right (show ¬(false : Bool) by decide)] at hb
  dsimp only [Q0] at hcoeff
  simpa only [apply_ite (fun t : ℤ => (t : ℂ)), Int.cast_zero, hcoeff,
    S0, apply_ite (fun t : ℝ => (t : ℂ)), Complex.ofReal_zero] using hb

open Classical in
theorem sifted_short_pair_window_iff
    (x : ℝ) (hx : 1 < x) (e : Fin 2) (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) :
    let z := x ^ ((8639 : ℝ) / 50000)
    let H := x ^ ((41361 : ℝ) / 100000)
    let B := x ^ ((58639 : ℝ) / 100000)
    let P := if e = 0 then True else
      Real.logb x (q : ℝ) < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000
    let L := if e = 0 then (q : ℝ) + 1 else
      max ((q : ℝ) + 1) ((Nat.floor (B / (q : ℝ)) : ℝ) + 1)
    let U := if e = 0 then
      min ((Nat.ceil H - 1 : ℕ) : ℝ) ((Nat.ceil (H / (q : ℝ)) - 1 : ℕ) : ℝ)
      else ((Nat.ceil H - 1 : ℕ) : ℝ)
    (z ≤ (p : ℝ) ∧ z ≤ (q : ℝ) ∧ q ≤ p ∧ P ∧ L ≤ (p : ℝ) ∧ (p : ℝ) ≤ U) ↔
      (8639 : ℝ) / 50000 ≤ Real.logb x (q : ℝ) ∧
        Real.logb x (q : ℝ) < Real.logb x (p : ℝ) ∧
        Real.logb x (p : ℝ) < (41361 : ℝ) / 100000 ∧
        (if e = 0 then
          Real.logb x (p : ℝ) + Real.logb x (q : ℝ) < (41361 : ℝ) / 100000 else
          (58639 : ℝ) / 100000 < Real.logb x (p : ℝ) + Real.logb x (q : ℝ) ∧
            Real.logb x (q : ℝ) < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000) := by
  intro z H B P L U
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hp0 : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hq0 : 0 < (q : ℝ) := Nat.cast_pos.mpr hq.pos
  have hH : 0 < H := Real.rpow_pos_of_pos hx0 _
  have hlo : (8639 : ℝ) / 50000 ≤ Real.logb x (q : ℝ) ↔ z ≤ (q : ℝ) :=
    Real.le_logb_iff_rpow_le hx hq0
  have horder : Real.logb x (q : ℝ) < Real.logb x (p : ℝ) ↔ q < p := by
    simpa only [Nat.cast_lt] using Real.logb_lt_logb_iff hx hq0 hp0
  have htop : Real.logb x (p : ℝ) < (41361 : ℝ) / 100000 ↔ (p : ℝ) < H :=
    Real.logb_lt_iff_lt_rpow hx hp0
  have hlogs : Real.logb x (p : ℝ) + Real.logb x (q : ℝ) =
      Real.logb x ((p : ℝ) * (q : ℝ)) := (Real.logb_mul hp0.ne' hq0.ne').symm
  have hproduct :
      Real.logb x (p : ℝ) + Real.logb x (q : ℝ) < (41361 : ℝ) / 100000 ↔
        (p : ℝ) < H / (q : ℝ) := by
    rw [hlogs]
    exact (Real.logb_lt_iff_lt_rpow hx (mul_pos hp0 hq0)).trans (lt_div_iff₀ hq0).symm
  have hproductLower :
      (58639 : ℝ) / 100000 < Real.logb x (p : ℝ) + Real.logb x (q : ℝ) ↔
        B / (q : ℝ) < (p : ℝ) := by
    rw [hlogs]
    exact (Real.lt_logb_iff_rpow_lt hx (mul_pos hp0 hq0)).trans (div_lt_iff₀ hq0).symm
  have hsucc : (q : ℝ) + 1 ≤ (p : ℝ) ↔ q < p := by
    exact_mod_cast (Nat.succ_le_iff : q + 1 ≤ p ↔ q < p)
  have hfloor :
      (Nat.floor (B / (q : ℝ)) : ℝ) + 1 ≤ (p : ℝ) ↔ B / (q : ℝ) < (p : ℝ) := by
    calc
      _ ↔ Nat.floor (B / (q : ℝ)) + 1 ≤ p := by norm_cast
      _ ↔ Nat.floor (B / (q : ℝ)) < p := Nat.succ_le_iff
      _ ↔ B / (q : ℝ) < (p : ℝ) := Nat.floor_lt' hp.ne_zero
  have hcap : (p : ℝ) ≤ ((Nat.ceil H - 1 : ℕ) : ℝ) ↔ (p : ℝ) < H := by
    rw [Nat.cast_le, Nat.le_sub_one_iff_lt (Nat.ceil_pos.mpr hH), Nat.lt_ceil]
  have hcapDiv :
      (p : ℝ) ≤ ((Nat.ceil (H / (q : ℝ)) - 1 : ℕ) : ℝ) ↔
        (p : ℝ) < H / (q : ℝ) := by
    rw [Nat.cast_le, Nat.le_sub_one_iff_lt (Nat.ceil_pos.mpr (div_pos hH hq0)), Nat.lt_ceil]
  by_cases he : e = 0
  · simp only [P, L, U, eq_true he, ite_true, true_and, le_min_iff,
      hsucc, hcap, hcapDiv, hlo, horder, htop, hproduct]
    constructor
    · rintro ⟨_hzp, hzq, _hqp, hqp, htop', hproduct'⟩
      exact ⟨hzq, hqp, htop', hproduct'⟩
    · rintro ⟨hzq, hqp, htop', hproduct'⟩
      exact ⟨hzq.trans (Nat.cast_le.mpr hqp.le), hzq, hqp.le, hqp, htop', hproduct'⟩
  · simp only [P, L, U, eq_false he, ite_false, max_le_iff,
      hsucc, hfloor, hcap, hlo, horder, htop, hproductLower]
    constructor
    · rintro ⟨_hzp, hzq, _hqp, hsmall, ⟨hqp, hproduct'⟩, htop'⟩
      exact ⟨hzq, hqp, htop', hproduct', hsmall⟩
    · rintro ⟨hzq, hqp, htop', hproduct', hsmall⟩
      exact ⟨hzq.trans (Nat.cast_le.mpr hqp.le), hzq, hqp.le, hsmall,
        ⟨hqp, hproduct'⟩, htop'⟩

open Classical in
theorem sifted_short_triple_window_iff
    (x : ℝ) (hx : 1 < x) (p q r : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r) :
    let z := x ^ ((8639 : ℝ) / 50000)
    let H := x ^ ((41361 : ℝ) / 100000)
    let P := r < q ∧
      Real.logb x (r : ℝ) < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000
    let L := (q : ℝ) + 1
    let U :=
      min ((Nat.ceil H - 1 : ℕ) : ℝ) ((Nat.ceil (H / (q : ℝ)) - 1 : ℕ) : ℝ)
    (z ≤ (p : ℝ) ∧ z ≤ (q : ℝ) ∧ q ≤ p ∧ z ≤ (r : ℝ) ∧ r ≤ p ∧
      P ∧ L ≤ (p : ℝ) ∧ (p : ℝ) ≤ U) ↔
      (8639 : ℝ) / 50000 ≤ Real.logb x (r : ℝ) ∧
        Real.logb x (r : ℝ) < Real.logb x (q : ℝ) ∧
        Real.logb x (q : ℝ) < Real.logb x (p : ℝ) ∧
        Real.logb x (p : ℝ) < (41361 : ℝ) / 100000 ∧
        Real.logb x (p : ℝ) + Real.logb x (q : ℝ) < (41361 : ℝ) / 100000 ∧
        Real.logb x (r : ℝ) < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000 := by
  intro z H P L U
  have hw :
      (z ≤ (p : ℝ) ∧ z ≤ (q : ℝ) ∧ q ≤ p ∧ True ∧
        L ≤ (p : ℝ) ∧ (p : ℝ) ≤ U) ↔
      (8639 : ℝ) / 50000 ≤ Real.logb x (q : ℝ) ∧
        Real.logb x (q : ℝ) < Real.logb x (p : ℝ) ∧
        Real.logb x (p : ℝ) < (41361 : ℝ) / 100000 ∧
        Real.logb x (p : ℝ) + Real.logb x (q : ℝ) < (41361 : ℝ) / 100000 := by
    simpa only [ite_true] using sifted_short_pair_window_iff x hx (0 : Fin 2) p q hp hq
  have hrlo : (8639 : ℝ) / 50000 ≤ Real.logb x (r : ℝ) ↔ z ≤ (r : ℝ) :=
    Real.le_logb_iff_rpow_le hx (Nat.cast_pos.mpr hr.pos)
  have hrorder : Real.logb x (r : ℝ) < Real.logb x (q : ℝ) ↔ r < q := by
    simpa only [Nat.cast_lt] using
      Real.logb_lt_logb_iff hx (Nat.cast_pos.mpr hr.pos) (Nat.cast_pos.mpr hq.pos)
  constructor
  · rintro ⟨hzp, hzq, hqp, hzr, _hrp, ⟨hrq, hsmall⟩, hL, hU⟩
    obtain ⟨_hxiq, hqp', htop, hproduct⟩ := hw.mp ⟨hzp, hzq, hqp, True.intro, hL, hU⟩
    exact ⟨hrlo.mpr hzr, hrorder.mpr hrq, hqp', htop, hproduct, hsmall⟩
  · rintro ⟨hxir, hrq, hqp, htop, hproduct, hsmall⟩
    obtain ⟨hzp, hzq, hqp', _htrue, hL, hU⟩ :=
      hw.mpr ⟨hxir.trans hrq.le, hqp, htop, hproduct⟩
    exact ⟨hzp, hzq, hqp', hrlo.mp hxir, (hrorder.mp hrq).le.trans hqp',
      ⟨hrorder.mp hrq, hsmall⟩, hL, hU⟩

open Classical in

open Classical in
theorem sifted_short_empty_coefficient_eq (x : ℝ) (n : ℕ) :
    (∑ ps ∈ siftedPrimeTuples x (0 : Fin 6), ∑ d ∈ n.divisorsAntidiagonal,
      if d.1 = ps.prod then smallPrimeMobius (x ^ ((8639 : ℝ) / 50000)) d.2 else 0) =
      smallPrimeMobius (x ^ ((8639 : ℝ) / 50000)) n := by
  have hs : siftedPrimeTuples x (0 : Fin 6) = {[]} := rfl
  rw [hs, Finset.sum_singleton, List.prod_nil]
  by_cases hn : n = 0
  · subst n
    simp
  have hunit : (1, n) ∈ n.divisorsAntidiagonal :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul _, hn⟩
  rw [Finset.sum_eq_single_of_mem (1, n) hunit]
  · rfl
  · intro d hd hne
    apply ite_eq_right
    intro hd1
    have hd2 : d.2 = n := by
      simpa only [hd1, one_mul] using (Nat.mem_divisorsAntidiagonal.mp hd).1
    exact hne (Prod.ext hd1 hd2)

open Classical in
theorem sifted_short_empty_all_moduli_siegelWalfisz
    (ε T c C A : ℝ) (hε : 0 < ε) (hT : 0 < T) (hc : 0 < c)
    (hC : 0 < C) (hA : 0 < A) :
    ∃ K X0 : ℝ, 0 < K ∧ Real.exp 1 ≤ X0 ∧
      ∀ x : ℝ, X0 ≤ x → ∀ N : ℝ, x ^ ε ≤ N → N ≤ x ^ C →
      ∀ nlo nhi : ℝ, c * N ≤ nlo →
      ∀ q : ℕ, 0 < q → ∀ r0 : ℕ, 0 < r0 →
      ∀ a : ℕ, Nat.Coprime a q →
      let z := x ^ ((8639 : ℝ) / 50000)
      let M0 := x ^ (1 - (34941 : ℝ) / 100000)
      let S0 : ℕ → ℝ := fun n =>
        if (n : ℝ) ≤ M0 then
          ∑ ps ∈ siftedPrimeTuples x (0 : Fin 6), ∑ d ∈ n.divisorsAntidiagonal,
            if d.1 = ps.prod then smallPrimeMobius z d.2 else 0
        else 0
      ‖fullDiscrepancy
        (∑ n ∈ Finset.Icc 1 (Nat.floor (T * N)), Finsupp.single n
          (if nlo ≤ (n : ℝ) ∧ (n : ℝ) ≤ nhi ∧ Nat.Coprime n r0
           then (S0 n : ℂ) else 0)) q a‖ ≤
        K * ((q * r0).divisors.card : ℝ) * N / (Real.log x) ^ A := by
  obtain ⟨K, X0, hK, hX0, hbound⟩ :=
    harmanA0_unit_all_moduli_siegelWalfisz ε T c C A hε hT hc hC hA
  refine ⟨K, X0, hK, hX0, ?_⟩
  intro x hx N hNL hNU nlo nhi hlo q hq r0 hr0 a ha z M0 S0
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le (hX0.trans hx)
  have hz : 0 < z := Real.rpow_pos_of_pos hx0 _
  have hS0 (n : ℕ) :
      S0 n = if (n : ℝ) ≤ M0 then smallPrimeMobius z n else 0 := by
    dsimp only [S0]
    rw [sifted_short_empty_coefficient_eq]
  have hb := hbound x hx N hNL hNU z M0 nlo nhi hz hlo false q hq r0 hr0 a ha
  dsimp only at hb
  simp only [Bool.coe_sort_false, ite_false] at hb
  simpa only [hS0, smallPrimeMobius,
    ArithmeticFunction.coe_mk, apply_ite (fun t : ℝ => (t : ℂ)),
    apply_ite (fun t : ℤ => (t : ℂ)), Complex.ofReal_intCast,
    Complex.ofReal_zero, Int.cast_zero, ← ite_and] using hb

open Classical in
theorem sifted_short_sixth_all_moduli_siegelWalfisz
    (ε T c C A : ℝ) (hε : 0 < ε) (hT : 0 < T) (hc : 0 < c)
    (hC : 0 < C) (hA : 0 < A) :
    ∃ K X0 : ℝ, 0 < K ∧ Real.exp 1 ≤ X0 ∧
      ∀ x : ℝ, X0 ≤ x → ∀ N : ℝ, x ^ ε ≤ N → N ≤ x ^ C →
      ∀ nlo nhi : ℝ, c * N ≤ nlo →
      ∀ q : ℕ, 0 < q → ∀ r0 : ℕ, 0 < r0 →
      ∀ a : ℕ, Nat.Coprime a q →
      let z := x ^ ((8639 : ℝ) / 50000)
      let M0 := x ^ (1 - (34941 : ℝ) / 100000)
      let S0 : ℕ → ℝ := fun n =>
        if (n : ℝ) ≤ M0 then
          ∑ ps ∈ siftedPrimeTuples x (5 : Fin 6), ∑ d ∈ n.divisorsAntidiagonal,
            if d.1 = ps.prod then smallPrimeMobius z d.2 else 0
        else 0
      ‖fullDiscrepancy
        (∑ n ∈ Finset.Icc 1 (Nat.floor (T * N)), Finsupp.single n
          (if nlo ≤ (n : ℝ) ∧ (n : ℝ) ≤ nhi ∧ Nat.Coprime n r0
           then (S0 n : ℂ) else 0)) q a‖ ≤
        K * ((q * r0).divisors.card : ℝ) * N / (Real.log x) ^ A := by
  obtain ⟨K, X0, hK, hX0, hbound⟩ :=
    theta6_a0_all_moduli_siegelWalfisz ε T c C A hε hT hc hC hA
  refine ⟨K, X0, hK, hX0, ?_⟩
  intro x hx N hNL hNU nlo nhi hlo q hq r0 hr0 a ha z M0 S0
  have hx1 : 1 < x :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le (hX0.trans hx)
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hz1 : 1 < z := Real.one_lt_rpow hx1 (by norm_num)
  let H := x ^ ((41361 : ℝ) / 100000)
  let S := x ^ (1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000)
  have hH : 0 < H := Real.rpow_pos_of_pos hx0 _
  have hS : 0 < S := Real.rpow_pos_of_pos hx0 _
  let Q0 : ℕ → ℤ := fun n =>
    ∑ p2 ∈ n.primeFactors, ∑ p3 ∈ n.primeFactors, ∑ p4 ∈ n.primeFactors,
      if p2 * p3 * p4 ∣ n ∧ z ≤ (p3 : ℝ) ∧ p3 < p2 ∧ (p2 : ℝ) < H ∧
          p3 ≤ p4 ∧ ((p3 * p4 : ℕ) : ℝ) < H ∧ (p2 : ℝ) < S ∧
          n / (p2 * p3 * p4) ∈ Nat.smoothNumbers (Nat.ceil z)
      then ArithmeticFunction.moebius (n / (p2 * p3 * p4)) else 0
  have hcoeff (n : ℕ) : (Q0 n : ℂ) =
      ((∑ ps ∈ siftedPrimeTuples x (5 : Fin 6), ∑ d ∈ n.divisorsAntidiagonal,
        if d.1 = ps.prod then smallPrimeMobius z d.2 else 0 : ℝ) : ℂ) := by
    have hs := congrArg (fun t : ℝ => (t : ℂ))
      (sifted_short_sixth_primeFactors_coefficient_eq x hx1 n)
    simpa only [Complex.ofReal_intCast] using hs.symm
  have hb := hbound x hx N hNL hNU z H S M0 nlo nhi hH hS hlo q hq r0 hr0 a ha
  dsimp only at hb
  simp only [eq_true hz1, true_and] at hb
  change ‖fullDiscrepancy
    (∑ n ∈ Finset.Icc 1 (Nat.floor (T * N)), Finsupp.single n
      (if nlo ≤ (n : ℝ) ∧ (n : ℝ) ≤ nhi ∧ Nat.Coprime n r0
       then ((if (n : ℝ) ≤ M0 then Q0 n else 0 : ℤ) : ℂ) else 0)) q a‖ ≤
    K * ((q * r0).divisors.card : ℝ) * N / (Real.log x) ^ A at hb
  simpa only [apply_ite (fun t : ℤ => (t : ℂ)),
    Int.cast_zero, hcoeff, S0, apply_ite (fun t : ℝ => (t : ℂ)),
    Complex.ofReal_zero] using hb

open Classical in
theorem sifted_short_empty_raw_norm_le (x : ℝ) (n : ℕ) :
    ‖((∑ ps ∈ siftedPrimeTuples x (0 : Fin 6), ∑ d ∈ n.divisorsAntidiagonal,
      if d.1 = ps.prod then smallPrimeMobius (x ^ ((8639 : ℝ) / 50000)) d.2
      else 0 : ℝ) : ℂ)‖ ≤ (n.divisors.card : ℝ) ^ 3 := by
  rw [sifted_short_empty_coefficient_eq]
  by_cases hn : n = 0
  · subst n
    simp
  have hτ : (1 : ℝ) ≤ n.divisors.card := by
    exact_mod_cast (Finset.one_le_card.mpr
      ⟨1, Nat.one_mem_divisors.mpr hn⟩ : 1 ≤ n.divisors.card)
  have hτ3 : (1 : ℝ) ≤ (n.divisors.card : ℝ) ^ 3 := by
    calc
      (1 : ℝ) = (1 : ℝ) ^ 3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ zero_le_one hτ 3
  have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  have hcut := norm_harman_int_cut_le_one
    (((max 1 (n.primeFactors.sup id) : ℕ) : ℝ) <
      x ^ ((8639 : ℝ) / 50000)) (ArithmeticFunction.moebius n) hmu
  have hsmall : ‖(smallPrimeMobius (x ^ ((8639 : ℝ) / 50000)) n : ℂ)‖ ≤ 1 := by
    simpa only [smallPrimeMobius, ArithmeticFunction.coe_mk,
      apply_ite (fun t : ℝ => (t : ℂ)), apply_ite (fun t : ℤ => (t : ℂ)),
      Complex.ofReal_intCast, Complex.ofReal_zero, Int.cast_zero] using hcut
  exact hsmall.trans hτ3

open Classical in
theorem sifted_short_one_raw_norm_le (x : ℝ) (hx : 1 < x) (n : ℕ) :
    ‖((∑ ps ∈ siftedPrimeTuples x (1 : Fin 6), ∑ d ∈ n.divisorsAntidiagonal,
      if d.1 = ps.prod then smallPrimeMobius (x ^ ((8639 : ℝ) / 50000)) d.2
      else 0 : ℝ) : ℂ)‖ ≤ (n.divisors.card : ℝ) ^ 3 := by
  let z := x ^ ((8639 : ℝ) / 50000)
  let H := x ^ ((41361 : ℝ) / 100000)
  let U0 : ℝ := ((Nat.ceil H - 1 : ℕ) : ℝ)
  let Q0 : ℤ :=
    ∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
      ∑ cc ∈ bb.2.divisorsAntidiagonal,
        if Nat.Prime aa.1 ∧ z ≤ (aa.1 : ℝ) ∧ bb.1 = 1 ∧ bb.1 ≤ aa.1 ∧
            cc.1 = 1 ∧ cc.1 ≤ aa.1 ∧
            ((max 1 (cc.2.primeFactors.sup id) : ℕ) : ℝ) < z ∧
            True ∧ 0 ≤ (aa.1 : ℝ) ∧ (aa.1 : ℝ) ≤ U0
        then ArithmeticFunction.moebius cc.2 else 0
  have hb := harmanA0_named_coefficient_norm_le n (0 : Fin 2) (0 : Fin 2)
    (fun _ _ _ => True) (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => U0) z (n : ℝ) false
  dsimp only at hb
  simp only [le_refl, ite_true] at hb
  change ‖(Q0 : ℂ)‖ ≤ (n.divisors.card : ℝ) ^ 3 at hb
  have hs := congrArg (fun t : ℝ => (t : ℂ))
    (sifted_short_one_prime_named_coefficient_eq x hx n)
  simp only [Complex.ofReal_intCast] at hs
  rw [← hs] at hb
  exact hb

open Classical in
theorem sifted_short_two_prime_coefficient_eq
    (x : ℝ) (hx : 1 < x) (e : Fin 2) (n : ℕ) :
    let j : Fin 6 := if e = 0 then 2 else 3
    let z : ℝ := x ^ ((8639 : ℝ) / 50000)
    let alpha : ℕ → ℝ := fun p => Real.logb x (p : ℝ)
    (∑ ps ∈ siftedPrimeTuples x j, ∑ d ∈ n.divisorsAntidiagonal,
      if d.1 = ps.prod then smallPrimeMobius z d.2 else 0) =
    ∑ a ∈ n.divisorsAntidiagonal, ∑ b ∈ a.2.divisorsAntidiagonal,
      if Nat.Prime a.1 ∧ Nat.Prime b.1 ∧ (8639 : ℝ) / 50000 ≤ alpha b.1 ∧
          alpha b.1 < alpha a.1 ∧ alpha a.1 < (41361 : ℝ) / 100000 ∧
          (if e = 0 then alpha a.1 + alpha b.1 < (41361 : ℝ) / 100000 else
            (58639 : ℝ) / 100000 < alpha a.1 + alpha b.1 ∧
              alpha b.1 < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000)
      then smallPrimeMobius z b.2 else 0 := by
  intro j z alpha
  have hpair (p q : ℕ) : [p, q] ∈ siftedPrimeTuples x j ↔
      Nat.Prime p ∧ Nat.Prime q ∧ (8639 : ℝ) / 50000 ≤ alpha q ∧
        alpha q < alpha p ∧ alpha p < (41361 : ℝ) / 100000 ∧
        (if e = 0 then alpha p + alpha q < (41361 : ℝ) / 100000 else
          (58639 : ℝ) / 100000 < alpha p + alpha q ∧
            alpha q < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000) := by
    have hmem := mem_siftedPrimeTuples_iff x hx j [p, q]
    by_cases he : e = 0 <;> simpa [j, he, alpha] using hmem
  have hshape (ps : List ℕ) (hps : ps ∈ siftedPrimeTuples x j) :
      ∃ p q : ℕ, ps = [p, q] := by
    have hmem := (mem_siftedPrimeTuples_iff x hx j ps).mp hps
    by_cases he : e = 0 <;>
      rcases ps with _ | ⟨p, _ | ⟨q, _ | ⟨r, rs⟩⟩⟩ <;>
      simp [j, he] at hmem ⊢
  simpa only [hpair] using
    sum_pair_list_divisorsAntidiagonal (siftedPrimeTuples x j) hshape
      (fun _ m => smallPrimeMobius z m) n

open Classical in
theorem sifted_short_three_prime_coefficient_eq
    (x : ℝ) (hx : 1 < x) (n : ℕ) :
    let z : ℝ := x ^ ((8639 : ℝ) / 50000)
    let alpha : ℕ → ℝ := fun p => Real.logb x (p : ℝ)
    (∑ ps ∈ siftedPrimeTuples x (4 : Fin 6), ∑ d ∈ n.divisorsAntidiagonal,
      if d.1 = ps.prod then smallPrimeMobius z d.2 else 0) =
    ∑ a ∈ n.divisorsAntidiagonal, ∑ b ∈ a.2.divisorsAntidiagonal,
      ∑ c ∈ b.2.divisorsAntidiagonal,
        if Nat.Prime a.1 ∧ Nat.Prime b.1 ∧ Nat.Prime c.1 ∧
            (8639 : ℝ) / 50000 ≤ alpha c.1 ∧ alpha c.1 < alpha b.1 ∧
            alpha b.1 < alpha a.1 ∧ alpha a.1 < (41361 : ℝ) / 100000 ∧
            alpha a.1 + alpha b.1 < (41361 : ℝ) / 100000 ∧
            alpha c.1 < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000
        then smallPrimeMobius z c.2 else 0 := by
  intro z alpha
  have htriple (p q r : ℕ) : [p, q, r] ∈ siftedPrimeTuples x (4 : Fin 6) ↔
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ (8639 : ℝ) / 50000 ≤ alpha r ∧
        alpha r < alpha q ∧ alpha q < alpha p ∧ alpha p < (41361 : ℝ) / 100000 ∧
        alpha p + alpha q < (41361 : ℝ) / 100000 ∧
        alpha r < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000 := by
    simpa [alpha] using mem_siftedPrimeTuples_iff x hx (4 : Fin 6) [p, q, r]
  have hshape (ps : List ℕ) (hps : ps ∈ siftedPrimeTuples x (4 : Fin 6)) :
      ∃ p q r : ℕ, ps = [p, q, r] := by
    have hmem := (mem_siftedPrimeTuples_iff x hx (4 : Fin 6) ps).mp hps
    rcases ps with _ | ⟨p, _ | ⟨q, _ | ⟨r, _ | ⟨s, ss⟩⟩⟩⟩ <;>
      simp at hmem ⊢
  simpa only [htriple] using
    sum_triple_list_divisorsAntidiagonal (siftedPrimeTuples x (4 : Fin 6)) hshape
      (fun _ m => smallPrimeMobius z m) n

open Classical in
theorem sifted_short_two_prime_named_coefficient_eq
    (x : ℝ) (hx : 1 < x) (e : Fin 2) (n : ℕ) :
    let j : Fin 6 := if e = 0 then 2 else 3
    let z := x ^ ((8639 : ℝ) / 50000)
    let H := x ^ ((41361 : ℝ) / 100000)
    let B := x ^ ((58639 : ℝ) / 100000)
    let P : ℕ → ℕ → ℕ → Prop := fun q _r _h =>
      if e = 0 then True else
        Real.logb x (q : ℝ) < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000
    let L : ℕ → ℕ → ℕ → ℝ := fun q _r _h =>
      if e = 0 then (q : ℝ) + 1 else
        max ((q : ℝ) + 1) ((Nat.floor (B / (q : ℝ)) : ℝ) + 1)
    let U : ℕ → ℕ → ℕ → ℝ := fun q _r _h =>
      if e = 0 then
        min ((Nat.ceil H - 1 : ℕ) : ℝ) ((Nat.ceil (H / (q : ℝ)) - 1 : ℕ) : ℝ)
      else ((Nat.ceil H - 1 : ℕ) : ℝ)
    let Q0 : ℤ :=
      ∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
        ∑ cc ∈ bb.2.divisorsAntidiagonal,
          if Nat.Prime aa.1 ∧ z ≤ (aa.1 : ℝ) ∧
              (Nat.Prime bb.1 ∧ z ≤ (bb.1 : ℝ)) ∧ bb.1 ≤ aa.1 ∧
              cc.1 = 1 ∧ cc.1 ≤ aa.1 ∧
              ((max 1 (cc.2.primeFactors.sup id) : ℕ) : ℝ) < z ∧
              P bb.1 cc.1 cc.2 ∧ L bb.1 cc.1 cc.2 ≤ (aa.1 : ℝ) ∧
              (aa.1 : ℝ) ≤ U bb.1 cc.1 cc.2
          then ArithmeticFunction.moebius cc.2 else 0
    (∑ ps ∈ siftedPrimeTuples x j, ∑ d ∈ n.divisorsAntidiagonal,
      if d.1 = ps.prod then smallPrimeMobius z d.2 else 0) = (Q0 : ℝ) := by
  intro j z H B P L U Q0
  have hrow (p q m : ℕ) (hm : 0 < m) :
      ((∑ cc ∈ m.divisorsAntidiagonal,
        if Nat.Prime p ∧ z ≤ (p : ℝ) ∧ (Nat.Prime q ∧ z ≤ (q : ℝ)) ∧ q ≤ p ∧
            cc.1 = 1 ∧ cc.1 ≤ p ∧ ((max 1 (cc.2.primeFactors.sup id) : ℕ) : ℝ) < z ∧
            P q cc.1 cc.2 ∧ L q cc.1 cc.2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ U q cc.1 cc.2
        then ArithmeticFunction.moebius cc.2 else 0 : ℤ) : ℝ) =
      if Nat.Prime p ∧ Nat.Prime q ∧ (8639 : ℝ) / 50000 ≤ Real.logb x (q : ℝ) ∧
          Real.logb x (q : ℝ) < Real.logb x (p : ℝ) ∧
          Real.logb x (p : ℝ) < (41361 : ℝ) / 100000 ∧
          (if e = 0 then
            Real.logb x (p : ℝ) + Real.logb x (q : ℝ) < (41361 : ℝ) / 100000 else
            (58639 : ℝ) / 100000 < Real.logb x (p : ℝ) + Real.logb x (q : ℝ) ∧
              Real.logb x (q : ℝ) < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000)
      then smallPrimeMobius z m else 0 := by
    have hunit : (1, m) ∈ m.divisorsAntidiagonal :=
      Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul _, hm.ne'⟩
    rw [Finset.sum_eq_single_of_mem (1, m) hunit]
    · simp only
      by_cases hp : Nat.Prime p
      · by_cases hq : Nat.Prime q
        · have hw := sifted_short_pair_window_iff x hx e p q hp hq
          dsimp only at hw
          have hp1 : 1 ≤ p := hp.one_lt.le
          have hguard :
              (Nat.Prime p ∧ z ≤ (p : ℝ) ∧ (Nat.Prime q ∧ z ≤ (q : ℝ)) ∧ q ≤ p ∧
                True ∧ 1 ≤ p ∧ ((max 1 (m.primeFactors.sup id) : ℕ) : ℝ) < z ∧
                P q 1 m ∧ L q 1 m ≤ (p : ℝ) ∧ (p : ℝ) ≤ U q 1 m) ↔
              (Nat.Prime p ∧ Nat.Prime q ∧ (8639 : ℝ) / 50000 ≤ Real.logb x (q : ℝ) ∧
                Real.logb x (q : ℝ) < Real.logb x (p : ℝ) ∧
                Real.logb x (p : ℝ) < (41361 : ℝ) / 100000 ∧
                (if e = 0 then
                  Real.logb x (p : ℝ) + Real.logb x (q : ℝ) < (41361 : ℝ) / 100000 else
                  (58639 : ℝ) / 100000 < Real.logb x (p : ℝ) + Real.logb x (q : ℝ) ∧
                    Real.logb x (q : ℝ) < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000)) ∧
                ((max 1 (m.primeFactors.sup id) : ℕ) : ℝ) < z := by
            dsimp only [P, L, U, z, H, B] at hw ⊢
            tauto
          simp only [hguard]
          simp only [smallPrimeMobius, ArithmeticFunction.coe_mk,
            apply_ite (fun t : ℤ => (t : ℝ)), Int.cast_zero, ← ite_and]
        · simp [hq]
      · simp [hp]
    · intro cc hcc hne
      apply ite_eq_right
      intro h
      have hc1 : cc.1 = 1 := h.2.2.2.2.1
      have hc2 : cc.2 = m := by
        simpa only [hc1, one_mul] using (Nat.mem_divisorsAntidiagonal.mp hcc).1
      exact hne (Prod.ext hc1 hc2)
  have hs := sifted_short_two_prime_coefficient_eq x hx e n
  dsimp only at hs
  rw [hs]
  simp only [Q0, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro aa haa
  apply Finset.sum_congr rfl
  intro bb hbb
  simpa only [Int.cast_sum] using (hrow aa.1 bb.1 bb.2
    (Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hbb))).symm

open Classical in
theorem sifted_short_two_prime_all_moduli_siegelWalfisz
    (ε T c C A : ℝ) (hε : 0 < ε) (hT : 0 < T) (hc : 0 < c)
    (hC : 0 < C) (hA : 0 < A) :
    ∃ K X0 : ℝ, 0 < K ∧ Real.exp 1 ≤ X0 ∧
      ∀ x : ℝ, X0 ≤ x → ∀ N : ℝ, x ^ ε ≤ N → N ≤ x ^ C →
      ∀ e : Fin 2, ∀ nlo nhi : ℝ, c * N ≤ nlo →
      ∀ q : ℕ, 0 < q → ∀ r0 : ℕ, 0 < r0 →
      ∀ a : ℕ, Nat.Coprime a q →
      let j : Fin 6 := if e = 0 then 2 else 3
      let z := x ^ ((8639 : ℝ) / 50000)
      let M0 := x ^ (1 - (34941 : ℝ) / 100000)
      let S0 : ℕ → ℝ := fun n =>
        if (n : ℝ) ≤ M0 then
          ∑ ps ∈ siftedPrimeTuples x j, ∑ d ∈ n.divisorsAntidiagonal,
            if d.1 = ps.prod then smallPrimeMobius z d.2 else 0
        else 0
      ‖fullDiscrepancy
        (∑ n ∈ Finset.Icc 1 (Nat.floor (T * N)), Finsupp.single n
          (if nlo ≤ (n : ℝ) ∧ (n : ℝ) ≤ nhi ∧ Nat.Coprime n r0
           then (S0 n : ℂ) else 0)) q a‖ ≤
        K * ((q * r0).divisors.card : ℝ) * N / (Real.log x) ^ A := by
  obtain ⟨K, X0, hK, hX0, hbound⟩ :=
    harmanA0_named_all_moduli_siegelWalfisz ε T c C A hε hT hc hC hA
  refine ⟨K, X0, hK, hX0, ?_⟩
  intro x hx N hNL hNU e nlo nhi hlo q hq r0 hr0 a ha j z M0 S0
  have hx1 : 1 < x :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le (hX0.trans hx)
  have hz : 0 < z := Real.rpow_pos_of_pos (zero_lt_one.trans hx1) _
  let H := x ^ ((41361 : ℝ) / 100000)
  let B := x ^ ((58639 : ℝ) / 100000)
  let P : ℕ → ℕ → ℕ → Prop := fun s _r _h =>
    if e = 0 then True else
      Real.logb x (s : ℝ) < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000
  let L : ℕ → ℕ → ℕ → ℝ := fun s _r _h =>
    if e = 0 then (s : ℝ) + 1 else
      max ((s : ℝ) + 1) ((Nat.floor (B / (s : ℝ)) : ℝ) + 1)
  let U : ℕ → ℕ → ℕ → ℝ := fun s _r _h =>
    if e = 0 then
      min ((Nat.ceil H - 1 : ℕ) : ℝ) ((Nat.ceil (H / (s : ℝ)) - 1 : ℕ) : ℝ)
    else ((Nat.ceil H - 1 : ℕ) : ℝ)
  let Q0 : ℕ → ℤ := fun n =>
    ∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
      ∑ cc ∈ bb.2.divisorsAntidiagonal,
        if Nat.Prime aa.1 ∧ z ≤ (aa.1 : ℝ) ∧
            (Nat.Prime bb.1 ∧ z ≤ (bb.1 : ℝ)) ∧ bb.1 ≤ aa.1 ∧
            cc.1 = 1 ∧ cc.1 ≤ aa.1 ∧
            ((max 1 (cc.2.primeFactors.sup id) : ℕ) : ℝ) < z ∧
            P bb.1 cc.1 cc.2 ∧ L bb.1 cc.1 cc.2 ≤ (aa.1 : ℝ) ∧
            (aa.1 : ℝ) ≤ U bb.1 cc.1 cc.2
        then ArithmeticFunction.moebius cc.2 else 0
  have hcoeff (n : ℕ) : (Q0 n : ℂ) =
      ((∑ ps ∈ siftedPrimeTuples x j, ∑ d ∈ n.divisorsAntidiagonal,
        if d.1 = ps.prod then smallPrimeMobius z d.2 else 0 : ℝ) : ℂ) := by
    have hs := congrArg (fun t : ℝ => (t : ℂ))
      (sifted_short_two_prime_named_coefficient_eq x hx1 e n)
    simpa only [Complex.ofReal_intCast] using hs.symm
  have hb := hbound x hx N hNL hNU (1 : Fin 2) (0 : Fin 2)
    P L U z M0 nlo nhi hz hlo false q hq r0 hr0 a ha
  dsimp only at hb
  simp only [show (1 : Fin 2) ≠ 0 by decide, ite_true, ite_false,
    ite_eq_right (show ¬(false : Bool) by decide)] at hb
  dsimp only [Q0] at hcoeff
  simpa only [apply_ite (fun t : ℤ => (t : ℂ)), Int.cast_zero, hcoeff,
    S0, apply_ite (fun t : ℝ => (t : ℂ)), Complex.ofReal_zero] using hb

open Classical in
theorem sifted_short_three_prime_named_coefficient_eq
    (x : ℝ) (hx : 1 < x) (n : ℕ) :
    let z := x ^ ((8639 : ℝ) / 50000)
    let H := x ^ ((41361 : ℝ) / 100000)
    let P : ℕ → ℕ → ℕ → Prop := fun q r _h => r < q ∧
      Real.logb x (r : ℝ) < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000
    let L : ℕ → ℕ → ℕ → ℝ := fun q _r _h => (q : ℝ) + 1
    let U : ℕ → ℕ → ℕ → ℝ := fun q _r _h =>
      min ((Nat.ceil H - 1 : ℕ) : ℝ) ((Nat.ceil (H / (q : ℝ)) - 1 : ℕ) : ℝ)
    let Q0 : ℤ :=
      ∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
        ∑ cc ∈ bb.2.divisorsAntidiagonal,
          if Nat.Prime aa.1 ∧ z ≤ (aa.1 : ℝ) ∧
              (Nat.Prime bb.1 ∧ z ≤ (bb.1 : ℝ)) ∧ bb.1 ≤ aa.1 ∧
              (Nat.Prime cc.1 ∧ z ≤ (cc.1 : ℝ)) ∧ cc.1 ≤ aa.1 ∧
              ((max 1 (cc.2.primeFactors.sup id) : ℕ) : ℝ) < z ∧
              P bb.1 cc.1 cc.2 ∧ L bb.1 cc.1 cc.2 ≤ (aa.1 : ℝ) ∧
              (aa.1 : ℝ) ≤ U bb.1 cc.1 cc.2
          then ArithmeticFunction.moebius cc.2 else 0
    (∑ ps ∈ siftedPrimeTuples x (4 : Fin 6), ∑ d ∈ n.divisorsAntidiagonal,
      if d.1 = ps.prod then smallPrimeMobius z d.2 else 0) = (Q0 : ℝ) := by
  intro z H P L U Q0
  have hscalar (p q r h : ℕ) :
      (if Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
          (8639 : ℝ) / 50000 ≤ Real.logb x (r : ℝ) ∧
          Real.logb x (r : ℝ) < Real.logb x (q : ℝ) ∧
          Real.logb x (q : ℝ) < Real.logb x (p : ℝ) ∧
          Real.logb x (p : ℝ) < (41361 : ℝ) / 100000 ∧
          Real.logb x (p : ℝ) + Real.logb x (q : ℝ) < (41361 : ℝ) / 100000 ∧
          Real.logb x (r : ℝ) < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000
       then smallPrimeMobius z h else 0) =
      ((if Nat.Prime p ∧ z ≤ (p : ℝ) ∧
          (Nat.Prime q ∧ z ≤ (q : ℝ)) ∧ q ≤ p ∧
          (Nat.Prime r ∧ z ≤ (r : ℝ)) ∧ r ≤ p ∧
          ((max 1 (h.primeFactors.sup id) : ℕ) : ℝ) < z ∧
          P q r h ∧ L q r h ≤ (p : ℝ) ∧ (p : ℝ) ≤ U q r h
        then ArithmeticFunction.moebius h else 0 : ℤ) : ℝ) := by
    by_cases hp : Nat.Prime p
    · by_cases hq : Nat.Prime q
      · by_cases hr : Nat.Prime r
        · have hw := sifted_short_triple_window_iff x hx p q r hp hq hr
          dsimp only at hw
          have hguard :
              (Nat.Prime p ∧ z ≤ (p : ℝ) ∧ (Nat.Prime q ∧ z ≤ (q : ℝ)) ∧ q ≤ p ∧
                (Nat.Prime r ∧ z ≤ (r : ℝ)) ∧ r ≤ p ∧
                ((max 1 (h.primeFactors.sup id) : ℕ) : ℝ) < z ∧
                P q r h ∧ L q r h ≤ (p : ℝ) ∧ (p : ℝ) ≤ U q r h) ↔
              (Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
                (8639 : ℝ) / 50000 ≤ Real.logb x (r : ℝ) ∧
                Real.logb x (r : ℝ) < Real.logb x (q : ℝ) ∧
                Real.logb x (q : ℝ) < Real.logb x (p : ℝ) ∧
                Real.logb x (p : ℝ) < (41361 : ℝ) / 100000 ∧
                Real.logb x (p : ℝ) + Real.logb x (q : ℝ) < (41361 : ℝ) / 100000 ∧
                Real.logb x (r : ℝ) < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000) ∧
                ((max 1 (h.primeFactors.sup id) : ℕ) : ℝ) < z := by
            dsimp only [P, L, U, z, H] at hw ⊢
            tauto
          simp only [hguard]
          simp only [smallPrimeMobius, ArithmeticFunction.coe_mk,
            apply_ite (fun t : ℤ => (t : ℝ)), Int.cast_zero, ← ite_and]
        · simp [hr]
      · simp [hq]
    · simp [hp]
  have hs := sifted_short_three_prime_coefficient_eq x hx n
  dsimp only at hs
  rw [hs]
  simp only [Q0, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro aa haa
  apply Finset.sum_congr rfl
  intro bb hbb
  apply Finset.sum_congr rfl
  intro cc hcc
  exact hscalar aa.1 bb.1 cc.1 cc.2

open Classical in
theorem sifted_short_three_prime_all_moduli_siegelWalfisz
    (ε T c C A : ℝ) (hε : 0 < ε) (hT : 0 < T) (hc : 0 < c)
    (hC : 0 < C) (hA : 0 < A) :
    ∃ K X0 : ℝ, 0 < K ∧ Real.exp 1 ≤ X0 ∧
      ∀ x : ℝ, X0 ≤ x → ∀ N : ℝ, x ^ ε ≤ N → N ≤ x ^ C →
      ∀ nlo nhi : ℝ, c * N ≤ nlo →
      ∀ q : ℕ, 0 < q → ∀ r0 : ℕ, 0 < r0 →
      ∀ a : ℕ, Nat.Coprime a q →
      let z := x ^ ((8639 : ℝ) / 50000)
      let M0 := x ^ (1 - (34941 : ℝ) / 100000)
      let S0 : ℕ → ℝ := fun n =>
        if (n : ℝ) ≤ M0 then
          ∑ ps ∈ siftedPrimeTuples x (4 : Fin 6), ∑ d ∈ n.divisorsAntidiagonal,
            if d.1 = ps.prod then smallPrimeMobius z d.2 else 0
        else 0
      ‖fullDiscrepancy
        (∑ n ∈ Finset.Icc 1 (Nat.floor (T * N)), Finsupp.single n
          (if nlo ≤ (n : ℝ) ∧ (n : ℝ) ≤ nhi ∧ Nat.Coprime n r0
           then (S0 n : ℂ) else 0)) q a‖ ≤
        K * ((q * r0).divisors.card : ℝ) * N / (Real.log x) ^ A := by
  obtain ⟨K, X0, hK, hX0, hbound⟩ :=
    harmanA0_named_all_moduli_siegelWalfisz ε T c C A hε hT hc hC hA
  refine ⟨K, X0, hK, hX0, ?_⟩
  intro x hx N hNL hNU nlo nhi hlo q hq r0 hr0 a ha z M0 S0
  have hx1 : 1 < x :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le (hX0.trans hx)
  have hz : 0 < z := Real.rpow_pos_of_pos (zero_lt_one.trans hx1) _
  let H := x ^ ((41361 : ℝ) / 100000)
  let P : ℕ → ℕ → ℕ → Prop := fun s t _h => t < s ∧
    Real.logb x (t : ℝ) < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000
  let L : ℕ → ℕ → ℕ → ℝ := fun s _t _h => (s : ℝ) + 1
  let U : ℕ → ℕ → ℕ → ℝ := fun s _t _h =>
    min ((Nat.ceil H - 1 : ℕ) : ℝ) ((Nat.ceil (H / (s : ℝ)) - 1 : ℕ) : ℝ)
  let Q0 : ℕ → ℤ := fun n =>
    ∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
      ∑ cc ∈ bb.2.divisorsAntidiagonal,
        if Nat.Prime aa.1 ∧ z ≤ (aa.1 : ℝ) ∧
            (Nat.Prime bb.1 ∧ z ≤ (bb.1 : ℝ)) ∧ bb.1 ≤ aa.1 ∧
            (Nat.Prime cc.1 ∧ z ≤ (cc.1 : ℝ)) ∧ cc.1 ≤ aa.1 ∧
            ((max 1 (cc.2.primeFactors.sup id) : ℕ) : ℝ) < z ∧
            P bb.1 cc.1 cc.2 ∧ L bb.1 cc.1 cc.2 ≤ (aa.1 : ℝ) ∧
            (aa.1 : ℝ) ≤ U bb.1 cc.1 cc.2
        then ArithmeticFunction.moebius cc.2 else 0
  have hcoeff (n : ℕ) : (Q0 n : ℂ) =
      ((∑ ps ∈ siftedPrimeTuples x (4 : Fin 6), ∑ d ∈ n.divisorsAntidiagonal,
        if d.1 = ps.prod then smallPrimeMobius z d.2 else 0 : ℝ) : ℂ) := by
    have hs := congrArg (fun t : ℝ => (t : ℂ))
      (sifted_short_three_prime_named_coefficient_eq x hx1 n)
    simpa only [Complex.ofReal_intCast] using hs.symm
  have hb := hbound x hx N hNL hNU (1 : Fin 2) (1 : Fin 2)
    P L U z M0 nlo nhi hz hlo false q hq r0 hr0 a ha
  dsimp only at hb
  simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false,
    ite_eq_right (show ¬(false : Bool) by decide)] at hb
  dsimp only [Q0] at hcoeff
  simpa only [apply_ite (fun t : ℤ => (t : ℂ)), Int.cast_zero, hcoeff,
    S0, apply_ite (fun t : ℝ => (t : ℂ)), Complex.ofReal_zero] using hb

open Classical in
theorem sifted_short_all_moduli_siegelWalfisz
    (ε T c C A : ℝ) (hε : 0 < ε) (hT : 0 < T) (hc : 0 < c)
    (hC : 0 < C) (hA : 0 < A) :
    ∃ K X0 : ℝ, 0 < K ∧ Real.exp 1 ≤ X0 ∧
      ∀ x : ℝ, X0 ≤ x → ∀ N : ℝ, x ^ ε ≤ N → N ≤ x ^ C →
      ∀ j : Fin 6, ∀ nlo nhi : ℝ, c * N ≤ nlo →
      ∀ q : ℕ, 0 < q → ∀ r0 : ℕ, 0 < r0 →
      ∀ a : ℕ, Nat.Coprime a q →
      let z := x ^ ((8639 : ℝ) / 50000)
      let M0 := x ^ (1 - (34941 : ℝ) / 100000)
      let S0 : ℕ → ℝ := fun n =>
        if (n : ℝ) ≤ M0 then
          ∑ ps ∈ siftedPrimeTuples x j, ∑ d ∈ n.divisorsAntidiagonal,
            if d.1 = ps.prod then smallPrimeMobius z d.2 else 0
        else 0
      ‖fullDiscrepancy
        (∑ n ∈ Finset.Icc 1 (Nat.floor (T * N)), Finsupp.single n
          (if nlo ≤ (n : ℝ) ∧ (n : ℝ) ≤ nhi ∧ Nat.Coprime n r0
           then (S0 n : ℂ) else 0)) q a‖ ≤
        K * ((q * r0).divisors.card : ℝ) * N / (Real.log x) ^ A := by
  obtain ⟨K0, X0, hK0, hX0, h0⟩ :=
    sifted_short_empty_all_moduli_siegelWalfisz ε T c C A hε hT hc hC hA
  obtain ⟨K1, X1, hK1, _hX1, h1⟩ :=
    sifted_short_one_prime_all_moduli_siegelWalfisz ε T c C A hε hT hc hC hA
  obtain ⟨K2, X2, hK2, _hX2, h2⟩ :=
    sifted_short_two_prime_all_moduli_siegelWalfisz ε T c C A hε hT hc hC hA
  obtain ⟨K3, X3, hK3, _hX3, h3⟩ :=
    sifted_short_three_prime_all_moduli_siegelWalfisz ε T c C A hε hT hc hC hA
  obtain ⟨K5, X5, hK5, _hX5, h5⟩ :=
    sifted_short_sixth_all_moduli_siegelWalfisz ε T c C A hε hT hc hC hA
  let K := K0 + K1 + K2 + K3 + K5
  let X := max X0 (max X1 (max X2 (max X3 X5)))
  refine ⟨K, X, by dsimp only [K]; positivity, hX0.trans (le_max_left _ _), ?_⟩
  intro x hx N hNL hNU j nlo nhi hlo q hq r0 hr0 a ha z M0 S0
  have hx0 : X0 ≤ x := (le_max_left _ _).trans hx
  have hx1 : X1 ≤ x :=
    (le_max_left X1 _).trans ((le_max_right X0 _).trans hx)
  have hx2 : X2 ≤ x :=
    (le_max_left X2 _).trans
      ((le_max_right X1 _).trans ((le_max_right X0 _).trans hx))
  have hx3 : X3 ≤ x :=
    (le_max_left X3 X5).trans
      ((le_max_right X2 _).trans
        ((le_max_right X1 _).trans ((le_max_right X0 _).trans hx)))
  have hx5 : X5 ≤ x :=
    (le_max_right X3 X5).trans
      ((le_max_right X2 _).trans
        ((le_max_right X1 _).trans ((le_max_right X0 _).trans hx)))
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le (hX0.trans hx0)
  have hN : 0 ≤ N := (Real.rpow_pos_of_pos hxpos ε).le.trans hNL
  have hlog : 0 ≤ Real.log x := by
    have hlog1 := (Real.le_log_iff_exp_le hxpos).mpr (hX0.trans hx0)
    exact zero_le_one.trans hlog1
  have hmono (k : ℝ) (hk : k ≤ K) :
      k * ((q * r0).divisors.card : ℝ) * N / (Real.log x) ^ A ≤
        K * ((q * r0).divisors.card : ℝ) * N / (Real.log x) ^ A :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg _)) hN)
      (Real.rpow_nonneg hlog A)
  have hk0 : K0 ≤ K := by dsimp only [K]; linarith
  have hk1 : K1 ≤ K := by dsimp only [K]; linarith
  have hk2 : K2 ≤ K := by dsimp only [K]; linarith
  have hk3 : K3 ≤ K := by dsimp only [K]; linarith
  have hk5 : K5 ≤ K := by dsimp only [K]; linarith
  fin_cases j
  · exact (h0 x hx0 N hNL hNU nlo nhi hlo q hq r0 hr0 a ha).trans (hmono K0 hk0)
  · exact (h1 x hx1 N hNL hNU nlo nhi hlo q hq r0 hr0 a ha).trans (hmono K1 hk1)
  · exact (h2 x hx2 N hNL hNU (0 : Fin 2) nlo nhi hlo q hq r0 hr0 a ha).trans
      (hmono K2 hk2)
  · exact (h2 x hx2 N hNL hNU (1 : Fin 2) nlo nhi hlo q hq r0 hr0 a ha).trans
      (hmono K2 hk2)
  · exact (h3 x hx3 N hNL hNU nlo nhi hlo q hq r0 hr0 a ha).trans (hmono K3 hk3)
  · exact (h5 x hx5 N hNL hNU nlo nhi hlo q hq r0 hr0 a ha).trans (hmono K5 hk5)

open Classical in
theorem sifted_short_weighted_all_moduli_siegelWalfisz
    (ε T c C A D : ℝ) (hε : 0 < ε) (hT : 0 < T) (hc : 0 < c)
    (hC : 0 < C) (hA : 0 < A) (hD : 0 ≤ D) :
    ∃ K X0 : ℝ, 0 < K ∧ Real.exp 1 ≤ X0 ∧
      ∀ x : ℝ, X0 ≤ x → ∀ N : ℝ, x ^ ε ≤ N → N ≤ x ^ C →
      ∀ j : Fin 6, ∀ nlo nhi : ℝ, c * N ≤ nlo →
      ∀ w : ℕ → ℂ,
        ‖w (Nat.floor (T * N))‖ +
          (∑ n ∈ Finset.Ico 1 (Nat.floor (T * N)), ‖w (n + 1) - w n‖) ≤
            (Real.log x) ^ D →
      ∀ q : ℕ, 0 < q → ∀ r0 : ℕ, 0 < r0 → ∀ a : ℕ, Nat.Coprime a q →
      let z := x ^ ((8639 : ℝ) / 50000)
      let M0 := x ^ (1 - (34941 : ℝ) / 100000)
      let S0 : ℕ → ℝ := fun n =>
        if (n : ℝ) ≤ M0 then
          ∑ ps ∈ siftedPrimeTuples x j, ∑ d ∈ n.divisorsAntidiagonal,
            if d.1 = ps.prod then smallPrimeMobius z d.2 else 0
        else 0
      ‖fullDiscrepancy
        (∑ n ∈ Finset.Icc 1 (Nat.floor (T * N)), Finsupp.single n
          (if nlo ≤ (n : ℝ) ∧ (n : ℝ) ≤ nhi ∧ Nat.Coprime n r0
           then w n * (S0 n : ℂ) else 0)) q a‖ ≤
        K * ((q * r0).divisors.card : ℝ) * N / (Real.log x) ^ A := by
  obtain ⟨K, X0, hK, hX0, hmain⟩ :=
    sifted_short_all_moduli_siegelWalfisz ε T c C (A + D) hε hT hc hC (by linarith)
  refine ⟨K, X0, hK, hX0, ?_⟩
  intro x hx N hNL hNU j nlo nhi hnlo w hw q hq r0 hr0 a ha z M0 S0
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le (hX0.trans hx)
  have hlog1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr (hX0.trans hx)
  have hlog : 0 < Real.log x := zero_lt_one.trans_le hlog1
  have hN : 0 ≤ N := (Real.rpow_pos_of_pos hx0 ε).le.trans hNL
  let NN := Nat.floor (T * N)
  let f : ℕ → ℂ := fun n =>
    if nlo ≤ (n : ℝ) ∧ (n : ℝ) ≤ nhi then (S0 n : ℂ) else 0
  let E : ℝ := K * ((q * r0).divisors.card : ℝ) * N / (Real.log x) ^ (A + D)
  have hE : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hmask (n : ℕ) :
      (if Nat.Coprime n r0 then f n else 0) =
        if nlo ≤ (n : ℝ) ∧ (n : ℝ) ≤ nhi ∧ Nat.Coprime n r0
        then (S0 n : ℂ) else 0 := by
    by_cases h1 : nlo ≤ (n : ℝ) <;> by_cases h2 : (n : ℝ) ≤ nhi <;>
      by_cases h3 : Nat.Coprime n r0 <;> simp [f, h1, h2, h3]
  have hprefix (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ NN) :
      ‖fullDiscrepancy (∑ n ∈ Finset.Icc 1 k, Finsupp.single n
        (if Nat.Coprime n r0 then f n else 0)) q a‖ ≤ E := by
    have hset : Finset.Icc 1 k = (Finset.Icc 1 NN).filter (fun n => n ≤ k) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_filter]
      omega
    have hsource :
        (∑ n ∈ Finset.Icc 1 k, Finsupp.single n
          (if Nat.Coprime n r0 then f n else 0)) =
        ∑ n ∈ Finset.Icc 1 NN, Finsupp.single n
          (if nlo ≤ (n : ℝ) ∧ (n : ℝ) ≤ min nhi (k : ℝ) ∧ Nat.Coprime n r0
           then (S0 n : ℂ) else 0) := by
      rw [hset, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _hn
      rw [hmask]
      by_cases hnk : n ≤ k <;> simp [hnk, Nat.cast_le]
    rw [hsource]
    simpa only [S0, z, M0, NN, E] using
      hmain x hx N hNL hNU j nlo (min nhi (k : ℝ)) hnlo q hq r0 hr0 a ha
  have hparts := norm_fullDiscrepancy_Icc_weighted_le_of_prefix
    1 NN q a r0 f w E hE hprefix
  have hsource :
      (∑ n ∈ Finset.Icc 1 NN, Finsupp.single n
        (if nlo ≤ (n : ℝ) ∧ (n : ℝ) ≤ nhi ∧ Nat.Coprime n r0
         then w n * (S0 n : ℂ) else 0)) =
      ∑ n ∈ Finset.Icc 1 NN, Finsupp.single n
        (if Nat.Coprime n r0 then w n * f n else 0) := by
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases h1 : nlo ≤ (n : ℝ) <;> by_cases h2 : (n : ℝ) ≤ nhi <;>
      by_cases h3 : Nat.Coprime n r0 <;> simp [f, h1, h2, h3]
  change ‖fullDiscrepancy (∑ n ∈ Finset.Icc 1 NN, Finsupp.single n
    (if nlo ≤ (n : ℝ) ∧ (n : ℝ) ≤ nhi ∧ Nat.Coprime n r0
     then w n * (S0 n : ℂ) else 0)) q a‖ ≤ _
  rw [hsource]
  calc
    _ ≤ E * (‖w NN‖ + ∑ n ∈ Finset.Ico 1 NN, ‖w (n + 1) - w n‖) := hparts
    _ ≤ E * (Real.log x) ^ D := mul_le_mul_of_nonneg_left hw hE
    _ = K * ((q * r0).divisors.card : ℝ) * N / (Real.log x) ^ A := by
      dsimp only [E]
      rw [Real.rpow_add hlog, div_mul_eq_div_div,
        div_mul_cancel₀ _ (Real.rpow_pos_of_pos hlog D).ne']

open Classical in
theorem sifted_short_mellin_all_moduli_siegelWalfisz
    (ε T c C A : ℝ) (hε : 0 < ε) (hT : 0 < T) (hc : 0 < c)
    (hC : 0 < C) (hA : 0 < A) :
    ∃ K X0 : ℝ, 0 < K ∧ Real.exp 1 ≤ X0 ∧
      ∀ x : ℝ, X0 ≤ x → ∀ N : ℝ, x ^ ε ≤ N → N ≤ x ^ C →
      ∀ j : Fin 6, ∀ nlo nhi : ℝ, c * N ≤ nlo → ∀ t : ℝ, 0 ≤ t →
      ∀ q : ℕ, 0 < q → ∀ r0 : ℕ, 0 < r0 → ∀ a : ℕ, Nat.Coprime a q →
      let z := x ^ ((8639 : ℝ) / 50000)
      let M0 := x ^ (1 - (34941 : ℝ) / 100000)
      let S0 : ℕ → ℝ := fun n =>
        if (n : ℝ) ≤ M0 then
          ∑ ps ∈ siftedPrimeTuples x j, ∑ d ∈ n.divisorsAntidiagonal,
            if d.1 = ps.prod then smallPrimeMobius z d.2 else 0
        else 0
      ‖fullDiscrepancy
        (∑ n ∈ Finset.Icc 1 (Nat.floor (T * N)), Finsupp.single n
          (if nlo ≤ (n : ℝ) ∧ (n : ℝ) ≤ nhi ∧ Nat.Coprime n r0
           then (((n : ℝ) ^ (-t) : ℝ) : ℂ) * (S0 n : ℂ) else 0)) q a‖ ≤
        K * ((q * r0).divisors.card : ℝ) * N / (Real.log x) ^ A := by
  obtain ⟨K, X0, hK, hX0, hmain⟩ :=
    sifted_short_weighted_all_moduli_siegelWalfisz ε T c C A 0 hε hT hc hC hA le_rfl
  refine ⟨K, X0, hK, hX0, ?_⟩
  intro x hx N hNL hNU j nlo nhi hnlo t ht q hq r0 hr0 a ha
  have hvariation :
      ‖(((Nat.floor (T * N) : ℝ) ^ (-t) : ℝ) : ℂ)‖ +
        (∑ n ∈ Finset.Ico 1 (Nat.floor (T * N)),
          ‖((((n + 1 : ℕ) : ℝ) ^ (-t) : ℝ) : ℂ) - (((n : ℝ) ^ (-t) : ℝ) : ℂ)‖) ≤
          (Real.log x) ^ (0 : ℝ) := by
    simpa only [Real.rpow_zero] using
      mellin_weight_discrete_variation_le_one (Nat.floor (T * N)) t ht
  exact hmain x hx N hNL hNU j nlo nhi hnlo
    (fun n => (((n : ℝ) ^ (-t) : ℝ) : ℂ)) hvariation q hq r0 hr0 a ha

open Classical in
theorem sifted_short_two_raw_norm_le
    (x : ℝ) (hx : 1 < x) (e : Fin 2) (n : ℕ) :
    let j : Fin 6 := if e = 0 then 2 else 3
    ‖((∑ ps ∈ siftedPrimeTuples x j, ∑ d ∈ n.divisorsAntidiagonal,
      if d.1 = ps.prod then smallPrimeMobius (x ^ ((8639 : ℝ) / 50000)) d.2
      else 0 : ℝ) : ℂ)‖ ≤ (n.divisors.card : ℝ) ^ 3 := by
  intro j
  let z := x ^ ((8639 : ℝ) / 50000)
  let H := x ^ ((41361 : ℝ) / 100000)
  let B := x ^ ((58639 : ℝ) / 100000)
  let P : ℕ → ℕ → ℕ → Prop := fun q _r _h =>
    if e = 0 then True else
      Real.logb x (q : ℝ) < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000
  let L : ℕ → ℕ → ℕ → ℝ := fun q _r _h =>
    if e = 0 then (q : ℝ) + 1 else
      max ((q : ℝ) + 1) ((Nat.floor (B / (q : ℝ)) : ℝ) + 1)
  let U : ℕ → ℕ → ℕ → ℝ := fun q _r _h =>
    if e = 0 then
      min ((Nat.ceil H - 1 : ℕ) : ℝ) ((Nat.ceil (H / (q : ℝ)) - 1 : ℕ) : ℝ)
    else ((Nat.ceil H - 1 : ℕ) : ℝ)
  let Q0 : ℤ :=
    ∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
      ∑ cc ∈ bb.2.divisorsAntidiagonal,
        if Nat.Prime aa.1 ∧ z ≤ (aa.1 : ℝ) ∧
            (Nat.Prime bb.1 ∧ z ≤ (bb.1 : ℝ)) ∧ bb.1 ≤ aa.1 ∧
            cc.1 = 1 ∧ cc.1 ≤ aa.1 ∧
            ((max 1 (cc.2.primeFactors.sup id) : ℕ) : ℝ) < z ∧
            P bb.1 cc.1 cc.2 ∧ L bb.1 cc.1 cc.2 ≤ (aa.1 : ℝ) ∧
            (aa.1 : ℝ) ≤ U bb.1 cc.1 cc.2
        then ArithmeticFunction.moebius cc.2 else 0
  have hb := harmanA0_named_coefficient_norm_le n (1 : Fin 2) (0 : Fin 2)
    P L U z (n : ℝ) false
  dsimp only at hb
  simp only [le_refl, ite_true] at hb
  change ‖(Q0 : ℂ)‖ ≤ (n.divisors.card : ℝ) ^ 3 at hb
  have hs := congrArg (fun t : ℝ => (t : ℂ))
    (sifted_short_two_prime_named_coefficient_eq x hx e n)
  simp only [Complex.ofReal_intCast] at hs
  rw [← hs] at hb
  exact hb

open Classical in
theorem sifted_short_three_raw_norm_le (x : ℝ) (hx : 1 < x) (n : ℕ) :
    ‖((∑ ps ∈ siftedPrimeTuples x (4 : Fin 6), ∑ d ∈ n.divisorsAntidiagonal,
      if d.1 = ps.prod then smallPrimeMobius (x ^ ((8639 : ℝ) / 50000)) d.2
      else 0 : ℝ) : ℂ)‖ ≤ (n.divisors.card : ℝ) ^ 3 := by
  let z := x ^ ((8639 : ℝ) / 50000)
  let H := x ^ ((41361 : ℝ) / 100000)
  let P : ℕ → ℕ → ℕ → Prop := fun q r _h => r < q ∧
    Real.logb x (r : ℝ) < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000
  let L : ℕ → ℕ → ℕ → ℝ := fun q _r _h => (q : ℝ) + 1
  let U : ℕ → ℕ → ℕ → ℝ := fun q _r _h =>
    min ((Nat.ceil H - 1 : ℕ) : ℝ) ((Nat.ceil (H / (q : ℝ)) - 1 : ℕ) : ℝ)
  let Q0 : ℤ :=
    ∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
      ∑ cc ∈ bb.2.divisorsAntidiagonal,
        if Nat.Prime aa.1 ∧ z ≤ (aa.1 : ℝ) ∧
            (Nat.Prime bb.1 ∧ z ≤ (bb.1 : ℝ)) ∧ bb.1 ≤ aa.1 ∧
            (Nat.Prime cc.1 ∧ z ≤ (cc.1 : ℝ)) ∧ cc.1 ≤ aa.1 ∧
            ((max 1 (cc.2.primeFactors.sup id) : ℕ) : ℝ) < z ∧
            P bb.1 cc.1 cc.2 ∧ L bb.1 cc.1 cc.2 ≤ (aa.1 : ℝ) ∧
            (aa.1 : ℝ) ≤ U bb.1 cc.1 cc.2
        then ArithmeticFunction.moebius cc.2 else 0
  have hb := harmanA0_named_coefficient_norm_le n (1 : Fin 2) (1 : Fin 2)
    P L U z (n : ℝ) false
  dsimp only at hb
  simp only [le_refl, show (1 : Fin 2) ≠ 0 by decide,
    Bool.coe_sort_false, ite_false, ite_true] at hb
  change ‖(Q0 : ℂ)‖ ≤ (n.divisors.card : ℝ) ^ 3 at hb
  have hs := congrArg (fun t : ℝ => (t : ℂ))
    (sifted_short_three_prime_named_coefficient_eq x hx n)
  simp only [Complex.ofReal_intCast] at hs
  rw [← hs] at hb
  exact hb

open Classical in
theorem sifted_short_source_bounds (x : ℝ) (hx : 1 < x) (j : Fin 6) (n : ℕ) :
    let z := x ^ ((8639 : ℝ) / 50000)
    let M0 := x ^ (1 - (34941 : ℝ) / 100000)
    let S0 : ℕ → ℝ := fun m =>
      if (m : ℝ) ≤ M0 then
        ∑ ps ∈ siftedPrimeTuples x j, ∑ d ∈ m.divisorsAntidiagonal,
          if d.1 = ps.prod then smallPrimeMobius z d.2 else 0
      else 0
    ‖(S0 n : ℂ)‖ ≤ (n.divisors.card : ℝ) ^ 3 ∧
      S0 0 = 0 ∧ (S0 n ≠ 0 → (n : ℝ) ≤ M0) := by
  intro z M0 S0
  refine ⟨?_, ?_, ?_⟩
  · by_cases hn : (n : ℝ) ≤ M0
    · simp only [S0, ite_eq_left hn]
      fin_cases j
      · exact sifted_short_empty_raw_norm_le x n
      · exact sifted_short_one_raw_norm_le x hx n
      · exact sifted_short_two_raw_norm_le x hx (0 : Fin 2) n
      · exact sifted_short_two_raw_norm_le x hx (1 : Fin 2) n
      · exact sifted_short_three_raw_norm_le x hx n
      · exact sifted_short_sixth_raw_norm_le x hx n
    · simp only [S0, ite_eq_right hn, Complex.ofReal_zero, norm_zero]
      exact pow_nonneg (Nat.cast_nonneg _) 3
  · simp [S0]
  · intro hne
    dsimp only [S0] at hne
    exact (ite_ne_right_iff.mp hne).1

#print axioms sifted_short_sixth_primeFactors_coefficient_eq
#print axioms sifted_short_all_moduli_siegelWalfisz
#print axioms sifted_short_weighted_all_moduli_siegelWalfisz
#print axioms sifted_short_mellin_all_moduli_siegelWalfisz
#print axioms sifted_short_source_bounds

end PrimeGap182Analytic.Harman
