import HarmanBuchstab182

/-! Literal new T3/T4 prime tuples, monomial cuts, and original-coordinate
support. At the new zeta, the residual-prime argument uses b+2*zeta>1;
the old 4*zeta>1 statement is neither retained nor assumed. The physical
box window is widened to [.23,.42]. Adapted from Apache-2.0 PrimeGaps186,
with source hash and all substantive changes recorded in the generator. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

theorem eventually_sourceT3_T4_large :
    ∀ᶠ x : ℝ in Filter.atTop,
      3 ≤ x ∧ 2 * x < x ^ ((101 : ℝ) / 100) := by
  have h := tendsto_rpow_atTop
    (by norm_num : (0 : ℝ) < (101 : ℝ) / 100 - 1)
  filter_upwards [Filter.eventually_ge_atTop (3 : ℝ), h.eventually_gt_atTop 2]
    with x hx hg
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) hx
  refine ⟨hx, ?_⟩
  calc
    2 * x < x ^ ((101 : ℝ) / 100 - 1) * x :=
      mul_lt_mul_of_pos_right hg hxPos
    _ = x ^ (((101 : ℝ) / 100 - 1) + 1) := by
      rw [Real.rpow_add hxPos, Real.rpow_one]
    _ = _ := by congr 1; ring

theorem sourceT3_eventually_residual_prime :
    ∃ X : ℝ, 3 ≤ X ∧
      ∀ x : ℝ, X ≤ x →
      ∀ n p q r : ℕ,
        x ≤ (n : ℝ) → (n : ℝ) ≤ 2 * x → n = p * q * r →
        p.Prime → q.Prime →
        (8639 : ℝ) / 50000 ≤ Real.logb x (q : ℝ) →
        Real.logb x (q : ℝ) < Real.logb x (p : ℝ) →
        Real.logb x (p : ℝ) < (41361 : ℝ) / 100000 →
        (58639 : ℝ) / 100000 < Real.logb x (p : ℝ) + Real.logb x (q : ℝ) →
        1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000 ≤ Real.logb x (q : ℝ) →
        roughWeight (q : ℝ) r ≠ 0 →
        r.Prime ∧ (q : ℝ) ≤ (r : ℝ) := by
  classical
  obtain ⟨X, hX⟩ := eventually_sourceT3_T4_large.exists_forall_of_atTop
  refine ⟨max 3 X, le_max_left _ _, ?_⟩
  intro x hx n p q r hnLo hnHi hn hp hq _hξ hqp hpa hpq hζ hrough
  obtain ⟨hxThree, hlarge⟩ := hX x ((le_max_right _ _).trans hx)
  have hxOne : 1 < x := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hxThree
  have hxPos : 0 < x := zero_lt_one.trans hxOne
  have hpPos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hqPos : 0 < (q : ℝ) := Nat.cast_pos.mpr hq.pos
  have hnReal : (n : ℝ) = (p : ℝ) * (q : ℝ) * (r : ℝ) := by exact_mod_cast hn
  have hrOne : r ≠ 1 := by
    intro hr
    have hnProduct : (n : ℝ) = (p : ℝ) * (q : ℝ) := by
      simpa only [hr, Nat.cast_one, mul_one] using hnReal
    have hlogn := Real.logb_le_logb_of_le hxOne hxPos hnLo
    rw [Real.logb_self_eq_one hxOne, hnProduct, Real.logb_mul hpPos.ne' hqPos.ne'] at hlogn
    linarith only [hlogn, hqp, hpa]
  have hrSmall : (r : ℝ) < (q : ℝ) ^ 2 := by
    by_contra hbad
    have hrSquare : (q : ℝ) ^ 2 ≤ (r : ℝ) := le_of_not_gt hbad
    have hrPos : 0 < (r : ℝ) := (sq_pos_of_pos hqPos).trans_le hrSquare
    have hlogr : 2 * Real.logb x (q : ℝ) ≤ Real.logb x (r : ℝ) := by
      have hh := Real.logb_le_logb_of_le hxOne (sq_pos_of_pos hqPos) hrSquare
      simpa only [Real.logb_pow, Nat.cast_ofNat] using hh
    have hnPos : 0 < (n : ℝ) := hxPos.trans_le hnLo
    have hbig : x ^ ((101 : ℝ) / 100) ≤ (n : ℝ) := by
      apply (Real.le_logb_iff_rpow_le hxOne hnPos).mp
      rw [hnReal, Real.logb_mul (mul_pos hpPos hqPos).ne' hrPos.ne',
        Real.logb_mul hpPos.ne' hqPos.ne']
      linarith only [hpq, hζ, hlogr]
    exact (not_lt_of_ge hnHi) (hlarge.trans_le hbig)
  exact roughWeight_prime_of_lt_square (q : ℝ) hqPos.le r hrOne hrough hrSmall

theorem sourceT4_eventually_residual_prime :
    ∃ X : ℝ, 3 ≤ X ∧
      ∀ x : ℝ, X ≤ x →
      ∀ n p q r s : ℕ,
        x ≤ (n : ℝ) → (n : ℝ) ≤ 2 * x → n = p * q * r * s →
        p.Prime → q.Prime → r.Prime →
        (8639 : ℝ) / 50000 ≤ Real.logb x (r : ℝ) →
        Real.logb x (r : ℝ) < Real.logb x (q : ℝ) →
        Real.logb x (q : ℝ) < Real.logb x (p : ℝ) →
        Real.logb x (p : ℝ) < (41361 : ℝ) / 100000 →
        (58639 : ℝ) / 100000 < Real.logb x (p : ℝ) + Real.logb x (q : ℝ) →
        Real.logb x (q : ℝ) < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000 →
        roughWeight (r : ℝ) s ≠ 0 →
        s.Prime ∧ (r : ℝ) ≤ (s : ℝ) := by
  classical
  obtain ⟨X, hX⟩ := eventually_sourceT3_T4_large.exists_forall_of_atTop
  refine ⟨max 3 X, le_max_left _ _, ?_⟩
  intro x hx n p q r s hnLo hnHi hn hp hq hr hξ hrq _hqp hpa hpq hζ hrough
  obtain ⟨hxThree, hlarge⟩ := hX x ((le_max_right _ _).trans hx)
  have hxOne : 1 < x := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hxThree
  have hxPos : 0 < x := zero_lt_one.trans hxOne
  have hpPos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hqPos : 0 < (q : ℝ) := Nat.cast_pos.mpr hq.pos
  have hrPos : 0 < (r : ℝ) := Nat.cast_pos.mpr hr.pos
  have hnReal : (n : ℝ) = (p : ℝ) * (q : ℝ) * (r : ℝ) * (s : ℝ) := by
    exact_mod_cast hn
  have hsOne : s ≠ 1 := by
    intro hs
    have hnProduct : (n : ℝ) = (p : ℝ) * (q : ℝ) * (r : ℝ) := by
      simpa only [hs, Nat.cast_one, mul_one] using hnReal
    have hlogn := Real.logb_le_logb_of_le hxOne hxPos hnLo
    rw [Real.logb_self_eq_one hxOne, hnProduct,
      Real.logb_mul (mul_pos hpPos hqPos).ne' hrPos.ne',
      Real.logb_mul hpPos.ne' hqPos.ne'] at hlogn
    linarith only [hlogn, hrq, hpa, hζ]
  have hsSmall : (s : ℝ) < (r : ℝ) ^ 2 := by
    by_contra hbad
    have hsSquare : (r : ℝ) ^ 2 ≤ (s : ℝ) := le_of_not_gt hbad
    have hrLo : x ^ ((8639 : ℝ) / 50000) ≤ (r : ℝ) :=
      (Real.le_logb_iff_rpow_le hxOne hrPos).mp hξ
    have hpqLo : x ^ ((58639 : ℝ) / 100000) ≤ (p : ℝ) * (q : ℝ) := by
      apply (Real.le_logb_iff_rpow_le hxOne (mul_pos hpPos hqPos)).mp
      simpa only [Real.logb_mul hpPos.ne' hqPos.ne'] using hpq.le
    have hrs : (x ^ ((8639 : ℝ) / 50000)) ^ (3 : ℕ) ≤ (r : ℝ) * (s : ℝ) := by
      calc
        _ ≤ (r : ℝ) ^ 3 := pow_le_pow_left₀ (Real.rpow_nonneg hxPos.le _) hrLo 3
        _ = (r : ℝ) * (r : ℝ) ^ 2 := by ring
        _ ≤ (r : ℝ) * (s : ℝ) := mul_le_mul_of_nonneg_left hsSquare hrPos.le
    have hbig :
        x ^ ((58639 : ℝ) / 100000 + 3 * ((8639 : ℝ) / 50000)) ≤ (n : ℝ) := by
      calc
        _ = x ^ ((58639 : ℝ) / 100000) *
            (x ^ ((8639 : ℝ) / 50000)) ^ (3 : ℕ) := by
          rw [Real.rpow_add hxPos, ← Real.rpow_mul_natCast hxPos.le]
          congr 2
          ring
        _ ≤ ((p : ℝ) * (q : ℝ)) * ((r : ℝ) * (s : ℝ)) :=
          mul_le_mul hpqLo hrs (by positivity) (mul_pos hpPos hqPos).le
        _ = (n : ℝ) := by rw [hnReal]; ring
    have hpower :
        x ^ ((101 : ℝ) / 100) ≤
          x ^ ((58639 : ℝ) / 100000 + 3 * ((8639 : ℝ) / 50000)) :=
      Real.rpow_le_rpow_of_exponent_le hxOne.le (by norm_num)
    exact (not_lt_of_ge hnHi) (hlarge.trans_le (hpower.trans hbig))
  exact roughWeight_prime_of_lt_square (r : ℝ) hrPos.le s hsOne hrough hsSmall

open Classical in
/--
The Boolean test for the three-exponent `T3` region, including the condition that the remaining
exponent is at least the smaller of the two selected prime exponents.
-/
noncomputable def sourceT3ExponentMask (α : Fin 3 → ℝ) : Bool :=
  decide ((8639 : ℝ) / 50000 ≤ α 1 ∧ α 1 < α 0 ∧
    α 0 < (41361 : ℝ) / 100000 ∧ (58639 : ℝ) / 100000 < α 0 + α 1 ∧
    1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000 ≤ α 1 ∧ α 1 ≤ α 2)

open Classical in
theorem sum_three_prime_divisorsAntidiagonal {A : Type*} [AddCommMonoid A]
    (n : ℕ) (w : (Fin 3 → ℕ) → A) :
    (∑ a ∈ n.divisorsAntidiagonal, ∑ b ∈ a.2.divisorsAntidiagonal,
      if a.1.Prime ∧ b.1.Prime ∧ b.2.Prime then w ![a.1, b.1, b.2] else 0) =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin 3 => Nat.primesLE n),
        if (∏ i, p i) = n then w p else 0 := by
  let S : Finset (Σ _ : ℕ × ℕ, ℕ × ℕ) :=
    (n.divisorsAntidiagonal.sigma (fun a => a.2.divisorsAntidiagonal)).filter
      (fun v => v.1.1.Prime ∧ v.2.1.Prime ∧ v.2.2.Prime)
  let T : Finset (Fin 3 → ℕ) :=
    (Fintype.piFinset (fun _ : Fin 3 => Nat.primesLE n)).filter (fun p => ∏ i, p i = n)
  let f : (Σ _ : ℕ × ℕ, ℕ × ℕ) → Fin 3 → ℕ := fun v => ![v.1.1, v.2.1, v.2.2]
  calc
    _ = ∑ v ∈ S, w (f v) := by
      simp only [S, f, Finset.sum_filter, Finset.sum_sigma]
    _ = ∑ p ∈ T, w p := by
      refine Finset.sum_bij (fun v _ => f v) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro v hv
        obtain ⟨hvs, hp, hq, hr⟩ := Finset.mem_filter.mp hv
        obtain ⟨ha, hb⟩ := Finset.mem_sigma.mp hvs
        have hproduct : ∏ i, f v i = n := by
          rw [Fin.prod_univ_three]
          change v.1.1 * v.2.1 * v.2.2 = n
          rw [Nat.mul_assoc, (Nat.mem_divisorsAntidiagonal.mp hb).1,
            (Nat.mem_divisorsAntidiagonal.mp ha).1]
        have hprime (i : Fin 3) : (f v i).Prime := by
          fin_cases i
          · simpa [f] using hp
          · simpa [f] using hq
          · simpa [f] using hr
        apply Finset.mem_filter.mpr
        refine ⟨Fintype.mem_piFinset.mpr (fun i => ?_), hproduct⟩
        apply Nat.mem_primesLE.mpr
        refine ⟨Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisorsAntidiagonal.mp ha).2) ?_,
          hprime i⟩
        rw [← hproduct]
        exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      · intro v hv u hu heq
        have h0 : v.1.1 = u.1.1 := congrArg (fun p : Fin 3 → ℕ => p 0) heq
        have h1 : v.2.1 = u.2.1 := congrArg (fun p : Fin 3 → ℕ => p 1) heq
        have h2 : v.2.2 = u.2.2 := congrArg (fun p : Fin 3 → ℕ => p 2) heq
        obtain ⟨_, hvb⟩ := Finset.mem_sigma.mp (Finset.mem_filter.mp hv).1
        obtain ⟨_, hub⟩ := Finset.mem_sigma.mp (Finset.mem_filter.mp hu).1
        have ha : v.1.2 = u.1.2 := by
          rw [← (Nat.mem_divisorsAntidiagonal.mp hvb).1,
            ← (Nat.mem_divisorsAntidiagonal.mp hub).1, h1, h2]
        exact Sigma.ext (Prod.ext h0 ha) (heq_of_eq (Prod.ext h1 h2))
      · intro p hp
        obtain ⟨hpp, hpn⟩ := Finset.mem_filter.mp hp
        have hprime (i : Fin 3) := Nat.prime_of_mem_primesLE (Fintype.mem_piFinset.mp hpp i)
        have hn : n ≠ 0 := by
          rw [← hpn]
          exact Finset.prod_ne_zero_iff.mpr (fun i _ => (hprime i).ne_zero)
        have hprod : p 0 * (p 1 * p 2) = n := by
          simpa only [Fin.prod_univ_three, Nat.mul_assoc] using hpn
        let v : Σ _ : ℕ × ℕ, ℕ × ℕ := ⟨(p 0, p 1 * p 2), (p 1, p 2)⟩
        have hv : v ∈ S := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_sigma.mpr ⟨?_, ?_⟩, hprime 0, hprime 1, hprime 2⟩
          · exact Nat.mem_divisorsAntidiagonal.mpr ⟨hprod, hn⟩
          · exact Nat.mem_divisorsAntidiagonal.mpr
              ⟨rfl, mul_ne_zero (hprime 1).ne_zero (hprime 2).ne_zero⟩
        refine ⟨v, hv, ?_⟩
        funext i
        fin_cases i <;> simp [f, v]
    _ = _ := by simp only [T, Finset.sum_filter]

open Classical in
theorem sourceT3_eventually_eq_three_prime_tuple_sum :
    ∃ X : ℝ, 3 ≤ X ∧ ∀ x : ℝ, X ≤ x → ∀ n : ℕ,
      x ≤ (n : ℝ) → (n : ℝ) ≤ 2 * x →
      sourceT3 x n =
        ∑ p ∈ Fintype.piFinset (fun _ : Fin 3 => Nat.primesLE n),
          if (∏ i, p i) = n then
            (if sourceT3ExponentMask (fun i => Real.logb x (p i : ℝ)) then (1 : ℝ) else 0)
          else 0 := by
  obtain ⟨X, hX, hres⟩ := sourceT3_eventually_residual_prime
  refine ⟨X, hX, ?_⟩
  intro x hx n hnlo hnhi
  have hxOne : 1 < x := (by norm_num : (1 : ℝ) < 3).trans_le (hX.trans hx)
  rw [← sum_three_prime_divisorsAntidiagonal n
    (fun p => if sourceT3ExponentMask (fun i => Real.logb x (p i : ℝ)) then 1 else 0)]
  change (∑ a ∈ n.divisorsAntidiagonal, ∑ b ∈ a.2.divisorsAntidiagonal, _) = _
  refine Finset.sum_congr rfl (fun a ha => ?_)
  refine Finset.sum_congr rfl (fun b hb => ?_)
  let α (p : ℕ) : ℝ := Real.logb x (p : ℝ)
  let P : Prop := a.1.Prime ∧ b.1.Prime ∧
    (8639 : ℝ) / 50000 ≤ α b.1 ∧ α b.1 < α a.1 ∧
    α a.1 < (41361 : ℝ) / 100000 ∧ (58639 : ℝ) / 100000 < α a.1 + α b.1 ∧
    1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000 ≤ α b.1
  change (if P then roughWeight (b.1 : ℝ) b.2 else 0) =
    if a.1.Prime ∧ b.1.Prime ∧ b.2.Prime then
      (if sourceT3ExponentMask ![α a.1, α b.1, α b.2] then 1 else 0) else 0
  by_cases hP : P
  · rw [ite_eq_left hP]
    obtain ⟨hp, hq, hξ, hqp, hpa, hpq, hζ⟩ := hP
    by_cases hr : b.2.Prime
    · have horder : α b.1 ≤ α b.2 ↔ (b.1 : ℝ) ≤ (b.2 : ℝ) :=
        Real.logb_le_logb hxOne (Nat.cast_pos.mpr hq.pos) (Nat.cast_pos.mpr hr.pos)
      have hm : sourceT3ExponentMask ![α a.1, α b.1, α b.2] =
          decide ((b.1 : ℝ) ≤ (b.2 : ℝ)) := by
        simp [sourceT3ExponentMask, hξ, hqp, hpa, hpq, hζ, horder]
      rw [ite_eq_left ⟨hp, hq, hr⟩, hm]
      rw [roughWeight_eq_ite_minFac (b.1 : ℝ) hr.ne_zero hr.ne_one, hr.minFac_eq]
      simp
    · rw [ite_eq_right (fun h => hr h.2.2)]
      by_contra hrough
      have hn : n = a.1 * b.1 * b.2 := by
        symm
        rw [Nat.mul_assoc, (Nat.mem_divisorsAntidiagonal.mp hb).1,
          (Nat.mem_divisorsAntidiagonal.mp ha).1]
      exact hr ((hres x hx n a.1 b.1 b.2 hnlo hnhi hn
        hp hq hξ hqp hpa hpq hζ hrough).1)
  · rw [ite_eq_right hP]
    by_cases hprime : a.1.Prime ∧ b.1.Prime ∧ b.2.Prime
    · rw [ite_eq_left hprime]
      symm
      apply ite_eq_right
      intro hm
      have hcuts : (8639 : ℝ) / 50000 ≤ α b.1 ∧ α b.1 < α a.1 ∧
          α a.1 < (41361 : ℝ) / 100000 ∧ (58639 : ℝ) / 100000 < α a.1 + α b.1 ∧
          1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000 ≤ α b.1 ∧ α b.1 ≤ α b.2 := by
        unfold sourceT3ExponentMask at hm
        simpa using of_decide_eq_true hm
      exact hP ⟨hprime.1, hprime.2.1, hcuts.1, hcuts.2.1,
        hcuts.2.2.1, hcuts.2.2.2.1, hcuts.2.2.2.2.1⟩
    · rw [ite_eq_right hprime]

open Classical in
theorem sourceT3_prime_tuple_exponent_bounds
    (x : ℝ) (hx : 1 < x) (p : Fin 3 → ℕ) (hp : ∀ i, (p i).Prime)
    (hproduct : ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x)
    (hcut : sourceT3ExponentMask (fun i => Real.logb x (p i : ℝ)) = true) :
    ∀ i, 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000 ≤
      Real.logb x (p i : ℝ) ∧
      Real.logb x (p i : ℝ) ≤ (41361 : ℝ) / 100000 + Real.logb x 2 := by
  let α (i : Fin 3) : ℝ := Real.logb x (p i : ℝ)
  have hcuts : (8639 : ℝ) / 50000 ≤ α 1 ∧ α 1 < α 0 ∧
      α 0 < (41361 : ℝ) / 100000 ∧ (58639 : ℝ) / 100000 < α 0 + α 1 ∧
      1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000 ≤ α 1 ∧ α 1 ≤ α 2 :=
    of_decide_eq_true hcut
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hpPos (i : Fin 3) : (0 : ℝ) < p i := Nat.cast_pos.mpr (hp i).pos
  have hproductPos : (0 : ℝ) < (∏ i, p i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => (hp i).pos)
  have hsum : α 0 + α 1 + α 2 ≤ 1 + Real.logb x 2 := by
    have h := Real.logb_le_logb_of_le hx hproductPos hproduct
    rw [Fin.prod_univ_three, Nat.cast_mul, Nat.cast_mul,
      Real.logb_mul (mul_pos (hpPos 0) (hpPos 1)).ne' (hpPos 2).ne',
      Real.logb_mul (hpPos 0).ne' (hpPos 1).ne',
      Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) hxpos.ne',
      Real.logb_self_eq_one hx] at h
    simpa only [α, add_comm (Real.logb x 2) 1] using h
  have htwo : 0 ≤ Real.logb x 2 := Real.logb_nonneg hx (by norm_num)
  obtain ⟨_, h10, h0a, h01b, hζ, h12⟩ := hcuts
  intro i
  fin_cases i
  · change _ ≤ α 0 ∧ α 0 ≤ _
    exact ⟨hζ.trans h10.le, h0a.le.trans (le_add_of_nonneg_right htwo)⟩
  · change _ ≤ α 1 ∧ α 1 ≤ _
    exact ⟨hζ, h10.le.trans (h0a.le.trans (le_add_of_nonneg_right htwo))⟩
  · change _ ≤ α 2 ∧ α 2 ≤ _
    exact ⟨hζ.trans h12, by linarith⟩

open Classical in
theorem minorant_t4_sub_u1_typeII_support (α : Fin 4 → ℝ)
    (_ : ∀ i, 0 ≤ α i)
    (hslo : 1 ≤ ∑ i, α i)
    (hshi : ∑ i, α i ≤ 1 + (1 / 10 ^ 10 : ℝ)) :
    let C4 : Prop :=
      (8639 / 50000 : ℝ) ≤ α 2 ∧ α 2 < α 1 ∧ α 1 < α 0 ∧
        α 0 < 41361 / 100000 ∧ 58639 / 100000 < α 0 + α 1 ∧
        α 1 < 1 - 34941 / 100000 - 41361 / 100000 ∧ α 2 ≤ α 3
    let U1 : Prop :=
      (8639 / 50000 : ℝ) ≤ α 2 ∧ α 2 < α 1 ∧ α 1 < 41361 / 100000 ∧
        α 2 + α 3 < 41361 / 100000 ∧
        α 1 < 1 - 34941 / 100000 - 41361 / 100000 ∧ α 2 ≤ α 3
    (if C4 then (1 : ℝ) else 0) - (if U1 then 1 else 0) ≠ 0 →
      (∀ i, (8639 / 50000 : ℝ) ≤ α i) ∧
        ∃ S : Finset (Fin 4), S.Nonempty ∧ S ≠ Finset.univ ∧
          (41361 / 100000 : ℝ) ≤ ∑ i ∈ S, α i ∧
            ∑ i ∈ S, α i ≤ (58639 / 100000 : ℝ) := by
  intro C4 U1 hmask
  rw [Fin.sum_univ_four] at hslo hshi
  by_cases hC : C4
  · by_cases hU : U1
    · simp [hC, hU] at hmask
    · rcases hC with ⟨h2, h21, h10, h0a, h01, h1z, h23⟩
      have h23lo : (41361 / 100000 : ℝ) ≤ α 2 + α 3 := by
        by_contra h
        apply hU
        exact ⟨h2, h21, h10.trans h0a, lt_of_not_ge h, h1z, h23⟩
      have h23hi : α 2 + α 3 ≤ (58639 / 100000 : ℝ) := by
        linarith
      refine ⟨?_, {2, 3}, by simp, by decide, ?_, ?_⟩
      · intro i
        fin_cases i <;> dsimp <;> linarith
      · simpa using h23lo
      · simpa using h23hi
  · by_cases hU : U1
    · rcases hU with ⟨h2, h21, h1a, h23a, h1z, h23⟩
      have h01 : (58639 / 100000 : ℝ) < α 0 + α 1 := by
        linarith
      have h10 : α 1 < α 0 := by
        linarith
      have h0lo : (41361 / 100000 : ℝ) ≤ α 0 := by
        by_contra h
        apply hC
        exact ⟨h2, h21, h10, lt_of_not_ge h, h01, h1z, h23⟩
      have h0hi : α 0 ≤ (58639 / 100000 : ℝ) := by
        linarith
      refine ⟨?_, {0}, by simp, by decide, ?_, ?_⟩
      · intro i
        fin_cases i <;> dsimp <;> linarith
      · simpa using h0lo
      · simpa using h0hi
    · simp [hC, hU] at hmask

theorem four_prime_geometric_bin_eq_closed_interval
    (x h : ℝ) (hx : 0 < x) (hh : 0 < h) (k : ℕ) :
    let P : Finset ℕ :=
      (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
        ⌊x ^ ((11 : ℝ) / 25)⌋₊).filter Nat.Prime
    let L : ℝ := max (x ^ ((8639 : ℝ) / 50000)) ((1 + h) ^ k)
    let U : ℝ := min (x ^ ((11 : ℝ) / 25))
      ((⌈(1 + h) ^ (k + 1)⌉₊ - 1 : ℕ) : ℝ)
    P.filter (fun n : ℕ => ⌊Real.logb (1 + h) (n : ℝ)⌋₊ = k) =
      (Finset.Icc ⌈L⌉₊ ⌊U⌋₊).filter Nat.Prime := by
  classical
  intro P L U
  have hpow : 0 ≤ x ^ ((11 : ℝ) / 25) := (Real.rpow_pos_of_pos hx _).le
  have hU : 0 ≤ U := le_min hpow (Nat.cast_nonneg _)
  ext n
  by_cases hp : n.Prime
  · simp only [P, Finset.mem_filter, Finset.mem_Icc, hp, and_true,
      geometric_bin_integer_interval h hh n k hp.one_lt.le,
      Nat.ceil_le, Nat.le_floor_iff hpow, Nat.le_floor_iff hU]
    dsimp [L, U]
    rw [max_le_iff, le_min_iff, Nat.cast_le]
    tauto
  · simp [P, hp]

theorem four_prime_geometric_active_scales
    (x h : ℝ) (hx : 2 ≤ x) (hh : 0 < h) (hh1 : h ≤ 1)
    (b p : Fin 4 → ℕ) :
    let P : Finset ℕ :=
      (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
        ⌊x ^ ((11 : ℝ) / 25)⌋₊).filter Nat.Prime
    let L (i : Fin 4) : ℝ := max (x ^ ((8639 : ℝ) / 50000)) ((1 + h) ^ b i)
    let U (i : Fin 4) : ℝ := min (x ^ ((11 : ℝ) / 25))
      ((⌈(1 + h) ^ (b i + 1)⌉₊ - 1 : ℕ) : ℝ)
    (∀ i, p i ∈ P) →
    (∀ i, ⌊Real.logb (1 + h) (p i : ℝ)⌋₊ = b i) →
    (∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ →
    (∀ i, x ^ ((1 : ℝ) / 10) ≤ L i ∧ L i ≤ U i ∧ U i ≤ 2 * L i) ∧
      x / 32 ≤ ∏ i, L i ∧ (∏ i, L i) ≤ 2 * x := by
  classical
  intro P L U hp hlabel hprod
  have hx1 : 1 ≤ x := (by norm_num : (1 : ℝ) ≤ 2).trans hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hbase : 0 < 1 + h := by linarith
  have hL (i : Fin 4) : 0 ≤ L i :=
    (Real.rpow_pos_of_pos hx0 _).le.trans (le_max_left _ _)
  have hpLU (i : Fin 4) : L i ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ U i := by
    have hm : p i ∈ P.filter (fun n : ℕ => ⌊Real.logb (1 + h) (n : ℝ)⌋₊ = b i) :=
      Finset.mem_filter.mpr ⟨hp i, hlabel i⟩
    rw [four_prime_geometric_bin_eq_closed_interval x h hx0 hh (b i)] at hm
    have hm' := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
    exact ⟨Nat.le_of_ceil_le hm'.1,
      (Nat.cast_le.mpr hm'.2).trans (Nat.floor_le (by positivity))⟩
  have hU (i : Fin 4) : U i ≤ 2 * L i := by
    have hceil : 0 < ⌈(1 + h) ^ (b i + 1)⌉₊ :=
      Nat.ceil_pos.mpr (pow_pos hbase _)
    have htop : ((⌈(1 + h) ^ (b i + 1)⌉₊ - 1 : ℕ) : ℝ) <
        (1 + h) ^ (b i + 1) := Nat.lt_ceil.mp (by omega)
    calc
      U i ≤ ((⌈(1 + h) ^ (b i + 1)⌉₊ - 1 : ℕ) : ℝ) := min_le_right _ _
      _ ≤ (1 + h) ^ (b i + 1) := htop.le
      _ = (1 + h) * (1 + h) ^ b i := by rw [pow_succ]; ring
      _ ≤ 2 * L i := mul_le_mul (by linarith) (le_max_right _ _)
        (pow_nonneg hbase.le _) (by norm_num)
  have hproduct : x ≤ ∏ i, (p i : ℝ) ∧ (∏ i, (p i : ℝ)) ≤ 2 * x := by
    have hmem := Finset.mem_Icc.mp hprod
    constructor
    · exact_mod_cast Nat.le_of_ceil_le hmem.1
    · exact_mod_cast (Nat.cast_le.mpr hmem.2).trans (Nat.floor_le (by positivity))
  have hupper : (∏ i, L i) ≤ 2 * x :=
    (Finset.prod_le_prod (fun i _ => hL i) (fun i _ => (hpLU i).1)).trans hproduct.2
  have hcompare : (∏ i, (p i : ℝ)) ≤ 32 * ∏ i, L i := by
    calc
      _ ≤ ∏ i, 2 * L i := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        (fun i _ => (hpLU i).2.trans (hU i))
      _ = (16 : ℝ) * ∏ i, L i := by rw [Finset.prod_mul_distrib]; norm_num
      _ ≤ 32 * ∏ i, L i := mul_le_mul_of_nonneg_right (by norm_num)
        (Finset.prod_nonneg fun i _ => hL i)
  refine ⟨?_, ?_, hupper⟩
  · intro i
    exact ⟨(Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num :
      (1 : ℝ) / 10 ≤ (8639 : ℝ) / 50000)).trans (le_max_left _ _),
      (hpLU i).1.trans (hpLU i).2, hU i⟩
  · linarith [hproduct.1, hcompare]

theorem four_geometric_label_ceiling_le (x h : ℝ)
    (hx : Real.exp 1 ≤ x) (hh : 0 < h) (hh1 : h ≤ 1) :
    ((⌈Real.logb (1 + h) (2 * x)⌉₊ + 1 : ℕ) : ℝ) ≤ 6 * Real.log x / h :=
  geometric_label_ceiling_le x h hx hh hh1

theorem four_geometric_log_mesh_spec (D x : ℝ) (hD : 0 ≤ D) (hx : Real.exp 1 ≤ x) :
    let h := (Real.log x) ^ (-D)
    0 < h ∧ h ≤ 1 ∧
      (((⌈Real.logb (1 + h) (2 * x)⌉₊ + 1 : ℕ) : ℝ) ^ 4 ≤
        (6 : ℝ) ^ 4 * (Real.log x) ^ (4 * (D + 1))) := by
  intro h
  have hlogx : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hx
  have hlogx0 : 0 < Real.log x := zero_lt_one.trans_le hlogx
  have hh : 0 < h := Real.rpow_pos_of_pos hlogx0 _
  have hh1 : h ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hlogx (neg_nonpos.mpr hD)
  refine ⟨hh, hh1, ?_⟩
  have halgebra : (6 * Real.log x / h) ^ 4 =
      (6 : ℝ) ^ 4 * (Real.log x) ^ (4 * (D + 1)) := by
    have hquot : 6 * Real.log x / h = 6 * (Real.log x) ^ (D + 1) := by
      dsimp [h]
      rw [Real.rpow_neg hlogx0.le, div_inv_eq_mul,
        Real.rpow_add hlogx0, Real.rpow_one]
      ring
    rw [hquot, mul_pow, ← Real.rpow_mul_natCast hlogx0.le (D + 1) 4]
    congr 2
    ring
  exact (pow_le_pow_left₀ (Nat.cast_nonneg _)
    (four_geometric_label_ceiling_le x h hx hh hh1) 4).trans_eq halgebra

/--
A multiplicative inequality on `k` coordinates, recorded as a quotient of coordinate products, a
threshold, and flags for lower versus upper comparison and strictness.
-/
structure MinorantSmallMonomialCut (k : ℕ) where
  /--
  Indices of the `k` coordinates multiplied in the quotient's numerator; the empty product is
  `1`.
  -/
  numerator : Finset (Fin k)
  /--
  Indices of the `k` coordinates multiplied in the quotient's denominator; the empty product is
  `1`.
  -/
  denominator : Finset (Fin k)
  /--
  The real comparison level for the coordinate-product quotient; the structure imposes no
  positivity condition on this field.
  -/
  threshold : ℝ
  /--
  Select a lower bound (`threshold ≤ value`) when `true`, and an upper bound (`value ≤
  threshold`) when `false`; `strict` changes `≤` to `<`.
  -/
  lower : Bool
  /--
  Select `<` when `true` and `≤` when `false`; `lower` determines which side contains the
  threshold.
  -/
  strict : Bool

/--
The real quotient of the numerator and denominator coordinate products of a `k`-coordinate cut,
using totalized real division.
-/
noncomputable def MinorantSmallMonomialCut.value {k : ℕ}
    (d : MinorantSmallMonomialCut k) (p : Fin k → ℕ) : ℝ :=
  (∏ i ∈ d.numerator, (p i : ℝ)) / ∏ i ∈ d.denominator, (p i : ℝ)

open Classical in
theorem prime_tuple_closed_sample_eq_compact
    (k A B : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (w : (Fin k → ℕ) → ℂ)
    (hcompact : ∀ p : Fin k → ℕ, (∀ i, (p i).Prime) →
      (∏ i, p i) ∈ Finset.Icc A B → w p ≠ 0 → ∀ i, p i ∈ P) :
    (∑ n ∈ Finset.Icc A B,
      Finsupp.single n
        (∑ p ∈ Fintype.piFinset (fun _ : Fin k => Nat.primesLE n),
          if (∏ i, p i) = n then w p else 0)) =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin k => P),
        Finsupp.single (∏ i, p i)
          (if (∏ i, p i) ∈ Finset.Icc A B then w p else 0) := by
  let N := Finset.Icc A B
  let T := Fintype.piFinset (fun _ : Fin k => P)
  have hprime (p : Fin k → ℕ) (hp : p ∈ T) (i : Fin k) : (p i).Prime :=
    hP (p i) (Fintype.mem_piFinset.mp hp i)
  ext n
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
  by_cases hn : n ∈ N
  · rw [ite_eq_left hn]
    have heq :
        (∑ p ∈ Fintype.piFinset (fun _ : Fin k => Nat.primesLE n),
          if (∏ i, p i) = n then w p else 0) =
        ∑ p ∈ T, if (∏ i, p i) = n then w p else 0 := by
      apply Finset.sum_congr_of_eq_on_inter
      · intro p hp hpT
        by_cases hpn : (∏ i, p i) = n
        · by_cases hw : w p = 0
          · simp only [ite_eq_left hpn, hw]
          · exfalso
            apply hpT
            apply Fintype.mem_piFinset.mpr
            exact hcompact p
              (fun i => Nat.prime_of_mem_primesLE (Fintype.mem_piFinset.mp hp i))
              (by simpa only [hpn] using hn) hw
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
theorem sourceCentralPair_three_monomial_representation (x : ℝ) (hx : 1 < x) :
    ∃ M : Finset (MinorantSmallMonomialCut 3), M.card ≤ 32 ∧
      (∀ d ∈ M, d.numerator.Nonempty ∧ Disjoint d.numerator d.denominator ∧
        d.numerator.card + d.denominator.card ≤ 3 ∧ 0 < d.threshold) ∧
      let P := (Finset.Icc (Nat.ceil (x ^ ((8639 : ℝ) / 50000)))
        (Nat.floor (x ^ ((9 : ℝ) / 10)))).filter Nat.Prime
      let T := Fintype.piFinset (fun _ : Fin 3 => P)
      let α (p : ℕ) : ℝ := Real.logb x (p : ℝ)
      let C (p : Fin 3 → ℕ) : Prop :=
        x ≤ ((∏ i, p i : ℕ) : ℝ) ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x ∧
        (8639 : ℝ) / 50000 ≤ α (p 1) ∧ α (p 1) < α (p 0) ∧
        α (p 0) < (41361 : ℝ) / 100000 ∧
        (41361 : ℝ) / 100000 ≤ α (p 0) + α (p 1) ∧
        α (p 0) + α (p 1) ≤ (58639 : ℝ) / 100000 ∧ p 1 ≤ p 2
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
  let M : Finset (MinorantSmallMonomialCut 3) :=
    {⟨Finset.univ, ∅, x, true, false⟩,
      ⟨Finset.univ, ∅, 2 * x, false, false⟩,
      ⟨{1}, ∅, x ^ ((8639 : ℝ) / 50000), true, false⟩,
      ⟨{1}, {0}, 1, false, true⟩,
      ⟨{0}, ∅, x ^ ((41361 : ℝ) / 100000), false, true⟩} ∪
    {⟨{0, 1}, ∅, x ^ ((41361 : ℝ) / 100000), true, false⟩,
      ⟨{0, 1}, ∅, x ^ ((58639 : ℝ) / 100000), false, false⟩,
      ⟨{1}, {2}, 1, false, false⟩}
  have hMcard : M.card ≤ 32 := by
    dsimp only [M]
    exact (Finset.card_union_le _ _).trans
      ((Nat.add_le_add Finset.card_le_five Finset.card_le_three).trans (by decide))
  have hMdata (d : MinorantSmallMonomialCut 3) (hd : d ∈ M) :
      d.numerator.Nonempty ∧ Disjoint d.numerator d.denominator ∧
        d.numerator.card + d.denominator.card ≤ 3 ∧ 0 < d.threshold := by
    simp only [M, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl) <;>
      norm_num [Finset.card_fin, Finset.disjoint_left] <;>
        first | positivity | decide
  refine ⟨M, hMcard, hMdata, ?_⟩
  intro P T α C
  have hCeq (p : Fin 3 → ℕ) (hp : p ∈ T) :
      C p ↔ ∀ d ∈ M,
        if d.lower then
          if d.strict then d.threshold < d.value p else d.threshold ≤ d.value p
        else if d.strict then d.value p < d.threshold else d.value p ≤ d.threshold := by
    have hpos (i : Fin 3) : 0 < (p i : ℝ) :=
      Nat.cast_pos.mpr (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)).2.pos
    have hlo : (8639 : ℝ) / 50000 ≤ α (p 1) ↔
        x ^ ((8639 : ℝ) / 50000) ≤ (p 1 : ℝ) :=
      Real.le_logb_iff_rpow_le hx (hpos 1)
    have h10 : α (p 1) < α (p 0) ↔ (p 1 : ℝ) / p 0 < 1 := by
      dsimp only [α]
      rw [Real.logb_lt_logb_iff hx (hpos 1) (hpos 0), div_lt_one (hpos 0)]
    have h0 : α (p 0) < (41361 : ℝ) / 100000 ↔
        (p 0 : ℝ) < x ^ ((41361 : ℝ) / 100000) :=
      Real.logb_lt_iff_lt_rpow hx (hpos 0)
    have hpairlo : (41361 : ℝ) / 100000 ≤ α (p 0) + α (p 1) ↔
        x ^ ((41361 : ℝ) / 100000) ≤ (p 0 : ℝ) * p 1 := by
      dsimp only [α]
      rw [← Real.logb_mul (hpos 0).ne' (hpos 1).ne',
        Real.le_logb_iff_rpow_le hx (mul_pos (hpos 0) (hpos 1))]
    have hpairhi : α (p 0) + α (p 1) ≤ (58639 : ℝ) / 100000 ↔
        (p 0 : ℝ) * p 1 ≤ x ^ ((58639 : ℝ) / 100000) := by
      dsimp only [α]
      rw [← Real.logb_mul (hpos 0).ne' (hpos 1).ne',
        Real.logb_le_iff_le_rpow hx (mul_pos (hpos 0) (hpos 1))]
    have h12 : p 1 ≤ p 2 ↔ (p 1 : ℝ) / p 2 ≤ 1 := by
      rw [div_le_one (hpos 2), Nat.cast_le]
    dsimp only [C]
    rw [hlo, h10, h0, hpairlo, hpairhi, h12]
    suffices h :
        ((x ≤ (∏ i, (p i : ℝ))) ∧
        ((∏ i, (p i : ℝ)) ≤ 2 * x) ∧
        (x ^ ((8639 : ℝ) / 50000) ≤ (p 1 : ℝ)) ∧
        ((p 1 : ℝ) / p 0 < 1) ∧
        ((p 0 : ℝ) < x ^ ((41361 : ℝ) / 100000)) ∧
        (x ^ ((41361 : ℝ) / 100000) ≤ (p 0 : ℝ) * p 1) ∧
        ((p 0 : ℝ) * p 1 ≤ x ^ ((58639 : ℝ) / 100000)) ∧
        ((p 1 : ℝ) / p 2 ≤ 1)) ↔
        ((x ^ ((41361 : ℝ) / 100000) ≤ (p 0 : ℝ) * p 1) ∧
        ((p 0 : ℝ) * p 1 ≤ x ^ ((58639 : ℝ) / 100000)) ∧
        (x ≤ (∏ i, (p i : ℝ))) ∧
        ((∏ i, (p i : ℝ)) ≤ 2 * x) ∧
        (x ^ ((8639 : ℝ) / 50000) ≤ (p 1 : ℝ)) ∧
        ((p 1 : ℝ) / p 0 < 1) ∧
        ((p 0 : ℝ) < x ^ ((41361 : ℝ) / 100000)) ∧
        ((p 1 : ℝ) / p 2 ≤ 1)) by
      simpa [M, MinorantSmallMonomialCut.value, Nat.cast_prod] using h
    constructor
    · rintro ⟨ha, hb, hc, hd, he, hf, hg, hh⟩
      exact ⟨hf, hg, ha, hb, hc, hd, he, hh⟩
    · rintro ⟨hf, hg, ha, hb, hc, hd, he, hh⟩
      exact ⟨ha, hb, hc, hd, he, hf, hg, hh⟩
  clear_value M P T
  intro p hp q hq hbits
  constructor
  · intro h
    apply (hCeq q hq).mpr
    intro d hd
    exact (hbits d hd).mp ((hCeq p hp).mp h d hd)
  · intro h
    apply (hCeq p hp).mpr
    intro d hd
    exact (hbits d hd).mpr ((hCeq q hq).mp h d hd)

open Classical in
theorem sourceCentralPair_four_monomial_representation (x : ℝ) (hx : 1 < x) :
    ∃ M : Finset (MinorantSmallMonomialCut 4), M.card ≤ 32 ∧
      (∀ d ∈ M, d.numerator.Nonempty ∧ Disjoint d.numerator d.denominator ∧
        d.numerator.card + d.denominator.card ≤ 4 ∧ 0 < d.threshold) ∧
      let P := (Finset.Icc (Nat.ceil (x ^ ((8639 : ℝ) / 50000)))
        (Nat.floor (x ^ ((9 : ℝ) / 10)))).filter Nat.Prime
      let T := Fintype.piFinset (fun _ : Fin 4 => P)
      let α (p : ℕ) : ℝ := Real.logb x (p : ℝ)
      let C (p : Fin 4 → ℕ) : Prop :=
        x ≤ ((∏ i, p i : ℕ) : ℝ) ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x ∧
        (8639 : ℝ) / 50000 ≤ α (p 1) ∧ α (p 1) < α (p 0) ∧
        α (p 0) < (41361 : ℝ) / 100000 ∧
        (41361 : ℝ) / 100000 ≤ α (p 0) + α (p 1) ∧
        α (p 0) + α (p 1) ≤ (58639 : ℝ) / 100000 ∧ p 1 ≤ p 2 ∧ p 2 ≤ p 3
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
  let M : Finset (MinorantSmallMonomialCut 4) :=
    {⟨Finset.univ, ∅, x, true, false⟩,
      ⟨Finset.univ, ∅, 2 * x, false, false⟩,
      ⟨{1}, ∅, x ^ ((8639 : ℝ) / 50000), true, false⟩,
      ⟨{1}, {0}, 1, false, true⟩,
      ⟨{0}, ∅, x ^ ((41361 : ℝ) / 100000), false, true⟩} ∪
    {⟨{0, 1}, ∅, x ^ ((41361 : ℝ) / 100000), true, false⟩,
      ⟨{0, 1}, ∅, x ^ ((58639 : ℝ) / 100000), false, false⟩,
      ⟨{1}, {2}, 1, false, false⟩,
      ⟨{2}, {3}, 1, false, false⟩}
  have hMcard : M.card ≤ 32 := by
    dsimp only [M]
    exact (Finset.card_union_le _ _).trans
      ((Nat.add_le_add Finset.card_le_five Finset.card_le_four).trans (by decide))
  have hMdata (d : MinorantSmallMonomialCut 4) (hd : d ∈ M) :
      d.numerator.Nonempty ∧ Disjoint d.numerator d.denominator ∧
        d.numerator.card + d.denominator.card ≤ 4 ∧ 0 < d.threshold := by
    simp only [M, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) <;>
      norm_num [Finset.card_fin, Finset.disjoint_left] <;>
        first | positivity | decide
  refine ⟨M, hMcard, hMdata, ?_⟩
  intro P T α C
  have hCeq (p : Fin 4 → ℕ) (hp : p ∈ T) :
      C p ↔ ∀ d ∈ M,
        if d.lower then
          if d.strict then d.threshold < d.value p else d.threshold ≤ d.value p
        else if d.strict then d.value p < d.threshold else d.value p ≤ d.threshold := by
    have hpos (i : Fin 4) : 0 < (p i : ℝ) :=
      Nat.cast_pos.mpr (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)).2.pos
    have hlo : (8639 : ℝ) / 50000 ≤ α (p 1) ↔
        x ^ ((8639 : ℝ) / 50000) ≤ (p 1 : ℝ) :=
      Real.le_logb_iff_rpow_le hx (hpos 1)
    have h10 : α (p 1) < α (p 0) ↔ (p 1 : ℝ) / p 0 < 1 := by
      dsimp only [α]
      rw [Real.logb_lt_logb_iff hx (hpos 1) (hpos 0), div_lt_one (hpos 0)]
    have h0 : α (p 0) < (41361 : ℝ) / 100000 ↔
        (p 0 : ℝ) < x ^ ((41361 : ℝ) / 100000) :=
      Real.logb_lt_iff_lt_rpow hx (hpos 0)
    have hpairlo : (41361 : ℝ) / 100000 ≤ α (p 0) + α (p 1) ↔
        x ^ ((41361 : ℝ) / 100000) ≤ (p 0 : ℝ) * p 1 := by
      dsimp only [α]
      rw [← Real.logb_mul (hpos 0).ne' (hpos 1).ne',
        Real.le_logb_iff_rpow_le hx (mul_pos (hpos 0) (hpos 1))]
    have hpairhi : α (p 0) + α (p 1) ≤ (58639 : ℝ) / 100000 ↔
        (p 0 : ℝ) * p 1 ≤ x ^ ((58639 : ℝ) / 100000) := by
      dsimp only [α]
      rw [← Real.logb_mul (hpos 0).ne' (hpos 1).ne',
        Real.logb_le_iff_le_rpow hx (mul_pos (hpos 0) (hpos 1))]
    have h12 : p 1 ≤ p 2 ↔ (p 1 : ℝ) / p 2 ≤ 1 := by
      rw [div_le_one (hpos 2), Nat.cast_le]
    have h23 : p 2 ≤ p 3 ↔ (p 2 : ℝ) / p 3 ≤ 1 := by
      rw [div_le_one (hpos 3), Nat.cast_le]
    dsimp only [C]
    rw [hlo, h10, h0, hpairlo, hpairhi, h12, h23]
    suffices h :
        ((x ≤ (∏ i, (p i : ℝ))) ∧
        ((∏ i, (p i : ℝ)) ≤ 2 * x) ∧
        (x ^ ((8639 : ℝ) / 50000) ≤ (p 1 : ℝ)) ∧
        ((p 1 : ℝ) / p 0 < 1) ∧
        ((p 0 : ℝ) < x ^ ((41361 : ℝ) / 100000)) ∧
        (x ^ ((41361 : ℝ) / 100000) ≤ (p 0 : ℝ) * p 1) ∧
        ((p 0 : ℝ) * p 1 ≤ x ^ ((58639 : ℝ) / 100000)) ∧
        ((p 1 : ℝ) / p 2 ≤ 1) ∧
        ((p 2 : ℝ) / p 3 ≤ 1)) ↔
        ((x ^ ((41361 : ℝ) / 100000) ≤ (p 0 : ℝ) * p 1) ∧
        ((p 0 : ℝ) * p 1 ≤ x ^ ((58639 : ℝ) / 100000)) ∧
        ((p 1 : ℝ) / p 2 ≤ 1) ∧
        (x ≤ (∏ i, (p i : ℝ))) ∧
        ((∏ i, (p i : ℝ)) ≤ 2 * x) ∧
        (x ^ ((8639 : ℝ) / 50000) ≤ (p 1 : ℝ)) ∧
        ((p 1 : ℝ) / p 0 < 1) ∧
        ((p 0 : ℝ) < x ^ ((41361 : ℝ) / 100000)) ∧
        ((p 2 : ℝ) / p 3 ≤ 1)) by
      simpa [M, MinorantSmallMonomialCut.value, Nat.cast_prod] using h
    constructor
    · rintro ⟨ha, hb, hc, hd, he, hf, hg, hh, hi⟩
      exact ⟨hf, hg, hh, ha, hb, hc, hd, he, hi⟩
    · rintro ⟨hf, hg, hh, ha, hb, hc, hd, he, hi⟩
      exact ⟨ha, hb, hc, hd, he, hf, hg, hh, hi⟩
  clear_value M P T
  intro p hp q hq hbits
  constructor
  · intro h
    apply (hCeq q hq).mpr
    intro d hd
    exact (hbits d hd).mp ((hCeq p hp).mp h d hd)
  · intro h
    apply (hCeq p hp).mpr
    intro d hd
    exact (hbits d hd).mpr ((hCeq q hq).mp h d hd)

open Classical in
theorem sourceCentralPair_five_monomial_representation (x : ℝ) (hx : 1 < x) :
    ∃ M : Finset MinorantMonomialCut, M.card ≤ 32 ∧
      (∀ d ∈ M, d.numerator.Nonempty ∧ Disjoint d.numerator d.denominator ∧
        d.numerator.card + d.denominator.card ≤ 5 ∧ 0 < d.threshold) ∧
      let P := (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
        ⌊x ^ ((6 : ℝ) / 25)⌋₊).filter Nat.Prime
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
/--
The multiplicative cuts for the three-factor `T3` region, including its prime ordering, exponent
thresholds, and the closed total-product window `[x, 2 * x]`.
-/
noncomputable def sourceT3MonomialCuts (x : ℝ) : Finset (MinorantSmallMonomialCut 3) :=
  {⟨Finset.univ, ∅, x, true, false⟩,
    ⟨Finset.univ, ∅, 2 * x, false, false⟩,
    ⟨{1}, ∅, x ^ ((8639 : ℝ) / 50000), true, false⟩,
    ⟨{1}, {0}, 1, false, true⟩} ∪
  {⟨{0}, ∅, x ^ ((41361 : ℝ) / 100000), false, true⟩,
    ⟨{0, 1}, ∅, x ^ ((58639 : ℝ) / 100000), true, true⟩,
    ⟨{1}, ∅, x ^ (1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000), true, false⟩,
    ⟨{1}, {2}, 1, false, false⟩}

theorem sourceT3MonomialCuts_card_le (x : ℝ) : (sourceT3MonomialCuts x).card ≤ 32 := by
  classical
  unfold sourceT3MonomialCuts
  exact (Finset.card_union_le _ _).trans
    ((Nat.add_le_add Finset.card_le_four Finset.card_le_four).trans (by decide))

theorem sourceT3MonomialCuts_data (x : ℝ) (hx : 0 < x)
    (d : MinorantSmallMonomialCut 3) (hd : d ∈ sourceT3MonomialCuts x) :
    d.numerator.Nonempty ∧ Disjoint d.numerator d.denominator ∧
      d.numerator.card + d.denominator.card ≤ 3 ∧ 0 < d.threshold := by
  classical
  simp only [sourceT3MonomialCuts, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) <;>
    norm_num [Finset.card_fin, Finset.disjoint_left] <;>
      first | positivity | decide

open Classical in
theorem sourceT3MonomialCuts_boolean (x : ℝ) (hx : 1 < x)
    (p q : Fin 3 → ℕ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (htests : ∀ d ∈ sourceT3MonomialCuts x,
      (if d.lower then
        if d.strict then d.threshold < d.value p else d.threshold ≤ d.value p
      else if d.strict then d.value p < d.threshold else d.value p ≤ d.threshold) ↔
      (if d.lower then
        if d.strict then d.threshold < d.value q else d.threshold ≤ d.value q
      else if d.strict then d.value q < d.threshold else d.value q ≤ d.threshold)) :
    ((∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧
      sourceT3ExponentMask (fun i => Real.logb x (p i : ℝ)) = true) ↔
    ((∏ i, q i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧
      sourceT3ExponentMask (fun i => Real.logb x (q i : ℝ)) = true) := by
  have hmask (r : Fin 3 → ℕ) (hr : ∀ i, 0 < r i) :
      sourceT3ExponentMask (fun i => Real.logb x (r i : ℝ)) = true ↔
        x ^ ((8639 : ℝ) / 50000) ≤ (r 1 : ℝ) ∧ (r 1 : ℝ) / r 0 < 1 ∧
        (r 0 : ℝ) < x ^ ((41361 : ℝ) / 100000) ∧
        x ^ ((58639 : ℝ) / 100000) < (r 0 : ℝ) * r 1 ∧
        x ^ (1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000) ≤ (r 1 : ℝ) ∧
        (r 1 : ℝ) / r 2 ≤ 1 := by
    have hpos (i : Fin 3) : (0 : ℝ) < r i := by exact_mod_cast hr i
    have horder : Real.logb x (r 1 : ℝ) < Real.logb x (r 0 : ℝ) ↔
        (r 1 : ℝ) / r 0 < 1 := by
      rw [Real.logb_lt_logb_iff hx (hpos 1) (hpos 0), div_lt_one (hpos 0)]
    have hlast : Real.logb x (r 1 : ℝ) ≤ Real.logb x (r 2 : ℝ) ↔
        (r 1 : ℝ) / r 2 ≤ 1 := by
      rw [Real.logb_le_logb hx (hpos 1) (hpos 2), div_le_one (hpos 2)]
    have hpair : (58639 : ℝ) / 100000 <
        Real.logb x (r 0 : ℝ) + Real.logb x (r 1 : ℝ) ↔
        x ^ ((58639 : ℝ) / 100000) < (r 0 : ℝ) * r 1 := by
      rw [← Real.logb_mul (hpos 0).ne' (hpos 1).ne',
        Real.lt_logb_iff_rpow_lt hx (mul_pos (hpos 0) (hpos 1))]
    simp only [sourceT3ExponentMask, decide_eq_true_eq]
    rw [Real.le_logb_iff_rpow_le hx (hpos 1), horder,
      Real.logb_lt_iff_lt_rpow hx (hpos 0), hpair,
      Real.le_logb_iff_rpow_le hx (hpos 1), hlast]
  have hcarrier (r : Fin 3 → ℕ) :
      (∏ i, r i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ↔
        x ≤ ∏ i, (r i : ℝ) ∧ (∏ i, (r i : ℝ)) ≤ 2 * x := by
    rw [Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff (by positivity)]
    push_cast
    rfl
  simp only [sourceT3MonomialCuts, Finset.forall_mem_union,
    Finset.forall_mem_insert, Finset.mem_singleton, forall_eq] at htests
  obtain ⟨⟨hlo, hhi, hxi, h10⟩, h0a, h01, h1z, h12⟩ := htests
  simp only [MinorantSmallMonomialCut.value, Bool.false_eq_true, ite_true, ite_false,
    Finset.prod_empty, Finset.prod_singleton, div_one,
    Finset.prod_pair (by decide : (0 : Fin 3) ≠ 1)] at hlo hhi hxi h10 h0a h01 h1z h12
  rw [hcarrier p, hcarrier q, hmask p hp, hmask q hq]
  exact and_congr (and_congr hlo hhi)
    (and_congr hxi (and_congr h10 (and_congr h0a (and_congr h01 (and_congr h1z h12)))))

theorem sourceT3_nearby_original_box_bounds (τ : ℝ) (hτ : 0 < τ)
    (hτsmall : τ ≤ 1 / 10 ^ 10) :
    let a : ℝ := 41361 / 100000
    let ζ : ℝ := 1 - 34941 / 100000 - a
    ∃ X : ℝ, 3 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      ∀ p : Fin 3 → ℕ, (∀ i, (p i).Prime) →
      ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x →
      sourceT3ExponentMask (fun i => Real.logb x (p i : ℝ)) = true →
      ∀ L U : Fin 3 → ℝ,
        (∀ i, L i ≤ (p i : ℝ) ∧ (p i : ℝ) ≤ U i ∧ U i ≤ 2 * L i) →
        ∀ i, x ^ (ζ - τ / 10) ≤ L i ∧ U i ≤ x ^ (a + τ / 10) ∧
          x ^ ((23 : ℝ) / 100) ≤ L i ∧ U i ≤ x ^ ((42 : ℝ) / 100) := by
  intro a ζ
  have hε : 0 < τ / 10 := div_pos hτ (by norm_num)
  obtain ⟨X, hX⟩ := ((tendsto_rpow_atTop hε).eventually_ge_atTop (4 : ℝ)).exists_forall_of_atTop
  refine ⟨max 3 X, le_max_left _ _, ?_⟩
  intro x hx p hp hprod hcut L U hLU i
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hx1 : 1 < x := (by norm_num : (1 : ℝ) < 3).trans_le hx3
  have hxpos : 0 < x := zero_lt_one.trans hx1
  have hεlarge : 4 ≤ x ^ (τ / 10) := hX x ((le_max_right _ _).trans hx)
  have hscale := sourceT3_prime_tuple_exponent_bounds x hx1 p hp hprod hcut i
  have hpPos : (0 : ℝ) < p i := Nat.cast_pos.mpr (hp i).pos
  have hpLo : x ^ ζ ≤ (p i : ℝ) :=
    (Real.le_logb_iff_rpow_le hx1 hpPos).mp hscale.1
  have hpHi : (p i : ℝ) ≤ 2 * x ^ a := by
    have h := (Real.logb_le_iff_le_rpow hx1 hpPos).mp hscale.2
    have htwo : x ^ Real.logb x 2 = 2 := Real.rpow_logb hxpos hx1.ne' (by norm_num)
    rw [Real.rpow_add hxpos, htwo] at h
    simpa only [a, mul_comm] using h
  have hL : x ^ (ζ - τ / 10) ≤ L i := by
    rw [Real.rpow_sub hxpos]
    calc
      _ ≤ x ^ ζ / 2 := div_le_div_of_nonneg_left (Real.rpow_nonneg hxpos.le _) (by norm_num)
        (by linarith : 2 ≤ x ^ (τ / 10))
      _ ≤ L i := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
        (by nlinarith only [hpLo, (hLU i).2.1, (hLU i).2.2])
  have hU : U i ≤ x ^ (a + τ / 10) := by
    rw [Real.rpow_add hxpos]
    calc
      _ ≤ 2 * (p i : ℝ) := (hLU i).2.2.trans
        (mul_le_mul_of_nonneg_left (hLU i).1 (by norm_num))
      _ ≤ 4 * x ^ a := by linarith only [hpHi]
      _ ≤ _ := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hεlarge
          (Real.rpow_nonneg hxpos.le a)
  refine ⟨hL, hU, ?_, ?_⟩
  · exact (Real.rpow_le_rpow_of_exponent_le hx1.le (by
      dsimp only [ζ, a]
      linarith only [hτsmall])).trans hL
  · exact hU.trans (Real.rpow_le_rpow_of_exponent_le hx1.le (by
      dsimp only [a]
      linarith only [hτsmall]))

open Classical in
theorem sourceT3_eventually_compact_prime_finsupp :
    ∃ X : ℝ, 3 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      let P := (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
        ⌊x ^ ((9 : ℝ) / 10)⌋₊).filter Nat.Prime
      let T := Fintype.piFinset (fun _ : Fin 3 => P)
      (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
        Finsupp.single n ((sourceT3 x n : ℝ) : ℂ)) =
        ∑ p ∈ T, Finsupp.single (∏ i, p i)
          (if (∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧
            sourceT3ExponentMask (fun i => Real.logb x (p i : ℝ)) = true
          then (1 : ℂ) else 0) := by
  obtain ⟨X₁, hX₁, hsource⟩ := sourceT3_eventually_eq_three_prime_tuple_sum
  obtain ⟨X₂, _hX₂, hnearby⟩ :=
    sourceT3_nearby_original_box_bounds (1 / 10 ^ 10) (by norm_num) le_rfl
  refine ⟨max X₁ X₂, hX₁.trans (le_max_left _ _), ?_⟩
  intro x hx P T
  have hx₁ : X₁ ≤ x := (le_max_left _ _).trans hx
  have hx₂ : X₂ ≤ x := (le_max_right _ _).trans hx
  have hx1 : 1 < x := (by norm_num : (1 : ℝ) < 3).trans_le (hX₁.trans hx₁)
  have hx0 : 0 < x := zero_lt_one.trans hx1
  let N := Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊
  let w : (Fin 3 → ℕ) → ℝ := fun p =>
    if sourceT3ExponentMask (fun i => Real.logb x (p i : ℝ)) then 1 else 0
  have hcompact (p : Fin 3 → ℕ) (hp : ∀ i, (p i).Prime)
      (hpn : (∏ i, p i) ∈ N)
      (hm : sourceT3ExponentMask (fun i => Real.logb x (p i : ℝ)) = true) : p ∈ T := by
    have hnhi : ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hpn).2).trans (Nat.floor_le (by positivity))
    have hbounds := hnearby x hx₂ p hp hnhi hm (fun i => (p i : ℝ))
      (fun i => (p i : ℝ)) (fun i => ⟨le_rfl, le_rfl, by
        nlinarith only [Nat.cast_nonneg (α := ℝ) (p i)]⟩)
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hp i⟩
    · apply Nat.ceil_le.mpr
      exact (Real.rpow_le_rpow_of_exponent_le hx1.le
        (by norm_num : (8639 : ℝ) / 50000 ≤ 23 / 100)).trans (hbounds i).2.2.1
    · apply Nat.le_floor
      exact (hbounds i).2.2.2.trans (Real.rpow_le_rpow_of_exponent_le hx1.le
        (by norm_num : (42 : ℝ) / 100 ≤ 9 / 10))
  have hprime (p : Fin 3 → ℕ) (hp : p ∈ T) (i : Fin 3) : (p i).Prime :=
    (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)).2
  ext n
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
  by_cases hn : n ∈ N
  · have hnlo : x ≤ (n : ℝ) := Nat.le_of_ceil_le (Finset.mem_Icc.mp hn).1
    have hnhi : (n : ℝ) ≤ 2 * x :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le (by positivity))
    have hcast : ((sourceT3 x n : ℝ) : ℂ) =
        ∑ p ∈ Fintype.piFinset (fun _ : Fin 3 => Nat.primesLE n),
          if (∏ i, p i) = n then (w p : ℂ) else 0 := by
      rw [hsource x hx₁ n hnlo hnhi, Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hpn : (∏ i, p i) = n
      · simp only [ite_eq_left hpn]
        rfl
      · simp only [ite_eq_right hpn, Complex.ofReal_zero]
    rw [ite_eq_left hn, hcast]
    have heq :
        (∑ p ∈ Fintype.piFinset (fun _ : Fin 3 => Nat.primesLE n),
          if (∏ i, p i) = n then (w p : ℂ) else 0) =
        ∑ p ∈ T, if (∏ i, p i) = n then (w p : ℂ) else 0 := by
      apply Finset.sum_congr_of_eq_on_inter
      · intro p hp hpT
        by_cases hpn : (∏ i, p i) = n
        · by_cases hm : sourceT3ExponentMask (fun i => Real.logb x (p i : ℝ)) = true
          · exact False.elim (hpT (hcompact p
              (fun i => Nat.prime_of_mem_primesLE (Fintype.mem_piFinset.mp hp i))
              (by simpa only [hpn] using hn) hm))
          · simp only [ite_eq_left hpn, w, ite_eq_right hm, Complex.ofReal_zero]
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
      simp only [ite_eq_left hpn, hm, true_and, w]
      split_ifs <;> rfl
    · simp only [ite_eq_right hpn]
  · rw [ite_eq_right hn]
    symm
    apply Finset.sum_eq_zero
    intro p _hp
    by_cases hpn : (∏ i, p i) = n
    · have hm : ¬(∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ := by
        simpa only [hpn] using hn
      simp only [ite_eq_left hpn, hm, false_and, ite_false]
    · exact ite_eq_right hpn

#print axioms sourceT3_eventually_residual_prime
#print axioms sourceT4_eventually_residual_prime
#print axioms sourceT3_eventually_eq_three_prime_tuple_sum
#print axioms sourceT3_prime_tuple_exponent_bounds
#print axioms sourceT3MonomialCuts_boolean
#print axioms sourceT3_nearby_original_box_bounds
#print axioms sourceT3_eventually_compact_prime_finsupp

end PrimeGap182Analytic.Harman
