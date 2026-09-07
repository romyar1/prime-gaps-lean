import HarmanData182

/-! Exact prime-indicator Buchstab identities with the actual 182 cutoffs.
Adapted from Apache-2.0 PrimeGaps186 at the source hash checked by
scripts/build_harman_buchstab.py. These are identities of actual integer
factorization sums. Every new cutoff inequality is checked in Lean.
No distribution theorem is used. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

theorem theta2_prime_tuples_eq (x : ℝ) (hx : 1 < x) :
    siftedPrimeTuples x (1 : Fin 6) =
      ((Nat.primesBelow (Nat.ceil (x ^ ((41361 : ℝ) / 100000)))).filter
        (fun p : ℕ => x ^ ((8639 : ℝ) / 50000) ≤ (p : ℝ))).image
        (fun p => [p]) := by
  classical
  ext ps
  have hm := mem_siftedPrimeTuples_iff x hx (1 : Fin 6) ps
  dsimp only at hm
  rw [hm]
  rcases ps with _ | ⟨p, _ | ⟨q, qs⟩⟩
  · simp
  · simp only [Finset.mem_image, List.cons.injEq, and_true,
      exists_eq_right, Finset.mem_filter, Nat.mem_primesBelow, Nat.lt_ceil]
    constructor
    · rintro ⟨hp, hlo, hhi⟩
      exact ⟨⟨(Real.logb_lt_iff_lt_rpow hx (Nat.cast_pos.mpr hp.pos)).1 hhi, hp⟩,
        (Real.le_logb_iff_rpow_le hx (Nat.cast_pos.mpr hp.pos)).1 hlo⟩
    · rintro ⟨⟨hhi, hp⟩, hlo⟩
      exact ⟨hp, (Real.le_logb_iff_rpow_le hx (Nat.cast_pos.mpr hp.pos)).2 hlo,
        (Real.logb_lt_iff_lt_rpow hx (Nat.cast_pos.mpr hp.pos)).2 hhi⟩
  · simp

theorem siftedTheta_one_eq_prime_sum (x : ℝ) (hx : 1 < x) (n : ℕ) :
    siftedTheta x (1 : Fin 6) (fun _ => 1) n =
      ∑ p ∈ (Nat.primesBelow (Nat.ceil (x ^ ((41361 : ℝ) / 100000)))).filter
          (fun p : ℕ => x ^ ((8639 : ℝ) / 50000) ≤ (p : ℝ)),
        ∑ d ∈ n.divisorsAntidiagonal,
          if d.1 = p then roughWeight (x ^ ((8639 : ℝ) / 50000)) d.2 else 0 := by
  classical
  change (∑ ps ∈ siftedPrimeTuples x (1 : Fin 6),
    ∑ d ∈ n.divisorsAntidiagonal,
      if d.1 = ps.prod then 1 * roughWeight (x ^ ((8639 : ℝ) / 50000)) d.2
      else 0) = _
  rw [theta2_prime_tuples_eq x hx, Finset.sum_image List.singleton_injective.injOn]
  simp

theorem siftedTheta_eq_weighted_divisor_sum (x : ℝ) (j : Fin 6)
    (w : List ℕ → ℝ) (n : ℕ) :
    siftedTheta x j w n =
      ∑ p ∈ siftedPrimeTuples x j,
        if p.prod ∣ n then
          w p * roughWeight (x ^ ((8639 : ℝ) / 50000)) (n / p.prod)
        else 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [siftedTheta]
  change (∑ p ∈ siftedPrimeTuples x j, ∑ d ∈ n.divisorsAntidiagonal,
    if d.1 = p.prod then
      w p * roughWeight (x ^ ((8639 : ℝ) / 50000)) d.2 else 0) = _
  apply Finset.sum_congr rfl
  intro p _
  rw [Nat.sum_divisorsAntidiagonal (fun d e =>
    if d = p.prod then w p * roughWeight (x ^ ((8639 : ℝ) / 50000)) e else 0),
    Finset.sum_ite_eq']
  simp [Nat.mem_divisors, hn]

theorem siftedTheta_zero_eq_roughWeight (x : ℝ) (n : ℕ) :
    siftedTheta x (0 : Fin 6) (fun _ => 1) n =
      roughWeight (x ^ ((8639 : ℝ) / 50000)) n := by
  classical
  rw [siftedTheta_eq_weighted_divisor_sum]
  simp [siftedPrimeTuples]

theorem siftedTheta_one_eq_buchstab_prime_sum (x : ℝ) (hx : 1 < x) (n : ℕ) :
    siftedTheta x (1 : Fin 6) (fun _ => 1) n =
      ∑ p ∈ (Nat.primesLE n).filter (fun p : ℕ =>
        x ^ ((8639 : ℝ) / 50000) ≤ (p : ℝ) ∧
        (p : ℝ) < x ^ ((41361 : ℝ) / 100000) ∧ p ∣ n),
        roughWeight (x ^ ((8639 : ℝ) / 50000)) (n / p) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  have hcarrier :
      (((Nat.primesBelow (Nat.ceil (x ^ ((41361 : ℝ) / 100000)))).filter
        (fun p : ℕ => x ^ ((8639 : ℝ) / 50000) ≤ (p : ℝ))).filter
          (fun p : ℕ => p ∣ n)) =
      (Nat.primesLE n).filter (fun p : ℕ =>
        x ^ ((8639 : ℝ) / 50000) ≤ (p : ℝ) ∧
        (p : ℝ) < x ^ ((41361 : ℝ) / 100000) ∧ p ∣ n) := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesBelow, Nat.lt_ceil,
      Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨⟨hhi, hp⟩, hlo⟩, hpn⟩
      exact ⟨⟨Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn, hp⟩, hlo, hhi, hpn⟩
    · rintro ⟨⟨_, hp⟩, hlo, hhi, hpn⟩
      exact ⟨⟨⟨hhi, hp⟩, hlo⟩, hpn⟩
  rw [siftedTheta_eq_weighted_divisor_sum,
    theta2_prime_tuples_eq x hx,
    Finset.sum_image List.singleton_injective.injOn]
  simp only [List.prod_cons, List.prod_nil, mul_one, one_mul]
  rw [← Finset.sum_filter, hcarrier]

theorem primeIndicator_eq_siftedTheta_zero_sub_one {x : ℝ} (hx : 3 ≤ x)
    {n : ℕ} (hlo : x ≤ (n : ℝ)) (hhi : (n : ℝ) ≤ 2 * x) :
    (if n.Prime then (1 : ℝ) else 0) =
      siftedTheta x (0 : Fin 6) (fun _ => 1) n -
      siftedTheta x (1 : Fin 6) (fun _ => 1) n -
      (∑ p ∈ (Nat.primesLE n).filter (fun p : ℕ =>
        x ^ ((41361 : ℝ) / 100000) ≤ (p : ℝ) ∧
        (p : ℝ) < Real.sqrt (3 * x) ∧ p ∣ n),
        roughWeight (p : ℝ) (n / p)) +
      ∑ p ∈ (Nat.primesLE n).filter (fun p : ℕ =>
        x ^ ((8639 : ℝ) / 50000) ≤ (p : ℝ) ∧
        (p : ℝ) < x ^ ((41361 : ℝ) / 100000) ∧ p ∣ n),
        ∑ q ∈ (Nat.primesLE (n / p)).filter (fun q : ℕ =>
          x ^ ((8639 : ℝ) / 50000) ≤ (q : ℝ) ∧
          (q : ℝ) < (p : ℝ) ∧ q ∣ n / p),
          roughWeight (q : ℝ) ((n / p) / q) := by
  classical
  have hx1 : 1 < x := by linarith
  have hzH : x ^ ((8639 : ℝ) / 50000) ≤ x ^ ((41361 : ℝ) / 100000) :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
  have hHT : x ^ ((41361 : ℝ) / 100000) ≤ Real.sqrt (3 * x) := by
    calc
      x ^ ((41361 : ℝ) / 100000) ≤ x ^ (1 / (2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
      _ = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
      _ ≤ Real.sqrt (3 * x) := Real.sqrt_le_sqrt (by linarith)
  rw [siftedTheta_zero_eq_roughWeight, siftedTheta_one_eq_buchstab_prime_sum x hx1]
  exact primeIndicator_buchstab_first_split hx hzH hHT hlo hhi

theorem eventually_exceptional_large :
    ∀ᶠ x : ℝ in Filter.atTop,
      1 < x ∧ 2 * x < x ^ (6 * ((8639 : ℝ) / 50000)) := by
  have h := tendsto_rpow_atTop
    (by norm_num : (0 : ℝ) < 6 * ((8639 : ℝ) / 50000) - 1)
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), h.eventually_gt_atTop 2] with x hx hh
  have hx0 : 0 < x := by linarith
  have heq : x ^ (6 * ((8639 : ℝ) / 50000)) =
      x * x ^ (6 * ((8639 : ℝ) / 50000) - 1) := by
    conv_lhs => rw [show (6 * ((8639 : ℝ) / 50000)) = 1 + (6 * ((8639 : ℝ) / 50000) - 1) by ring]
    rw [Real.rpow_add hx0, Real.rpow_one]
  exact ⟨hx, by rw [heq]; nlinarith⟩

noncomputable def sourceLargeFirst (x : ℝ) : ArithmeticFunction ℝ := by
  classical
  exact ⟨fun n => ∑ d ∈ n.divisorsAntidiagonal,
    if d.1.Prime ∧ x ^ ((41361 : ℝ) / 100000) ≤ (d.1 : ℝ) ∧
        (d.1 : ℝ) < Real.sqrt (3 * x)
    then roughWeight (d.1 : ℝ) d.2 else 0, by simp⟩

/--
The contribution of two prime factors with ordered exponents between `8639 / 50000` and `41361 /
100000`, whose exponent sum lies in the closed central interval `[41361 / 100000, 58639 /
100000]`. The remaining cofactor is weighted by roughness at the smaller prime.
-/
noncomputable def sourceCentralPair (x : ℝ) : ArithmeticFunction ℝ := by
  classical
  let α (p : ℕ) : ℝ := Real.logb x (p : ℝ)
  exact ⟨fun n => ∑ d ∈ n.divisorsAntidiagonal, ∑ e ∈ d.2.divisorsAntidiagonal,
    if d.1.Prime ∧ e.1.Prime ∧ (8639 : ℝ) / 50000 ≤ α e.1 ∧
        α e.1 < α d.1 ∧ α d.1 < (41361 : ℝ) / 100000 ∧
        (41361 : ℝ) / 100000 ≤ α d.1 + α e.1 ∧
        α d.1 + α e.1 ≤ (58639 : ℝ) / 100000
    then roughWeight (e.1 : ℝ) e.2 else 0, by simp⟩

/--
The two-prime Buchstab contribution above the central exponent-sum interval, with the smaller
prime exponent at least `1 - 34941 / 100000 - 41361 / 100000`. The cofactor is weighted by
roughness at that smaller prime.
-/
noncomputable def sourceT3 (x : ℝ) : ArithmeticFunction ℝ := by
  classical
  let α (p : ℕ) : ℝ := Real.logb x (p : ℝ)
  exact ⟨fun n => ∑ d ∈ n.divisorsAntidiagonal, ∑ e ∈ d.2.divisorsAntidiagonal,
    if d.1.Prime ∧ e.1.Prime ∧ (8639 : ℝ) / 50000 ≤ α e.1 ∧
        α e.1 < α d.1 ∧ α d.1 < (41361 : ℝ) / 100000 ∧
        (58639 : ℝ) / 100000 < α d.1 + α e.1 ∧
        1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000 ≤ α e.1
    then roughWeight (e.1 : ℝ) e.2 else 0, by simp⟩

/--
The three-prime Buchstab contribution with strictly decreasing prime exponents, first-two
exponent sum greater than `58639 / 100000`, and second exponent below `1 - 34941 / 100000 - 41361 /
100000`. The cofactor is weighted by roughness at the third prime.
-/
noncomputable def sourceT4 (x : ℝ) : ArithmeticFunction ℝ := by
  classical
  let α (p : ℕ) : ℝ := Real.logb x (p : ℝ)
  exact ⟨fun n => ∑ d ∈ n.divisorsAntidiagonal, ∑ e ∈ d.2.divisorsAntidiagonal,
    ∑ f ∈ e.2.divisorsAntidiagonal,
      if d.1.Prime ∧ e.1.Prime ∧ f.1.Prime ∧
          (8639 : ℝ) / 50000 ≤ α f.1 ∧ α f.1 < α e.1 ∧ α e.1 < α d.1 ∧
          α d.1 < (41361 : ℝ) / 100000 ∧
          (58639 : ℝ) / 100000 < α d.1 + α e.1 ∧
          α e.1 < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000
      then roughWeight (f.1 : ℝ) f.2 else 0, by simp⟩

/--
The four-prime Buchstab contribution with strictly decreasing prime exponents at least `8639 /
50000` and first-two exponent sum below `41361 / 100000`. The cofactor is weighted by roughness
at the fourth prime.
-/
noncomputable def sourceT5 (x : ℝ) : ArithmeticFunction ℝ := by
  classical
  let α (p : ℕ) : ℝ := Real.logb x (p : ℝ)
  exact ⟨fun n => ∑ d ∈ n.divisorsAntidiagonal, ∑ e ∈ d.2.divisorsAntidiagonal,
    ∑ f ∈ e.2.divisorsAntidiagonal, ∑ g ∈ f.2.divisorsAntidiagonal,
      if d.1.Prime ∧ e.1.Prime ∧ f.1.Prime ∧ g.1.Prime ∧
          (8639 : ℝ) / 50000 ≤ α g.1 ∧ α g.1 < α f.1 ∧ α f.1 < α e.1 ∧
          α e.1 < α d.1 ∧ α d.1 < (41361 : ℝ) / 100000 ∧
          α d.1 + α e.1 < (41361 : ℝ) / 100000
      then roughWeight (g.1 : ℝ) g.2 else 0, by simp⟩

/--
The contribution of two prime factors with strictly ordered exponents in the interval from `8639
/ 50000` to `41361 / 100000`, with a cofactor rough at the smaller prime. No restriction on the
sum of the two exponents is imposed.
-/
noncomputable def sourceOrderedPair (x : ℝ) : ArithmeticFunction ℝ := by
  classical
  let α (p : ℕ) : ℝ := Real.logb x (p : ℝ)
  exact ⟨fun n => ∑ d ∈ n.divisorsAntidiagonal, ∑ e ∈ d.2.divisorsAntidiagonal,
    if d.1.Prime ∧ e.1.Prime ∧ (8639 : ℝ) / 50000 ≤ α e.1 ∧
        α e.1 < α d.1 ∧ α d.1 < (41361 : ℝ) / 100000
    then roughWeight (e.1 : ℝ) e.2 else 0, by simp⟩

/--
The contribution from sifted two-prime region `2` when `e = 0`, and region `3` otherwise, with
the remaining cofactor weighted by roughness at the second prime.
-/
noncomputable def sourceRoughPair (x : ℝ) (e : Fin 2) : ArithmeticFunction ℝ := by
  classical
  let j : Fin 6 := if e = 0 then 2 else 3
  exact ⟨fun n => ∑ d ∈ n.divisorsAntidiagonal, ∑ f ∈ d.2.divisorsAntidiagonal,
    if [d.1, f.1] ∈ siftedPrimeTuples x j
    then roughWeight (f.1 : ℝ) f.2 else 0, by simp⟩

/--
The contribution from sifted three-prime region `4`, with the remaining cofactor weighted by
roughness at the third prime.
-/
noncomputable def sourceRoughTriple (x : ℝ) : ArithmeticFunction ℝ := by
  classical
  exact ⟨fun n => ∑ d ∈ n.divisorsAntidiagonal, ∑ e ∈ d.2.divisorsAntidiagonal,
    ∑ f ∈ e.2.divisorsAntidiagonal,
      if [d.1, e.1, f.1] ∈ siftedPrimeTuples x (4 : Fin 6)
      then roughWeight (f.1 : ℝ) f.2 else 0, by simp⟩

theorem sum_prime_divisorsAntidiagonal
    {A : Type*} [AddCommMonoid A] (n : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (w : ℕ → ℕ → A) :
    (∑ d ∈ n.divisorsAntidiagonal, if d.1.Prime ∧ P d.1 then w d.1 d.2 else 0) =
      ∑ p ∈ (Nat.primesLE n).filter (fun p => P p ∧ p ∣ n), w p (n / p) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  rw [Nat.sum_divisorsAntidiagonal (fun p r => if p.Prime ∧ P p then w p r else 0)]
  have hcarrier : n.divisors.filter (fun p => p.Prime ∧ P p) =
      (Nat.primesLE n).filter (fun p => P p ∧ p ∣ n) := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hpn, _⟩, hp, hP⟩
      exact ⟨⟨Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn, hp⟩, hP, hpn⟩
    · rintro ⟨⟨_, hp⟩, hP, hpn⟩
      exact ⟨⟨hpn, hn⟩, hp, hP⟩
  rw [← Finset.sum_filter, hcarrier]

theorem roughWeight_buchstab_antidiagonal {z Z : ℝ} (hzZ : z ≤ Z) (n : ℕ) :
    roughWeight Z n = roughWeight z n -
      ∑ d ∈ n.divisorsAntidiagonal,
        if d.1.Prime ∧ z ≤ (d.1 : ℝ) ∧ (d.1 : ℝ) < Z
        then roughWeight (d.1 : ℝ) d.2 else 0 := by
  rw [sum_prime_divisorsAntidiagonal n (fun p => z ≤ (p : ℝ) ∧ (p : ℝ) < Z)
    (fun p r => roughWeight (p : ℝ) r)]
  simpa only [and_assoc] using roughWeight_buchstab hzZ n

theorem siftedTheta_pair_antidiagonal (x : ℝ) (hx : 1 < x) (e : Fin 2) (n : ℕ) :
    let j : Fin 6 := if e = 0 then 2 else 3
    siftedTheta x j (fun _ => 1) n =
      ∑ d ∈ n.divisorsAntidiagonal, ∑ f ∈ d.2.divisorsAntidiagonal,
        if [d.1, f.1] ∈ siftedPrimeTuples x j
        then roughWeight (x ^ ((8639 : ℝ) / 50000)) f.2 else 0 := by
  classical
  intro j
  have hshape (ps : List ℕ) (hps : ps ∈ siftedPrimeTuples x j) :
      ∃ p q : ℕ, ps = [p, q] := by
    have hmem := (mem_siftedPrimeTuples_iff x hx j ps).mp hps
    by_cases he : e = 0 <;>
      rcases ps with _ | ⟨p, _ | ⟨q, _ | ⟨r, rs⟩⟩⟩ <;>
      simp [j, he] at hmem ⊢
  simpa only [siftedTheta, ArithmeticFunction.coe_mk, one_mul] using
    sum_pair_list_divisorsAntidiagonal (siftedPrimeTuples x j) hshape
      (fun _ r => roughWeight (x ^ ((8639 : ℝ) / 50000)) r) n

theorem siftedTheta_triple_antidiagonal (x : ℝ) (hx : 1 < x) (e : Fin 2) (n : ℕ) :
    let j : Fin 6 := if e = 0 then 4 else 5
    siftedTheta x j (fun _ => 1) n =
      ∑ d ∈ n.divisorsAntidiagonal, ∑ f ∈ d.2.divisorsAntidiagonal,
        ∑ g ∈ f.2.divisorsAntidiagonal,
          if [d.1, f.1, g.1] ∈ siftedPrimeTuples x j
          then roughWeight (x ^ ((8639 : ℝ) / 50000)) g.2 else 0 := by
  classical
  intro j
  have hshape (ps : List ℕ) (hps : ps ∈ siftedPrimeTuples x j) :
      ∃ p q r : ℕ, ps = [p, q, r] := by
    have hmem := (mem_siftedPrimeTuples_iff x hx j ps).mp hps
    by_cases he : e = 0 <;>
      rcases ps with _ | ⟨p, _ | ⟨q, _ | ⟨r, _ | ⟨s, ss⟩⟩⟩⟩ <;>
      simp [j, he] at hmem ⊢
  simpa only [siftedTheta, ArithmeticFunction.coe_mk, one_mul] using
    sum_triple_list_divisorsAntidiagonal (siftedPrimeTuples x j) hshape
      (fun _ r => roughWeight (x ^ ((8639 : ℝ) / 50000)) r) n

theorem roughWeight_buchstab_indicator (P : Prop) [Decidable P] (z : ℝ) (p n : ℕ)
    (hP : P → z ≤ (p : ℝ)) :
    (if P then roughWeight (p : ℝ) n else 0) =
      (if P then roughWeight z n else 0) -
        ∑ d ∈ n.divisorsAntidiagonal,
          if P ∧ d.1.Prime ∧ z ≤ (d.1 : ℝ) ∧ (d.1 : ℝ) < (p : ℝ)
          then roughWeight (d.1 : ℝ) d.2 else 0 := by
  classical
  by_cases h : P
  · simpa only [h, ite_true, true_and] using
      roughWeight_buchstab_antidiagonal (hP h) n
  · simp only [h, ite_false, false_and, Finset.sum_const_zero, sub_zero]

theorem prime_logb_buchstab_band (x : ℝ) (hx : 1 < x) (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) :
    (x ^ ((8639 : ℝ) / 50000) ≤ (p : ℝ) ∧ (p : ℝ) < (q : ℝ)) ↔
      (8639 : ℝ) / 50000 ≤ Real.logb x (p : ℝ) ∧
        Real.logb x (p : ℝ) < Real.logb x (q : ℝ) := by
  rw [Real.le_logb_iff_rpow_le hx (Nat.cast_pos.mpr hp.pos),
    Real.logb_lt_logb_iff hx (Nat.cast_pos.mpr hp.pos) (Nat.cast_pos.mpr hq.pos)]

theorem sourceRoughPair_zero_buchstab (x : ℝ) (hx : 1 < x) (n : ℕ) :
    sourceRoughPair x 0 n = siftedTheta x 2 (fun _ => 1) n - sourceRoughTriple x n := by
  classical
  let α (p : ℕ) : ℝ := Real.logb x (p : ℝ)
  let z : ℝ := x ^ ((8639 : ℝ) / 50000)
  have hpair (p q : ℕ) : [p, q] ∈ siftedPrimeTuples x (2 : Fin 6) ↔
      p.Prime ∧ q.Prime ∧ (8639 : ℝ) / 50000 ≤ α q ∧ α q < α p ∧
        α p < (41361 : ℝ) / 100000 ∧ α p + α q < (41361 : ℝ) / 100000 := by
    simpa [α] using mem_siftedPrimeTuples_iff x hx (2 : Fin 6) [p, q]
  have htriple (p q r : ℕ) : [p, q, r] ∈ siftedPrimeTuples x (4 : Fin 6) ↔
      p.Prime ∧ q.Prime ∧ r.Prime ∧ (8639 : ℝ) / 50000 ≤ α r ∧ α r < α q ∧
        α q < α p ∧ α p < (41361 : ℝ) / 100000 ∧
        α p + α q < (41361 : ℝ) / 100000 ∧
        α r < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000 := by
    simpa [α] using mem_siftedPrimeTuples_iff x hx (4 : Fin 6) [p, q, r]
  have hcut (p q r : ℕ) :
      ([p, q] ∈ siftedPrimeTuples x (2 : Fin 6) ∧ r.Prime ∧
        z ≤ (r : ℝ) ∧ (r : ℝ) < (q : ℝ)) ↔
      [p, q, r] ∈ siftedPrimeTuples x (4 : Fin 6) := by
    rw [hpair, htriple]
    constructor
    · rintro ⟨⟨hp, hq, hqlo, hqp, hphi, hpq⟩, hr, hrlo, hrq⟩
      obtain ⟨hrlog, hrqlog⟩ := (prime_logb_buchstab_band x hx r q hr hq).mp
        ⟨hrlo, hrq⟩
      exact ⟨hp, hq, hr, hrlog, hrqlog, hqp, hphi, hpq, by dsimp [α] at *; linarith⟩
    · rintro ⟨hp, hq, hr, hrlo, hrq, hqp, hphi, hpq, _⟩
      obtain ⟨hrreal, hrqreal⟩ := (prime_logb_buchstab_band x hx r q hr hq).mpr
        ⟨hrlo, hrq⟩
      exact ⟨⟨hp, hq, hrlo.trans hrq.le, hqp, hphi, hpq⟩, hr, hrreal, hrqreal⟩
  have hstep (p q r : ℕ) := roughWeight_buchstab_indicator
    ([p, q] ∈ siftedPrimeTuples x (2 : Fin 6)) z q r (by
      intro h
      have hm := (hpair p q).mp h
      exact (Real.le_logb_iff_rpow_le hx (Nat.cast_pos.mpr hm.2.1.pos)).mp hm.2.2.1)
  have hθ : siftedTheta x (2 : Fin 6) (fun _ => 1) n =
      ∑ d ∈ n.divisorsAntidiagonal, ∑ e ∈ d.2.divisorsAntidiagonal,
        if [d.1, e.1] ∈ siftedPrimeTuples x (2 : Fin 6) then roughWeight z e.2 else 0 := by
    simpa only [ite_true] using siftedTheta_pair_antidiagonal x hx (0 : Fin 2) n
  rw [hθ]
  simp only [sourceRoughPair, sourceRoughTriple, ArithmeticFunction.coe_mk, ite_true]
  simp_rw [hstep, hcut, Finset.sum_sub_distrib]

theorem sourceRoughPair_one_buchstab (x : ℝ) (hx : 1 < x) (n : ℕ) :
    sourceRoughPair x 1 n = siftedTheta x 3 (fun _ => 1) n - sourceT4 x n := by
  classical
  let α (p : ℕ) : ℝ := Real.logb x (p : ℝ)
  let z : ℝ := x ^ ((8639 : ℝ) / 50000)
  have hpair (p q : ℕ) : [p, q] ∈ siftedPrimeTuples x (3 : Fin 6) ↔
      p.Prime ∧ q.Prime ∧ (8639 : ℝ) / 50000 ≤ α q ∧ α q < α p ∧
        α p < (41361 : ℝ) / 100000 ∧ (58639 : ℝ) / 100000 < α p + α q ∧
        α q < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000 := by
    simpa [α] using mem_siftedPrimeTuples_iff x hx (3 : Fin 6) [p, q]
  have hcut (p q r : ℕ) :
      ([p, q] ∈ siftedPrimeTuples x (3 : Fin 6) ∧ r.Prime ∧
        z ≤ (r : ℝ) ∧ (r : ℝ) < (q : ℝ)) ↔
      p.Prime ∧ q.Prime ∧ r.Prime ∧ (8639 : ℝ) / 50000 ≤ α r ∧ α r < α q ∧
        α q < α p ∧ α p < (41361 : ℝ) / 100000 ∧
        (58639 : ℝ) / 100000 < α p + α q ∧
        α q < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000 := by
    rw [hpair]
    constructor
    · rintro ⟨⟨hp, hq, _, hqp, hphi, hpq, hqhi⟩, hr, hrlo, hrq⟩
      obtain ⟨hrlog, hrqlog⟩ := (prime_logb_buchstab_band x hx r q hr hq).mp
        ⟨hrlo, hrq⟩
      exact ⟨hp, hq, hr, hrlog, hrqlog, hqp, hphi, hpq, hqhi⟩
    · rintro ⟨hp, hq, hr, hrlo, hrq, hqp, hphi, hpq, hqhi⟩
      obtain ⟨hrreal, hrqreal⟩ := (prime_logb_buchstab_band x hx r q hr hq).mpr
        ⟨hrlo, hrq⟩
      exact ⟨⟨hp, hq, hrlo.trans hrq.le, hqp, hphi, hpq, hqhi⟩, hr, hrreal, hrqreal⟩
  have hstep (p q r : ℕ) := roughWeight_buchstab_indicator
    ([p, q] ∈ siftedPrimeTuples x (3 : Fin 6)) z q r (by
      intro h
      have hm := (hpair p q).mp h
      exact (Real.le_logb_iff_rpow_le hx (Nat.cast_pos.mpr hm.2.1.pos)).mp hm.2.2.1)
  have hθ : siftedTheta x (3 : Fin 6) (fun _ => 1) n =
      ∑ d ∈ n.divisorsAntidiagonal, ∑ e ∈ d.2.divisorsAntidiagonal,
        if [d.1, e.1] ∈ siftedPrimeTuples x (3 : Fin 6) then roughWeight z e.2 else 0 := by
    simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false] using
      siftedTheta_pair_antidiagonal x hx (1 : Fin 2) n
  rw [hθ]
  simp only [sourceRoughPair, sourceT4, ArithmeticFunction.coe_mk,
    show (1 : Fin 2) ≠ 0 by decide, ite_false]
  simp_rw [hstep, hcut, Finset.sum_sub_distrib]
  rfl

theorem sourceRoughTriple_buchstab (x : ℝ) (hx : 1 < x) (n : ℕ) :
    sourceRoughTriple x n = siftedTheta x 4 (fun _ => 1) n - sourceT5 x n := by
  classical
  let α (p : ℕ) : ℝ := Real.logb x (p : ℝ)
  let z : ℝ := x ^ ((8639 : ℝ) / 50000)
  have htriple (p q r : ℕ) : [p, q, r] ∈ siftedPrimeTuples x (4 : Fin 6) ↔
      p.Prime ∧ q.Prime ∧ r.Prime ∧ (8639 : ℝ) / 50000 ≤ α r ∧ α r < α q ∧
        α q < α p ∧ α p < (41361 : ℝ) / 100000 ∧
        α p + α q < (41361 : ℝ) / 100000 ∧
        α r < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000 := by
    simpa [α] using mem_siftedPrimeTuples_iff x hx (4 : Fin 6) [p, q, r]
  have hcut (p q r s : ℕ) :
      ([p, q, r] ∈ siftedPrimeTuples x (4 : Fin 6) ∧ s.Prime ∧
        z ≤ (s : ℝ) ∧ (s : ℝ) < (r : ℝ)) ↔
      p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧
        (8639 : ℝ) / 50000 ≤ α s ∧ α s < α r ∧ α r < α q ∧ α q < α p ∧
        α p < (41361 : ℝ) / 100000 ∧ α p + α q < (41361 : ℝ) / 100000 := by
    rw [htriple]
    constructor
    · rintro ⟨⟨hp, hq, hr, _, hrq, hqp, hphi, hpq, _⟩, hs, hslo, hsr⟩
      obtain ⟨hslog, hsrlog⟩ := (prime_logb_buchstab_band x hx s r hs hr).mp
        ⟨hslo, hsr⟩
      exact ⟨hp, hq, hr, hs, hslog, hsrlog, hrq, hqp, hphi, hpq⟩
    · rintro ⟨hp, hq, hr, hs, hslo, hsr, hrq, hqp, hphi, hpq⟩
      obtain ⟨hsreal, hsrreal⟩ := (prime_logb_buchstab_band x hx s r hs hr).mpr
        ⟨hslo, hsr⟩
      exact ⟨⟨hp, hq, hr, hslo.trans hsr.le, hrq, hqp, hphi, hpq,
        by dsimp [α] at *; linarith⟩, hs, hsreal, hsrreal⟩
  have hstep (p q r s : ℕ) := roughWeight_buchstab_indicator
    ([p, q, r] ∈ siftedPrimeTuples x (4 : Fin 6)) z r s (by
      intro h
      have hm := (htriple p q r).mp h
      exact (Real.le_logb_iff_rpow_le hx (Nat.cast_pos.mpr hm.2.2.1.pos)).mp hm.2.2.2.1)
  have hθ : siftedTheta x (4 : Fin 6) (fun _ => 1) n =
      ∑ d ∈ n.divisorsAntidiagonal, ∑ e ∈ d.2.divisorsAntidiagonal,
        ∑ f ∈ e.2.divisorsAntidiagonal,
          if [d.1, e.1, f.1] ∈ siftedPrimeTuples x (4 : Fin 6)
          then roughWeight z f.2 else 0 := by
    simpa only [ite_true] using siftedTheta_triple_antidiagonal x hx (0 : Fin 2) n
  rw [hθ]
  simp only [sourceRoughTriple, sourceT5, ArithmeticFunction.coe_mk]
  simp_rw [hstep, hcut, Finset.sum_sub_distrib]
  rfl

theorem pair_cut_partition (P : Prop) [Decidable P]
    (a b ζ s t v : ℝ) (hab : a ≤ b) :
    (if P then v else 0) =
      (if P ∧ s < a then v else 0) +
      (if P ∧ b < s ∧ t < ζ then v else 0) +
      (if P ∧ a ≤ s ∧ s ≤ b then v else 0) +
      (if P ∧ b < s ∧ ζ ≤ t then v else 0) := by
  classical
  by_cases hP : P
  · by_cases hlo : s < a
    · have hnb : ¬ b < s := by linarith
      simp only [hP, true_and, hlo, not_le.mpr hlo, hnb, false_and,
        ite_true, ite_false, add_zero]
    · have hla : a ≤ s := le_of_not_gt hlo
      by_cases hhi : s ≤ b
      · simp only [hP, true_and, hlo, hla, hhi, not_lt.mpr hhi, false_and,
          true_and, ite_true, ite_false, zero_add, add_zero]
      · have hbs : b < s := lt_of_not_ge hhi
        by_cases ht : t < ζ
        · simp only [hP, true_and, hlo, hla, hhi, hbs, ht, not_le.mpr ht,
            true_and, ite_true, ite_false, zero_add, add_zero]
        · simp only [hP, true_and, hlo, hla, hhi, hbs, ht, le_of_not_gt ht,
            true_and, ite_true, ite_false, zero_add, add_zero]
  · simp only [hP, false_and, ite_false, add_zero]

theorem sourceOrderedPair_partition (x : ℝ) (hx : 1 < x) (n : ℕ) :
    sourceOrderedPair x n = sourceRoughPair x 0 n + sourceRoughPair x 1 n +
      sourceCentralPair x n + sourceT3 x n := by
  classical
  let α (p : ℕ) : ℝ := Real.logb x (p : ℝ)
  have hpair0 (p q : ℕ) : [p, q] ∈ siftedPrimeTuples x (2 : Fin 6) ↔
      p.Prime ∧ q.Prime ∧ (8639 : ℝ) / 50000 ≤ α q ∧ α q < α p ∧
        α p < (41361 : ℝ) / 100000 ∧ α p + α q < (41361 : ℝ) / 100000 := by
    simpa [α] using mem_siftedPrimeTuples_iff x hx (2 : Fin 6) [p, q]
  have hpair1 (p q : ℕ) : [p, q] ∈ siftedPrimeTuples x (3 : Fin 6) ↔
      p.Prime ∧ q.Prime ∧ (8639 : ℝ) / 50000 ≤ α q ∧ α q < α p ∧
        α p < (41361 : ℝ) / 100000 ∧ (58639 : ℝ) / 100000 < α p + α q ∧
        α q < 1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000 := by
    simpa [α] using mem_siftedPrimeTuples_iff x hx (3 : Fin 6) [p, q]
  simp only [sourceOrderedPair, sourceRoughPair, sourceCentralPair, sourceT3,
    ArithmeticFunction.coe_mk, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  simp only [hpair0, hpair1]
  simpa only [and_assoc, α] using pair_cut_partition
    (d.1.Prime ∧ e.1.Prime ∧ (8639 : ℝ) / 50000 ≤ α e.1 ∧
      α e.1 < α d.1 ∧ α d.1 < (41361 : ℝ) / 100000)
    ((41361 : ℝ) / 100000) ((58639 : ℝ) / 100000)
    (1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000)
    (α d.1 + α e.1) (α e.1) (roughWeight (e.1 : ℝ) e.2) (by norm_num)

theorem sum_prime_pair_divisorsAntidiagonal
    {A : Type*} [AddCommMonoid A] (n : ℕ) (P : ℕ → Prop) (Q : ℕ → ℕ → Prop)
    [DecidablePred P] [∀ p, DecidablePred (Q p)]
    (w : ℕ → ℕ → ℕ → A) :
    (∑ d ∈ n.divisorsAntidiagonal, ∑ e ∈ d.2.divisorsAntidiagonal,
      if (d.1.Prime ∧ P d.1) ∧ (e.1.Prime ∧ Q d.1 e.1) then w d.1 e.1 e.2 else 0) =
    ∑ p ∈ (Nat.primesLE n).filter (fun p => P p ∧ p ∣ n),
      ∑ q ∈ (Nat.primesLE (n / p)).filter (fun q => Q p q ∧ q ∣ n / p),
        w p q ((n / p) / q) := by
  classical
  calc
    _ = ∑ d ∈ n.divisorsAntidiagonal,
        if d.1.Prime ∧ P d.1 then
          ∑ e ∈ d.2.divisorsAntidiagonal,
            if e.1.Prime ∧ Q d.1 e.1 then w d.1 e.1 e.2 else 0
        else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases h : d.1.Prime ∧ P d.1
      · simp only [h, true_and, ite_true]
      · simp only [h, false_and, ite_false, Finset.sum_const_zero]
    _ = _ := by
      simp_rw [sum_prime_divisorsAntidiagonal]
      exact sum_prime_divisorsAntidiagonal n P
        (fun p r => ∑ q ∈ (Nat.primesLE r).filter (fun q => Q p q ∧ q ∣ r),
          w p q (r / q))

theorem sourceOrderedPair_eq_prime_divisor_sum (x : ℝ) (hx : 1 < x) (n : ℕ) :
    sourceOrderedPair x n =
      ∑ p ∈ (Nat.primesLE n).filter (fun p : ℕ =>
        x ^ ((8639 : ℝ) / 50000) ≤ (p : ℝ) ∧
        (p : ℝ) < x ^ ((41361 : ℝ) / 100000) ∧ p ∣ n),
        ∑ q ∈ (Nat.primesLE (n / p)).filter (fun q : ℕ =>
          x ^ ((8639 : ℝ) / 50000) ≤ (q : ℝ) ∧
          (q : ℝ) < (p : ℝ) ∧ q ∣ n / p),
          roughWeight (q : ℝ) ((n / p) / q) := by
  classical
  have hmask (p q : ℕ) :
      (p.Prime ∧ q.Prime ∧
        (8639 : ℝ) / 50000 ≤ Real.logb x (q : ℝ) ∧
        Real.logb x (q : ℝ) < Real.logb x (p : ℝ) ∧
        Real.logb x (p : ℝ) < (41361 : ℝ) / 100000) ↔
      (p.Prime ∧ x ^ ((8639 : ℝ) / 50000) ≤ (p : ℝ) ∧
        (p : ℝ) < x ^ ((41361 : ℝ) / 100000)) ∧
      (q.Prime ∧ x ^ ((8639 : ℝ) / 50000) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)) := by
    by_cases hp : p.Prime
    · by_cases hq : q.Prime
      · simp only [hp, hq, true_and,
          Real.le_logb_iff_rpow_le hx (Nat.cast_pos.mpr hq.pos),
          Real.logb_lt_logb_iff hx (Nat.cast_pos.mpr hq.pos) (Nat.cast_pos.mpr hp.pos),
          Real.logb_lt_iff_lt_rpow hx (Nat.cast_pos.mpr hp.pos)]
        constructor
        · rintro ⟨hlo, hqp, hphi⟩
          exact ⟨⟨hlo.trans hqp.le, hphi⟩, hlo, hqp⟩
        · rintro ⟨⟨_, hphi⟩, hlo, hqp⟩
          exact ⟨hlo, hqp, hphi⟩
      · simp only [hq, false_and, and_false]
    · simp only [hp, false_and]
  simp only [sourceOrderedPair, ArithmeticFunction.coe_mk, hmask]
  simpa only [and_assoc] using sum_prime_pair_divisorsAntidiagonal n
    (fun p => x ^ ((8639 : ℝ) / 50000) ≤ (p : ℝ) ∧
      (p : ℝ) < x ^ ((41361 : ℝ) / 100000))
    (fun p q => x ^ ((8639 : ℝ) / 50000) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ))
    (fun _ q r => roughWeight (q : ℝ) r)

theorem primeIndicator_source_buchstab {x : ℝ} (hx : 3 ≤ x)
    {n : ℕ} (hlo : x ≤ (n : ℝ)) (hhi : (n : ℝ) ≤ 2 * x) :
    (if n.Prime then (1 : ℝ) else 0) =
      siftedTheta x 0 (fun _ => 1) n - siftedTheta x 1 (fun _ => 1) n +
      siftedTheta x 2 (fun _ => 1) n + siftedTheta x 3 (fun _ => 1) n -
      siftedTheta x 4 (fun _ => 1) n - sourceLargeFirst x n + sourceCentralPair x n +
      sourceT3 x n + sourceT5 x n - sourceT4 x n := by
  have hx1 : 1 < x := by linarith
  have hlarge : sourceLargeFirst x n =
      ∑ p ∈ (Nat.primesLE n).filter (fun p : ℕ =>
        x ^ ((41361 : ℝ) / 100000) ≤ (p : ℝ) ∧
        (p : ℝ) < Real.sqrt (3 * x) ∧ p ∣ n),
        roughWeight (p : ℝ) (n / p) := by
    classical
    simpa only [sourceLargeFirst, ArithmeticFunction.coe_mk, and_assoc] using
      sum_prime_divisorsAntidiagonal n
        (fun p => x ^ ((41361 : ℝ) / 100000) ≤ (p : ℝ) ∧
          (p : ℝ) < Real.sqrt (3 * x)) (fun p r => roughWeight (p : ℝ) r)
  have hstart := primeIndicator_eq_siftedTheta_zero_sub_one hx hlo hhi
  rw [← hlarge, ← sourceOrderedPair_eq_prime_divisor_sum x hx1 n] at hstart
  have hparts := sourceOrderedPair_partition x hx1 n
  have hlow := sourceRoughPair_zero_buchstab x hx1 n
  have hhigh := sourceRoughPair_one_buchstab x hx1 n
  have hlast := sourceRoughTriple_buchstab x hx1 n
  linarith

/--
The number of factorizations of `n` into a prime tuple from sifted region `5` and a prime
cofactor.
-/
noncomputable def sourceU1 (x : ℝ) : ArithmeticFunction ℝ := by
  classical
  exact ⟨fun n =>
    ∑ ps ∈ siftedPrimeTuples x (5 : Fin 6), ∑ d ∈ n.divisorsAntidiagonal,
      if d.1 = ps.prod then (if d.2.Prime then 1 else 0) else 0, by simp⟩

/--
The number of factorizations of `n` into a prime tuple from sifted region `5` and two additional
primes in nondecreasing order, with the smaller additional prime at least `x^(8639 / 50000)`.
-/
noncomputable def sourceU3 (x : ℝ) : ArithmeticFunction ℝ := by
  classical
  exact ⟨fun n =>
    ∑ ps ∈ siftedPrimeTuples x (5 : Fin 6), ∑ d ∈ n.divisorsAntidiagonal,
      if d.1 = ps.prod then
        ∑ e ∈ d.2.divisorsAntidiagonal,
          if e.1.Prime ∧ e.2.Prime ∧ x ^ ((8639 : ℝ) / 50000) ≤ (e.1 : ℝ) ∧
              e.1 ≤ e.2 then 1 else 0
      else 0, by simp⟩

theorem sourceU1_eventually_eq_siftedTheta_five_sub_sourceU3 :
    ∃ X : ℝ, 3 ≤ X ∧ ∀ x : ℝ, X ≤ x → ∀ n : ℕ,
      x ≤ (n : ℝ) → (n : ℝ) ≤ 2 * x →
      sourceU1 x n = siftedTheta x (5 : Fin 6) (fun _ => 1) n - sourceU3 x n := by
  classical
  obtain ⟨X, hX⟩ := eventually_exceptional_large.exists_forall_of_atTop
  refine ⟨max 3 X, le_max_left _ _, ?_⟩
  intro x hx n hnlo hnhi
  obtain ⟨hx1, hgrowth⟩ := hX x ((le_max_right _ _).trans hx)
  have hx0 : 0 < x := zero_lt_one.trans hx1
  let z : ℝ := x ^ ((8639 : ℝ) / 50000)
  have hz : 1 < z := Real.one_lt_rpow hx1 (by norm_num)
  have hz0 : 0 ≤ z := (zero_lt_one.trans hz).le
  have hpoint (ps : List ℕ) (hps : ps ∈ siftedPrimeTuples x (5 : Fin 6))
      (d : ℕ × ℕ) (hd : d ∈ n.divisorsAntidiagonal) (heq : d.1 = ps.prod) :
      roughWeight z d.2 = (if d.2.Prime then 1 else 0) +
        ∑ e ∈ d.2.divisorsAntidiagonal,
          if e.1.Prime ∧ e.2.Prime ∧ z ≤ (e.1 : ℝ) ∧ e.1 ≤ e.2 then 1 else 0 := by
    have hmul : ps.prod * d.2 = n := by
      simpa only [heq] using (Nat.mem_divisorsAntidiagonal.mp hd).1
    have hmpos : 0 < (d.2 : ℝ) := Nat.cast_pos.mpr
      (Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hd))
    have hmulR : (ps.prod : ℝ) * (d.2 : ℝ) = (n : ℝ) := by exact_mod_cast hmul
    obtain ⟨_hgp, hgq, hgeq, hgphi, hgqhi, hprimes⟩ :=
      siftedPrimeTuples_group_bounds x hx1 (5 : Fin 6) ps hps
    have hprodhi : (ps.prod : ℝ) < x ^ (1 - (34941 : ℝ) / 100000) := by
      rw [← Real.rpow_sub hx0] at hgqhi
      calc
        (ps.prod : ℝ) =
            ((siftedPrimeGroups (5 : Fin 6) ps).1 : ℝ) *
              ((siftedPrimeGroups (5 : Fin 6) ps).2 : ℝ) := by
          exact_mod_cast hgeq.symm
        _ < x ^ ((41361 : ℝ) / 100000) *
            x ^ (1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000) :=
          mul_lt_mul hgphi hgqhi.le (Nat.cast_pos.mpr hgq)
            (Real.rpow_nonneg hx0.le _)
        _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
    have hmlarge : x ^ ((34941 : ℝ) / 100000) < (d.2 : ℝ) := by
      by_contra hbad
      have hmle := le_of_not_gt hbad
      have hnsmall : (n : ℝ) <
          x ^ (1 - (34941 : ℝ) / 100000) * x ^ ((34941 : ℝ) / 100000) := by
        rw [← hmulR]
        exact mul_lt_mul hprodhi hmle hmpos (Real.rpow_nonneg hx0.le _)
      rw [← Real.rpow_add hx0, sub_add_cancel, Real.rpow_one] at hnsmall
      exact (not_lt_of_ge hnlo) hnsmall
    have hmlo : z ≤ (d.2 : ℝ) :=
      (Real.rpow_le_rpow_of_exponent_le hx1.le
        (by norm_num : (8639 : ℝ) / 50000 ≤ (34941 : ℝ) / 100000)).trans hmlarge.le
    have hshape : ∃ p q r : ℕ, ps = [p, q, r] := by
      have hmem := (mem_siftedPrimeTuples_iff x hx1 (5 : Fin 6) ps).mp hps
      dsimp only at hmem
      rcases ps with _ | ⟨p, _ | ⟨q, _ | ⟨r, _ | ⟨s, ss⟩⟩⟩⟩
      · exact False.elim hmem
      · exact False.elim hmem
      · exact False.elim hmem
      · exact ⟨p, q, r, rfl⟩
      · exact False.elim hmem
    have hprodlo : z ^ (3 : ℕ) ≤ (ps.prod : ℝ) := by
      obtain ⟨p, q, r, rfl⟩ := hshape
      have hpz := (hprimes p (by simp)).2
      have hqz := (hprimes q (by simp)).2
      have hrz := (hprimes r (by simp)).2
      calc
        z ^ (3 : ℕ) = z * z * z := by ring
        _ ≤ (p : ℝ) * (q : ℝ) * (r : ℝ) :=
          mul_le_mul (mul_le_mul hpz hqz hz0 (Nat.cast_nonneg _)) hrz hz0
            (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        _ = (([p, q, r] : List ℕ).prod : ℝ) := by
          simp only [List.prod_cons, List.prod_nil, Nat.cast_mul, mul_one, mul_assoc]
    have hmsmall : (d.2 : ℝ) < z ^ (3 : ℕ) := by
      by_contra hbad
      have hmge := le_of_not_gt hbad
      have hlarge : x ^ (6 * ((8639 : ℝ) / 50000)) ≤ (n : ℝ) := by
        calc
          x ^ (6 * ((8639 : ℝ) / 50000)) = z ^ (3 : ℕ) * z ^ (3 : ℕ) := by
            dsimp only [z]
            rw [← pow_add, ← Real.rpow_mul_natCast hx0.le]
            congr 1
            norm_num
          _ ≤ (ps.prod : ℝ) * (d.2 : ℝ) :=
            mul_le_mul hprodlo hmge (pow_nonneg hz0 _)
              (Nat.cast_nonneg _)
          _ = (n : ℝ) := hmulR
      exact (not_lt_of_ge hnhi) (hgrowth.trans_le hlarge)
    exact roughWeight_eq_prime_add_ordered_semiprime z d.2 hz hmlo hmsmall
  apply (eq_sub_iff_add_eq).mpr
  simp only [sourceU1, sourceU3, siftedTheta, ArithmeticFunction.coe_mk, one_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ps hps
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases heq : d.1 = ps.prod
  · simp only [ite_eq_left heq]
    exact (hpoint ps hps d hd heq).symm
  · simp only [ite_eq_right heq, add_zero]

#print axioms primeIndicator_eq_siftedTheta_zero_sub_one
#print axioms sourceRoughPair_zero_buchstab
#print axioms sourceRoughPair_one_buchstab
#print axioms sourceRoughTriple_buchstab
#print axioms primeIndicator_source_buchstab
#print axioms sourceU1_eventually_eq_siftedTheta_five_sub_sourceU3

end PrimeGap182Analytic.Harman
