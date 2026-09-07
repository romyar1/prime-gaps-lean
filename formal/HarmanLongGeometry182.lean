import HarmanData182

/-!
# Actual long-branch geometry and raw identities at the 182 thresholds

The thresholds are lambda=.17278, a=.41361, b=.58639, I=.34941,
and zeta=1-I-a=.23698. Both a+lambda=b and a+b=1 are used as
proved rational identities. No distribution theorem is assumed.

Adapted from the hash-pinned Apache-2.0 public PrimeGaps186 source by
scripts/build_harman_long.py. No original source is modified.
-/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000

open Classical in
theorem restricted_harman_long_source_scales
    (x : ℝ) (hx : 1 < x) (r s h d k : ℕ)
    (hs : 0 < s) (hh : 1 < h) (hd : 0 < d) (hk : 0 < k)
    (hcap : ((max 1 (h.primeFactors.sup id) : ℕ) : ℝ) <
      x ^ ((8639 : ℝ) / 50000))
    (hprevious : ((r * h : ℕ) : ℝ) / (h.minFac : ℝ) <
      x ^ ((41361 : ℝ) / 100000))
    (hcrossing : x ^ ((41361 : ℝ) / 100000) ≤ ((r * h : ℕ) : ℝ))
    (hproduct : x ≤ ((r * s * h * d * k : ℕ) : ℝ) ∧
      ((r * s * h * d * k : ℕ) : ℝ) ≤ 2 * x)
    (hlong : x ^ (1 - (34941 : ℝ) / 100000) < ((r * s * h * d : ℕ) : ℝ)) :
    x ^ ((41361 : ℝ) / 100000) ≤ ((r * h : ℕ) : ℝ) ∧
      ((r * h : ℕ) : ℝ) < x ^ ((58639 : ℝ) / 100000) ∧
      x ^ ((41361 : ℝ) / 100000) < ((s * d * k : ℕ) : ℝ) ∧
      ((s * d * k : ℕ) : ℝ) ≤ 2 * x ^ ((58639 : ℝ) / 100000) ∧
      (k : ℝ) < 2 * x ^ ((34941 : ℝ) / 100000) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hmin : h.minFac.Prime := Nat.minFac_prime hh.ne'
  have hminmem : h.minFac ∈ h.primeFactors :=
    hmin.mem_primeFactors (Nat.minFac_dvd h) (by omega)
  have hminle : (h.minFac : ℝ) ≤ ((max 1 (h.primeFactors.sup id) : ℕ) : ℝ) := by
    exact_mod_cast (Finset.le_sup (f := id) hminmem).trans (le_max_right _ _)
  have hminpos : (0 : ℝ) < h.minFac := Nat.cast_pos.mpr hmin.pos
  have hupper : ((r * h : ℕ) : ℝ) < x ^ ((58639 : ℝ) / 100000) := by
    calc
      ((r * h : ℕ) : ℝ) <
          x ^ ((41361 : ℝ) / 100000) * (h.minFac : ℝ) :=
        (div_lt_iff₀ hminpos).mp hprevious
      _ < x ^ ((41361 : ℝ) / 100000) * x ^ ((8639 : ℝ) / 50000) :=
        mul_lt_mul_of_pos_left (hminle.trans_lt hcap) (Real.rpow_pos_of_pos hx0 _)
      _ = x ^ ((58639 : ℝ) / 100000) := by
        rw [← Real.rpow_add hx0]
        norm_num
  have hnpos : (0 : ℝ) < ((s * d * k : ℕ) : ℝ) := by positivity
  have hfactor : ((r * h : ℕ) : ℝ) * ((s * d * k : ℕ) : ℝ) =
      ((r * s * h * d * k : ℕ) : ℝ) := by
    push_cast
    ring
  have hcomplement :
      x ^ ((41361 : ℝ) / 100000) * x ^ ((58639 : ℝ) / 100000) = x := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hnlo : x ^ ((41361 : ℝ) / 100000) < ((s * d * k : ℕ) : ℝ) := by
    apply (mul_lt_mul_iff_left₀ (Real.rpow_pos_of_pos hx0 ((58639 : ℝ) / 100000))).mp
    rw [hcomplement]
    calc
      x ≤ ((r * s * h * d * k : ℕ) : ℝ) := hproduct.1
      _ = ((s * d * k : ℕ) : ℝ) * ((r * h : ℕ) : ℝ) :=
        hfactor.symm.trans (mul_comm _ _)
      _ < ((s * d * k : ℕ) : ℝ) * x ^ ((58639 : ℝ) / 100000) :=
        mul_lt_mul_of_pos_left hupper hnpos
  have hnhi : ((s * d * k : ℕ) : ℝ) ≤ 2 * x ^ ((58639 : ℝ) / 100000) := by
    apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hx0 ((41361 : ℝ) / 100000))).mp
    calc
      x ^ ((41361 : ℝ) / 100000) * ((s * d * k : ℕ) : ℝ) ≤
          ((r * h : ℕ) : ℝ) * ((s * d * k : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hcrossing hnpos.le
      _ = ((r * s * h * d * k : ℕ) : ℝ) := hfactor
      _ ≤ 2 * x := hproduct.2
      _ = x ^ ((41361 : ℝ) / 100000) *
          (2 * x ^ ((58639 : ℝ) / 100000)) := by
        rw [mul_left_comm, hcomplement]
  have hkhi : (k : ℝ) < 2 * x ^ ((34941 : ℝ) / 100000) := by
    apply (mul_lt_mul_iff_right₀ (Real.rpow_pos_of_pos hx0 (1 - (34941 : ℝ) / 100000))).mp
    calc
      x ^ (1 - (34941 : ℝ) / 100000) * (k : ℝ) <
          ((r * s * h * d : ℕ) : ℝ) * (k : ℝ) :=
        mul_lt_mul_of_pos_right hlong (Nat.cast_pos.mpr hk)
      _ = ((r * s * h * d * k : ℕ) : ℝ) := by push_cast; ring
      _ ≤ 2 * x := hproduct.2
      _ = x ^ (1 - (34941 : ℝ) / 100000) *
          (2 * x ^ ((34941 : ℝ) / 100000)) := by
        rw [mul_left_comm, ← Real.rpow_add hx0]
        norm_num
  exact ⟨hcrossing, hupper, hnlo, hnhi, hkhi⟩

open Classical in
theorem siftedPrimeTuples_named_cuts (x : ℝ) (hx : 1 < x) (l : Fin 6)
    (p q s : ℕ)
    (hdummy : match l.val with
      | 0 => p = 1 ∧ q = 1 ∧ s = 1
      | 1 => q = 1 ∧ s = 1
      | 2 => q = 1
      | 3 => q = 1
      | _ => True) :
    let z : ℝ := x ^ ((8639 : ℝ) / 50000)
    let H : ℝ := x ^ ((41361 : ℝ) / 100000)
    let B : ℝ := x ^ ((58639 : ℝ) / 100000)
    let S : ℝ := x ^ (1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000)
    let ps : List ℕ := match l.val with
      | 0 => []
      | 1 => [p]
      | 2 => [p, s]
      | 3 => [p, s]
      | 4 => [q, p, s]
      | _ => [s, p, q]
    let r : ℕ := if l.val ≤ 3 then (if l.val = 0 then 1 else p) else p * q
    siftedPrimeGroups l ps = (r, s) ∧ ps.prod = r * s ∧
      (ps ∈ siftedPrimeTuples x l ↔ match l.val with
        | 0 => True
        | 1 => p.Prime ∧ z ≤ (p : ℝ) ∧ (p : ℝ) < H
        | 2 => p.Prime ∧ s.Prime ∧ z ≤ (s : ℝ) ∧ s < p ∧
            (p : ℝ) < H ∧ ((p * s : ℕ) : ℝ) < H
        | 3 => p.Prime ∧ s.Prime ∧ z ≤ (s : ℝ) ∧ s < p ∧
            (p : ℝ) < H ∧ B < ((p * s : ℕ) : ℝ) ∧ (s : ℝ) < S
        | 4 => p.Prime ∧ q.Prime ∧ s.Prime ∧ z ≤ (s : ℝ) ∧ s < p ∧
            p < q ∧ ((p * q : ℕ) : ℝ) < H ∧ (s : ℝ) < S
        | _ => s.Prime ∧ p.Prime ∧ q.Prime ∧ z ≤ (p : ℝ) ∧ p < s ∧
            (s : ℝ) < H ∧ p ≤ q ∧ ((p * q : ℕ) : ℝ) < H ∧ (s : ℝ) < S) := by
  have hlo (n : ℕ) (hn : n.Prime) (t : ℝ) :
      t ≤ Real.logb x (n : ℝ) ↔ x ^ t ≤ (n : ℝ) :=
    Real.le_logb_iff_rpow_le hx (Nat.cast_pos.mpr hn.pos)
  have hlt (n : ℕ) (hn : n.Prime) (t : ℝ) :
      Real.logb x (n : ℝ) < t ↔ (n : ℝ) < x ^ t :=
    Real.logb_lt_iff_lt_rpow hx (Nat.cast_pos.mpr hn.pos)
  have horder (n m : ℕ) (hn : n.Prime) (hm : m.Prime) :
      Real.logb x (n : ℝ) < Real.logb x (m : ℝ) ↔ n < m := by
    simpa only [Nat.cast_lt] using
      Real.logb_lt_logb_iff hx (Nat.cast_pos.mpr hn.pos) (Nat.cast_pos.mpr hm.pos)
  have horder_le (n m : ℕ) (hn : n.Prime) (hm : m.Prime) :
      Real.logb x (n : ℝ) ≤ Real.logb x (m : ℝ) ↔ n ≤ m := by
    simpa only [Nat.cast_le] using
      Real.logb_le_logb hx (Nat.cast_pos.mpr hn.pos) (Nat.cast_pos.mpr hm.pos)
  have hproduct_lt (n m : ℕ) (hn : n.Prime) (hm : m.Prime) (t : ℝ) :
      Real.logb x (n : ℝ) + Real.logb x (m : ℝ) < t ↔
        ((n * m : ℕ) : ℝ) < x ^ t := by
    rw [Nat.cast_mul, ← Real.logb_mul (Nat.cast_ne_zero.mpr hn.ne_zero)
      (Nat.cast_ne_zero.mpr hm.ne_zero)]
    exact Real.logb_lt_iff_lt_rpow hx
      (mul_pos (Nat.cast_pos.mpr hn.pos) (Nat.cast_pos.mpr hm.pos))
  have hlt_product (n m : ℕ) (hn : n.Prime) (hm : m.Prime) (t : ℝ) :
      t < Real.logb x (n : ℝ) + Real.logb x (m : ℝ) ↔
        x ^ t < ((n * m : ℕ) : ℝ) := by
    rw [Nat.cast_mul, ← Real.logb_mul (Nat.cast_ne_zero.mpr hn.ne_zero)
      (Nat.cast_ne_zero.mpr hm.ne_zero)]
    exact Real.lt_logb_iff_rpow_lt hx
      (mul_pos (Nat.cast_pos.mpr hn.pos) (Nat.cast_pos.mpr hm.pos))
  dsimp only
  fin_cases l
  · change p = 1 ∧ q = 1 ∧ s = 1 at hdummy
    rcases hdummy with ⟨rfl, rfl, rfl⟩
    simp [siftedPrimeGroups, mem_siftedPrimeTuples_iff x hx]
  · change q = 1 ∧ s = 1 at hdummy
    rcases hdummy with ⟨rfl, rfl⟩
    refine ⟨by simp [siftedPrimeGroups], by simp, ?_⟩
    change [p] ∈ siftedPrimeTuples x (1 : Fin 6) ↔
      p.Prime ∧ x ^ ((8639 : ℝ) / 50000) ≤ (p : ℝ) ∧
        (p : ℝ) < x ^ ((41361 : ℝ) / 100000)
    have hm := mem_siftedPrimeTuples_iff x hx (1 : Fin 6) [p]
    dsimp only at hm ⊢
    rw [hm]
    constructor
    · rintro ⟨hp, hz, hH⟩
      exact ⟨hp, (hlo p hp _).mp hz, (hlt p hp _).mp hH⟩
    · rintro ⟨hp, hz, hH⟩
      exact ⟨hp, (hlo p hp _).mpr hz, (hlt p hp _).mpr hH⟩
  · change q = 1 at hdummy
    subst q
    refine ⟨by simp [siftedPrimeGroups], by simp, ?_⟩
    change [p, s] ∈ siftedPrimeTuples x (2 : Fin 6) ↔
      p.Prime ∧ s.Prime ∧ x ^ ((8639 : ℝ) / 50000) ≤ (s : ℝ) ∧ s < p ∧
        (p : ℝ) < x ^ ((41361 : ℝ) / 100000) ∧
        ((p * s : ℕ) : ℝ) < x ^ ((41361 : ℝ) / 100000)
    have hm := mem_siftedPrimeTuples_iff x hx (2 : Fin 6) [p, s]
    dsimp only at hm ⊢
    rw [hm]
    constructor
    · rintro ⟨hp, hs, hz, hsp, hH, hprod⟩
      exact ⟨hp, hs, (hlo s hs _).mp hz, (horder s p hs hp).mp hsp,
        (hlt p hp _).mp hH, (hproduct_lt p s hp hs _).mp hprod⟩
    · rintro ⟨hp, hs, hz, hsp, hH, hprod⟩
      exact ⟨hp, hs, (hlo s hs _).mpr hz, (horder s p hs hp).mpr hsp,
        (hlt p hp _).mpr hH, (hproduct_lt p s hp hs _).mpr hprod⟩
  · change q = 1 at hdummy
    subst q
    refine ⟨by simp [siftedPrimeGroups], by simp, ?_⟩
    change [p, s] ∈ siftedPrimeTuples x (3 : Fin 6) ↔
      p.Prime ∧ s.Prime ∧ x ^ ((8639 : ℝ) / 50000) ≤ (s : ℝ) ∧ s < p ∧
        (p : ℝ) < x ^ ((41361 : ℝ) / 100000) ∧
        x ^ ((58639 : ℝ) / 100000) < ((p * s : ℕ) : ℝ) ∧
        (s : ℝ) < x ^ (1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000)
    have hm := mem_siftedPrimeTuples_iff x hx (3 : Fin 6) [p, s]
    dsimp only at hm ⊢
    rw [hm]
    constructor
    · rintro ⟨hp, hs, hz, hsp, hH, hprod, hS⟩
      exact ⟨hp, hs, (hlo s hs _).mp hz, (horder s p hs hp).mp hsp,
        (hlt p hp _).mp hH, (hlt_product p s hp hs _).mp hprod,
        (hlt s hs _).mp hS⟩
    · rintro ⟨hp, hs, hz, hsp, hH, hprod, hS⟩
      exact ⟨hp, hs, (hlo s hs _).mpr hz, (horder s p hs hp).mpr hsp,
        (hlt p hp _).mpr hH, (hlt_product p s hp hs _).mpr hprod,
        (hlt s hs _).mpr hS⟩
  · clear hdummy
    refine ⟨by simp [siftedPrimeGroups, mul_comm],
      by simp [mul_comm, mul_left_comm], ?_⟩
    change [q, p, s] ∈ siftedPrimeTuples x (4 : Fin 6) ↔
      p.Prime ∧ q.Prime ∧ s.Prime ∧ x ^ ((8639 : ℝ) / 50000) ≤ (s : ℝ) ∧
        s < p ∧ p < q ∧ ((p * q : ℕ) : ℝ) < x ^ ((41361 : ℝ) / 100000) ∧
        (s : ℝ) < x ^ (1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000)
    have hm := mem_siftedPrimeTuples_iff x hx (4 : Fin 6) [q, p, s]
    dsimp only at hm ⊢
    rw [hm]
    constructor
    · rintro ⟨hq, hp, hs, hz, hsp, hpq, _hqH, hprod, hS⟩
      refine ⟨hp, hq, hs, (hlo s hs _).mp hz, (horder s p hs hp).mp hsp,
        (horder p q hp hq).mp hpq, ?_, (hlt s hs _).mp hS⟩
      simpa only [Nat.mul_comm] using (hproduct_lt q p hq hp _).mp hprod
    · rintro ⟨hp, hq, hs, hz, hsp, hpq, hprod, hS⟩
      have hqH : (q : ℝ) < x ^ ((41361 : ℝ) / 100000) :=
        (Nat.cast_le.mpr (Nat.le_mul_of_pos_left q hp.pos)).trans_lt hprod
      have hprod' : ((q * p : ℕ) : ℝ) < x ^ ((41361 : ℝ) / 100000) := by
        simpa only [Nat.mul_comm] using hprod
      exact ⟨hq, hp, hs, (hlo s hs _).mpr hz, (horder s p hs hp).mpr hsp,
        (horder p q hp hq).mpr hpq, (hlt q hq _).mpr hqH,
        (hproduct_lt q p hq hp _).mpr hprod', (hlt s hs _).mpr hS⟩
  · clear hdummy
    refine ⟨by simp [siftedPrimeGroups], by simp [mul_comm, mul_left_comm], ?_⟩
    change [s, p, q] ∈ siftedPrimeTuples x (5 : Fin 6) ↔
      s.Prime ∧ p.Prime ∧ q.Prime ∧ x ^ ((8639 : ℝ) / 50000) ≤ (p : ℝ) ∧
        p < s ∧ (s : ℝ) < x ^ ((41361 : ℝ) / 100000) ∧ p ≤ q ∧
        ((p * q : ℕ) : ℝ) < x ^ ((41361 : ℝ) / 100000) ∧
        (s : ℝ) < x ^ (1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000)
    have hm := mem_siftedPrimeTuples_iff x hx (5 : Fin 6) [s, p, q]
    dsimp only at hm ⊢
    rw [hm]
    constructor
    · rintro ⟨hs, hp, hq, hz, hps, hH, hpq, hprod, hS⟩
      exact ⟨hs, hp, hq, (hlo p hp _).mp hz, (horder p s hp hs).mp hps,
        (hlt s hs _).mp hH, (horder_le p q hp hq).mp hpq,
        (hproduct_lt p q hp hq _).mp hprod, (hlt s hs _).mp hS⟩
    · rintro ⟨hs, hp, hq, hz, hps, hH, hpq, hprod, hS⟩
      exact ⟨hs, hp, hq, (hlo p hp _).mpr hz, (horder p s hp hs).mpr hps,
        (hlt s hs _).mpr hH, (horder_le p q hp hq).mpr hpq,
        (hproduct_lt p q hp hq _).mpr hprod, (hlt s hs _).mpr hS⟩

open Classical in
theorem harman_named_factor_cuts
    (x : ℝ) (hx : 1 < x) (l : Fin 6) (u v s : ℕ) :
    let z := x ^ ((8639 : ℝ) / 50000)
    let H := x ^ ((41361 : ℝ) / 100000)
    let B := x ^ ((58639 : ℝ) / 100000)
    let S := x ^ (1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000)
    let ps : List ℕ := match l.val with
      | 0 => []
      | 1 => [v]
      | 2 => [v, s]
      | 3 => [v, s]
      | 4 => [v, u, s]
      | _ => [s, u, v]
    ((match l.val with
      | 0 => u = 1 ∧ v = 1 ∧ s = 1
      | 1 => u = 1 ∧ s = 1
      | 2 => u = 1
      | 3 => u = 1
      | _ => True) ∧ ps ∈ siftedPrimeTuples x l) ↔
      (match l.val with
        | 0 => u = 1 ∧ v = 1
        | 1 | 2 | 3 => u = 1 ∧ v.Prime ∧ z ≤ (v : ℝ)
        | 4 => u.Prime ∧ v.Prime ∧ z ≤ (u : ℝ) ∧ u < v
        | _ => u.Prime ∧ v.Prime ∧ z ≤ (u : ℝ) ∧ u ≤ v) ∧
      ((u * v : ℕ) : ℝ) < H ∧
      (if l.val ≤ 1 then s = 1 else s.Prime ∧ z ≤ (s : ℝ)) ∧
      (s : ℝ) < S ∧
      (match l.val with
        | 2 => s < v ∧ ((v * s : ℕ) : ℝ) < H
        | 3 => s < v ∧ B < ((v * s : ℕ) : ℝ)
        | 4 => s < u
        | 5 => u < s
        | _ => True) := by
  intro z H B S ps
  have hH : (1 : ℝ) < H := Real.one_lt_rpow hx (by norm_num)
  have hS : (1 : ℝ) < S := Real.one_lt_rpow hx (by norm_num)
  have hSH : S < H := Real.rpow_lt_rpow_of_exponent_lt hx (by norm_num)
  have hsize (j : Fin 6) (p : List ℕ) (hp : p ∈ siftedPrimeTuples x j) :
      ((siftedPrimeGroups j p).2 : ℝ) < S := by
    have hg := (siftedPrimeTuples_group_bounds x hx j p hp).2.2.2.2.1
    simpa only [S, ← Real.rpow_sub (zero_lt_one.trans hx)] using hg
  fin_cases l
  · change ((u = 1 ∧ v = 1 ∧ s = 1) ∧ [] ∈ siftedPrimeTuples x (0 : Fin 6)) ↔
      (u = 1 ∧ v = 1) ∧ ((u * v : ℕ) : ℝ) < H ∧ s = 1 ∧ (s : ℝ) < S ∧ True
    have hempty : [] ∈ siftedPrimeTuples x (0 : Fin 6) := by
      have hm := mem_siftedPrimeTuples_iff x hx (0 : Fin 6) []
      simpa only using hm.mpr True.intro
    constructor
    · rintro ⟨⟨rfl, rfl, rfl⟩, _⟩
      exact ⟨⟨rfl, rfl⟩, by simpa using hH, rfl,
        by simpa only [Nat.cast_one] using hS, True.intro⟩
    · rintro ⟨⟨rfl, rfl⟩, _, rfl, _, _⟩
      exact ⟨⟨rfl, rfl, rfl⟩, hempty⟩
  · have hm := (siftedPrimeTuples_named_cuts x hx (1 : Fin 6) v 1 1
      ⟨rfl, rfl⟩).2.2
    change [v] ∈ siftedPrimeTuples x (1 : Fin 6) ↔
      v.Prime ∧ z ≤ (v : ℝ) ∧ (v : ℝ) < H at hm
    change ((u = 1 ∧ s = 1) ∧ [v] ∈ siftedPrimeTuples x (1 : Fin 6)) ↔
      (u = 1 ∧ v.Prime ∧ z ≤ (v : ℝ)) ∧ ((u * v : ℕ) : ℝ) < H ∧
        s = 1 ∧ (s : ℝ) < S ∧ True
    rw [hm]
    constructor
    · rintro ⟨⟨rfl, rfl⟩, hv, hzv, hvH⟩
      exact ⟨⟨rfl, hv, hzv⟩, by simpa using hvH, rfl,
        by simpa only [Nat.cast_one] using hS, True.intro⟩
    · rintro ⟨⟨rfl, hv, hzv⟩, hvH, rfl, _, _⟩
      exact ⟨⟨rfl, rfl⟩, hv, hzv, by simpa using hvH⟩
  · have hm := (siftedPrimeTuples_named_cuts x hx (2 : Fin 6) v 1 s rfl).2.2
    change [v, s] ∈ siftedPrimeTuples x (2 : Fin 6) ↔
      v.Prime ∧ s.Prime ∧ z ≤ (s : ℝ) ∧ s < v ∧ (v : ℝ) < H ∧
        ((v * s : ℕ) : ℝ) < H at hm
    change (u = 1 ∧ [v, s] ∈ siftedPrimeTuples x (2 : Fin 6)) ↔
      (u = 1 ∧ v.Prime ∧ z ≤ (v : ℝ)) ∧ ((u * v : ℕ) : ℝ) < H ∧
        (s.Prime ∧ z ≤ (s : ℝ)) ∧ (s : ℝ) < S ∧ s < v ∧
          ((v * s : ℕ) : ℝ) < H
    rw [hm]
    constructor
    · rintro ⟨rfl, hv, hs, hzs, hsv, hvH, hprod⟩
      have hzv : z ≤ (v : ℝ) := hzs.trans (Nat.cast_le.mpr hsv.le)
      have hsS := hsize (2 : Fin 6) [v, s] (hm.mpr ⟨hv, hs, hzs, hsv, hvH, hprod⟩)
      exact ⟨⟨rfl, hv, hzv⟩, by simpa using hvH, ⟨hs, hzs⟩,
        by simpa [siftedPrimeGroups] using hsS, hsv, hprod⟩
    · rintro ⟨⟨rfl, hv, _⟩, hvH, ⟨hs, hzs⟩, _, hsv, hprod⟩
      exact ⟨rfl, hv, hs, hzs, hsv, by simpa using hvH, hprod⟩
  · have hm := (siftedPrimeTuples_named_cuts x hx (3 : Fin 6) v 1 s rfl).2.2
    change [v, s] ∈ siftedPrimeTuples x (3 : Fin 6) ↔
      v.Prime ∧ s.Prime ∧ z ≤ (s : ℝ) ∧ s < v ∧ (v : ℝ) < H ∧
        B < ((v * s : ℕ) : ℝ) ∧ (s : ℝ) < S at hm
    change (u = 1 ∧ [v, s] ∈ siftedPrimeTuples x (3 : Fin 6)) ↔
      (u = 1 ∧ v.Prime ∧ z ≤ (v : ℝ)) ∧ ((u * v : ℕ) : ℝ) < H ∧
        (s.Prime ∧ z ≤ (s : ℝ)) ∧ (s : ℝ) < S ∧ s < v ∧
          B < ((v * s : ℕ) : ℝ)
    rw [hm]
    constructor
    · rintro ⟨rfl, hv, hs, hzs, hsv, hvH, hprod, hsS⟩
      exact ⟨⟨rfl, hv, hzs.trans (Nat.cast_le.mpr hsv.le)⟩,
        by simpa using hvH, ⟨hs, hzs⟩, hsS, hsv, hprod⟩
    · rintro ⟨⟨rfl, hv, _⟩, hvH, ⟨hs, hzs⟩, hsS, hsv, hprod⟩
      exact ⟨rfl, hv, hs, hzs, hsv, by simpa using hvH, hprod, hsS⟩
  · have hm := (siftedPrimeTuples_named_cuts x hx (4 : Fin 6) u v s True.intro).2.2
    change [v, u, s] ∈ siftedPrimeTuples x (4 : Fin 6) ↔
      u.Prime ∧ v.Prime ∧ s.Prime ∧ z ≤ (s : ℝ) ∧ s < u ∧ u < v ∧
        ((u * v : ℕ) : ℝ) < H ∧ (s : ℝ) < S at hm
    change (True ∧ [v, u, s] ∈ siftedPrimeTuples x (4 : Fin 6)) ↔
      (u.Prime ∧ v.Prime ∧ z ≤ (u : ℝ) ∧ u < v) ∧
        ((u * v : ℕ) : ℝ) < H ∧ (s.Prime ∧ z ≤ (s : ℝ)) ∧ (s : ℝ) < S ∧ s < u
    rw [hm]
    constructor
    · rintro ⟨_, hu, hv, hs, hzs, hsu, huv, hprod, hsS⟩
      exact ⟨⟨hu, hv, hzs.trans (Nat.cast_le.mpr hsu.le), huv⟩,
        hprod, ⟨hs, hzs⟩, hsS, hsu⟩
    · rintro ⟨⟨hu, hv, _hzu, huv⟩, hprod, ⟨hs, hzs⟩, hsS, hsu⟩
      exact ⟨True.intro, hu, hv, hs, hzs, hsu, huv, hprod, hsS⟩
  · have hm := (siftedPrimeTuples_named_cuts x hx (5 : Fin 6) u v s True.intro).2.2
    change [s, u, v] ∈ siftedPrimeTuples x (5 : Fin 6) ↔
      s.Prime ∧ u.Prime ∧ v.Prime ∧ z ≤ (u : ℝ) ∧ u < s ∧ (s : ℝ) < H ∧
        u ≤ v ∧ ((u * v : ℕ) : ℝ) < H ∧ (s : ℝ) < S at hm
    change (True ∧ [s, u, v] ∈ siftedPrimeTuples x (5 : Fin 6)) ↔
      (u.Prime ∧ v.Prime ∧ z ≤ (u : ℝ) ∧ u ≤ v) ∧
        ((u * v : ℕ) : ℝ) < H ∧ (s.Prime ∧ z ≤ (s : ℝ)) ∧ (s : ℝ) < S ∧ u < s
    rw [hm]
    constructor
    · rintro ⟨_, hs, hu, hv, hzu, hus, _hsH, huv, hprod, hsS⟩
      exact ⟨⟨hu, hv, hzu, huv⟩, hprod,
        ⟨hs, hzu.trans (Nat.cast_le.mpr hus.le)⟩, hsS, hus⟩
    · rintro ⟨⟨hu, hv, hzu, huv⟩, hprod, ⟨hs, _hzs⟩, hsS, hus⟩
      exact ⟨True.intro, hs, hu, hv, hzu, hus, hsS.trans hSH, huv, hprod, hsS⟩

open Classical in
theorem siftedPrimeTuples_named_enumeration
    (x : ℝ) (hx : 1 < x) (l : Fin 6) (U : ℕ)
    (hU : ⌈x ^ ((41361 : ℝ) / 100000)⌉₊ ≤ U) (hUone : 1 ≤ U)
    (w : List ℕ → ℝ) :
    let C := Finset.Icc 1 U
    let ps (p q s : ℕ) : List ℕ := match l.val with
      | 0 => []
      | 1 => [p]
      | 2 => [p, s]
      | 3 => [p, s]
      | 4 => [q, p, s]
      | _ => [s, p, q]
    (∑ zs ∈ siftedPrimeTuples x l, w zs) =
      ∑ p ∈ C, ∑ q ∈ C, ∑ s ∈ C,
        if (match l.val with
          | 0 => p = 1 ∧ q = 1 ∧ s = 1
          | 1 => q = 1 ∧ s = 1
          | 2 => q = 1
          | 3 => q = 1
          | _ => True) ∧ ps p q s ∈ siftedPrimeTuples x l then
            w (ps p q s)
        else 0 := by
  intro C ps
  have hone : 1 ∈ C := Finset.mem_Icc.mpr ⟨le_refl _, hUone⟩
  have hentries (zs : List ℕ) (hzs : zs ∈ siftedPrimeTuples x l) :
      ∀ p ∈ zs, p ∈ C := by
    obtain ⟨_, _, _, hR, hS, hprime⟩ := siftedPrimeTuples_group_bounds x hx l zs hzs
    have hSle : x ^ (1 - (34941 : ℝ) / 100000) /
        x ^ ((41361 : ℝ) / 100000) ≤ x ^ ((41361 : ℝ) / 100000) := by
      rw [← Real.rpow_sub (zero_lt_one.trans hx)]
      exact Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num)
    have htake (k p : ℕ) (hp : p ∈ zs.take k) : p ≤ (zs.take k).prod :=
      List.single_le_prod (fun q hq =>
        (hprime q (List.mem_of_mem_take hq)).1.one_le) p hp
    have hdrop (k p : ℕ) (hp : p ∈ zs.drop k) : p ≤ (zs.drop k).prod :=
      List.single_le_prod (fun q hq =>
        (hprime q (List.mem_of_mem_drop hq)).1.one_le) p hp
    intro p hp
    have hloc (k : ℕ) : p ∈ zs.take k ∨ p ∈ zs.drop k := by
      rw [← List.mem_append, List.take_append_drop]
      exact hp
    have hpH : (p : ℝ) < x ^ ((41361 : ℝ) / 100000) := by
      by_cases hl : l.val = 5
      · rcases hloc 1 with ht | hd
        · have hle : p ≤ (siftedPrimeGroups l zs).2 := by
            simpa only [siftedPrimeGroups, ite_eq_left hl] using htake 1 p ht
          exact (Nat.cast_le.mpr hle).trans_lt (hS.trans_le hSle)
        · have hle : p ≤ (siftedPrimeGroups l zs).1 := by
            simpa only [siftedPrimeGroups, ite_eq_left hl] using hdrop 1 p hd
          exact (Nat.cast_le.mpr hle).trans_lt hR
      · rcases hloc (if l.val = 4 then 2 else 1) with ht | hd
        · have hle : p ≤ (siftedPrimeGroups l zs).1 := by
            simpa only [siftedPrimeGroups, ite_eq_right hl] using
              htake (if l.val = 4 then 2 else 1) p ht
          exact (Nat.cast_le.mpr hle).trans_lt hR
        · have hle : p ≤ (siftedPrimeGroups l zs).2 := by
            simpa only [siftedPrimeGroups, ite_eq_right hl] using
              hdrop (if l.val = 4 then 2 else 1) p hd
          exact (Nat.cast_le.mpr hle).trans_lt (hS.trans_le hSle)
    exact Finset.mem_Icc.mpr ⟨(hprime p hp).1.pos, (Nat.lt_ceil.mpr hpH).le.trans hU⟩
  have hshape (zs : List ℕ) (hzs : zs ∈ siftedPrimeTuples x l) :
      match l.val with
      | 0 => zs = []
      | 1 => ∃ p, zs = [p]
      | 2 => ∃ p s, zs = [p, s]
      | 3 => ∃ p s, zs = [p, s]
      | 4 => ∃ p q s, zs = [q, p, s]
      | _ => ∃ p q s, zs = [s, p, q] := by
    have hmem := (mem_siftedPrimeTuples_iff x hx l zs).mp hzs
    fin_cases l <;>
      rcases zs with _ | ⟨p, _ | ⟨q, _ | ⟨s, _ | ⟨t, ts⟩⟩⟩⟩ <;>
      simp at hmem ⊢
  let R : Finset (ℕ × (ℕ × ℕ)) :=
    (C ×ˢ (C ×ˢ C)).filter (fun t =>
      (match l.val with
        | 0 => t.1 = 1 ∧ t.2.1 = 1 ∧ t.2.2 = 1
        | 1 => t.2.1 = 1 ∧ t.2.2 = 1
        | 2 => t.2.1 = 1
        | 3 => t.2.1 = 1
        | _ => True) ∧ ps t.1 t.2.1 t.2.2 ∈ siftedPrimeTuples x l)
  calc
    _ = ∑ t ∈ R, w (ps t.1 t.2.1 t.2.2) := by
      symm
      refine Finset.sum_bij (fun t _ => ps t.1 t.2.1 t.2.2) ?_ ?_ ?_
        (fun _ _ => rfl)
      · intro t ht
        exact (Finset.mem_filter.mp ht).2.2
      · intro t ht t' ht' heq
        have htDummy := (Finset.mem_filter.mp ht).2.1
        have ht'Dummy := (Finset.mem_filter.mp ht').2.1
        rcases t with ⟨p, q, s⟩
        rcases t' with ⟨p', q', s'⟩
        fin_cases l
        · change p = 1 ∧ q = 1 ∧ s = 1 at htDummy
          change p' = 1 ∧ q' = 1 ∧ s' = 1 at ht'Dummy
          exact Prod.ext (htDummy.1.trans ht'Dummy.1.symm)
            (Prod.ext (htDummy.2.1.trans ht'Dummy.2.1.symm)
              (htDummy.2.2.trans ht'Dummy.2.2.symm))
        · change [p] = [p'] at heq
          change q = 1 ∧ s = 1 at htDummy
          change q' = 1 ∧ s' = 1 at ht'Dummy
          exact Prod.ext (List.cons.inj heq).1
            (Prod.ext (htDummy.1.trans ht'Dummy.1.symm)
              (htDummy.2.trans ht'Dummy.2.symm))
        · change [p, s] = [p', s'] at heq
          change q = 1 at htDummy
          change q' = 1 at ht'Dummy
          obtain ⟨hpp, htail⟩ := List.cons.inj heq
          exact Prod.ext hpp (Prod.ext (htDummy.trans ht'Dummy.symm)
            (List.cons.inj htail).1)
        · change [p, s] = [p', s'] at heq
          change q = 1 at htDummy
          change q' = 1 at ht'Dummy
          obtain ⟨hpp, htail⟩ := List.cons.inj heq
          exact Prod.ext hpp (Prod.ext (htDummy.trans ht'Dummy.symm)
            (List.cons.inj htail).1)
        · change [q, p, s] = [q', p', s'] at heq
          obtain ⟨hqq, htail⟩ := List.cons.inj heq
          obtain ⟨hpp, hlast⟩ := List.cons.inj htail
          exact Prod.ext hpp (Prod.ext hqq (List.cons.inj hlast).1)
        · change [s, p, q] = [s', p', q'] at heq
          obtain ⟨hss, htail⟩ := List.cons.inj heq
          obtain ⟨hpp, hlast⟩ := List.cons.inj htail
          exact Prod.ext hpp (Prod.ext (List.cons.inj hlast).1 hss)
      · intro zs hzs
        have hzC := hentries zs hzs
        have hzshape := hshape zs hzs
        have hmk (p q s : ℕ) (hp : p ∈ C) (hq : q ∈ C) (hs : s ∈ C)
            (hdummy : match l.val with
              | 0 => p = 1 ∧ q = 1 ∧ s = 1
              | 1 => q = 1 ∧ s = 1
              | 2 => q = 1
              | 3 => q = 1
              | _ => True)
            (heq : ps p q s = zs) :
            ∃ t, ∃ _ht : t ∈ R, ps t.1 t.2.1 t.2.2 = zs := by
          refine ⟨(p, (q, s)), Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hp, Finset.mem_product.mpr ⟨hq, hs⟩⟩,
              ⟨hdummy, ?_⟩⟩, heq⟩
          rw [heq]
          exact hzs
        fin_cases l
        · change zs = [] at hzshape
          subst zs
          exact hmk 1 1 1 hone hone hone (by simp) (by simp [ps])
        · change ∃ p, zs = [p] at hzshape
          obtain ⟨p, rfl⟩ := hzshape
          exact hmk p 1 1 (hzC p (by simp)) hone hone (by simp) (by simp [ps])
        · change ∃ p s, zs = [p, s] at hzshape
          obtain ⟨p, s, rfl⟩ := hzshape
          exact hmk p 1 s (hzC p (by simp)) hone (hzC s (by simp))
            rfl (by simp [ps])
        · change ∃ p s, zs = [p, s] at hzshape
          obtain ⟨p, s, rfl⟩ := hzshape
          exact hmk p 1 s (hzC p (by simp)) hone (hzC s (by simp))
            rfl (by simp [ps])
        · change ∃ p q s, zs = [q, p, s] at hzshape
          obtain ⟨p, q, s, rfl⟩ := hzshape
          exact hmk p q s (hzC p (by simp)) (hzC q (by simp)) (hzC s (by simp))
            True.intro (by simp [ps])
        · change ∃ p q s, zs = [s, p, q] at hzshape
          obtain ⟨p, q, s, rfl⟩ := hzshape
          exact hmk p q s (hzC p (by simp)) (hzC q (by simp)) (hzC s (by simp))
            True.intro (by simp [ps])
    _ = _ := by simp only [R, Finset.sum_filter, Finset.sum_product]

open Classical in
theorem siftedTheta_restricted_harman_raw_long_identity
    (x : ℝ) (hx : 1 < x) (l : Fin 6) (w : List ℕ → ℝ)
    (n : ℕ) (hn : n ≤ ⌊2 * x⌋₊) :
    let H := x ^ ((41361 : ℝ) / 100000)
    let z := x ^ ((8639 : ℝ) / 50000)
    let M0 := x ^ (1 - (34941 : ℝ) / 100000)
    let C := Finset.Icc 1 ⌊2 * x⌋₊
    let U (ps : List ℕ) : ArithmeticFunction ℝ :=
      ⟨fun r => if r = 0 then 0 else
        if r = (siftedPrimeGroups l ps).1 then 1 else 0, by simp⟩
    let V (ps : List ℕ) : ArithmeticFunction ℝ :=
      ⟨fun s => if s = 0 then 0 else
        if s = (siftedPrimeGroups l ps).2 then 1 else 0, by simp⟩
    let rawLong : ℝ := ∑ ps ∈ siftedPrimeTuples x l,
      let r := (siftedPrimeGroups l ps).1
      let s := (siftedPrimeGroups l ps).2
      w ps * ∑ h ∈ C, ∑ d ∈ C, ∑ k ∈ C,
        if ps.prod * h * d * k = n ∧ 1 < h ∧
            ((max 1 (h.primeFactors.sup id) : ℕ) : ℝ) < z ∧
            ((r * h : ℕ) : ℝ) / (h.minFac : ℝ) < H ∧
            H ≤ ((r * h : ℕ) : ℝ) ∧
            max 1 (d.primeFactors.sup id) < h.minFac ∧
            M0 < ((r * s * h * d : ℕ) : ℝ) then
          (ArithmeticFunction.moebius h : ℝ) * (ArithmeticFunction.moebius d : ℝ)
        else 0
    (∑ ps ∈ siftedPrimeTuples x l, w ps *
      ∑ a ∈ n.divisorsAntidiagonal, ∑ b ∈ a.2.divisorsAntidiagonal,
        ∑ c ∈ b.2.divisorsAntidiagonal, ∑ e ∈ c.2.divisorsAntidiagonal,
          if 1 < c.1 ∧
              ((max 1 (c.1.primeFactors.sup id) : ℕ) : ℝ) < z ∧
              ((a.1 * c.1 : ℕ) : ℝ) / (c.1.minFac : ℝ) < H ∧
              H ≤ ((a.1 * c.1 : ℕ) : ℝ) ∧
              max 1 (e.1.primeFactors.sup id) < c.1.minFac ∧
              M0 < ((a.1 * b.1 * c.1 * e.1 : ℕ) : ℝ) then
            U ps a.1 * V ps b.1 * (ArithmeticFunction.moebius c.1 : ℝ) *
              (ArithmeticFunction.moebius e.1 : ℝ)
          else 0) = rawLong ∧
      siftedTheta x l w n =
        (∑ ps ∈ siftedPrimeTuples x l, w ps *
          (harmanA0 (U ps) (V ps) z M0 *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n) + rawLong := by
  intro H z M0 C U V rawLong
  have hfinite (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (F : ℕ → ℕ → ℝ) :
      (∑ a ∈ n.divisorsAntidiagonal, ∑ b ∈ a.2.divisorsAntidiagonal,
        ∑ c ∈ b.2.divisorsAntidiagonal, ∑ e ∈ c.2.divisorsAntidiagonal,
          if a.1 = r ∧ b.1 = s then F c.1 e.1 else 0) =
        ∑ h ∈ C, ∑ d ∈ C, ∑ k ∈ C,
          if r * s * h * d * k = n then F h d else 0 := by
    let T : Finset (Σ _ : ℕ × ℕ, Σ _ : ℕ × ℕ, Σ _ : ℕ × ℕ, ℕ × ℕ) :=
      (n.divisorsAntidiagonal.sigma (fun a =>
        a.2.divisorsAntidiagonal.sigma (fun b =>
          b.2.divisorsAntidiagonal.sigma (fun c => c.2.divisorsAntidiagonal)))).filter
        (fun v => v.1.1 = r ∧ v.2.1.1 = s)
    let R : Finset (ℕ × (ℕ × ℕ)) :=
      (C ×ˢ (C ×ˢ C)).filter (fun u => r * s * u.1 * u.2.1 * u.2.2 = n)
    let f : (Σ _ : ℕ × ℕ, Σ _ : ℕ × ℕ, Σ _ : ℕ × ℕ, ℕ × ℕ) →
        ℕ × (ℕ × ℕ) := fun v => (v.2.2.1.1, (v.2.2.2.1, v.2.2.2.2))
    calc
      _ = ∑ v ∈ T, F v.2.2.1.1 v.2.2.2.1 := by
        simp only [T, Finset.sum_filter, Finset.sum_sigma]
      _ = ∑ u ∈ R, F u.1 u.2.1 := by
        refine Finset.sum_bij (fun v _ => f v) ?_ ?_ ?_ (fun _ _ => rfl)
        · intro v hv
          obtain ⟨hvT, hvEq⟩ := Finset.mem_filter.mp hv
          obtain ⟨ha, hbc⟩ := Finset.mem_sigma.mp hvT
          obtain ⟨hb, hce⟩ := Finset.mem_sigma.mp hbc
          obtain ⟨hc, he⟩ := Finset.mem_sigma.mp hce
          have htotal : r * s * v.2.2.1.1 * v.2.2.2.1 * v.2.2.2.2 = n := by
            rw [← hvEq.1, ← hvEq.2]
            simp only [Nat.mul_assoc, (Nat.mem_divisorsAntidiagonal.mp he).1,
              (Nat.mem_divisorsAntidiagonal.mp hc).1,
              (Nat.mem_divisorsAntidiagonal.mp hb).1,
              (Nat.mem_divisorsAntidiagonal.mp ha).1]
          have hnpos : 0 < n :=
            Nat.pos_of_ne_zero (Nat.mem_divisorsAntidiagonal.mp ha).2
          have hbox (m : ℕ) (hm : 0 < m) (hmd : m ∣ n) : m ∈ C :=
            Finset.mem_Icc.mpr ⟨hm, (Nat.le_of_dvd hnpos hmd).trans hn⟩
          have hhdiv : v.2.2.1.1 ∣ n := by
            refine ⟨r * s * v.2.2.2.1 * v.2.2.2.2, ?_⟩
            rw [← htotal]
            ring
          have hddiv : v.2.2.2.1 ∣ n := by
            refine ⟨r * s * v.2.2.1.1 * v.2.2.2.2, ?_⟩
            rw [← htotal]
            ring
          have hkdiv : v.2.2.2.2 ∣ n := by
            refine ⟨r * s * v.2.2.1.1 * v.2.2.2.1, ?_⟩
            rw [← htotal]
            ring
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_product.mpr ⟨?_, Finset.mem_product.mpr ⟨?_, ?_⟩⟩,
            htotal⟩
          · exact hbox _
              (Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hc)) hhdiv
          · exact hbox _
              (Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal he)) hddiv
          · exact hbox _
              (Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal he)) hkdiv
        · intro v hv v' hv' heq
          dsimp only [f] at heq
          have hh : v.2.2.1.1 = v'.2.2.1.1 :=
            congrArg (fun u : ℕ × (ℕ × ℕ) => u.1) heq
          have hd : v.2.2.2.1 = v'.2.2.2.1 :=
            congrArg (fun u : ℕ × (ℕ × ℕ) => u.2.1) heq
          have hk : v.2.2.2.2 = v'.2.2.2.2 :=
            congrArg (fun u : ℕ × (ℕ × ℕ) => u.2.2) heq
          obtain ⟨hvT, hvEq⟩ := Finset.mem_filter.mp hv
          obtain ⟨hv'T, hv'Eq⟩ := Finset.mem_filter.mp hv'
          obtain ⟨_ha, hbc⟩ := Finset.mem_sigma.mp hvT
          obtain ⟨hb, hce⟩ := Finset.mem_sigma.mp hbc
          obtain ⟨hc, he⟩ := Finset.mem_sigma.mp hce
          obtain ⟨_ha', hbc'⟩ := Finset.mem_sigma.mp hv'T
          obtain ⟨hb', hce'⟩ := Finset.mem_sigma.mp hbc'
          obtain ⟨hc', he'⟩ := Finset.mem_sigma.mp hce'
          have hctail : v.2.2.1.2 = v'.2.2.1.2 := by
            rw [← (Nat.mem_divisorsAntidiagonal.mp he).1,
              ← (Nat.mem_divisorsAntidiagonal.mp he').1, hd, hk]
          have hbtail : v.2.1.2 = v'.2.1.2 := by
            rw [← (Nat.mem_divisorsAntidiagonal.mp hc).1,
              ← (Nat.mem_divisorsAntidiagonal.mp hc').1, hh, hctail]
          have hatail : v.1.2 = v'.1.2 := by
            rw [← (Nat.mem_divisorsAntidiagonal.mp hb).1,
              ← (Nat.mem_divisorsAntidiagonal.mp hb').1,
              hvEq.2.trans hv'Eq.2.symm, hbtail]
          exact Sigma.ext (Prod.ext (hvEq.1.trans hv'Eq.1.symm) hatail)
            (heq_of_eq (Sigma.ext (Prod.ext (hvEq.2.trans hv'Eq.2.symm) hbtail)
              (heq_of_eq (Sigma.ext (Prod.ext hh hctail) (heq_of_eq (Prod.ext hd hk))))))
        · intro u hu
          obtain ⟨huR, hproduct⟩ := Finset.mem_filter.mp hu
          obtain ⟨hhC, hdkC⟩ := Finset.mem_product.mp huR
          obtain ⟨hdC, hkC⟩ := Finset.mem_product.mp hdkC
          have hhpos : 0 < u.1 := (Finset.mem_Icc.mp hhC).1
          have hdpos : 0 < u.2.1 := (Finset.mem_Icc.mp hdC).1
          have hkpos : 0 < u.2.2 := (Finset.mem_Icc.mp hkC).1
          have hdk : u.2.1 * u.2.2 ≠ 0 := (Nat.mul_pos hdpos hkpos).ne'
          have hhdk : u.1 * (u.2.1 * u.2.2) ≠ 0 :=
            (Nat.mul_pos hhpos (Nat.mul_pos hdpos hkpos)).ne'
          have hshdk : s * (u.1 * (u.2.1 * u.2.2)) ≠ 0 :=
            (Nat.mul_pos hs (Nat.mul_pos hhpos (Nat.mul_pos hdpos hkpos))).ne'
          have hnzero : n ≠ 0 := by
            rw [← hproduct]
            exact (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hr hs) hhpos)
              hdpos) hkpos).ne'
          let v : Σ _ : ℕ × ℕ, Σ _ : ℕ × ℕ, Σ _ : ℕ × ℕ, ℕ × ℕ :=
            ⟨(r, s * (u.1 * (u.2.1 * u.2.2))),
              ⟨(s, u.1 * (u.2.1 * u.2.2)), ⟨(u.1, u.2.1 * u.2.2), u.2⟩⟩⟩
          have hv : v ∈ T := by
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_sigma.mpr ⟨?_,
              Finset.mem_sigma.mpr ⟨?_, Finset.mem_sigma.mpr ⟨?_, ?_⟩⟩⟩, ⟨rfl, rfl⟩⟩
            · exact Nat.mem_divisorsAntidiagonal.mpr
                ⟨by simpa only [Nat.mul_assoc] using hproduct, hnzero⟩
            · exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hshdk⟩
            · exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hhdk⟩
            · exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hdk⟩
          exact ⟨v, hv, rfl⟩
      _ = _ := by
        simp only [R, Finset.sum_filter, Finset.sum_product]
  have hdelta (d : ℕ) (hd : 0 < d) (m : ℕ) :
      (if m = 0 then (0 : ℝ) else if m = d then 1 else 0) =
        if m = d then 1 else 0 := by
    by_cases hm : m = 0 <;> simp [hm, hd.ne]
  have hraw : (∑ ps ∈ siftedPrimeTuples x l, w ps *
      ∑ a ∈ n.divisorsAntidiagonal, ∑ b ∈ a.2.divisorsAntidiagonal,
        ∑ c ∈ b.2.divisorsAntidiagonal, ∑ e ∈ c.2.divisorsAntidiagonal,
          if 1 < c.1 ∧
              ((max 1 (c.1.primeFactors.sup id) : ℕ) : ℝ) < z ∧
              ((a.1 * c.1 : ℕ) : ℝ) / (c.1.minFac : ℝ) < H ∧
              H ≤ ((a.1 * c.1 : ℕ) : ℝ) ∧
              max 1 (e.1.primeFactors.sup id) < c.1.minFac ∧
              M0 < ((a.1 * b.1 * c.1 * e.1 : ℕ) : ℝ) then
            U ps a.1 * V ps b.1 * (ArithmeticFunction.moebius c.1 : ℝ) *
              (ArithmeticFunction.moebius e.1 : ℝ)
          else 0) = rawLong := by
    dsimp only [rawLong]
    apply Finset.sum_congr rfl
    intro ps hps
    apply congrArg (fun t : ℝ => w ps * t)
    let r := (siftedPrimeGroups l ps).1
    let s := (siftedPrimeGroups l ps).2
    obtain ⟨hr, hs, hprod, _, _, _⟩ := siftedPrimeTuples_group_bounds x hx l ps hps
    have hU (a : ℕ) : U ps a = if a = r then 1 else 0 := hdelta _ hr a
    have hV (b : ℕ) : V ps b = if b = s then 1 else 0 := hdelta _ hs b
    let F (h d : ℕ) : ℝ :=
      if 1 < h ∧ ((max 1 (h.primeFactors.sup id) : ℕ) : ℝ) < z ∧
          ((r * h : ℕ) : ℝ) / (h.minFac : ℝ) < H ∧
          H ≤ ((r * h : ℕ) : ℝ) ∧
          max 1 (d.primeFactors.sup id) < h.minFac ∧
          M0 < ((r * s * h * d : ℕ) : ℝ) then
        (ArithmeticFunction.moebius h : ℝ) * (ArithmeticFunction.moebius d : ℝ)
      else 0
    have hpoint (a b h d : ℕ) :
        (if 1 < h ∧ ((max 1 (h.primeFactors.sup id) : ℕ) : ℝ) < z ∧
            ((a * h : ℕ) : ℝ) / (h.minFac : ℝ) < H ∧
            H ≤ ((a * h : ℕ) : ℝ) ∧
            max 1 (d.primeFactors.sup id) < h.minFac ∧
            M0 < ((a * b * h * d : ℕ) : ℝ) then
          U ps a * V ps b * (ArithmeticFunction.moebius h : ℝ) *
            (ArithmeticFunction.moebius d : ℝ) else 0) =
          if a = r ∧ b = s then F h d else 0 := by
      by_cases ha : a = r <;> by_cases hb : b = s <;> simp [hU, hV, ha, hb, F]
    simp_rw [hpoint]
    simpa only [F, r, s, ← ite_and, hprod] using hfinite r s hr hs F
  refine ⟨hraw, ?_⟩
  rw [← hraw]
  simpa only [mul_add, Finset.sum_add_distrib] using
    siftedTheta_restricted_harman_decomposition x hx l w n

open Classical in
theorem sifted_short_harmanA0_arithmetic_identity
    (x : ℝ) (hx : 1 < x) (l : Fin 6) :
    let z := x ^ ((8639 : ℝ) / 50000)
    let M0 := x ^ (1 - (34941 : ℝ) / 100000)
    let U (p : List ℕ) : ArithmeticFunction ℝ :=
      ⟨fun r => if r = 0 then 0 else
        if r = (siftedPrimeGroups l p).1 then 1 else 0, by simp⟩
    let V (p : List ℕ) : ArithmeticFunction ℝ :=
      ⟨fun s => if s = 0 then 0 else
        if s = (siftedPrimeGroups l p).2 then 1 else 0, by simp⟩
    let S0 : ArithmeticFunction ℝ :=
      ⟨fun n => if (n : ℝ) ≤ M0 then
        ∑ ps ∈ siftedPrimeTuples x l, ∑ d ∈ n.divisorsAntidiagonal,
          if d.1 = ps.prod then smallPrimeMobius z d.2 else 0 else 0, by simp⟩
    S0 = ∑ ps ∈ siftedPrimeTuples x l, harmanA0 (U ps) (V ps) z M0 ∧
      S0 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
        ∑ ps ∈ siftedPrimeTuples x l,
          harmanA0 (U ps) (V ps) z M0 *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
  intro z M0 U V S0
  have hdelta (d : ℕ) (hd : 0 < d) (m : ℕ) :
      (if m = 0 then (0 : ℝ) else if m = d then 1 else 0) =
        if m = d then 1 else 0 := by
    by_cases hm : m = 0 <;> simp [hm, hd.ne]
  have hA0 (p : List ℕ) (hp : p ∈ siftedPrimeTuples x l) (m : ℕ) :
      harmanA0 (U p) (V p) z M0 m =
        if (m : ℝ) ≤ M0 then
          ∑ d ∈ m.divisorsAntidiagonal,
            if d.1 = p.prod then smallPrimeMobius z d.2 else 0
        else 0 := by
    obtain ⟨hrpos, hspos, hprod, _, _, _⟩ :=
      siftedPrimeTuples_group_bounds x hx l p hp
    have hU (r : ℕ) : U p r = if r = (siftedPrimeGroups l p).1 then 1 else 0 :=
      hdelta _ hrpos r
    have hV (s : ℕ) : V p s = if s = (siftedPrimeGroups l p).2 then 1 else 0 :=
      hdelta _ hspos s
    have hprodpos : 0 < p.prod := hprod ▸ Nat.mul_pos hrpos hspos
    have hUV (k : ℕ) : (U p * V p) k = if k = p.prod then 1 else 0 := by
      rw [ArithmeticFunction.mul_apply]
      have hpoint (d : ℕ × ℕ) :
          U p d.1 * V p d.2 = if d = siftedPrimeGroups l p then 1 else 0 := by
        simp only [hU, hV, ite_mul, one_mul, zero_mul, Prod.ext_iff, ite_and]
      simp_rw [hpoint]
      rw [Finset.sum_ite_eq']
      by_cases hk : k = p.prod <;>
        simp [Nat.mem_divisorsAntidiagonal, hprod, hk, hprodpos.ne', eq_comm]
    change (if (m : ℝ) ≤ M0 then (U p * V p * smallPrimeMobius z) m else 0) = _
    rw [ArithmeticFunction.mul_apply]
    simp_rw [hUV]
    simp only [ite_mul, one_mul, zero_mul]
  have hshort (m : ℕ) :
      (∑ ps ∈ siftedPrimeTuples x l, harmanA0 (U ps) (V ps) z M0 m) = S0 m := by
    change (∑ ps ∈ siftedPrimeTuples x l, harmanA0 (U ps) (V ps) z M0 m) =
      if (m : ℝ) ≤ M0 then
        ∑ ps ∈ siftedPrimeTuples x l, ∑ d ∈ m.divisorsAntidiagonal,
          if d.1 = ps.prod then smallPrimeMobius z d.2 else 0
      else 0
    by_cases hm : (m : ℝ) ≤ M0
    · rw [ite_eq_left hm]
      exact Finset.sum_congr rfl (fun ps hps => by
        simpa only [ite_eq_left hm] using hA0 ps hps m)
    · rw [ite_eq_right hm]
      exact Finset.sum_eq_zero (fun ps hps => by
        simpa only [ite_eq_right hm] using hA0 ps hps m)
  have hidentity : S0 = ∑ ps ∈ siftedPrimeTuples x l,
      harmanA0 (U ps) (V ps) z M0 := by
    apply ArithmeticFunction.ext
    intro n
    let ev : ArithmeticFunction ℝ →+ ℝ :=
      { toFun := fun F => F n
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    change S0 n = ev (∑ ps ∈ siftedPrimeTuples x l, harmanA0 (U ps) (V ps) z M0)
    rw [map_sum]
    exact (hshort n).symm
  refine ⟨hidentity, ?_⟩
  rw [hidentity, Finset.sum_mul]

#print axioms restricted_harman_long_source_scales
#print axioms siftedPrimeTuples_named_cuts
#print axioms harman_named_factor_cuts
#print axioms siftedPrimeTuples_named_enumeration
#print axioms siftedTheta_restricted_harman_raw_long_identity
#print axioms sifted_short_harmanA0_arithmetic_identity

end PrimeGap182Analytic.Harman

end
