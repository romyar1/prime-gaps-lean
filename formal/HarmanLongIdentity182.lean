import HarmanLongGeometry182

/-!
# Exact independent-factor identity for the actual long remainder

This identifies the restricted difference of sifted theta and its short
Harman convolution with the actual finite product of independent factors.

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
theorem sifted_long_independent_factor_identity (x : ℝ) (hx : 1 < x) (l : Fin 6) :
    let H := x ^ ((41361 : ℝ) / 100000)
    let z := x ^ ((8639 : ℝ) / 50000)
    let M0 := x ^ (1 - (34941 : ℝ) / 100000)
    let S := x ^ (1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000)
    let Bthreshold := x ^ ((58639 : ℝ) / 100000)
    let U := ⌊8 * x⌋₊
    let C := Finset.Icc 1 U
    let A := (Fintype.piFinset (fun _ : Fin 3 => C)).filter (fun a : Fin 3 → ℕ =>
      let u : ℕ := a 0
      let v : ℕ := a 1
      let h : ℕ := a 2
      let r : ℕ := u * v
      let m : ℕ := r * h
      m ≤ U ∧
        (match l.val with
          | 0 => u = 1 ∧ v = 1
          | 1 | 2 | 3 => u = 1 ∧ v.Prime ∧ z ≤ (v : ℝ)
          | 4 => u.Prime ∧ v.Prime ∧ z ≤ (u : ℝ) ∧ u < v
          | _ => u.Prime ∧ v.Prime ∧ z ≤ (u : ℝ) ∧ u ≤ v) ∧
        (r : ℝ) < H ∧ 1 < h ∧ ((max 1 (h.primeFactors.sup id) : ℕ) : ℝ) < z ∧
        ((m / h.minFac : ℕ) : ℝ) < H ∧ H ≤ (m : ℝ))
    let B := (Fintype.piFinset (fun _ : Fin 3 => C)).filter (fun b : Fin 3 → ℕ =>
      let s : ℕ := b 0
      let d : ℕ := b 1
      let k : ℕ := b 2
      let n : ℕ := s * d * k
      n ≤ U ∧ (if l.val ≤ 1 then s = 1 else s.Prime ∧ z ≤ (s : ℝ)) ∧ (s : ℝ) < S)
    let feature (a b : Fin 3 → ℕ) : Fin 7 → ℕ :=
      ![a 0 * a 1 * a 2, (a 2).minFac, if l.val ≤ 3 then a 1 else a 0,
        b 0 * b 1 * b 2, b 0 * b 1, max 1 ((b 1).primeFactors.sup id), b 0]
    let Good (f : Fin 7 → ℕ) : Prop :=
      f 5 < f 1 ∧ M0 < ((f 0 * f 4 : ℕ) : ℝ) ∧
        x ≤ ((f 0 * f 3 : ℕ) : ℝ) ∧ ((f 0 * f 3 : ℕ) : ℝ) ≤ 2 * x ∧
        match l.val with
        | 2 => f 6 < f 2 ∧ ((f 2 * f 6 : ℕ) : ℝ) < H
        | 3 => f 6 < f 2 ∧ Bthreshold < ((f 2 * f 6 : ℕ) : ℝ)
        | 4 => f 6 < f 2
        | 5 => f 2 < f 6
        | _ => True
    let S0 : ArithmeticFunction ℝ :=
      ⟨fun n => if (n : ℝ) ≤ M0 then
        ∑ ps ∈ siftedPrimeTuples x l, ∑ d ∈ n.divisorsAntidiagonal,
          if d.1 = ps.prod then smallPrimeMobius z d.2 else 0 else 0, by simp⟩
    (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
      Finsupp.single n
        ((siftedTheta x l (fun _ => 1) n -
          (S0 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ)) =
      ∑ a ∈ A, ∑ b ∈ B,
        Finsupp.single (feature a b 0 * feature a b 3)
          ((if Good (feature a b) then
            (ArithmeticFunction.moebius (a 2) : ℝ) *
              (ArithmeticFunction.moebius (b 1) : ℝ) else 0 : ℝ) : ℂ) := by
  intro H z M0 S Bthreshold U C A B feature Good S0
  let W := Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊
  let C2 := Finset.Icc 1 ⌊2 * x⌋₊
  let cube := Fintype.piFinset (fun _ : Fin 3 => C)
  let ps (u v s : ℕ) : List ℕ := match l.val with
    | 0 => [] | 1 => [v] | 2 => [v, s] | 3 => [v, s]
    | 4 => [v, u, s] | _ => [s, u, v]
  let Dummy (u v s : ℕ) : Prop := match l.val with
    | 0 => u = 1 ∧ v = 1 ∧ s = 1
    | 1 => u = 1 ∧ s = 1 | 2 => u = 1 | 3 => u = 1 | _ => True
  let NamedA (u v : ℕ) : Prop := match l.val with
    | 0 => u = 1 ∧ v = 1
    | 1 | 2 | 3 => u = 1 ∧ v.Prime ∧ z ≤ (v : ℝ)
    | 4 => u.Prime ∧ v.Prime ∧ z ≤ (u : ℝ) ∧ u < v
    | _ => u.Prime ∧ v.Prime ∧ z ≤ (u : ℝ) ∧ u ≤ v
  let NamedB (s : ℕ) : Prop := if l.val ≤ 1 then s = 1 else s.Prime ∧ z ≤ (s : ℝ)
  let Cross (u v s : ℕ) : Prop := match l.val with
    | 2 => s < v ∧ ((v * s : ℕ) : ℝ) < H
    | 3 => s < v ∧ Bthreshold < ((v * s : ℕ) : ℝ)
    | 4 => s < u | 5 => u < s | _ => True
  let RA (u v h : ℕ) : Prop :=
    u * v * h ≤ U ∧ NamedA u v ∧ ((u * v : ℕ) : ℝ) < H ∧ 1 < h ∧
      ((max 1 (h.primeFactors.sup id) : ℕ) : ℝ) < z ∧
      ((u * v * h / h.minFac : ℕ) : ℝ) < H ∧ H ≤ ((u * v * h : ℕ) : ℝ)
  let RB (s d k : ℕ) : Prop := s * d * k ≤ U ∧ NamedB s ∧ (s : ℝ) < S
  let Raw (n : ℕ) (zs : List ℕ) (h d k : ℕ) : Prop :=
    zs.prod * h * d * k = n ∧ 1 < h ∧
      ((max 1 (h.primeFactors.sup id) : ℕ) : ℝ) < z ∧
      (((siftedPrimeGroups l zs).1 * h : ℕ) : ℝ) / (h.minFac : ℝ) < H ∧
      H ≤ (((siftedPrimeGroups l zs).1 * h : ℕ) : ℝ) ∧
      max 1 (d.primeFactors.sup id) < h.minFac ∧
      M0 < (((siftedPrimeGroups l zs).1 * (siftedPrimeGroups l zs).2 * h * d : ℕ) : ℝ)
  let U0 (zs : List ℕ) : ArithmeticFunction ℝ :=
    ⟨fun r => if r = 0 then 0 else
      if r = (siftedPrimeGroups l zs).1 then 1 else 0, by simp⟩
  let V0 (zs : List ℕ) : ArithmeticFunction ℝ :=
    ⟨fun s => if s = 0 then 0 else
      if s = (siftedPrimeGroups l zs).2 then 1 else 0, by simp⟩
  have hxpos : 0 < x := zero_lt_one.trans hx
  have h2nonneg : 0 ≤ 2 * x := by positivity
  have hUone : 1 ≤ U := (Nat.one_le_floor_iff (8 * x)).mpr (by linarith)
  have h2U : ⌊2 * x⌋₊ ≤ U := Nat.floor_mono (by linarith)
  have hU : ⌈H⌉₊ ≤ U := by
    have hHle : H ≤ x := Real.rpow_le_self_of_one_le hx.le (by norm_num)
    have hceil : (⌈H⌉₊ : ℝ) < H + 1 := Nat.ceil_lt_add_one (by positivity)
    exact Nat.le_floor (by linarith)
  have hCsub : C2 ⊆ C := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
      (Finset.mem_Icc.mp hn).2.trans h2U⟩
  have hW (n : ℕ) : n ∈ W ↔ x ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x := by
    simp only [W, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff h2nonneg]
  have hcuts (u v s : ℕ) :
      (Dummy u v s ∧ ps u v s ∈ siftedPrimeTuples x l) ↔
        NamedA u v ∧ ((u * v : ℕ) : ℝ) < H ∧ NamedB s ∧ (s : ℝ) < S ∧
          Cross u v s := harman_named_factor_cuts x hx l u v s
  have hgroups (u v s : ℕ) (hd : Dummy u v s) :
      siftedPrimeGroups l (ps u v s) = (u * v, s) ∧ (ps u v s).prod = u * v * s := by
    fin_cases l
    · change u = 1 ∧ v = 1 ∧ s = 1 at hd
      rcases hd with ⟨rfl, rfl, rfl⟩
      simp [ps, siftedPrimeGroups]
    · change u = 1 ∧ s = 1 at hd
      rcases hd with ⟨rfl, rfl⟩
      simp [ps, siftedPrimeGroups]
    · change u = 1 at hd
      subst u
      simp [ps, siftedPrimeGroups]
    · change u = 1 at hd
      subst u
      simp [ps, siftedPrimeGroups]
    · simp [ps, siftedPrimeGroups, Nat.mul_comm]
      ring
    · simp [ps, siftedPrimeGroups, Nat.mul_comm, Nat.mul_left_comm]
  have hgood (u v h s d k : ℕ) :
      Good (feature ![u, v, h] ![s, d, k]) ↔
        max 1 (d.primeFactors.sup id) < h.minFac ∧
          M0 < (((u * v * h) * (s * d) : ℕ) : ℝ) ∧
          x ≤ (((u * v * h) * (s * d * k) : ℕ) : ℝ) ∧
          (((u * v * h) * (s * d * k) : ℕ) : ℝ) ≤ 2 * x ∧ Cross u v s := by
    fin_cases l <;> rfl
  have henum (w : List ℕ → ℝ) :
      (∑ zs ∈ siftedPrimeTuples x l, w zs) =
        ∑ u ∈ C, ∑ v ∈ C, ∑ s ∈ C,
          if Dummy u v s ∧ ps u v s ∈ siftedPrimeTuples x l then w (ps u v s) else 0 := by
    have he := siftedPrimeTuples_named_enumeration x hx l U hU hUone w
    dsimp only at he
    fin_cases l
    · rw [Finset.sum_comm] at he
      simpa only [Dummy, ps, and_left_comm] using he
    · rw [Finset.sum_comm] at he
      simpa only [Dummy, ps] using he
    · rw [Finset.sum_comm] at he
      simpa only [Dummy, ps] using he
    · rw [Finset.sum_comm] at he
      simpa only [Dummy, ps] using he
    · simpa only [Dummy, ps] using he
    · simpa only [Dummy, ps] using he
  have hcube (f : (Fin 3 → ℕ) → ℝ) :
      (∑ a ∈ cube, f a) = ∑ u ∈ C, ∑ v ∈ C, ∑ h ∈ C, f ![u, v, h] := by
    calc
      _ = ∑ t ∈ C ×ˢ (C ×ˢ C), f ![t.1, t.2.1, t.2.2] := by
        symm
        refine Finset.sum_bij (fun t _ => ![t.1, t.2.1, t.2.2]) ?_ ?_ ?_
          (fun _ _ => rfl)
        · intro t ht
          obtain ⟨hu, hvh⟩ := Finset.mem_product.mp ht
          obtain ⟨hv, hh⟩ := Finset.mem_product.mp hvh
          apply Fintype.mem_piFinset.mpr
          intro i
          fin_cases i <;> assumption
        · intro t _ht t' _ht' heq
          exact Prod.ext (congrFun heq 0)
            (Prod.ext (congrFun heq 1) (congrFun heq 2))
        · intro a ha
          have haC := Fintype.mem_piFinset.mp ha
          refine ⟨(a 0, (a 1, a 2)), Finset.mem_product.mpr
            ⟨haC 0, Finset.mem_product.mpr ⟨haC 1, haC 2⟩⟩, ?_⟩
          funext i
          fin_cases i <;> rfl
      _ = _ := by simp only [Finset.sum_product]
  have hext (n : ℕ) (hn : n ≤ ⌊2 * x⌋₊)
      (zs : List ℕ) (hzs : zs ∈ siftedPrimeTuples x l) :
      (∑ h ∈ C2, ∑ d ∈ C2, ∑ k ∈ C2,
        if Raw n zs h d k then
          (ArithmeticFunction.moebius h : ℝ) * (ArithmeticFunction.moebius d : ℝ) else 0) =
      ∑ h ∈ C, ∑ d ∈ C, ∑ k ∈ C,
        if Raw n zs h d k then
          (ArithmeticFunction.moebius h : ℝ) * (ArithmeticFunction.moebius d : ℝ) else 0 := by
    obtain ⟨hr, hs, hp, _, _, _⟩ := siftedPrimeTuples_group_bounds x hx l zs hzs
    have hpPos : 0 < zs.prod := hp ▸ Nat.mul_pos hr hs
    calc
      _ = ∑ t ∈ C2 ×ˢ (C2 ×ˢ C2),
          if Raw n zs t.1 t.2.1 t.2.2 then
            (ArithmeticFunction.moebius t.1 : ℝ) *
              (ArithmeticFunction.moebius t.2.1 : ℝ) else 0 := by
        simp only [Finset.sum_product]
      _ = ∑ t ∈ C ×ˢ (C ×ˢ C),
          if Raw n zs t.1 t.2.1 t.2.2 then
            (ArithmeticFunction.moebius t.1 : ℝ) *
              (ArithmeticFunction.moebius t.2.1 : ℝ) else 0 := by
        apply Finset.sum_subset
        · intro t ht
          obtain ⟨hh, hdk⟩ := Finset.mem_product.mp ht
          obtain ⟨hd, hk⟩ := Finset.mem_product.mp hdk
          exact Finset.mem_product.mpr ⟨hCsub hh,
            Finset.mem_product.mpr ⟨hCsub hd, hCsub hk⟩⟩
        · intro t ht hnot
          by_cases hraw : Raw n zs t.1 t.2.1 t.2.2
          · obtain ⟨hh, hdk⟩ := Finset.mem_product.mp ht
            obtain ⟨hd, hk⟩ := Finset.mem_product.mp hdk
            have hhpos : 0 < t.1 := (Finset.mem_Icc.mp hh).1
            have hdpos : 0 < t.2.1 := (Finset.mem_Icc.mp hd).1
            have hkpos : 0 < t.2.2 := (Finset.mem_Icc.mp hk).1
            have hnpos : 0 < n := hraw.1 ▸
              Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hpPos hhpos) hdpos) hkpos
            have hbound (m : ℕ) (hm : 0 < m) (hmd : m ∣ n) : m ∈ C2 :=
              Finset.mem_Icc.mpr ⟨hm, (Nat.le_of_dvd hnpos hmd).trans hn⟩
            have hhdiv : t.1 ∣ n := by
              refine ⟨zs.prod * t.2.1 * t.2.2, ?_⟩
              rw [← hraw.1]
              ring
            have hddiv : t.2.1 ∣ n := by
              refine ⟨zs.prod * t.1 * t.2.2, ?_⟩
              rw [← hraw.1]
              ring
            have hkdiv : t.2.2 ∣ n := by
              refine ⟨zs.prod * t.1 * t.2.1, ?_⟩
              rw [← hraw.1]
              ring
            exact (hnot (Finset.mem_product.mpr ⟨hbound _ hhpos hhdiv,
              Finset.mem_product.mpr ⟨hbound _ hdpos hddiv, hbound _ hkpos hkdiv⟩⟩)).elim
          · exact ite_eq_right hraw
      _ = _ := by simp only [Finset.sum_product]
  have hshort (n : ℕ) :
      (S0 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n =
        ∑ zs ∈ siftedPrimeTuples x l,
          (harmanA0 (U0 zs) (V0 zs) z M0 *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n := by
    have he := (sifted_short_harmanA0_arithmetic_identity x hx l).2
    change S0 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
      ∑ zs ∈ siftedPrimeTuples x l,
        harmanA0 (U0 zs) (V0 zs) z M0 *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) at he
    let ev : ArithmeticFunction ℝ →+ ℝ :=
      { toFun := fun F => F n
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    change ev (S0 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) = _
    rw [he, map_sum]
    rfl
  have hrawCoefficient (n : ℕ) (hn : n ≤ ⌊2 * x⌋₊) :
      siftedTheta x l (fun _ => 1) n -
          (S0 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n =
        ∑ zs ∈ siftedPrimeTuples x l, ∑ h ∈ C, ∑ d ∈ C, ∑ k ∈ C,
          if Raw n zs h d k then
            (ArithmeticFunction.moebius h : ℝ) * (ArithmeticFunction.moebius d : ℝ) else 0 := by
    have he := (siftedTheta_restricted_harman_raw_long_identity x hx l (fun _ => 1) n hn).2
    change siftedTheta x l (fun _ => 1) n =
      (∑ zs ∈ siftedPrimeTuples x l, 1 *
        (harmanA0 (U0 zs) (V0 zs) z M0 *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n) +
      ∑ zs ∈ siftedPrimeTuples x l, 1 * ∑ h ∈ C2, ∑ d ∈ C2, ∑ k ∈ C2,
        if Raw n zs h d k then
          (ArithmeticFunction.moebius h : ℝ) * (ArithmeticFunction.moebius d : ℝ) else 0 at he
    simp only [one_mul] at he
    rw [hshort]
    calc
      _ = ∑ zs ∈ siftedPrimeTuples x l, ∑ h ∈ C2, ∑ d ∈ C2, ∑ k ∈ C2,
          if Raw n zs h d k then
            (ArithmeticFunction.moebius h : ℝ) * (ArithmeticFunction.moebius d : ℝ) else 0 := by
        linarith [he]
      _ = _ := Finset.sum_congr rfl (fun zs hzs => hext n hn zs hzs)
  have hgate (n : ℕ) (hn : n ∈ W) (u v h s d k : ℕ) :
      ((Dummy u v s ∧ ps u v s ∈ siftedPrimeTuples x l) ∧ Raw n (ps u v s) h d k) ↔
        RA u v h ∧ RB s d k ∧
          feature ![u, v, h] ![s, d, k] 0 * feature ![u, v, h] ![s, d, k] 3 = n ∧
          Good (feature ![u, v, h] ![s, d, k]) := by
    have hnreal := (hW n).mp hn
    have hnpos : 0 < n := Nat.cast_pos.mp (hxpos.trans_le hnreal.1)
    have hnU : n ≤ U := (Finset.mem_Icc.mp hn).2.trans h2U
    have hquot : ((u * v * h / h.minFac : ℕ) : ℝ) =
        ((u * v * h : ℕ) : ℝ) / (h.minFac : ℝ) :=
      Nat.cast_div_charZero (dvd_mul_of_dvd_right (Nat.minFac_dvd h) (u * v))
    have hbound (heq : (u * v * h) * (s * d * k) = n) :
        u * v * h ≤ U ∧ s * d * k ≤ U := by
      constructor
      · exact (Nat.le_of_dvd hnpos ⟨s * d * k, heq.symm⟩).trans hnU
      · exact (Nat.le_of_dvd hnpos ⟨u * v * h, by rw [← heq]; ring⟩).trans hnU
    constructor
    · rintro ⟨hnamed, hraw⟩
      obtain ⟨hna, hrH, hnb, hsS, hcross⟩ := (hcuts u v s).mp hnamed
      obtain ⟨hgrp, hprod⟩ := hgroups u v s hnamed.1
      dsimp only [Raw] at hraw
      rw [hgrp, hprod] at hraw
      obtain ⟨heq, hhone, hhP, hhquot, hhH, hdP, hM⟩ := hraw
      have hmn : (u * v * h) * (s * d * k) = n := by
        calc
          _ = u * v * s * h * d * k := by ring
          _ = n := heq
      obtain ⟨hmU, hnBU⟩ := hbound hmn
      refine ⟨⟨hmU, hna, hrH, hhone, hhP, by simpa only [hquot] using hhquot, hhH⟩,
        ⟨hnBU, hnb, hsS⟩, hmn, (hgood u v h s d k).mpr ?_⟩
      refine ⟨hdP, ?_, ?_, ?_, hcross⟩
      · convert hM using 1
        congr 1
        ring
      · simpa only [hmn] using hnreal.1
      · simpa only [hmn] using hnreal.2
    · rintro ⟨⟨_hmU, hna, hrH, hhone, hhP, hhquot, hhH⟩,
        ⟨_hnBU, hnb, hsS⟩, heq, hg⟩
      obtain ⟨hdP, hM, _hlo, _hhi, hcross⟩ := (hgood u v h s d k).mp hg
      have hnamed := (hcuts u v s).mpr ⟨hna, hrH, hnb, hsS, hcross⟩
      obtain ⟨hgrp, hprod⟩ := hgroups u v s hnamed.1
      refine ⟨hnamed, ?_⟩
      dsimp only [Raw]
      rw [hgrp, hprod]
      refine ⟨?_, hhone, hhP, by simpa only [hquot] using hhquot, hhH, hdP, ?_⟩
      · change (u * v * h) * (s * d * k) = n at heq
        calc
          _ = (u * v * h) * (s * d * k) := by ring
          _ = n := heq
      · convert hM using 1
        congr 1
        ring
  have hbox (n : ℕ) :
      (∑ a ∈ A, ∑ b ∈ B,
        if feature a b 0 * feature a b 3 = n ∧ Good (feature a b) then
          (ArithmeticFunction.moebius (a 2) : ℝ) *
            (ArithmeticFunction.moebius (b 1) : ℝ) else 0) =
      ∑ u ∈ C, ∑ v ∈ C, ∑ h ∈ C, ∑ s ∈ C, ∑ d ∈ C, ∑ k ∈ C,
        if RA u v h ∧ RB s d k ∧
            feature ![u, v, h] ![s, d, k] 0 * feature ![u, v, h] ![s, d, k] 3 = n ∧
            Good (feature ![u, v, h] ![s, d, k]) then
          (ArithmeticFunction.moebius h : ℝ) * (ArithmeticFunction.moebius d : ℝ) else 0 := by
    change (∑ a ∈ cube.filter (fun a => RA (a 0) (a 1) (a 2)),
      ∑ b ∈ cube.filter (fun b => RB (b 0) (b 1) (b 2)),
        if feature a b 0 * feature a b 3 = n ∧ Good (feature a b) then
          (ArithmeticFunction.moebius (a 2) : ℝ) *
            (ArithmeticFunction.moebius (b 1) : ℝ) else 0) = _
    simp only [Finset.sum_filter]
    simp_rw [hcube, Finset.ite_sum_zero, ← ite_and]
    rfl
  have hreal (n : ℕ) :
      (if n ∈ W then siftedTheta x l (fun _ => 1) n -
          (S0 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n else 0) =
      ∑ a ∈ A, ∑ b ∈ B,
        if feature a b 0 * feature a b 3 = n ∧ Good (feature a b) then
          (ArithmeticFunction.moebius (a 2) : ℝ) *
            (ArithmeticFunction.moebius (b 1) : ℝ) else 0 := by
    by_cases hn : n ∈ W
    · rw [ite_eq_left hn, hrawCoefficient n (Finset.mem_Icc.mp hn).2, hbox]
      calc
        _ = ∑ u ∈ C, ∑ v ∈ C, ∑ s ∈ C,
            if Dummy u v s ∧ ps u v s ∈ siftedPrimeTuples x l then
              ∑ h ∈ C, ∑ d ∈ C, ∑ k ∈ C,
                if Raw n (ps u v s) h d k then
                  (ArithmeticFunction.moebius h : ℝ) *
                    (ArithmeticFunction.moebius d : ℝ) else 0
            else 0 := henum (fun zs => ∑ h ∈ C, ∑ d ∈ C, ∑ k ∈ C,
              if Raw n zs h d k then
                (ArithmeticFunction.moebius h : ℝ) *
                  (ArithmeticFunction.moebius d : ℝ) else 0)
        _ = ∑ u ∈ C, ∑ v ∈ C, ∑ s ∈ C, ∑ h ∈ C, ∑ d ∈ C, ∑ k ∈ C,
            if (Dummy u v s ∧ ps u v s ∈ siftedPrimeTuples x l) ∧
                Raw n (ps u v s) h d k then
              (ArithmeticFunction.moebius h : ℝ) *
                (ArithmeticFunction.moebius d : ℝ) else 0 := by
          simp only [Finset.ite_sum_zero, ← ite_and]
        _ = ∑ u ∈ C, ∑ v ∈ C, ∑ h ∈ C, ∑ s ∈ C, ∑ d ∈ C, ∑ k ∈ C,
            if (Dummy u v s ∧ ps u v s ∈ siftedPrimeTuples x l) ∧
                Raw n (ps u v s) h d k then
              (ArithmeticFunction.moebius h : ℝ) *
                (ArithmeticFunction.moebius d : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro u _hu
          apply Finset.sum_congr rfl
          intro v _hv
          rw [Finset.sum_comm]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro u _hu
          apply Finset.sum_congr rfl
          intro v _hv
          apply Finset.sum_congr rfl
          intro h _hh
          apply Finset.sum_congr rfl
          intro s _hs
          apply Finset.sum_congr rfl
          intro d _hd
          apply Finset.sum_congr rfl
          intro k _hk
          simp only [hgate n hn u v h s d k]
    · rw [ite_eq_right hn]
      symm
      apply Finset.sum_eq_zero
      intro a _ha
      apply Finset.sum_eq_zero
      intro b _hb
      apply ite_eq_right
      rintro ⟨heq, hg⟩
      apply hn
      apply (hW n).mpr
      have hlo : x ≤ ((feature a b 0 * feature a b 3 : ℕ) : ℝ) := hg.2.2.1
      have hhi : ((feature a b 0 * feature a b 3 : ℕ) : ℝ) ≤ 2 * x := hg.2.2.2.1
      exact ⟨heq ▸ hlo, heq ▸ hhi⟩
  ext n
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
  have he := congrArg (fun r : ℝ => (r : ℂ)) (hreal n)
  simpa only [W, Complex.ofReal_sum, apply_ite, Complex.ofReal_zero, ← ite_and] using he

#print axioms sifted_long_independent_factor_identity

end PrimeGap182Analytic.Harman

end
