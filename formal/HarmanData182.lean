import PrimeGaps186

/-! The actual six Buchstab tuple regions at a = .41361, I = .34941 and
lambda = .17278. Adapted from Apache-2.0 PrimeGaps186 at the source hash
checked by scripts/build_harman_data.py. All factor-size conclusions and
the exact restricted Harman identity are rechecked at these parameters.
No distribution or minorant decomposition is assumed here. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

noncomputable def siftedPrimeTuples (x : ℝ) (j : Fin 6) :
    Finset (List ℕ) := by
  classical
  let a : ℝ := 41361 / 100000
  let b : ℝ := 58639 / 100000
  let c : ℝ := 34941 / 100000
  let xi : ℝ := 8639 / 50000
  let zeta : ℝ := 1 - c - a
  let alpha (p : ℕ) : ℝ := Real.logb x (p : ℝ)
  let box (k : ℕ) : Finset (Fin k → ℕ) :=
    Fintype.piFinset (fun _ => Nat.primesBelow (Nat.ceil (x ^ a)))
  exact match j.val with
    | 0 => {[]}
    | 1 => ((box 1).filter fun p =>
        xi ≤ alpha (p 0) ∧ alpha (p 0) < a).image List.ofFn
    | 2 => ((box 2).filter fun p =>
        xi ≤ alpha (p 1) ∧ alpha (p 1) < alpha (p 0) ∧
        alpha (p 0) < a ∧ alpha (p 0) + alpha (p 1) < a).image List.ofFn
    | 3 => ((box 2).filter fun p =>
        xi ≤ alpha (p 1) ∧ alpha (p 1) < alpha (p 0) ∧
        alpha (p 0) < a ∧ b < alpha (p 0) + alpha (p 1) ∧
        alpha (p 1) < zeta).image List.ofFn
    | 4 => ((box 3).filter fun p =>
        xi ≤ alpha (p 2) ∧ alpha (p 2) < alpha (p 1) ∧
        alpha (p 1) < alpha (p 0) ∧ alpha (p 0) < a ∧
        alpha (p 0) + alpha (p 1) < a ∧ alpha (p 2) < zeta).image List.ofFn
    | _ => ((box 3).filter fun p =>
        xi ≤ alpha (p 1) ∧ alpha (p 1) < alpha (p 0) ∧
        alpha (p 0) < a ∧ alpha (p 1) ≤ alpha (p 2) ∧
        alpha (p 1) + alpha (p 2) < a ∧ alpha (p 0) < zeta).image List.ofFn

/--
The two factor products assigned to a sifted prime tuple. Region `5` groups the tail against the
first entry; region `4` groups the first two entries against the rest; the other regions split
after the first entry.
-/
def siftedPrimeGroups (j : Fin 6) (p : List ℕ) : ℕ × ℕ :=
  if j.val = 5 then
    ((p.drop 1).prod, (p.take 1).prod)
  else
    let k := if j.val = 4 then 2 else 1
    ((p.take k).prod, (p.drop k).prod)

/--
The weighted count of factorizations of `n` into a tuple from sifted region `j` and a cofactor
rough at level `x^(8639 / 50000)`. Each tuple contributes its weight `w p`.
-/
noncomputable def siftedTheta (x : ℝ) (j : Fin 6)
    (w : List ℕ → ℝ) : ArithmeticFunction ℝ := by
  classical
  exact ⟨fun n =>
    ∑ p ∈ siftedPrimeTuples x j, ∑ d ∈ n.divisorsAntidiagonal,
      if d.1 = p.prod then
        w p * roughWeight (x ^ ((8639 : ℝ) / 50000)) d.2
      else 0, by simp⟩

theorem mem_siftedPrimeTuples_iff
    (x : ℝ) (hx : 1 < x) (j : Fin 6) (p : List ℕ) :
    let a : ℝ := 41361 / 100000
    let b : ℝ := 58639 / 100000
    let c : ℝ := 34941 / 100000
    let xi : ℝ := 8639 / 50000
    let zeta : ℝ := 1 - c - a
    let alpha (q : ℕ) : ℝ := Real.logb x (q : ℝ)
    p ∈ siftedPrimeTuples x j ↔
      match j.val, p with
      | 0, [] => True
      | 1, [p1] =>
          p1.Prime ∧ xi ≤ alpha p1 ∧ alpha p1 < a
      | 2, [p1, p2] =>
          p1.Prime ∧ p2.Prime ∧ xi ≤ alpha p2 ∧ alpha p2 < alpha p1 ∧
          alpha p1 < a ∧ alpha p1 + alpha p2 < a
      | 3, [p1, p2] =>
          p1.Prime ∧ p2.Prime ∧ xi ≤ alpha p2 ∧ alpha p2 < alpha p1 ∧
          alpha p1 < a ∧ b < alpha p1 + alpha p2 ∧ alpha p2 < zeta
      | 4, [p1, p2, p3] =>
          p1.Prime ∧ p2.Prime ∧ p3.Prime ∧
          xi ≤ alpha p3 ∧ alpha p3 < alpha p2 ∧ alpha p2 < alpha p1 ∧
          alpha p1 < a ∧ alpha p1 + alpha p2 < a ∧ alpha p3 < zeta
      | 5, [p2, p3, p4] =>
          p2.Prime ∧ p3.Prime ∧ p4.Prime ∧
          xi ≤ alpha p3 ∧ alpha p3 < alpha p2 ∧ alpha p2 < a ∧
          alpha p3 ≤ alpha p4 ∧ alpha p3 + alpha p4 < a ∧ alpha p2 < zeta
      | _, _ => False := by
  dsimp only
  have hbox (q : ℕ) :
      q ∈ Nat.primesBelow (Nat.ceil (x ^ ((41361 : ℝ) / 100000))) ↔
        q.Prime ∧ Real.logb x (q : ℝ) < (41361 : ℝ) / 100000 := by
    rw [Nat.mem_primesBelow, Nat.lt_ceil, and_comm]
    exact and_congr_right fun hq =>
      (Real.logb_lt_iff_lt_rpow hx (Nat.cast_pos.mpr hq.pos)).symm
  fin_cases j <;>
    rcases p with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, ps⟩⟩⟩⟩ <;>
    simp [siftedPrimeTuples, Finset.mem_image, Finset.mem_filter,
      Fintype.mem_piFinset, Fin.exists_fin_succ_pi, Fin.exists_fin_zero_pi,
      Fin.forall_fin_succ, hbox]
  all_goals grind

theorem siftedPrimeTuples_group_bounds
    (x : ℝ) (hx : 1 < x) (j : Fin 6) (p : List ℕ)
    (hp : p ∈ siftedPrimeTuples x j) :
    let g := siftedPrimeGroups j p
    0 < g.1 ∧ 0 < g.2 ∧ g.1 * g.2 = p.prod ∧
      (g.1 : ℝ) < x ^ ((41361 : ℝ) / 100000) ∧
      (g.2 : ℝ) <
        x ^ (1 - (34941 : ℝ) / 100000) / x ^ ((41361 : ℝ) / 100000) ∧
      ∀ q ∈ p, q.Prime ∧ x ^ ((8639 : ℝ) / 50000) ≤ (q : ℝ) := by
  have hlt (q : ℕ) (hq : 0 < q) {s : ℝ}
      (h : Real.logb x (q : ℝ) < s) : (q : ℝ) < x ^ s :=
    (Real.logb_lt_iff_lt_rpow hx (Nat.cast_pos.mpr hq)).mp h
  have hlo (q : ℕ) (hq : 0 < q)
      (h : (8639 : ℝ) / 50000 ≤ Real.logb x (q : ℝ)) :
      x ^ ((8639 : ℝ) / 50000) ≤ (q : ℝ) :=
    (Real.le_logb_iff_rpow_le hx (Nat.cast_pos.mpr hq)).mp h
  have hmul (q r : ℕ) (hq : 0 < q) (hr : 0 < r) {s : ℝ}
      (h : Real.logb x (q : ℝ) + Real.logb x (r : ℝ) < s) :
      (q : ℝ) * (r : ℝ) < x ^ s := by
    apply (Real.logb_lt_iff_lt_rpow hx (by positivity)).mp
    rwa [Real.logb_mul (by positivity) (by positivity)]
  have hmem := (mem_siftedPrimeTuples_iff x hx j p).mp hp
  dsimp only at hmem ⊢
  rw [← Real.rpow_sub (zero_lt_one.trans hx)]
  have ha : (1 : ℝ) < x ^ ((41361 : ℝ) / 100000) :=
    Real.one_lt_rpow hx (by norm_num)
  have hs : (1 : ℝ) < x ^ (1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000) :=
    Real.one_lt_rpow hx (by norm_num)
  fin_cases j <;>
    rcases p with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, ps⟩⟩⟩⟩ <;>
    simp only at hmem
  · simp [siftedPrimeGroups, ha, hs]
  · rcases hmem with ⟨hp1, hxi, htop⟩
    simp [siftedPrimeGroups, hs, hp1.pos, hp1, hlt p1 hp1.pos htop, hlo p1 hp1.pos hxi]
  · rcases hmem with ⟨hp1, hp2, hxi, h21, htop, hsum⟩
    have hR := hlt p1 hp1.pos htop
    have hS := hlt p2 hp2.pos
      (show Real.logb x (p2 : ℝ) <
        1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000 by linarith)
    have hL1 := hlo p1 hp1.pos (hxi.trans h21.le)
    have hL2 := hlo p2 hp2.pos hxi
    simp [siftedPrimeGroups, hp1.pos, hp2.pos, hp1, hp2, hR, hS, hL1, hL2]
  · rcases hmem with ⟨hp1, hp2, hxi, h21, htop, _, hcap⟩
    simp [siftedPrimeGroups, hp1.pos, hp2.pos, hp1, hp2,
      hlt p1 hp1.pos htop, hlt p2 hp2.pos hcap,
      hlo p1 hp1.pos (hxi.trans h21.le), hlo p2 hp2.pos hxi]
  · rcases hmem with ⟨hp1, hp2, hp3, hxi, h32, h21, _, hsum, hcap⟩
    have hR := hmul p1 p2 hp1.pos hp2.pos hsum
    have hS := hlt p3 hp3.pos hcap
    have hL1 := hlo p1 hp1.pos ((hxi.trans h32.le).trans h21.le)
    have hL2 := hlo p2 hp2.pos (hxi.trans h32.le)
    have hL3 := hlo p3 hp3.pos hxi
    simp [siftedPrimeGroups, hp1.pos, hp2.pos, hp3.pos, hp1, hp2, hp3,
      hR, hS, hL1, hL2, hL3, mul_assoc]
  · rcases hmem with ⟨hp1, hp2, hp3, hxi, h21, _, h23, hsum, hcap⟩
    have hR := hmul p2 p3 hp2.pos hp3.pos hsum
    have hS := hlt p1 hp1.pos hcap
    have hL1 := hlo p1 hp1.pos (hxi.trans h21.le)
    have hL2 := hlo p2 hp2.pos hxi
    have hL3 := hlo p3 hp3.pos (hxi.trans h23)
    simp [siftedPrimeGroups, hp1.pos, hp2.pos, hp3.pos, hp1, hp2, hp3,
      hR, hS, hL1, hL2, hL3, mul_comm]

open Classical in
theorem siftedTheta_restricted_harman_decomposition
    (x : ℝ) (hx : 1 < x) (j : Fin 6)
    (w : List ℕ → ℝ) (n : ℕ) :
    let H := x ^ ((41361 : ℝ) / 100000)
    let z := x ^ ((8639 : ℝ) / 50000)
    let M0 := x ^ (1 - (34941 : ℝ) / 100000)
    let U (p : List ℕ) : ArithmeticFunction ℝ :=
      ⟨fun r => if r = 0 then 0 else
        if r = (siftedPrimeGroups j p).1 then 1 else 0, by simp⟩
    let V (p : List ℕ) : ArithmeticFunction ℝ :=
      ⟨fun s => if s = 0 then 0 else
        if s = (siftedPrimeGroups j p).2 then 1 else 0, by simp⟩
    siftedTheta x j w n =
      ∑ p ∈ siftedPrimeTuples x j, w p *
        ((harmanA0 (U p) (V p) z M0 *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n +
          ∑ a ∈ n.divisorsAntidiagonal,
            ∑ b ∈ a.2.divisorsAntidiagonal,
              ∑ c ∈ b.2.divisorsAntidiagonal,
                ∑ e ∈ c.2.divisorsAntidiagonal,
                  if 1 < c.1 ∧
                      ((max 1 (c.1.primeFactors.sup id) : ℕ) : ℝ) < z ∧
                      ((a.1 * c.1 : ℕ) : ℝ) / (c.1.minFac : ℝ) < H ∧
                      H ≤ ((a.1 * c.1 : ℕ) : ℝ) ∧
                      max 1 (e.1.primeFactors.sup id) < c.1.minFac ∧
                      M0 < ((a.1 * b.1 * c.1 * e.1 : ℕ) : ℝ) then
                    U p a.1 * V p b.1 * (ArithmeticFunction.moebius c.1 : ℝ) *
                      (ArithmeticFunction.moebius e.1 : ℝ)
                  else 0) := by
  intro H z M0 U V
  have hH : 0 < H := Real.rpow_pos_of_pos (zero_lt_one.trans hx) _
  have hz : 1 < z := Real.one_lt_rpow hx (by norm_num)
  have hdelta (d : ℕ) (hd : 0 < d) (m : ℕ) :
      (if m = 0 then (0 : ℝ) else if m = d then 1 else 0) =
        if m = d then 1 else 0 := by
    by_cases hm : m = 0 <;> simp [hm, hd.ne]
  change (∑ p ∈ siftedPrimeTuples x j, ∑ d ∈ n.divisorsAntidiagonal,
    if d.1 = p.prod then w p * roughWeight z d.2 else 0) = _
  apply Finset.sum_congr rfl
  intro p hp
  rcases siftedPrimeTuples_group_bounds x hx j p hp with
    ⟨hrpos, hspos, hprod, hrH, hsH, _⟩
  have hU (r : ℕ) : U p r = if r = (siftedPrimeGroups j p).1 then 1 else 0 :=
    hdelta _ hrpos r
  have hV (s : ℕ) : V p s = if s = (siftedPrimeGroups j p).2 then 1 else 0 :=
    hdelta _ hspos s
  have hprodpos : 0 < p.prod := hprod ▸ Nat.mul_pos hrpos hspos
  have hUV (m : ℕ) : (U p * V p) m = if m = p.prod then 1 else 0 := by
    rw [ArithmeticFunction.mul_apply]
    have hpoint (d : ℕ × ℕ) :
        U p d.1 * V p d.2 = if d = siftedPrimeGroups j p then 1 else 0 := by
      simp only [hU, hV, ite_mul, one_mul, zero_mul, Prod.ext_iff, ite_and]
    simp_rw [hpoint]
    rw [Finset.sum_ite_eq']
    by_cases hm : m = p.prod <;>
      simp [Nat.mem_divisorsAntidiagonal, hprod, hm, hprodpos.ne', eq_comm]
  have hu : ∀ r, U p r ≠ 0 → (r : ℝ) < H := by
    intro r hr
    simp only [hU, ite_ne_right_iff] at hr
    simpa only [hr] using hrH
  have hv : ∀ s, V p s ≠ 0 → (s : ℝ) < M0 / H := by
    intro s hs
    simp only [hV, ite_ne_right_iff] at hs
    simpa only [hs] using hsH
  rw [← restricted_harman_decomposition (U p) (V p) H z M0 hH hz hu hv n,
    ArithmeticFunction.mul_apply, Finset.mul_sum]
  simp only [hUV, ite_mul, one_mul, zero_mul, mul_ite, mul_zero]


#print axioms mem_siftedPrimeTuples_iff
#print axioms siftedPrimeTuples_group_bounds
#print axioms siftedTheta_restricted_harman_decomposition

end PrimeGap182Analytic.Harman
