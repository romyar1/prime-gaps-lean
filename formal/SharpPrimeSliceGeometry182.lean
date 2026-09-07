import SharpPrimeMeasure182

/-! Adapted from Apache-2.0 PrimeGaps186 at the hash checked by the generator.
Literal final-prime motion on [x,2x], with lower prime exponent 0.17278.
-/
noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.SharpMean

theorem prime_prefix_interval_log_geometry
    (x u v : ℝ) (hx : 1 < x) (hu : 1 ≤ u) (hv : v ≤ 2)
    (p : Fin 4 → ℕ)
    (hp : ∀ i, p i ∈
      (Finset.Icc (Nat.ceil (x ^ ((8639 : ℝ) / 50000)))
        (Nat.floor (x ^ ((6 : ℝ) / 25)))).filter Nat.Prime)
    (q : ℕ)
    (hprod : (∏ i, p i) * q ∈
      Finset.Icc (Nat.ceil (u * x)) (Nat.floor (v * x))) :
    let t : Fin 4 → ℝ := fun i => Real.logb x (p i : ℝ)
    let P : ℝ := ∏ i, (p i : ℝ)
    let beta : ℝ := 1 - ∑ i, t i
    let w : ℝ := (q : ℝ) * P / x
    (∀ i, (8639 : ℝ) / 50000 ≤ t i ∧ t i ≤ (6 : ℝ) / 25) ∧
      0 < P ∧
      x ^ (4 * ((8639 : ℝ) / 50000)) ≤ P ∧ P ≤ x ^ ((24 : ℝ) / 25) ∧
      (1 : ℝ) / 25 ≤ beta ∧ beta ≤ 1 - 4 * ((8639 : ℝ) / 50000) ∧
      Real.logb x P = ∑ i, t i ∧
      u ≤ w ∧ w ≤ v ∧
      Real.logb x (q : ℝ) = beta + Real.log w / Real.log x ∧
      0 ≤ Real.log w / Real.log x ∧
      Real.log w / Real.log x ≤ Real.log 2 / Real.log x := by
  let t : Fin 4 → ℝ := fun i => Real.logb x (p i : ℝ)
  let P : ℝ := ∏ i, (p i : ℝ)
  let beta : ℝ := 1 - ∑ i, t i
  let w : ℝ := (q : ℝ) * P / x
  change (∀ i, (8639 : ℝ) / 50000 ≤ t i ∧ t i ≤ (6 : ℝ) / 25) ∧
    0 < P ∧ x ^ (4 * ((8639 : ℝ) / 50000)) ≤ P ∧ P ≤ x ^ ((24 : ℝ) / 25) ∧
    (1 : ℝ) / 25 ≤ beta ∧ beta ≤ 1 - 4 * ((8639 : ℝ) / 50000) ∧
    Real.logb x P = ∑ i, t i ∧ u ≤ w ∧ w ≤ v ∧
    Real.logb x (q : ℝ) = beta + Real.log w / Real.log x ∧
    0 ≤ Real.log w / Real.log x ∧
    Real.log w / Real.log x ≤ Real.log 2 / Real.log x
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hpos (i : Fin 4) : 0 < (p i : ℝ) :=
    Nat.cast_pos.mpr (Finset.mem_filter.mp (hp i)).2.pos
  have ht : ∀ i, (8639 : ℝ) / 50000 ≤ t i ∧ t i ≤ (6 : ℝ) / 25 := by
    intro i
    have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp (hp i)).1
    constructor
    · exact (Real.le_logb_iff_rpow_le hx (hpos i)).mpr (Nat.ceil_le.mp hi.1)
    · exact (Real.logb_le_iff_le_rpow hx (hpos i)).mpr
        ((Nat.le_floor_iff (Real.rpow_pos_of_pos hx0 _).le).mp hi.2)
  have hPpos : 0 < P := Finset.prod_pos (fun i _ => hpos i)
  have hlog : Real.logb x P = ∑ i, t i :=
    Real.logb_prod Finset.univ (fun i : Fin 4 => (p i : ℝ))
      (fun i _ => (hpos i).ne')
  have hsum : 4 * ((8639 : ℝ) / 50000) ≤ ∑ i, t i ∧
      (∑ i, t i) ≤ (24 : ℝ) / 25 := by
    simp only [Fin.sum_univ_four]
    constructor <;> linarith [(ht 0).1, (ht 1).1, (ht 2).1, (ht 3).1,
      (ht 0).2, (ht 1).2, (ht 2).2, (ht 3).2]
  have hPlo : x ^ (4 * ((8639 : ℝ) / 50000)) ≤ P :=
    (Real.le_logb_iff_rpow_le hx hPpos).mp (by rw [hlog]; exact hsum.1)
  have hPhi : P ≤ x ^ ((24 : ℝ) / 25) :=
    (Real.logb_le_iff_le_rpow hx hPpos).mp (by rw [hlog]; exact hsum.2)
  have hbetalo : (1 : ℝ) / 25 ≤ beta := by dsimp only [beta]; linarith [hsum.2]
  have hbetahi : beta ≤ 1 - 4 * ((8639 : ℝ) / 50000) := by
    dsimp only [beta]
    linarith [hsum.1]
  have huxpos : 0 < u * x := mul_pos (zero_lt_one.trans_le hu) hx0
  have hNpos : 0 < (∏ i, p i) * q :=
    (Nat.ceil_pos.mpr huxpos).trans_le (Finset.mem_Icc.mp hprod).1
  have hq0 : q ≠ 0 := by
    intro hq
    simp only [hq, mul_zero, lt_self_iff_false] at hNpos
  have hqpos : 0 < (q : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hq0)
  have hvx : 0 ≤ v * x :=
    (Nat.pos_of_floor_pos (hNpos.trans_le (Finset.mem_Icc.mp hprod).2)).le
  have hlow : u * x ≤ (q : ℝ) * P := by
    simpa only [Nat.cast_mul, Nat.cast_prod, P, mul_comm] using
      Nat.ceil_le.mp (Finset.mem_Icc.mp hprod).1
  have hhigh : (q : ℝ) * P ≤ v * x := by
    simpa only [Nat.cast_mul, Nat.cast_prod, P, mul_comm] using
      (Nat.le_floor_iff hvx).mp (Finset.mem_Icc.mp hprod).2
  have hwlo : u ≤ w := (le_div_iff₀ hx0).mpr hlow
  have hwhi : w ≤ v := (div_le_iff₀ hx0).mpr hhigh
  have hwone : 1 ≤ w := hu.trans hwlo
  have hwtwo : w ≤ 2 := hwhi.trans hv
  have hwpos : 0 < w := zero_lt_one.trans_le hwone
  have hlogw : Real.logb x w = Real.logb x (q : ℝ) + (∑ i, t i) - 1 := by
    dsimp only [w]
    rw [Real.logb_div (mul_ne_zero hqpos.ne' hPpos.ne') hx0.ne',
      Real.logb_mul hqpos.ne' hPpos.ne', hlog, Real.logb_self_eq_one hx]
  have hlast : Real.logb x (q : ℝ) = beta + Real.log w / Real.log x := by
    change Real.logb x (q : ℝ) = beta + Real.logb x w
    dsimp only [beta]
    linarith [hlogw]
  refine ⟨ht, hPpos, hPlo, hPhi, hbetalo, hbetahi, hlog, hwlo, hwhi, hlast, ?_, ?_⟩
  · exact div_nonneg (Real.log_nonneg hwone) (Real.log_pos hx).le
  · exact div_le_div_of_nonneg_right (Real.log_le_log hwpos hwtwo) (Real.log_pos hx).le


#print axioms prime_prefix_interval_log_geometry
end PrimeGap182Analytic.SharpMean
