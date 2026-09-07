import SharpMeanRegion182

/-! Exact reindexing of the sharp residual into four-prime prefixes and
one final prime. The literal integer product in [x,2x] is retained. -/

noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Filter MeasureTheory Set PrimeGap186

namespace PrimeGap182Analytic.SharpMean

def sharpPrimeCut (x : ℝ) (p : Fin 5 → ℕ) : Prop :=
  Function.Injective p ∧ sharpCoreStrict (fun i => Real.logb x (p i : ℝ))

theorem prime_log_pair_iff (x : ℝ) (hx : 1 < x) (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) :
    Real.logb x (p : ℝ) + Real.logb x (q : ℝ) < 41361 / 100000 ↔
      (p : ℝ) * (q : ℝ) < x ^ ((41361 : ℝ) / 100000) := by
  have hp0 : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hq0 : 0 < (q : ℝ) := Nat.cast_pos.mpr hq.pos
  rw [← Real.logb_mul hp0.ne' hq0.ne']
  exact Real.logb_lt_iff_lt_rpow hx (mul_pos hp0 hq0)

theorem sharpPrimeCut_iff (x : ℝ) (hx : 1 < x) (p : Fin 5 → ℕ)
    (hp : ∀ i, (p i).Prime) (hprod : x ≤ (∏ i, (p i : ℝ))) :
    sharpPrimeCut x p ↔ Function.Injective p ∧ sharpResidualOrder 0 p ∧
      (∀ i j : Fin 5, i < j → (p i : ℝ) * (p j : ℝ) < x ^ ((41361 : ℝ) / 100000)) := by
  have hord : sharpResidualOrder 0 (fun i => Real.logb x (p i : ℝ)) ↔
      sharpResidualOrder 0 p := by
    have hlog (i j : Fin 5) :
        Real.logb x (p i : ℝ) < Real.logb x (p j : ℝ) ↔ p i < p j := by
      rw [lt_iff_not_ge, Real.logb_le_logb hx (Nat.cast_pos.mpr (hp j).pos)
        (Nat.cast_pos.mpr (hp i).pos), Nat.cast_le, not_le]
    simp only [sharpResidualOrder, hlog]
  have hpair : (∀ i j : Fin 5, i < j →
      Real.logb x (p i : ℝ) + Real.logb x (p j : ℝ) < 41361 / 100000) ↔
      (∀ i j : Fin 5, i < j → (p i : ℝ) * (p j : ℝ) < x ^ ((41361 : ℝ) / 100000)) := by
    exact forall_congr' fun i => forall_congr' fun j =>
      imp_congr_right fun _ => prime_log_pair_iff x hx (p i) (p j) (hp i) (hp j)
  simp only [sharpPrimeCut, sharpCoreStrict_iff, hord, hpair]
  constructor
  · rintro ⟨hi, _, ho, hc⟩
    exact ⟨hi, ho, hc⟩
  · rintro ⟨hi, ho, hc⟩
    refine ⟨hi, ?_, ho, hc⟩
    have hsum := five_prime_log_sum x hx p hp rfl (by simpa only [Nat.cast_prod] using hprod)
    have hg := five_pair_bounds_geometry ((41361 : ℝ) / 100000)
      (fun i => Real.logb x (p i : ℝ)) hsum (hpair.mpr hc)
    intro i
    convert (hg i).1 using 1
    norm_num

theorem sharpPrimeCut_band (x : ℝ) (hx : 1 < x) (p : Fin 5 → ℕ)
    (hp : ∀ i, (p i).Prime) (hprod : x ≤ (∏ i, (p i : ℝ)))
    (hc : sharpPrimeCut x p) : ∀ i, p i ∈ exceptionalPrimeBand x := by
  obtain ⟨_, _, hpair⟩ := (sharpPrimeCut_iff x hx p hp hprod).mp hc
  have hsum := five_prime_log_sum x hx p hp rfl (by simpa only [Nat.cast_prod] using hprod)
  have hg := five_pair_bounds_geometry ((41361 : ℝ) / 100000)
    (fun i => Real.logb x (p i : ℝ)) hsum (five_prime_log_pair x _ hx p hp hpair)
  intro i
  apply (mem_prime_rpow_interval_iff_logb_bounds hx (hp i) _ _).mpr
  constructor
  · exact (by norm_num [exceptionalExponentLower] : exceptionalExponentLower = 1 - 2 * ((41361 : ℝ) / 100000)) ▸ (hg i).1.le
  · exact (hg i).2.le.trans (by norm_num [exceptionalExponentUpper])

open Classical in
theorem sharpResidualTuples_eq_band (x : ℝ) (hx : 1 < x) (n : ℕ) (hxn : x ≤ (n : ℝ)) :
    sharpResidualTuples x (41361 / 100000) n 0 =
      (Fintype.piFinset (fun _ : Fin 5 => exceptionalPrimeBand x)).filter
        (fun p => (∏ i, p i) = n ∧ sharpPrimeCut x p) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpr, hi, hn, hc, ho⟩ := sharpResidualTuples_mem.mp hp
    have hprod : x ≤ ∏ i, (p i : ℝ) := by simpa only [← Nat.cast_prod, hn] using hxn
    have hcut := (sharpPrimeCut_iff x hx p hpr hprod).mpr ⟨hi, ho, hc⟩
    exact Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (sharpPrimeCut_band x hx p hpr hprod hcut), hn, hcut⟩
  · intro hp
    obtain ⟨hb, hn, hcut⟩ := Finset.mem_filter.mp hp
    have hpr : ∀ i, (p i).Prime := fun i => (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hb i)).2
    have hprod : x ≤ ∏ i, (p i : ℝ) := by simpa only [← Nat.cast_prod, hn] using hxn
    obtain ⟨hi, ho, hc⟩ := (sharpPrimeCut_iff x hx p hpr hprod).mp hcut
    exact sharpResidualTuples_mem.mpr ⟨hpr, hi, hn, hc, ho⟩

open Classical in
theorem sharp_first_count_as_prefix (x : ℝ) (hx : 1 < x) :
    (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
      ((sharpResidualTuples x (41361 / 100000) n 0).card : ℝ)) =
    ∑ p ∈ exceptionalPrimeQuadruples x,
      ∑ q ∈ (Finset.Icc ⌈x / (∏ i, (p i : ℝ))⌉₊ ⌊2 * x / (∏ i, (p i : ℝ))⌋₊).filter Nat.Prime,
        if q ∈ exceptionalPrimeBand x ∧ sharpPrimeCut x (Fin.snoc p q) then (1 : ℝ) else 0 := by
  have hrep : (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
      ((sharpResidualTuples x (41361 / 100000) n 0).card : ℝ)) =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin 5 => exceptionalPrimeBand x),
        if (∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧ sharpPrimeCut x p then (1 : ℝ) else 0 := by
    calc
      _ = ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
          ∑ p ∈ Fintype.piFinset (fun _ : Fin 5 => exceptionalPrimeBand x),
            if (∏ i, p i) = n ∧ sharpPrimeCut x p then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [sharpResidualTuples_eq_band x hx n (Nat.ceil_le.mp (Finset.mem_Icc.mp hn).1)]
        simp only [Finset.sum_boole]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        by_cases hc : sharpPrimeCut x p <;> simp [hc]
  rw [hrep]
  simpa only [exceptionalPrimeQuadruples, Nat.cast_prod, one_mul] using
    sum_primeTuples_closed_prefix 4 (exceptionalPrimeBand x)
      (fun q hq => (Finset.mem_filter.mp hq).2) x (2 * x)
      (by linarith only [hx]) (sharpPrimeCut x)

#print axioms sharpPrimeCut_iff
#print axioms sharpPrimeCut_band
#print axioms sharp_first_count_as_prefix

end PrimeGap182Analytic.SharpMean
