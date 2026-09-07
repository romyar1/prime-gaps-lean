import PrimeGaps186

/-!
Prime reciprocal measures and uniform final-prime counting on the actual
sharp-defect band [0.17278, 0.24]. Adapted from the public Apache-2.0
PrimeGaps186 proof at the source hash recorded by the generator. The PNT,
weak-convergence and boundary-strip arguments are rechecked at this band;
no old minorant region or distribution estimate is imported as a premise.
Regenerate/check with scripts/build_sharp_prime_measure.py.
-/

noncomputable section
open scoped BigOperators ENNReal NNReal Topology BoundedContinuousFunction
open Filter MeasureTheory Set PrimeGap186

namespace PrimeGap182Analytic.SharpMean

def exceptionalExponentLower : ℝ := 8639 / 50000
def exceptionalExponentUpper : ℝ := 6 / 25
local notation "box" =>
  (Set.Icc (fun _ : Fin 4 => exceptionalExponentLower)
    (fun _ : Fin 4 => exceptionalExponentUpper))

theorem exists_recip_band_error :
    ∃ D : ℝ, 0 < D ∧
      ∀ x : ℝ, 1 < x → 2 ≤ x ^ ((8639 : ℝ) / 50000) →
        ∀ a b : ℝ, 8639 / 50000 ≤ a → a ≤ b → b ≤ 6 / 25 →
          |(∑ p ∈ (Finset.Icc (Nat.ceil (x ^ a)) (Nat.floor (x ^ b))).filter Nat.Prime,
              (p : ℝ)⁻¹) - Real.log (b / a)| ≤
           2 * D / (((8639 : ℝ) / 50000) * Real.log x) + (x ^ ((8639 : ℝ) / 50000))⁻¹ := by
  obtain ⟨D, M, hD, hbound⟩ := exists_real_reciprocal_prefix
  refine ⟨D, hD, ?_⟩
  intro x hx hax a b ha hab hb
  have hx0 : 0 < x := by linarith
  have hL := Real.log_pos hx
  have hxi : 0 < (8639 : ℝ) / 50000 := by norm_num
  have ha0 : 0 < a := hxi.trans_le ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hA : 2 ≤ x ^ a := hax.trans (Real.rpow_le_rpow_of_exponent_le hx.le ha)
  have hB : 2 ≤ x ^ b := hA.trans (Real.rpow_le_rpow_of_exponent_le hx.le hab)
  have hlogA : Real.log (x ^ a) = a * Real.log x := Real.log_rpow hx0 a
  have hlogB : Real.log (x ^ b) = b * Real.log x := Real.log_rpow hx0 b
  have hmain : Real.log (Real.log (x ^ b)) - Real.log (Real.log (x ^ a)) = Real.log (b / a) := by
    rw [hlogA, hlogB]
    rw [Real.log_mul hb0.ne' hL.ne', Real.log_mul ha0.ne' hL.ne', Real.log_div hb0.ne' ha0.ne']
    ring
  have hpreA := hbound (x ^ a) hA
  have hpreB := hbound (x ^ b) hB
  have hpre :
      |((∑ p ∈ Nat.primesLE (Nat.floor (x ^ b)), (p : ℝ)⁻¹) -
          (∑ p ∈ Nat.primesLE (Nat.floor (x ^ a)), (p : ℝ)⁻¹)) - Real.log (b / a)| ≤
        2 * D / (((8639 : ℝ) / 50000) * Real.log x) := by
    have hle (c : ℝ) (hc : 8639 / 50000 ≤ c) :
        D / Real.log (x ^ c) ≤ D / (((8639 : ℝ) / 50000) * Real.log x) := by
      rw [Real.log_rpow hx0]
      apply div_le_div_of_nonneg_left hD.le (mul_pos hxi hL)
      gcongr
    calc
      _ = |((∑ p ∈ Nat.primesLE (Nat.floor (x ^ b)), (p : ℝ)⁻¹) - Real.log (Real.log (x ^ b)) - M) -
          ((∑ p ∈ Nat.primesLE (Nat.floor (x ^ a)), (p : ℝ)⁻¹) -
            Real.log (Real.log (x ^ a)) - M)| := by
              rw [← hmain]; congr 1; ring
      _ ≤ _ := by
        calc
          _ ≤ _ := abs_sub _ _
          _ ≤ D / Real.log (x ^ b) + D / Real.log (x ^ a) := add_le_add hpreB hpreA
          _ ≤ D / (((8639 : ℝ) / 50000) * Real.log x) + D / (((8639 : ℝ) / 50000) * Real.log x) :=
            add_le_add (hle _ (ha.trans hab)) (hle _ ha)
          _ = _ := by ring
  calc
    _ ≤ |(∑ p ∈ (Finset.Icc (Nat.ceil (x ^ a)) (Nat.floor (x ^ b))).filter Nat.Prime, (p : ℝ)⁻¹) -
      ((∑ p ∈ Nat.primesLE (Nat.floor (x ^ b)), (p : ℝ)⁻¹) -
        (∑ p ∈ Nat.primesLE (Nat.floor (x ^ a)), (p : ℝ)⁻¹))| +
      |((∑ p ∈ Nat.primesLE (Nat.floor (x ^ b)), (p : ℝ)⁻¹) -
        (∑ p ∈ Nat.primesLE (Nat.floor (x ^ a)), (p : ℝ)⁻¹)) - Real.log (b / a)| := abs_sub_le _ _ _
    _ ≤ _ := by
      have hcls := abs_closed_recip_sub_prefix (x ^ a) (x ^ b)
        (Real.rpow_pos_of_pos hx0 _) (Real.rpow_le_rpow_of_exponent_le hx.le hab)
      have hxil := (Real.rpow_le_rpow_of_exponent_le hx.le ha)
      have hins : (x ^ a)⁻¹ ≤ (x ^ ((8639 : ℝ) / 50000))⁻¹ :=
        inv_anti₀ (by positivity) hxil
      linarith

theorem reciprocal_band_tendsto {a b : ℝ}
    (ha : (8639 : ℝ) / 50000 ≤ a) (hab : a ≤ b) (hb : b ≤ 6 / 25) :
    Tendsto (fun x : ℝ =>
      ∑ p ∈ (Finset.Icc (Nat.ceil (x ^ a)) (Nat.floor (x ^ b))).filter Nat.Prime, (p : ℝ)⁻¹)
      atTop (nhds (Real.log (b / a))) := by
  obtain ⟨D, hD, hbnd⟩ := exists_recip_band_error
  have he : Tendsto (fun x : ℝ => (2 * D / ((8639 : ℝ) / 50000) / Real.log x) +
      (x ^ ((8639 : ℝ) / 50000))⁻¹) atTop (nhds 0) := by
    simpa only [zero_add, Pi.inv_apply] using
      (Real.tendsto_log_atTop.const_div_atTop (2 * D / ((8639 : ℝ) / 50000))).add
        ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8639 / 50000)).inv_tendsto_atTop)
  apply tendsto_iff_dist_tendsto_zero.mpr
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg) ?_ he
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8639 / 50000)).eventually_ge_atTop 2]
    with x hx hscale
  simpa only [Real.dist_eq, div_div] using hbnd x hx hscale a b ha hab hb

theorem reciprocal_four_box_tendsto (a b : Fin 4 → ℝ)
    (ha : ∀ i, 8639 / 50000 ≤ a i) (hab : ∀ i, a i ≤ b i) (hb : ∀ i, b i ≤ 6 / 25) :
    Tendsto (fun x : ℝ =>
      ∑ p ∈ Fintype.piFinset (fun i : Fin 4 =>
        (Finset.Icc (Nat.ceil (x ^ (a i))) (Nat.floor (x ^ (b i)))).filter Nat.Prime),
            ∏ i, (p i : ℝ)⁻¹) atTop (nhds (∏ i, Real.log (b i / a i))) := by
  have hprod := tendsto_finsetProd (Finset.univ : Finset (Fin 4))
    (fun i _ => reciprocal_band_tendsto (ha i) (hab i) (hb i))
  simpa only [Finset.prod_univ_sum] using hprod

theorem five_prime_error_envelope (K : ℝ) :
    Tendsto (fun x : ℝ =>
      K / (Real.log x) *
        (∑ p ∈ (Finset.Icc (Nat.ceil (x ^ ((8639 : ℝ) / 50000)))
            (Nat.floor (x ^ ((6 : ℝ) / 25)))).filter Nat.Prime, (p : ℝ)⁻¹) ^ 4 +
      Real.log x / x * (Nat.floor (x ^ ((6 : ℝ) / 25)) : ℝ) ^ 4)
    atTop (nhds 0) := by
  have hH := reciprocal_band_tendsto (b := (6 : ℝ) / 25) (a := (8639 : ℝ) / 50000)
        (by norm_num) (by norm_num) (by norm_num)
  have hH4 := hH.pow 4
  have hsmall : Tendsto (fun x : ℝ => K / Real.log x) atTop (nhds 0) :=
    Real.tendsto_log_atTop.const_div_atTop K
  have hfirst := hsmall.mul hH4
  have hsecond : Tendsto
      (fun x : ℝ => Real.log x / x * (Nat.floor (x ^ ((6 : ℝ) / 25)) : ℝ) ^ 4)
      atTop (nhds 0) := by
    have hmaj := (isLittleO_log_rpow_atTop
      (by norm_num : (0 : ℝ) < 1-4 * ((6 : ℝ) / 25))).tendsto_div_nhds_zero
    apply squeeze_zero' ?_ ?_ hmaj
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
      exact mul_nonneg (div_nonneg (Real.log_nonneg hx) (le_trans (by norm_num) hx))
        (pow_nonneg (Nat.cast_nonneg _) _)
    · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
      have hlog := Real.log_pos hx
      have hfl : ((Nat.floor (x ^ ((6 : ℝ) / 25)) : ℕ) : ℝ) ≤ x ^ ((6 : ℝ) / 25) :=
        Nat.floor_le (by positivity)
      have hx0 : 0 < x := by linarith
      have hpows : (x ^ ((6 : ℝ) / 25)) ^ 4 * (x ^ (1-4 * ((6 : ℝ) / 25))) = x := by
        rw [← Real.rpow_mul_natCast hx0.le, ← Real.rpow_add hx0]
        norm_num
      calc
        _ ≤ Real.log x / x * (x ^ ((6 : ℝ) / 25)) ^ 4 := by
          gcongr
        _ = Real.log x / (x ^ (1-4 * ((6 : ℝ) / 25))) := by
          have hne : (x ^ (1-4 * ((6 : ℝ) / 25))) ≠ 0 := (Real.rpow_pos_of_pos hx0 _).ne'
          rw [eq_div_iff hne]
          field_simp [hx0.ne']
          nlinarith [hpows]
  simpa only [zero_mul, zero_add] using hfirst.add hsecond

theorem exceptionalExponentLower_pos : 0 < exceptionalExponentLower := by
  norm_num [exceptionalExponentLower]

theorem exceptionalExponentLower_lt_upper :
    exceptionalExponentLower < exceptionalExponentUpper := by
  norm_num [exceptionalExponentLower, exceptionalExponentUpper]

/--
The primes in the closed size interval with endpoints `x^exceptionalExponentLower` and
`x^exceptionalExponentUpper`, represented by natural-number ceiling and
floor endpoints.
-/
noncomputable def exceptionalPrimeBand (x : ℝ) : Finset ℕ :=
  (Finset.Icc (Nat.ceil (x ^ exceptionalExponentLower))
    (Nat.floor (x ^ exceptionalExponentUpper))).filter Nat.Prime

/-- All ordered four-tuples of primes from `exceptionalPrimeBand x`. -/
noncomputable def exceptionalPrimeQuadruples (x : ℝ) : Finset (Fin 4 → ℕ) :=
  Fintype.piFinset (fun _ => exceptionalPrimeBand x)

/-- The reciprocal product of the four coordinates, used as the mass of a prime-tuple atom. -/
noncomputable def reciprocalQuadrupleWeight (p : Fin 4 → ℕ) : ℝ := ∏ i, (p i : ℝ)⁻¹

theorem reciprocalQuadrupleWeight_nonneg (p : Fin 4 → ℕ) : 0 ≤ reciprocalQuadrupleWeight p := by
  dsimp [reciprocalQuadrupleWeight]
  exact Finset.prod_nonneg (by intro i _; exact inv_nonneg.mpr (Nat.cast_nonneg _))

/--
The finite atomic measure placing reciprocal-product mass at the base-`x` exponent vector of
every four-tuple in the prime band.
-/
noncomputable def primeQuadrupleExponentMeasure (x : ℝ) : FiniteMeasure (Fin 4 → ℝ) := by
  let d (p : Fin 4 → ℕ) : FiniteMeasure (Fin 4 → ℝ) :=
    ⟨Measure.dirac (primeQuadrupleExponents x p), by infer_instance⟩
  exact ∑ p ∈ exceptionalPrimeQuadruples x, Real.toNNReal (reciprocalQuadrupleWeight p) • d p

theorem mem_prime_rpow_interval_iff_logb_bounds {x : ℝ} (hx : 1 < x)
    {q : ℕ} (hq : q.Prime) (a b : ℝ) :
    q ∈ (Finset.Icc (Nat.ceil (x ^ a)) (Nat.floor (x ^ b))).filter Nat.Prime ↔
       a ≤ Real.logb x (q : ℝ) ∧ Real.logb x (q : ℝ) ≤ b := by
  have hx0 : 0 < x := by linarith
  have hq0 : 0 < (q : ℝ) := Nat.cast_pos.mpr hq.pos
  rw [Finset.mem_filter, Finset.mem_Icc, and_iff_left hq,
    Nat.ceil_le, Nat.le_floor_iff (Real.rpow_nonneg hx0.le _),
    Real.le_logb_iff_rpow_le hx hq0, Real.logb_le_iff_le_rpow hx hq0]

theorem primeQuadrupleExponents_mem_box {x : ℝ} (hx : 1 < x) {p : Fin 4 → ℕ}
    (hp : p ∈ exceptionalPrimeQuadruples x) : primeQuadrupleExponents x p ∈ box := by
  have common (i : Fin 4) :
      exceptionalExponentLower ≤ primeQuadrupleExponents x p i ∧
        primeQuadrupleExponents x p i ≤ exceptionalExponentUpper := by
    have m := Fintype.mem_piFinset.mp hp i
    exact (mem_prime_rpow_interval_iff_logb_bounds hx (Finset.mem_filter.mp m).2
      exceptionalExponentLower exceptionalExponentUpper).mp m
  exact ⟨fun i => (common i).1, fun i => (common i).2⟩

theorem integral_primeQuadrupleExponentMeasure (x : ℝ) (f : (Fin 4 → ℝ) → ℝ) :
    (∫ t, f t ∂(primeQuadrupleExponentMeasure x : Measure (Fin 4 → ℝ))) =
      ∑ p ∈ exceptionalPrimeQuadruples x,
        f (primeQuadrupleExponents x p) * reciprocalQuadrupleWeight p := by
  rw [primeQuadrupleExponentMeasure, FiniteMeasure.toMeasure_sum, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro p _
    change (∫ a, f a ∂(Real.toNNReal (reciprocalQuadrupleWeight p) •
      Measure.dirac (primeQuadrupleExponents x p))) = _
    rw [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def,
      Real.coe_toNNReal _ (reciprocalQuadrupleWeight_nonneg p)]
    exact mul_comm _ _
  · intro p hp
    change Integrable f
      (Real.toNNReal (reciprocalQuadrupleWeight p) • Measure.dirac (primeQuadrupleExponents x p))
    apply Integrable.smul_measure_nnreal
    exact integrable_dirac (by finiteness)

open Classical in
theorem primeQuadrupleExponentMeasure_real (x : ℝ) (s : Set (Fin 4 → ℝ)) (hs : MeasurableSet s) :
    (primeQuadrupleExponentMeasure x : Measure (Fin 4 → ℝ)).real s =
      ∑ p ∈ exceptionalPrimeQuadruples x,
        if primeQuadrupleExponents x p ∈ s then reciprocalQuadrupleWeight p else 0 := by
  rw [← integral_indicator_one hs, integral_primeQuadrupleExponentMeasure]
  simp only [Set.indicator_apply, Pi.one_apply, ite_mul, one_mul, zero_mul]

theorem reciprocal_exponent_density_nonneg {t : Fin 4 → ℝ} (ht : t ∈ box) : 0 ≤ (∏ i, t i)⁻¹ := by
  apply inv_nonneg.mpr
  exact Finset.prod_nonneg (by intro i _; exact exceptionalExponentLower_pos.le.trans (ht.1 i))

theorem continuousOn_reciprocal_exponent_density :
    ContinuousOn (fun t : Fin 4 → ℝ => (∏ i, t i)⁻¹) box := by
  apply (continuousOn_finsetProd (Finset.univ : Finset (Fin 4))
    (by intro i _; exact (continuous_apply i).continuousOn)).inv₀
  intro t ht
  exact Finset.prod_ne_zero_iff.mpr (by
    intro i _
    exact (exceptionalExponentLower_pos.trans_le (ht.1 i)).ne')

/--
The finite measure on the box `[exceptionalExponentLower, exceptionalExponentUpper]^4`,
with density `1 / ∏ i, t i` relative to
four-dimensional Lebesgue measure.
-/
noncomputable def reciprocalExponentMeasure : FiniteMeasure (Fin 4 → ℝ) :=
  ⟨(volume.restrict box).withDensity (fun t : Fin 4 → ℝ => ENNReal.ofReal ((∏ i, t i)⁻¹)), by
    apply isFiniteMeasure_withDensity_ofReal
    exact (continuousOn_reciprocal_exponent_density.integrableOn_compact isCompact_Icc).2⟩

theorem measurable_reciprocal_exponent_density :
    Measurable (fun t : Fin 4 → ℝ => ENNReal.ofReal ((∏ i, t i)⁻¹)) := by
  fun_prop

theorem setIntegral_reciprocalExponentMeasure (g : (Fin 4 → ℝ) → ℝ) (s : Set (Fin 4 → ℝ))
    (hs : MeasurableSet s) :
    (∫ t in s, g t ∂(reciprocalExponentMeasure : Measure (Fin 4 → ℝ))) =
      ∫ t in s ∩ box, g t * (∏ i, t i)⁻¹ := by
  change (∫ t in s, g t ∂(volume.restrict box).withDensity
    (fun t : Fin 4 → ℝ => ENNReal.ofReal ((∏ i, t i)⁻¹))) = _
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul measurable_reciprocal_exponent_density
    (.of_forall (by intro t; exact ENNReal.ofReal_lt_top)) g hs,
    Measure.restrict_restrict hs]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (hs.inter measurableSet_Icc)] with t ht
  simp [ENNReal.toReal_ofReal (reciprocal_exponent_density_nonneg ht.2), smul_eq_mul, mul_comm]

theorem reciprocalExponentMeasure_real (s : Set (Fin 4 → ℝ)) (hs : MeasurableSet s) :
    (reciprocalExponentMeasure : Measure (Fin 4 → ℝ)).real s = ∫ t in s ∩ box, (∏ i, t i)⁻¹ := by
  rw [← setIntegral_one_eq_measureReal, setIntegral_reciprocalExponentMeasure (fun _ => 1) s hs]
  simp

theorem reciprocalExponentMeasure_absolutelyContinuous_volume :
    (reciprocalExponentMeasure : Measure (Fin 4 → ℝ)) ≪ volume :=
  (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict

theorem integral_Icc_reciprocal_prod (a b : Fin 4 → ℝ) (hab : a ≤ b)
    (hapos : ∀ i, 0 < a i) :
    (∫ t : Fin 4 → ℝ in Set.Icc a b, (∏ i, t i)⁻¹) = ∏ i, Real.log (b i / a i) := by
  simp_rw [← Finset.prod_inv_distrib]
  rw [← Set.pi_univ_Icc, volume_pi,
    Measure.restrict_pi_pi (fun _ : Fin 4 => (volume : Measure ℝ))]
  rw [integral_fin_nat_prod_eq_prod (fun (_ : Fin 4) (r : ℝ) => r⁻¹)]
  apply Finset.prod_congr rfl
  intro i _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hab i)]
  exact integral_inv_of_pos (hapos i) ((hapos i).trans_le (hab i))

theorem tendsto_primeQuadrupleExponentMeasure_Icc (a b : Fin 4 → ℝ) :
    Filter.Tendsto (fun x : ℝ => (primeQuadrupleExponentMeasure x) (Set.Icc a b)) Filter.atTop
      (nhds (reciprocalExponentMeasure (Set.Icc a b))) := by
  apply NNReal.tendsto_coe.mp
  classical
  have hs : MeasurableSet (Set.Icc a b) := measurableSet_Icc
  let L : Fin 4 → ℝ := a ⊔ (fun _ => exceptionalExponentLower)
  let U : Fin 4 → ℝ := b ⊓ (fun _ => exceptionalExponentUpper)
  have hI : Set.Icc a b ∩ box = Set.Icc L U := by simp [L, U, Set.Icc_inter_Icc]
  by_cases good : L ≤ U
  · have hapos : ∀ i, 0 < L i := fun i =>
      exceptionalExponentLower_pos.trans_le (le_sup_right : exceptionalExponentLower ≤ L i)
    have hbup : ∀ i, U i ≤ exceptionalExponentUpper := fun i => inf_le_right
    have hlim : Filter.Tendsto
        (fun x : ℝ => ∑ p ∈ Fintype.piFinset (fun i : Fin 4 =>
          (Finset.Icc (Nat.ceil (x ^ L i)) (Nat.floor (x ^ U i))).filter Nat.Prime),
            ∏ i, (p i : ℝ)⁻¹) Filter.atTop (nhds (∏ i, Real.log (U i / L i))) :=
      reciprocal_four_box_tendsto _ _ (fun i => le_sup_right) good hbup
    have eqx : ∀ᶠ x : ℝ in Filter.atTop,
        (primeQuadrupleExponentMeasure x : Measure (Fin 4 → ℝ)).real (Set.Icc a b) =
        ∑ p ∈ Fintype.piFinset (fun i : Fin 4 =>
          (Finset.Icc (Nat.ceil (x ^ L i)) (Nat.floor (x ^ U i))).filter Nat.Prime),
            reciprocalQuadrupleWeight p := by
      filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
      have heq : (exceptionalPrimeQuadruples x).filter
          (fun p => primeQuadrupleExponents x p ∈ Set.Icc a b) =
          Fintype.piFinset (fun i : Fin 4 =>
            (Finset.Icc (Nat.ceil (x ^ L i)) (Nat.floor (x ^ U i))).filter Nat.Prime) := by
        ext p
        rw [Finset.mem_filter]
        simp only [exceptionalPrimeQuadruples, Fintype.mem_piFinset]
        by_cases hp : ∀ i, (p i).Prime
        · have hmem (i : Fin 4) (A B : ℝ) := mem_prime_rpow_interval_iff_logb_bounds hx (hp i) A B
          simp only [exceptionalPrimeBand, hmem, Set.mem_Icc, Pi.le_def,
            primeQuadrupleExponents, L, U,
            Pi.sup_apply, Pi.inf_apply, sup_le_iff, le_inf_iff, forall_and]
          tauto
        · simp only [exceptionalPrimeBand, Finset.mem_filter, forall_and, hp, and_false, false_and]
      rw [primeQuadrupleExponentMeasure_real x _ hs, ← heq]
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun _ _ => ite_cond_congr rfl
    have Hν := reciprocalExponentMeasure_real (Set.Icc a b) hs
    rw [hI, integral_Icc_reciprocal_prod L U good hapos] at Hν
    simp only [FiniteMeasure.measureReal_eq_coe_coeFn] at eqx Hν
    rw [← Hν] at hlim
    refine Filter.Tendsto.congr' ?_ hlim
    exact eqx.mono (fun _ e => e.symm)
  · have empty : Set.Icc a b ∩ box = ∅ := by
      rw [hI, Set.Icc_eq_empty_iff]
      exact good
    have eqx : ∀ᶠ x : ℝ in Filter.atTop,
        (primeQuadrupleExponentMeasure x : Measure (Fin 4 → ℝ)).real (Set.Icc a b) = 0 := by
      filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
      rw [primeQuadrupleExponentMeasure_real x _ hs]
      apply Finset.sum_eq_zero
      intro p hp
      rw [ite_eq_right]
      intro ht
      have : primeQuadrupleExponents x p ∈ Set.Icc a b ∩ box :=
        ⟨ht, primeQuadrupleExponents_mem_box hx hp⟩
      rw [empty] at this
      exact this
    have eqn : (reciprocalExponentMeasure : Measure (Fin 4 → ℝ)).real (Set.Icc a b) = 0 := by
      rw [reciprocalExponentMeasure_real (Set.Icc a b) hs, empty]
      simp
    simp only [FiniteMeasure.measureReal_eq_coe_coeFn] at eqx eqn
    simpa only [eqn] using
      (Filter.Tendsto.congr' (eqx.mono (fun _ hh => hh.symm))
        (tendsto_const_nhds (x := (0 : ℝ))))

theorem primeQuadrupleExponentMeasure_box {x : ℝ} (hx : 1 < x) :
    (primeQuadrupleExponentMeasure x) box = (primeQuadrupleExponentMeasure x).mass := by
  apply NNReal.coe_injective
  simp only [← FiniteMeasure.measureReal_eq_coe_coeFn, FiniteMeasure.mass]
  rw [primeQuadrupleExponentMeasure_real x box measurableSet_Icc,
    primeQuadrupleExponentMeasure_real x Set.univ MeasurableSet.univ]
  apply Finset.sum_congr rfl
  intro p hp
  simp [primeQuadrupleExponents_mem_box hx hp]

theorem reciprocalExponentMeasure_box :
    reciprocalExponentMeasure box = reciprocalExponentMeasure.mass := by
  apply NNReal.coe_injective
  simp only [← FiniteMeasure.measureReal_eq_coe_coeFn, FiniteMeasure.mass]
  rw [reciprocalExponentMeasure_real box measurableSet_Icc,
    reciprocalExponentMeasure_real Set.univ MeasurableSet.univ]
  simp

theorem reciprocalExponentMeasure_ne_zero : reciprocalExponentMeasure ≠ 0 := by
  apply (FiniteMeasure.mass_nonzero_iff _).mp
  apply ne_of_gt
  apply (NNReal.coe_pos.mp ?_)
  have W := reciprocalExponentMeasure_real box measurableSet_Icc
  rw [Set.inter_self] at W
  have P := integral_Icc_reciprocal_prod (fun _ : Fin 4 => exceptionalExponentLower)
    (fun _ => exceptionalExponentUpper)
    (by intro i; exact exceptionalExponentLower_lt_upper.le) (fun _ => exceptionalExponentLower_pos)
  have hz : 0 < Real.log (exceptionalExponentUpper / exceptionalExponentLower) :=
    Real.log_pos ((lt_div_iff₀ exceptionalExponentLower_pos).mpr
      (by simpa using exceptionalExponentLower_lt_upper))
  rw [← reciprocalExponentMeasure_box]
  change 0 < (reciprocalExponentMeasure : Measure (Fin 4 → ℝ)).real box
  rw [W, P]
  positivity

theorem tendsto_primeQuadrupleExponentMeasure :
    Filter.Tendsto primeQuadrupleExponentMeasure Filter.atTop (nhds reciprocalExponentMeasure) := by
  have hmass : Filter.Tendsto (fun x : ℝ => (primeQuadrupleExponentMeasure x).mass) Filter.atTop
      (nhds reciprocalExponentMeasure.mass) := by
    have h := tendsto_primeQuadrupleExponentMeasure_Icc (fun _ => exceptionalExponentLower)
      (fun _ => exceptionalExponentUpper)
    change Filter.Tendsto (fun x => (primeQuadrupleExponentMeasure x) box) Filter.atTop
      (nhds (reciprocalExponentMeasure box)) at h
    rw [reciprocalExponentMeasure_box] at h
    refine Filter.Tendsto.congr' ?_ h
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    exact (primeQuadrupleExponentMeasure_box hx)
  have nn := (FiniteMeasure.mass_nonzero_iff reciprocalExponentMeasure).mpr
    reciprocalExponentMeasure_ne_zero
  have ev := (hmass.eventually_ne nn).mono fun x h =>
    (FiniteMeasure.mass_nonzero_iff (primeQuadrupleExponentMeasure x)).mp h
  let S : Set (Set (Fin 4 → ℝ)) :=
    {s | ∃ a b : Fin 4 → ℝ, a ≤ b ∧ Set.Icc a b = s}
  have spi : IsPiSystem S := by
    rintro _ ⟨a, b, hab, rfl⟩ _ ⟨d, e, hde, rfl⟩ hne
    rw [Set.Icc_inter_Icc] at hne ⊢
    exact ⟨_, _, Set.nonempty_Icc.mp hne, rfl⟩
  have normals := spi.tendsto_probabilityMeasure_of_tendsto_of_mem
    (μ := fun x : ℝ => (primeQuadrupleExponentMeasure x).normalize)
    (ν := reciprocalExponentMeasure.normalize)
    (l := Filter.atTop)
    (by rintro _ ⟨a, b, _, rfl⟩; exact measurableSet_Icc)
    (by
      intro u hu x hx
      obtain ⟨r, hr, hru⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hu.mem_nhds hx)
      refine ⟨Set.Icc (fun i => x i - r) (fun i => x i + r),
        ⟨_, _, by intro i; linarith, rfl⟩, ?_, ?_⟩
      · apply pi_Icc_mem_nhds <;> intro i <;> linarith
      · simpa [closedBall_pi x hr.le, Real.closedBall_eq_Icc, Set.pi_univ_Icc] using hru)
    (by
      rintro _ ⟨a, b, _, rfl⟩
      have key : Filter.Tendsto
          (fun x : ℝ => (primeQuadrupleExponentMeasure x).mass⁻¹ *
            ((primeQuadrupleExponentMeasure x) (Set.Icc a b)))
          Filter.atTop
            (nhds (reciprocalExponentMeasure.mass⁻¹ * reciprocalExponentMeasure (Set.Icc a b))) :=
        (hmass.inv₀ nn).mul (tendsto_primeQuadrupleExponentMeasure_Icc a b)
      rw [← FiniteMeasure.normalize_eq_of_nonzero reciprocalExponentMeasure
        reciprocalExponentMeasure_ne_zero] at key
      refine Filter.Tendsto.congr' ?_ key
      filter_upwards [ev] with x hx
      exact ((primeQuadrupleExponentMeasure x).normalize_eq_of_nonzero hx _).symm)
  exact FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass normals hmass

noncomputable def exceptionalExponentClamp (t : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => max exceptionalExponentLower (min exceptionalExponentUpper (t i))

theorem exceptionalExponentClamp_mem_box (t : Fin 4 → ℝ) : exceptionalExponentClamp t ∈ box :=
  ⟨by intro i; exact le_max_left _ _,
         by intro i; exact max_le exceptionalExponentLower_lt_upper.le (min_le_left _ _)⟩

theorem continuous_exceptionalExponentClamp : Continuous exceptionalExponentClamp := by
  apply continuous_pi
  intro i
  exact continuous_const.max (continuous_const.min (continuous_apply i))

theorem exceptionalExponentClamp_eq_self_of_mem_box {t : Fin 4 → ℝ} (ht : t ∈ box) :
    exceptionalExponentClamp t = t := by
  funext i
  dsimp [exceptionalExponentClamp]
  rw [min_eq_right (ht.2 i), max_eq_right (ht.1 i)]

/--
The bounded continuous extension of a function continuous on the exponent box, obtained by
composing it with coordinatewise clamping.
-/
noncomputable def extendFromExceptionalExponentBox (f : (Fin 4 → ℝ) → ℝ) (hf : ContinuousOn f box) :
    (Fin 4 → ℝ) →ᵇ ℝ where
  toFun t := f (exceptionalExponentClamp t)
  continuous_toFun := hf.comp_continuous continuous_exceptionalExponentClamp
    exceptionalExponentClamp_mem_box
  map_bounded' := by
    apply Metric.isBounded_range_iff.mp
    apply ((isCompact_Icc.image_of_continuousOn hf).isBounded).subset
    rintro z ⟨t, rfl⟩
    exact ⟨exceptionalExponentClamp t, exceptionalExponentClamp_mem_box t, rfl⟩

open Classical in
theorem reciprocal_four_continuous_tendsto
    (f : (Fin 4 → ℝ) → ℝ)
    (hf : ContinuousOn f
      (Set.Icc (fun _ : Fin 4 => (8639 : ℝ) / 50000)
        (fun _ : Fin 4 => (6 : ℝ) / 25))) :
    Filter.Tendsto
      (fun x : ℝ =>
        let P : Finset ℕ :=
          (Finset.Icc (Nat.ceil (x ^ ((8639 : ℝ) / 50000)))
            (Nat.floor (x ^ ((6 : ℝ) / 25)))).filter Nat.Prime
        ∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => P),
          f (fun i => Real.logb x (p i : ℝ)) * ∏ i, (p i : ℝ)⁻¹)
      Filter.atTop
      (nhds (∫ t in Set.Icc (fun _ : Fin 4 => (8639 : ℝ) / 50000)
          (fun _ : Fin 4 => (6 : ℝ) / 25), f t * (∏ i, t i)⁻¹)) := by
  change ContinuousOn f box at hf
  let F := extendFromExceptionalExponentBox f hf
  have hlim := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp
    tendsto_primeQuadrupleExponentMeasure F
  have hv : (∫ t, F t ∂(reciprocalExponentMeasure : Measure (Fin 4 → ℝ))) =
      ∫ t in Set.Icc (fun _ : Fin 4 => (8639 : ℝ) / 50000)
          (fun _ : Fin 4 => (6 : ℝ) / 25), f t * (∏ i, t i)⁻¹ := by
    rw [← setIntegral_univ]
    rw [setIntegral_reciprocalExponentMeasure F Set.univ MeasurableSet.univ, Set.univ_inter]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    simp [F, extendFromExceptionalExponentBox, exceptionalExponentClamp_eq_self_of_mem_box ht]
  rw [hv] at hlim
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
  rw [integral_primeQuadrupleExponentMeasure]
  simp only [exceptionalPrimeQuadruples, exceptionalPrimeBand, exceptionalExponentLower,
    exceptionalExponentUpper, reciprocalQuadrupleWeight]
  apply Finset.sum_congr rfl
  intro p hp
  rw [show F (primeQuadrupleExponents x p) = f (primeQuadrupleExponents x p) from by
    simp [F, extendFromExceptionalExponentBox,
      exceptionalExponentClamp_eq_self_of_mem_box (primeQuadrupleExponents_mem_box hx hp)]]
  rfl

theorem one_sub_sum_ge_of_mem_exceptional_exponent_box {t : Fin 4 → ℝ} (ht : t ∈ box) :
    1 / 25 ≤ 1 - ∑ i, t i := by
  have hbnd : (∑ i, t i) ≤ 4 * exceptionalExponentUpper := by
    calc
      (∑ i : Fin 4, t i) ≤ ∑ _i : Fin 4, exceptionalExponentUpper :=
        Finset.sum_le_sum (by intro i _; exact ht.2 i)
      _ = 4 * exceptionalExponentUpper := by simp
  norm_num [exceptionalExponentUpper] at hbnd ⊢
  linarith

theorem continuousOn_inv_one_sub_sum_exceptional_exponent_box :
    ContinuousOn (fun t : Fin 4 → ℝ => (1 - ∑ i, t i)⁻¹) box := by
  apply (continuousOn_const.sub (continuousOn_finsetSum _
      (by intro i _; exact (continuous_apply i).continuousOn))).inv₀
  intro t ht
  exact (by norm_num : (0 : ℝ) < 1 / 25).trans_le
    (one_sub_sum_ge_of_mem_exceptional_exponent_box ht) |>.ne'

/--
The reciprocal remaining exponent `1 / (1 - ∑ i, t i)` on the exponent box, extended to a
bounded continuous function by clamping.
-/
noncomputable def reciprocalResidualExponent : (Fin 4 → ℝ) →ᵇ ℝ :=
  extendFromExceptionalExponentBox (fun t => (1 - ∑ i, t i)⁻¹)
    continuousOn_inv_one_sub_sum_exceptional_exponent_box

theorem reciprocalResidualExponent_pos (t : Fin 4 → ℝ) : 0 < reciprocalResidualExponent t := by
  change 0 < (1 - ∑ i, exceptionalExponentClamp t i)⁻¹
  exact inv_pos.mpr (((by norm_num : (0 : ℝ) < 1 / 25).trans_le
    (one_sub_sum_ge_of_mem_exceptional_exponent_box (exceptionalExponentClamp_mem_box t))))

theorem reciprocalResidualExponent_eq_inv_one_sub_sum_of_mem_box {t : Fin 4 → ℝ} (ht : t ∈ box) :
    reciprocalResidualExponent t = (1 - ∑ i, t i)⁻¹ := by
  simp [reciprocalResidualExponent, extendFromExceptionalExponentBox,
    exceptionalExponentClamp_eq_self_of_mem_box ht]

open Classical in
theorem weighted_primeQuadrupleExponentMeasure_real (x : ℝ) (hx : 1 < x)
    (s : Set (Fin 4 → ℝ)) (hs : MeasurableSet s) :
    (finiteMeasureWithContinuousDensity (primeQuadrupleExponentMeasure x)
      reciprocalResidualExponent : Measure (Fin 4 → ℝ)).real s =
      ∑ p ∈ exceptionalPrimeQuadruples x,
        if primeQuadrupleExponents x p ∈ s then
          ((∏ i, (p i : ℝ)) * (1 - ∑ i, primeQuadrupleExponents x p i))⁻¹ else 0 := by
  rw [finiteMeasureWithContinuousDensity_real (primeQuadrupleExponentMeasure x)
      reciprocalResidualExponent (fun t => (reciprocalResidualExponent_pos t).le) s hs,
      ← integral_indicator hs, integral_primeQuadrupleExponentMeasure]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp only [Set.indicator_apply, ite_mul, zero_mul,
    reciprocalResidualExponent_eq_inv_one_sub_sum_of_mem_box
      (primeQuadrupleExponents_mem_box hx hp), mul_inv_rev, reciprocalQuadrupleWeight,
    Finset.prod_inv_distrib]

theorem strip_frontier_null (c : Fin 4 → ℝ) (b r : ℝ) (hc : ∃ i, c i ≠ 0) :
    (finiteMeasureWithContinuousDensity reciprocalExponentMeasure
      reciprocalResidualExponent : Measure (Fin 4 → ℝ))
      (frontier {t : Fin 4 → ℝ | |(∑ i, c i * t i) - b| ≤ r}) = 0 := by
  have hf : Continuous (fun t : Fin 4 → ℝ => |(∑ i, c i * t i) - b|) := by fun_prop
  apply ((finiteMeasureWithContinuousDensity_absolutelyContinuous _ _).trans
    reciprocalExponentMeasure_absolutelyContinuous_volume)
  refine measure_mono_null ?_ (measure_union_null
    (affine_hyperplane_null c (b + r) hc) (affine_hyperplane_null c (b - r) hc))
  intro t ht
  have h := eq_or_eq_neg_of_abs_eq (frontier_le_subset_eq hf continuous_const ht)
  simp only [sub_eq_iff_eq_add] at h
  simpa only [Set.mem_union, Set.mem_ofPred_eq, sub_eq_add_neg, add_comm] using h

open Classical in
theorem reciprocal_four_weighted_affine_strip_uniform
    (c : Fin 4 → ℝ) (hc : c ≠ 0) (b : ℝ) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta : ℝ, 0 < delta ∧
        ∀ᶠ x : ℝ in Filter.atTop,
          ∀ s : ℝ, 0 ≤ s → s ≤ delta →
            (let P : Finset ℕ :=
              (Finset.Icc (Nat.ceil (x ^ ((8639 : ℝ) / 50000)))
                (Nat.floor (x ^ ((6 : ℝ) / 25)))).filter Nat.Prime
             ∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => P),
               let t : Fin 4 → ℝ := fun i => Real.logb x (p i : ℝ)
               if |(∑ i, c i * t i) - b| ≤ s
               then ((∏ i, (p i : ℝ)) * (1 - ∑ i, t i))⁻¹ else 0) ≤ epsilon := by
  intro epsilon he
  have hc' : ∃ i, c i ≠ 0 := Function.ne_iff.mp hc
  let strip (d : ℝ) : Set (Fin 4 → ℝ) := {t | |(∑ i, c i * t i)-b| ≤ d}
  have sm (d : ℝ) : MeasurableSet (strip d) := by
    apply measurableSet_le <;> fun_prop
  let d : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hd (n) : 0 < d n := by dsimp [d]; positivity
  have hd_antitone : Antitone d := by
    intro n m hnm
    change ((m : ℝ) + 1)⁻¹ ≤ ((n : ℝ) + 1)⁻¹
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have A := fun r => strip_frontier_null c b r hc'
  have hint : (⋂ n, strip (d n)) = {t : Fin 4 → ℝ | (∑ i, c i * t i) = b} := by
    ext t
    constructor
    · intro h
      have hd_lim : Filter.Tendsto d Filter.atTop (nhds 0) := by
        simpa only [d, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hle : |(∑ i, c i * t i) - b| ≤ (0 : ℝ) :=
        ge_of_tendsto hd_lim (.of_forall (fun n : ℕ => Set.mem_iInter.mp h n))
      simp only [Set.mem_ofPred_eq]
      exact sub_eq_zero.mp (abs_eq_zero.mp ((le_antisymm hle (abs_nonneg _))))
    · intro h
      simp only [Set.mem_ofPred_eq] at h
      simp only [Set.mem_iInter, strip, Set.mem_ofPred_eq, h, sub_self, abs_zero]
      intro n
      exact (hd n).le
  have hlim : Filter.Tendsto (fun n : ℕ =>
      (finiteMeasureWithContinuousDensity reciprocalExponentMeasure
        reciprocalResidualExponent) (strip (d n)))
      Filter.atTop (nhds (0 : ℝ≥0)) := by
    have HE : Filter.Tendsto
        (fun n : ℕ =>
          (finiteMeasureWithContinuousDensity reciprocalExponentMeasure
            reciprocalResidualExponent : Measure (Fin 4 → ℝ)) (strip (d n)))
        Filter.atTop (nhds (0 : ENNReal)) := by
      rw [← ((finiteMeasureWithContinuousDensity_absolutelyContinuous _ _).trans
        reciprocalExponentMeasure_absolutelyContinuous_volume)
        (affine_hyperplane_null c b hc'), ← hint]
      apply tendsto_measure_iInter_atTop
      · intro n; exact (sm (d n)).nullMeasurableSet
      · intro n m hnm t ht; exact le_trans ht (hd_antitone hnm)
      · exact ⟨0, measure_ne_top _ _⟩
    exact (ENNReal.tendsto_toNNReal (by simp)).comp HE
  have hr : ∃ n : ℕ,
    (finiteMeasureWithContinuousDensity reciprocalExponentMeasure
      reciprocalResidualExponent : Measure (Fin 4 → ℝ)).real
      (strip (d n)) < epsilon := by
    obtain ⟨n, hn⟩ := ((NNReal.tendsto_coe.mpr hlim).eventually_lt_const he).exists
    exact ⟨n, hn⟩
  obtain ⟨n, hn⟩ := hr
  refine ⟨d n, hd n, ?_⟩
  have hw := tendsto_finiteMeasureWithContinuousDensity reciprocalResidualExponent
    (fun t => (reciprocalResidualExponent_pos t).le)
    tendsto_primeQuadrupleExponentMeasure
  have B := tendsto_finiteMeasure_apply_of_null_frontier hw (A (d n))
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    (NNReal.tendsto_coe.mpr B).eventually_le_const hn] with x hx hxlim
  intro s _ sdn
  calc
    _ = (finiteMeasureWithContinuousDensity (primeQuadrupleExponentMeasure x)
      reciprocalResidualExponent : Measure (Fin 4 → ℝ)).real (strip s) := by
      symm
      simpa [exceptionalPrimeQuadruples, exceptionalPrimeBand, exceptionalExponentLower,
        exceptionalExponentUpper, primeQuadrupleExponents, strip] using
        (weighted_primeQuadrupleExponentMeasure_real x hx (strip s) (sm s))
    _ ≤ (finiteMeasureWithContinuousDensity (primeQuadrupleExponentMeasure x)
      reciprocalResidualExponent : Measure (Fin 4 → ℝ)).real (strip (d n)) := by
      apply measureReal_mono (fun _ ht => le_trans ht sdn)
    _ ≤ epsilon := hxlim

theorem reciprocal_primeQuadruple_strip_sum_nonneg
    (x : ℝ) (hx : 1 < x) (c : Fin 4 → ℝ) (b s : ℝ) :
    0 ≤ ∑ p ∈ exceptionalPrimeQuadruples x,
      if |(∑ i, c i * primeQuadrupleExponents x p i) - b| ≤ s
      then ((∏ i, (p i : ℝ)) * (1 - ∑ i, primeQuadrupleExponents x p i))⁻¹ else 0 := by
  classical
  refine Finset.sum_nonneg fun p hp => ite_nonneg (inv_nonneg.mpr ?_) le_rfl
  exact mul_nonneg (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
    ((by norm_num : (0 : ℝ) ≤ 1 / 25).trans
      (one_sub_sum_ge_of_mem_exceptional_exponent_box
        (primeQuadrupleExponents_mem_box hx hp)))

open Classical in
theorem reciprocal_four_weighted_affine_moving_strip_tendsto
    (c : Fin 4 → ℝ) (hc : c ≠ 0) (b r : ℝ) (hr : 0 ≤ r) :
    Filter.Tendsto
      (fun x : ℝ =>
        let P : Finset ℕ :=
          (Finset.Icc (Nat.ceil (x ^ ((8639 : ℝ) / 50000)))
            (Nat.floor (x ^ ((6 : ℝ) / 25)))).filter Nat.Prime
        ∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => P),
          let t : Fin 4 → ℝ := fun i => Real.logb x (p i : ℝ)
          if |(∑ i, c i * t i) - b| ≤ r * Real.log 2 / Real.log x
          then ((∏ i, (p i : ℝ)) * (1 - ∑ i, t i))⁻¹ else 0)
      Filter.atTop (nhds 0) := by
  change Filter.Tendsto
    (fun x : ℝ => ∑ p ∈ exceptionalPrimeQuadruples x,
      if |(∑ i, c i * primeQuadrupleExponents x p i) - b| ≤ r * Real.log 2 / Real.log x
      then ((∏ i, (p i : ℝ)) * (1 - ∑ i, primeQuadrupleExponents x p i))⁻¹ else 0)
    Filter.atTop (nhds 0)
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    exact lt_of_lt_of_le ha
      (reciprocal_primeQuadruple_strip_sum_nonneg x hx c b (r * Real.log 2 / Real.log x))
  · intro epsilon he
    obtain ⟨delta, hd, H⟩ :=
      reciprocal_four_weighted_affine_strip_uniform c hc b (epsilon / 2) (half_pos he)
    have hscale : Filter.Tendsto
        (fun x : ℝ => r * Real.log 2 / Real.log x) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), H,
      hscale.eventually_le_const hd] with x hx hxstrip hxscale
    have hnonneg : 0 ≤ r * Real.log 2 / Real.log x :=
      div_nonneg (mul_nonneg hr (Real.log_nonneg (by norm_num)))
        (Real.log_nonneg hx.le)
    have hmass : (∑ p ∈ exceptionalPrimeQuadruples x,
        if |(∑ i, c i * primeQuadrupleExponents x p i) - b| ≤ r * Real.log 2 / Real.log x
        then ((∏ i, (p i : ℝ)) * (1 - ∑ i, primeQuadrupleExponents x p i))⁻¹
        else 0) ≤ epsilon / 2 :=
      hxstrip (r * Real.log 2 / Real.log x) hnonneg hxscale
    exact lt_of_le_of_lt hmass (half_lt_self he)

open Classical in
theorem reciprocal_four_weighted_affine_moving_strip_finset_tendsto
    {ι : Type*} (S : Finset ι) (c : ι → Fin 4 → ℝ) (b r : ι → ℝ)
    (hc : ∀ a ∈ S, c a ≠ 0) (hr : ∀ a ∈ S, 0 ≤ r a) :
    Filter.Tendsto
      (fun x : ℝ => ∑ a ∈ S,
        let P : Finset ℕ :=
          (Finset.Icc (Nat.ceil (x ^ ((8639 : ℝ) / 50000)))
            (Nat.floor (x ^ ((6 : ℝ) / 25)))).filter Nat.Prime
        ∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => P),
          let t : Fin 4 → ℝ := fun i => Real.logb x (p i : ℝ)
          if |(∑ i, c a i * t i) - b a| ≤ r a * Real.log 2 / Real.log x
          then ((∏ i, (p i : ℝ)) * (1 - ∑ i, t i))⁻¹ else 0)
      Filter.atTop (nhds 0) := by
  simpa only [Finset.sum_const_zero] using
    (tendsto_finsetSum S (fun a ha =>
      reciprocal_four_weighted_affine_moving_strip_tendsto
        (c a) (hc a ha) (b a) (r a) (hr a ha)))

theorem prime_prefix_compact_geometry
    (x : ℝ) (hx : 1 < x) (p : Fin 4 → ℕ)
    (hp : ∀ i, p i ∈
      (Finset.Icc (Nat.ceil (x ^ ((8639 : ℝ) / 50000)))
        (Nat.floor (x ^ ((6 : ℝ) / 25)))).filter Nat.Prime) :
    let t : Fin 4 → ℝ := fun i => Real.logb x (p i : ℝ)
    let M : ℝ := ∏ i, (p i : ℝ)
    (∀ i, (8639 : ℝ) / 50000 ≤ t i ∧ t i ≤ (6 : ℝ) / 25) ∧
      0 < M ∧ M ≤ x ^ ((24 : ℝ) / 25) ∧
      (1 : ℝ) / 25 ≤ 1 - ∑ i, t i ∧ Real.logb x M = ∑ i, t i := by
  let t : Fin 4 → ℝ := fun i => Real.logb x (p i : ℝ)
  let M : ℝ := ∏ i, (p i : ℝ)
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
  have hMpos : 0 < M := Finset.prod_pos (fun i _ => hpos i)
  have hlog : Real.logb x M = ∑ i, t i :=
    Real.logb_prod Finset.univ (fun i : Fin 4 => (p i : ℝ))
      (fun i _ => (hpos i).ne')
  have hsum : (∑ i, t i) ≤ (24 : ℝ) / 25 := by
    simp only [Fin.sum_univ_four]
    linarith [(ht 0).2, (ht 1).2, (ht 2).2, (ht 3).2]
  have hMhi : M ≤ x ^ ((24 : ℝ) / 25) :=
    (Real.logb_le_iff_le_rpow hx hMpos).mp (by rw [hlog]; exact hsum)
  have hbeta : (1 : ℝ) / 25 ≤ 1 - ∑ i, t i := by linarith
  exact ⟨ht, hMpos, hMhi, hbeta, hlog⟩

open Classical in
theorem exists_closed_final_prime_prefix_error_control :
    ∃ K : ℝ, 0 < K ∧
      ∀ᶠ x : ℝ in Filter.atTop,
        ∀ u v : ℝ, 1 ≤ u → u ≤ v → v ≤ 2 →
          let P : Finset ℕ :=
            (Finset.Icc (Nat.ceil (x ^ ((8639 : ℝ) / 50000)))
              (Nat.floor (x ^ ((6 : ℝ) / 25)))).filter Nat.Prime
          let E : (Fin 4 → ℕ) → ℝ := fun p =>
            let M : ℝ := ∏ i, (p i : ℝ)
            let beta : ℝ := 1 - ∑ i, Real.logb x (p i : ℝ)
            Real.log x / x *
                (((Finset.Icc (Nat.ceil (u * x / M)) (Nat.floor (v * x / M))).filter
                  Nat.Prime).card : ℝ) -
              (v - u) * (M * beta)⁻¹
          (∀ p ∈ Fintype.piFinset (fun _ : Fin 4 => P),
            |E p| ≤ K / ((∏ i, (p i : ℝ)) * ((1 : ℝ) / 25) ^ 2 * Real.log x) +
              Real.log x / x) ∧
          (∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => P), |E p|) ≤
            625 * K / Real.log x * (∑ q ∈ P, (q : ℝ)⁻¹) ^ 4 +
              Real.log x / x * (Nat.floor (x ^ ((6 : ℝ) / 25)) : ℝ) ^ 4 := by
  obtain ⟨K, Y, hK, _, hcount⟩ := exists_closed_final_prime_uniform
  refine ⟨K, hK, ?_⟩
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 25)).eventually_ge_atTop Y]
      with x hx hYx
  intro u v hu huv hv
  let P : Finset ℕ :=
    (Finset.Icc (Nat.ceil (x ^ ((8639 : ℝ) / 50000)))
      (Nat.floor (x ^ ((6 : ℝ) / 25)))).filter Nat.Prime
  let E : (Fin 4 → ℕ) → ℝ := fun p =>
    let M : ℝ := ∏ i, (p i : ℝ)
    let beta : ℝ := 1 - ∑ i, Real.logb x (p i : ℝ)
    Real.log x / x *
        (((Finset.Icc (Nat.ceil (u * x / M)) (Nat.floor (v * x / M))).filter
          Nat.Prime).card : ℝ) -
      (v - u) * (M * beta)⁻¹
  have hpoint : ∀ p ∈ Fintype.piFinset (fun _ : Fin 4 => P),
      |E p| ≤ K / ((∏ i, (p i : ℝ)) * ((1 : ℝ) / 25) ^ 2 * Real.log x) +
        Real.log x / x := by
    intro p hp
    obtain ⟨_, hMpos, hMhi, _, hlog⟩ :=
      prime_prefix_compact_geometry x hx p (Fintype.mem_piFinset.mp hp)
    have hscale : (∏ i, (p i : ℝ)) ≤ x ^ (1 - (1 : ℝ) / 25) := by
      norm_num
      exact hMhi
    simpa only [E, hlog] using
      hcount ((1 : ℝ) / 25) x (∏ i, (p i : ℝ)) u v (by norm_num) hx hYx
        hMpos hscale hu huv hv
  refine ⟨hpoint, ?_⟩
  have hterm (p : Fin 4 → ℕ) :
      K / ((∏ i, (p i : ℝ)) * ((1 : ℝ) / 25) ^ 2 * Real.log x) =
        (625 * K / Real.log x) * (∏ i, (p i : ℝ))⁻¹ := by
    norm_num [div_eq_mul_inv, mul_inv_rev]
    ring
  have hrecip :
      (∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => P), (∏ i, (p i : ℝ))⁻¹) =
        (∑ q ∈ P, (q : ℝ)⁻¹) ^ 4 := by
    simpa only [Finset.prod_inv_distrib] using
      (Finset.sum_pow' P (fun q : ℕ => (q : ℝ)⁻¹) 4).symm
  have hcard : P.card ≤ Nat.floor (x ^ ((6 : ℝ) / 25)) := by
    calc
      P.card ≤ (Finset.Icc 1 (Nat.floor (x ^ ((6 : ℝ) / 25)))).card := by
        apply Finset.card_le_card
        intro q hq
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hq).2.pos,
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2⟩
      _ = Nat.floor (x ^ ((6 : ℝ) / 25)) := by simp
  have hcardR : (P.card : ℝ) ≤ (Nat.floor (x ^ ((6 : ℝ) / 25)) : ℝ) := by
    exact_mod_cast hcard
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  have hxpos : 0 < x := zero_lt_one.trans hx
  calc
    _ ≤ ∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => P),
        ((625 * K / Real.log x) * (∏ i, (p i : ℝ))⁻¹ + Real.log x / x) := by
      change (∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => P), |E p|) ≤ _
      apply Finset.sum_le_sum
      intro p hp
      rw [← hterm p]
      exact hpoint p hp
    _ = 625 * K / Real.log x * (∑ q ∈ P, (q : ℝ)⁻¹) ^ 4 +
        Real.log x / x * (P.card : ℝ) ^ 4 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hrecip]
      simp [mul_comm]
    _ ≤ _ := add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hcardR 4)
        (div_nonneg hlogpos.le hxpos.le))

open Classical in
theorem closed_final_prime_prefix_error_uniform :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ x : ℝ in Filter.atTop,
        ∀ u v : ℝ, 1 ≤ u → u ≤ v → v ≤ 2 →
          let P : Finset ℕ :=
            (Finset.Icc (Nat.ceil (x ^ ((8639 : ℝ) / 50000)))
              (Nat.floor (x ^ ((6 : ℝ) / 25)))).filter Nat.Prime
          (∑ p ∈ Fintype.piFinset (fun _ : Fin 4 => P),
            |let M : ℝ := ∏ i, (p i : ℝ)
             let beta : ℝ := 1 - ∑ i, Real.logb x (p i : ℝ)
             Real.log x / x *
                 (((Finset.Icc (Nat.ceil (u * x / M)) (Nat.floor (v * x / M))).filter
                   Nat.Prime).card : ℝ) -
               (v - u) * (M * beta)⁻¹|) ≤ epsilon := by
  intro epsilon hepsilon
  obtain ⟨K, _, hcontrol⟩ := exists_closed_final_prime_prefix_error_control
  have hlimit := five_prime_error_envelope (625 * K)
  filter_upwards [hcontrol, hlimit.eventually_le_const hepsilon] with x hx hsmall
  intro u v hu huv hv
  exact ((hx u v hu huv hv).2).trans hsmall

#print axioms reciprocal_band_tendsto
#print axioms tendsto_primeQuadrupleExponentMeasure
#print axioms reciprocal_four_weighted_affine_moving_strip_finset_tendsto
#print axioms closed_final_prime_prefix_error_uniform

end PrimeGap182Analytic.SharpMean
