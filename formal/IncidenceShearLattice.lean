import IncidenceSquarefreeCompletion

/-!
# A uniform sheared lattice bound

The reciprocal-square majorant is summed with arbitrary real translation,
then the zero pair is removed before the two-dimensional sum. In particular,
subunit scales do not introduce an erroneous constant term.
-/

noncomputable section

namespace PrimeGap182Audit

open scoped BigOperators

def incidenceDecay (a x : ℝ) : ℝ := (1 + a * |x|)⁻¹ ^ 2

theorem incidenceDecay_nonneg (a x : ℝ) : 0 ≤ incidenceDecay a x := sq_nonneg _

theorem incidenceDecay_antitone_abs (a : ℝ) (ha : 0 ≤ a) {x y : ℝ}
    (hxy : |x| ≤ |y|) : incidenceDecay a y ≤ incidenceDecay a x := by
  have hx : 0 < 1 + a * |x| := by positivity
  unfold incidenceDecay
  apply pow_le_pow_left₀ (by positivity)
  exact inv_anti₀ hx (by gcongr)

/-- Uniformity first on the unit interval; both endpoint cases are included. -/
theorem incidenceDecay_shift_unit_interval (a θ : ℝ) (ha : 0 < a)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Summable (fun j : ℤ => incidenceDecay a ((j : ℝ) + θ)) ∧
      (∑' j : ℤ, incidenceDecay a ((j : ℝ) + θ)) ≤ 2 + 4 / a := by
  have hc := PrimeGap186.reciprocalSquare_integer_lattice_bounds a ha
  have hs0 : Summable (fun j : ℤ => incidenceDecay a (j : ℝ)) := hc.1
  have hs1 : Summable (fun j : ℤ => incidenceDecay a ((j + 1 : ℤ) : ℝ)) :=
    hs0.comp_injective (fun _ _ h => add_right_cancel h)
  have hp (j : ℤ) :
      incidenceDecay a ((j : ℝ) + θ) ≤
        incidenceDecay a (j : ℝ) + incidenceDecay a ((j + 1 : ℤ) : ℝ) := by
    by_cases hj : 0 ≤ j
    · have hjR : (0 : ℝ) ≤ j := by exact_mod_cast hj
      have habs : |(j : ℝ)| ≤ |(j : ℝ) + θ| := by
        rw [abs_of_nonneg hjR, abs_of_nonneg (add_nonneg hjR hθ0)]
        linarith
      exact (incidenceDecay_antitone_abs a ha.le habs).trans
        (le_add_of_nonneg_right (incidenceDecay_nonneg _ _))
    · have hj1 : j + 1 ≤ 0 := by omega
      have hj1R : (j : ℝ) + 1 ≤ 0 := by exact_mod_cast hj1
      have habs : |((j + 1 : ℤ) : ℝ)| ≤ |(j : ℝ) + θ| := by
        rw [Int.cast_add, Int.cast_one, abs_of_nonpos hj1R,
          abs_of_nonpos (by linarith : (j : ℝ) + θ ≤ 0)]
        linarith
      exact (incidenceDecay_antitone_abs a ha.le habs).trans
        (le_add_of_nonneg_left (incidenceDecay_nonneg _ _))
  have hs := Summable.of_nonneg_of_le (fun j => incidenceDecay_nonneg _ _) hp (hs0.add hs1)
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' j : ℤ, (incidenceDecay a (j : ℝ) + incidenceDecay a ((j + 1 : ℤ) : ℝ)) :=
      Summable.tsum_le_tsum hp hs (hs0.add hs1)
    _ = (∑' j : ℤ, incidenceDecay a (j : ℝ)) +
        ∑' j : ℤ, incidenceDecay a ((j + 1 : ℤ) : ℝ) := hs0.tsum_add hs1
    _ = 2 * ∑' j : ℤ, incidenceDecay a (j : ℝ) := by
      have ht : (∑' j : ℤ, incidenceDecay a ((j + 1 : ℤ) : ℝ)) =
          ∑' j : ℤ, incidenceDecay a (j : ℝ) :=
        (Equiv.addRight (1 : ℤ)).tsum_eq (fun j : ℤ => incidenceDecay a (j : ℝ))
      rw [ht]
      ring
    _ ≤ 2 * (1 + 2 / a) := mul_le_mul_of_nonneg_left hc.2.1 (by norm_num)
    _ = _ := by ring

/-- Arbitrary real translations, with a constant independent of the translation. -/
theorem incidenceDecay_shift_bounds (a θ : ℝ) (ha : 0 < a) :
    Summable (fun j : ℤ => incidenceDecay a ((j : ℝ) + θ)) ∧
      (∑' j : ℤ, incidenceDecay a ((j : ℝ) + θ)) ≤ 2 + 4 / a := by
  let k : ℤ := ⌊θ⌋
  let r : ℝ := θ - k
  have hr0 : 0 ≤ r := sub_nonneg.mpr (Int.floor_le θ)
  have hr1 : r ≤ 1 := by
    dsimp only [r, k]
    linarith [Int.lt_floor_add_one θ]
  have hs := incidenceDecay_shift_unit_interval a r ha hr0 hr1
  let e := Equiv.addRight k
  have heq (j : ℤ) : incidenceDecay a ((j : ℝ) + θ) =
      incidenceDecay a (((e j : ℤ) : ℝ) + r) := by
    change incidenceDecay a ((j : ℝ) + θ) =
      incidenceDecay a (((j + k : ℤ) : ℝ) + r)
    congr 1
    push_cast
    dsimp only [r]
    ring
  have hsum : Summable (fun j : ℤ => incidenceDecay a (((e j : ℤ) : ℝ) + r)) :=
    hs.1.comp_injective e.injective
  refine ⟨hsum.congr (fun j => (heq j).symm), ?_⟩
  simp_rw [heq]
  rw [e.tsum_eq (fun j : ℤ => incidenceDecay a ((j : ℝ) + r))]
  exact hs.2

/-- Excluding the zero integer costs only the scale, even when it is below one. -/
theorem incidenceDecay_nonzero_bounds (a : ℝ) (ha : 0 < a) :
    Summable (fun j : ℤ => if j = 0 then 0 else incidenceDecay a (j : ℝ)) ∧
      (∑' j : ℤ, if j = 0 then 0 else incidenceDecay a (j : ℝ)) ≤ 2 / a := by
  have hc := PrimeGap186.reciprocalSquare_integer_lattice_bounds a ha
  have hs : Summable (fun j : ℤ => if j = 0 then 0 else incidenceDecay a (j : ℝ)) :=
    Summable.of_nonneg_of_le
      (fun j => by split_ifs <;> first | exact le_rfl | exact incidenceDecay_nonneg _ _)
      (fun j => by split_ifs <;> first | exact incidenceDecay_nonneg _ _ | exact le_rfl) hc.1
  refine ⟨hs, ?_⟩
  have hb := hc.2.2 0
  simpa only [Nat.cast_zero, abs_pos, Int.cast_ne_zero, mul_zero, add_zero,
    mul_one, incidenceDecay, ite_not] using hb

/-- Both frequency coordinates are integers, and only the pair (0,0) is removed. -/
def incidenceShearedNonzeroDecay (a b τ : ℝ) (z : ℤ × ℤ) : ℝ :=
  if z = 0 then 0 else
    incidenceDecay a ((z.1 : ℝ) + τ * (z.2 : ℝ)) * incidenceDecay b (z.2 : ℝ)

theorem incidenceShearedNonzeroDecay_nonneg (a b τ : ℝ) (z : ℤ × ℤ) :
    0 ≤ incidenceShearedNonzeroDecay a b τ z := by
  unfold incidenceShearedNonzeroDecay
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (incidenceDecay_nonneg _ _) (incidenceDecay_nonneg _ _)

/-- The uniform two-dimensional sum, with no constant remaining after the
zero pair is excluded. This is valid for every real shear. -/
theorem incidenceShearedNonzeroDecay_bounds (a b τ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Summable (incidenceShearedNonzeroDecay a b τ) ∧
      (∑' z : ℤ × ℤ, incidenceShearedNonzeroDecay a b τ z) ≤
        8 / (a * b) + 4 / b + 2 / a := by
  let F (z : ℤ × ℤ) := incidenceShearedNonzeroDecay a b τ (z.2, z.1)
  let B (ν : ℤ) := (if ν = 0 then 2 / a else 0) +
    (2 + 4 / a) * (if ν = 0 then 0 else incidenceDecay b (ν : ℝ))
  have hzero := incidenceDecay_nonzero_bounds a ha
  have hvertical := incidenceDecay_nonzero_bounds b hb
  have hF0 (h : ℤ) : F (0, h) = if h = 0 then 0 else incidenceDecay a (h : ℝ) := by
    by_cases hh : h = 0 <;> simp [F, incidenceShearedNonzeroDecay, incidenceDecay, hh]
  have hFn (ν : ℤ) (hν : ν ≠ 0) (h : ℤ) :
      F (ν, h) = incidenceDecay a ((h : ℝ) + τ * (ν : ℝ)) * incidenceDecay b (ν : ℝ) := by
    simp [F, incidenceShearedNonzeroDecay, hν]
  have hrows (ν : ℤ) : Summable (fun h : ℤ => F (ν, h)) := by
    by_cases hν : ν = 0
    · subst ν
      simpa only [hF0] using hzero.1
    · simpa only [hFn ν hν] using
        (incidenceDecay_shift_bounds a (τ * (ν : ℝ)) ha).1.mul_right
          (incidenceDecay b (ν : ℝ))
  have hrows_le (ν : ℤ) : (∑' h : ℤ, F (ν, h)) ≤ B ν := by
    by_cases hν : ν = 0
    · subst ν
      simpa only [hF0, B, ite_true, mul_zero, add_zero] using hzero.2
    · simp only [hFn ν hν, B, ite_eq_right hν, zero_add, tsum_mul_right]
      exact mul_le_mul_of_nonneg_right
        (incidenceDecay_shift_bounds a (τ * (ν : ℝ)) ha).2 (incidenceDecay_nonneg _ _)
  have hsingle : Summable (fun ν : ℤ => if ν = 0 then 2 / a else 0) :=
    (hasSum_ite_eq (0 : ℤ) (2 / a)).summable
  have hB : Summable B := hsingle.add (hvertical.1.mul_left (2 + 4 / a))
  have hBsum : (∑' ν : ℤ, B ν) ≤ 8 / (a * b) + 4 / b + 2 / a := by
    calc
      _ = 2 / a + (2 + 4 / a) *
          ∑' ν : ℤ, (if ν = 0 then 0 else incidenceDecay b (ν : ℝ)) := by
        rw [hsingle.tsum_add (hvertical.1.mul_left (2 + 4 / a))]
        simp only [tsum_mul_left, tsum_ite_eq]
      _ ≤ 2 / a + (2 + 4 / a) * (2 / b) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hvertical.2 (by positivity))
      _ = _ := by ring
  have hsumrows : Summable (fun ν : ℤ => ∑' h : ℤ, F (ν, h)) :=
    Summable.of_nonneg_of_le
      (fun ν => tsum_nonneg (fun h => incidenceShearedNonzeroDecay_nonneg a b τ (h, ν)))
      hrows_le hB
  have hF : Summable F :=
    (summable_prod_of_nonneg (fun z => incidenceShearedNonzeroDecay_nonneg a b τ (z.2, z.1))).mpr
      ⟨hrows, hsumrows⟩
  have hFbound : (∑' z : ℤ × ℤ, F z) ≤ 8 / (a * b) + 4 / b + 2 / a := by
    rw [hF.tsum_prod]
    exact (hsumrows.tsum_le_tsum hrows_le hB).trans hBsum
  have hactual : Summable (incidenceShearedNonzeroDecay a b τ) :=
    (Equiv.prodComm ℤ ℤ).summable_iff.mp hF
  refine ⟨hactual, ?_⟩
  have heq : (∑' z : ℤ × ℤ, F z) =
      ∑' z : ℤ × ℤ, incidenceShearedNonzeroDecay a b τ z :=
    (Equiv.prodComm ℤ ℤ).tsum_eq (incidenceShearedNonzeroDecay a b τ)
  rwa [← heq]

/-- The scaled form used after restricting both frequencies to multiples of d. -/
theorem incidenceShearedNonzeroDecay_scaled_bound (T₁ T₂ d τ : ℝ)
    (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (hd : 0 < d) :
    (∑' z : ℤ × ℤ, incidenceShearedNonzeroDecay (d / T₁) (d / T₂) τ z) ≤
      8 * (T₁ * T₂ / d ^ 2 + (T₁ + T₂) / d) := by
  have hb := (incidenceShearedNonzeroDecay_bounds (d / T₁) (d / T₂) τ
    (div_pos hd hT₁) (div_pos hd hT₂)).2
  refine hb.trans ?_
  have hcalc : 8 / ((d / T₁) * (d / T₂)) + 4 / (d / T₂) + 2 / (d / T₁) =
      8 * (T₁ * T₂ / d ^ 2) + 4 * (T₂ / d) + 2 * (T₁ / d) := by
    field_simp
  rw [hcalc]
  have h1 : 0 ≤ T₁ / d := div_nonneg hT₁.le hd.le
  have h2 : 0 ≤ T₂ / d := div_nonneg hT₂.le hd.le
  rw [add_div]
  nlinarith

#print axioms incidenceShearedNonzeroDecay_bounds
#print axioms incidenceShearedNonzeroDecay_scaled_bound

#print axioms incidenceDecay_shift_bounds
#print axioms incidenceDecay_nonzero_bounds

end PrimeGap182Audit
