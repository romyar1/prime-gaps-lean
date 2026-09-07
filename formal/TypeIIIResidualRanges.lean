import TypeIIIZeroFrequency

/-!
# Positive residual modulus ranges and reciprocal weights

These are the actual u-ranges obtained from R ≤ gu ≤ 2R. Both endpoints and every
small-range case are retained; the reciprocal-square estimate needs no R/g ≥ 1 premise.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def residualRange (R g : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (2 * R / g)).filter (fun u => R ≤ g * u)

theorem residualRange_spec {R g u : ℕ} (hu : u ∈ residualRange R g) :
    0 < u ∧ R ≤ g * u ∧ u ≤ 2 * R / g := by
  obtain ⟨hu, hl⟩ := Finset.mem_filter.mp hu
  exact ⟨(Finset.mem_Icc.mp hu).1, hl, (Finset.mem_Icc.mp hu).2⟩

theorem residualRange_upper {R g u : ℕ} (hu : u ∈ residualRange R g) :
    u ≤ 2 * R :=
  (residualRange_spec hu).2.2.trans (Nat.div_le_self _ _)

theorem residualRange_card_le {R g : ℕ} (hg : 0 < g) :
    ((residualRange R g).card : ℝ) ≤ 2 * (R : ℝ) / (g : ℝ) := by
  have hc : (residualRange R g).card ≤ 2 * R / g := by
    simpa only [residualRange, Nat.card_Icc, Nat.add_sub_cancel] using
      Finset.card_filter_le (Finset.Icc 1 (2 * R / g)) (fun u => R ≤ g * u)
  have hg' : (0 : ℝ) < g := Nat.cast_pos.mpr hg
  apply (le_div_iff₀ hg').2
  have hh := (Nat.mul_le_mul_right g hc).trans (Nat.div_mul_le_self (2 * R) g)
  exact_mod_cast hh

theorem residualRange_inv_le {R g u : ℕ} (hR : 0 < R)
    (hu : u ∈ residualRange R g) : (u : ℝ)⁻¹ ≤ (g : ℝ) / (R : ℝ) := by
  have hu' : (0 : ℝ) < u := Nat.cast_pos.mpr (residualRange_spec hu).1
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ hu' (Nat.cast_pos.mpr hR)).2
  simpa only [one_mul, Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr (residualRange_spec hu).2.1

/-- The positive reciprocal weights have the expected bound even when R/g < 1. -/
theorem residualRange_inv_sq_sum_le {R g : ℕ} (hR : 0 < R) (hg : 0 < g) :
    (∑ u ∈ residualRange R g, (u : ℝ)⁻¹ ^ 2) ≤ 2 * (g : ℝ) / (R : ℝ) := by
  have hR' : (0 : ℝ) < R := Nat.cast_pos.mpr hR
  have hg' : (0 : ℝ) < g := Nat.cast_pos.mpr hg
  calc
    _ ≤ ∑ _u ∈ residualRange R g, ((g : ℝ) / (R : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro u hu
      exact pow_le_pow_left₀ (by positivity) (residualRange_inv_le hR hu) 2
    _ = ((residualRange R g).card : ℝ) * ((g : ℝ) / (R : ℝ)) ^ 2 := by simp
    _ ≤ (2 * (R : ℝ) / (g : ℝ)) * ((g : ℝ) / (R : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right (residualRange_card_le hg) (sq_nonneg _)
    _ = _ := by field_simp

theorem residualRange_pair_inv_sq_sum_le {R g : ℕ} (hR : 0 < R) (hg : 0 < g) :
    (∑ u ∈ residualRange R g, ∑ v ∈ residualRange R g,
      ((u : ℝ)⁻¹ ^ 2) * ((v : ℝ)⁻¹ ^ 2)) ≤
      4 * (g : ℝ) ^ 2 / (R : ℝ) ^ 2 := by
  rw [← Finset.sum_mul_sum]
  have hnon : 0 ≤ ∑ u ∈ residualRange R g, (u : ℝ)⁻¹ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hh := mul_le_mul (residualRange_inv_sq_sum_le hR hg)
    (residualRange_inv_sq_sum_le hR hg) hnon (by positivity)
  convert! hh using 1
  ring

/-- The fixed-gcd off-diagonal weight is dominated before the positive s-sum is enlarged. -/
theorem integer_gcd_mul_le (s g : ℕ) (hg : 0 < g) (D : ℤ) (hD : D ≠ 0) :
    (Int.gcd D ((s * g : ℕ) : ℤ) : ℝ) ≤ (g : ℝ) * (Int.gcd D (s : ℤ) : ℝ) := by
  have hd : Nat.gcd D.natAbs (s * g) ∣ Nat.gcd D.natAbs s * g :=
    (gcd_mul_dvd_mul_gcd D.natAbs s g).trans
      (mul_dvd_mul_left _ (Nat.gcd_dvd_right D.natAbs g))
  have hp : 0 < Nat.gcd D.natAbs s * g :=
    mul_pos (Nat.gcd_pos_of_pos_left s (Int.natAbs_pos.mpr hD)) hg
  have hh := Nat.le_of_dvd hp hd
  simpa only [Int.gcd_def, Int.natAbs_mul, Int.natAbs_natCast, Nat.cast_mul, mul_comm] using
    (Nat.cast_le (α := ℝ)).mpr hh

/-- Exact divisor summation avoids any spurious large-divisor error. -/
theorem zeroFrequency_offDiagonal_s_sum (S g : ℕ) (hg : 0 < g) (D : ℤ) (hD : D ≠ 0) :
    (∑ s ∈ Finset.Icc 1 S, (Int.gcd D ((s * g : ℕ) : ℤ) : ℝ)) ≤
      (g : ℝ) * (S : ℝ) * (D.natAbs.divisors.card : ℝ) := by
  calc
    _ ≤ ∑ s ∈ Finset.Icc 1 S, (g : ℝ) * (Int.gcd D (s : ℤ) : ℝ) :=
      Finset.sum_le_sum (fun s _ => integer_gcd_mul_le s g hg D hD)
    _ = (g : ℝ) * ∑ s ∈ Finset.Icc 1 S, (Int.gcd D (s : ℤ) : ℝ) := by rw [Finset.mul_sum]
    _ ≤ (g : ℝ) * ((S : ℝ) * (D.natAbs.divisors.card : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg g)
      simpa only [Int.gcd_def, Int.natAbs_natCast] using
        (PrimeGap186.reciprocal_differencing_gcd_sums D.natAbs S (Int.natAbs_pos.mpr hD)).1
    _ = _ := by ring

#print axioms residualRange_inv_sq_sum_le
#print axioms residualRange_pair_inv_sq_sum_le
#print axioms zeroFrequency_offDiagonal_s_sum

end

end PrimeGap182.TypeIII
