import IncidencePhysicalSource
import IncidenceSourceCRT

/-!
# Actual coprimality masks and positive divisor-sector bounds

The unit masks are expanded using the arithmetic Möbius function. The
energy bound is taken only after the exact signed expansion; no
coprimality restriction inside a complex sum is discarded.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators

theorem incidenceIntegerUnit_iff (w : ℕ) (n : ℤ) :
    IsUnit (n : ZMod w) ↔ n.natAbs.Coprime w := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_gcd_eq_one,
    Int.gcd_def, Int.natAbs_natCast]
  exact Nat.coprime_comm

theorem incidenceIntegerUnit_moebius (w : ℕ) (hw : 0 < w) (n : ℤ) :
    (if IsUnit (n : ZMod w) then (1 : ℂ) else 0) =
      ∑ d ∈ w.divisors, if (d : ℤ) ∣ n then
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0 := by
  classical
  have hd : (n.natAbs.gcd w).divisors =
      w.divisors.filter (fun d : ℕ => (d : ℤ) ∣ n) := by
    ext d
    have hg := (Nat.gcd_pos_of_pos_right n.natAbs hw).ne'
    simp [Nat.mem_divisors, Nat.dvd_gcd_iff, Int.natCast_dvd, hg, hw.ne', and_comm]
  simp only [incidenceIntegerUnit_iff]
  rw [← Finset.sum_filter, ← hd]
  symm
  change (∑ d ∈ (n.natAbs.gcd w).divisors,
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ) d) = _
  rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.coe_moebius_mul_coe_zeta]
  by_cases h : n.natAbs.Coprime w <;> simp [h]

theorem incidenceUnitMask_sum (w : ℕ) (hw : 0 < w) (S : Finset ℤ) (f : ℤ → ℂ) :
    (∑ n ∈ S, if IsUnit (n : ZMod w) then f n else 0) =
      ∑ d ∈ w.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        ∑ n ∈ S, if (d : ℤ) ∣ n then f n else 0 := by
  classical
  have hpoint (n : ℤ) : (if IsUnit (n : ZMod w) then f n else 0) =
      (if IsUnit (n : ZMod w) then (1 : ℂ) else 0) * f n := by split_ifs <;> simp
  simp_rw [hpoint, incidenceIntegerUnit_moebius w hw, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> simp

theorem incidenceMoebius_norm_le_one (d : ℕ) :
    ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
  have hd := ArithmeticFunction.abs_moebius_le_one (n := d)
  exact_mod_cast hd

theorem incidenceWeightedSum_energy_le {ι : Type*} (S : Finset ι)
    (a f : ι → ℂ) (ha : ∀ i ∈ S, ‖a i‖ ≤ 1) :
    ‖∑ i ∈ S, a i * f i‖ ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, ‖f i‖ ^ 2 := by
  apply (incidenceNormSum_sq_le S (fun i => a i * f i)).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro i hi
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (ha i hi) (norm_nonneg _)).trans_eq (one_mul _)

theorem incidenceUnitMask_energy_le (w : ℕ) (hw : 0 < w)
    (S : Finset ℤ) (f : ℤ → ℂ) :
    ‖∑ n ∈ S, if IsUnit (n : ZMod w) then f n else 0‖ ^ 2 ≤
      (w.divisors.card : ℝ) * ∑ d ∈ w.divisors,
        ‖∑ n ∈ S, if (d : ℤ) ∣ n then f n else 0‖ ^ 2 := by
  rw [incidenceUnitMask_sum w hw]
  exact incidenceWeightedSum_energy_le w.divisors _ _
    (fun d _ => incidenceMoebius_norm_le_one d)

theorem incidenceUnitMask_weighted_energy_le {ρ : Type*}
    (w : ℕ) (hw : 0 < w) (R : Finset ρ) (S : ρ → Finset ℤ)
    (weight : ρ → ℝ) (hweight : ∀ r ∈ R, 0 ≤ weight r) (f : ρ → ℤ → ℂ) :
    (∑ r ∈ R, weight r *
      ‖∑ n ∈ S r, if IsUnit (n : ZMod w) then f r n else 0‖ ^ 2) ≤
      (w.divisors.card : ℝ) * ∑ d ∈ w.divisors, ∑ r ∈ R, weight r *
        ‖∑ n ∈ S r, if (d : ℤ) ∣ n then f r n else 0‖ ^ 2 := by
  calc
    _ ≤ ∑ r ∈ R, weight r * ((w.divisors.card : ℝ) * ∑ d ∈ w.divisors,
        ‖∑ n ∈ S r, if (d : ℤ) ∣ n then f r n else 0‖ ^ 2) :=
      Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left
        (incidenceUnitMask_energy_le w hw (S r) (f r)) (hweight r hr))
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro r _
      ring

/-- The actual finite integer reindexing used after a divisor is selected. -/
theorem incidenceDivisor_sum_reindex (d : ℕ)
    (S : Finset ℤ) (f : ℤ → ℂ) :
    (∑ n ∈ S, if (d : ℤ) ∣ n then f n else 0) =
      ∑ k ∈ (S.filter (fun n => (d : ℤ) ∣ n)).image (fun n => n / (d : ℤ)),
        f ((d : ℤ) * k) := by
  classical
  rw [← Finset.sum_filter, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [Int.mul_ediv_cancel' (Finset.mem_filter.mp hn).2]
  · intro a ha b hb hab
    have ha' := Int.mul_ediv_cancel' (Finset.mem_filter.mp ha).2
    have hb' := Int.mul_ediv_cancel' (Finset.mem_filter.mp hb).2
    exact ha'.symm.trans ((congrArg (fun k : ℤ => (d : ℤ) * k) hab).trans hb')

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceIntegerUnit_iff
#print axioms PrimeGap182Audit.incidenceIntegerUnit_moebius
#print axioms PrimeGap182Audit.incidenceUnitMask_sum
#print axioms PrimeGap182Audit.incidenceMoebius_norm_le_one
#print axioms PrimeGap182Audit.incidenceWeightedSum_energy_le
#print axioms PrimeGap182Audit.incidenceUnitMask_energy_le
#print axioms PrimeGap182Audit.incidenceUnitMask_weighted_energy_le
#print axioms PrimeGap182Audit.incidenceDivisor_sum_reindex
