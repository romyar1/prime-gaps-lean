import IncidenceSourceMasks

/-!
# Exact outside-divisor reduction of the physical source energy

The Möbius expansion is performed on each original unit row. The
substitution n=c n₁ and the permutation of all residue classes are
proved before taking the positive sector bound.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators

def incidenceUnmaskedPhysicalRow {m e : ℕ} [NeZero m] [NeZero e]
    (A : ZMod m) (B : ℤ) (Λ I : Finset ℤ) (a χ : ℤ → ℂ) (γ : ZMod e) : ℂ :=
  ∑ l ∈ Λ, a l * if IsUnit (l : ZMod e) then
    ∑ n ∈ I, if (n : ZMod e) = γ * (l : ZMod e) then
      χ n * PrimeGap186.reciprocalUnitPhase m (A * (l : ZMod m))
        ((e : ZMod m) * ((n : ZMod m) + (B : ZMod m) * (e : ZMod m)))
    else 0
  else 0

def incidencePhysicalDivisorSector {m w e : ℕ} [NeZero m] [NeZero w] [NeZero e]
    (c : ℕ) (A B : ℤ) (Λ I : Finset ℤ) (a χ : ℤ → ℂ) (γ : ZMod e) : ℂ :=
  ∑ n ∈ I, if (c : ℤ) ∣ n then
    ∑ l ∈ Λ, if IsUnit (l : ZMod e) ∧ (n : ZMod e) = γ * (l : ZMod e) then
      a l * (χ n * PrimeGap186.reciprocalUnitPhase m ((A : ZMod m) * (l : ZMod m))
        ((e : ZMod m) * ((n : ZMod m) + (B : ZMod m) * ((w * e : ℕ) : ZMod m))))
    else 0
  else 0

theorem incidencePhysicalRow_moebius {m w e : ℕ} [NeZero m] [NeZero w] [NeZero e]
    (A B : ℤ) (Λ I : Finset ℤ) (a χ : ℤ → ℂ) (γ : ZMod e) :
    incidencePhysicalRow (m := m) (w := w) A B Λ I a χ γ =
      ∑ c ∈ w.divisors, ((ArithmeticFunction.moebius c : ℤ) : ℂ) *
        incidencePhysicalDivisorSector (m := m) (w := w) c A B Λ I a χ γ := by
  let f : ℤ → ℂ := fun n =>
    ∑ l ∈ Λ, if IsUnit (l : ZMod e) ∧ (n : ZMod e) = γ * (l : ZMod e) then
      a l * (χ n * PrimeGap186.reciprocalUnitPhase m ((A : ZMod m) * (l : ZMod m))
        ((e : ZMod m) * ((n : ZMod m) + (B : ZMod m) * ((w * e : ℕ) : ZMod m))))
    else 0
  have hrow : incidencePhysicalRow (m := m) (w := w) A B Λ I a χ γ =
      ∑ n ∈ I, if IsUnit (n : ZMod w) then f n else 0 := by
    unfold incidencePhysicalRow
    simp only [Finset.mul_sum, Finset.ite_sum_zero, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [f]
    rw [Finset.ite_sum_zero]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs <;> simp_all
  rw [hrow]
  simpa only [incidencePhysicalDivisorSector, f] using
    incidenceUnitMask_sum w (Nat.pos_of_ne_zero (NeZero.ne w)) I f

theorem incidencePhysicalDivisorSector_reindex {m w e : ℕ}
    [NeZero m] [NeZero w] [NeZero e]
    (hwm : Nat.Coprime w m) (hwe : Nat.Coprime w e)
    (c : ℕ) (hc : c ∣ w) (A B : ℤ) (Λ I : Finset ℤ) (a χ : ℤ → ℂ) (γ : ZMod e) :
    incidencePhysicalDivisorSector (m := m) (w := w) c A B Λ I a χ
        ((c : ZMod e) * γ) =
      incidenceUnmaskedPhysicalRow
        ((A : ZMod m) * (((ZMod.unitOfCoprime c (hwm.of_dvd_left hc))⁻¹ :
          (ZMod m)ˣ) : ZMod m))
        (B * ((w / c : ℕ) : ℤ)) Λ
        ((I.filter (fun n => (c : ℤ) ∣ n)).image (fun n => n / (c : ℤ)))
        a (fun n => χ ((c : ℤ) * n)) γ := by
  let uc : (ZMod m)ˣ := ZMod.unitOfCoprime c (hwm.of_dvd_left hc)
  let vc : (ZMod e)ˣ := ZMod.unitOfCoprime c (hwe.of_dvd_left hc)
  have hcancel (n l : ℤ) : (((c : ℤ) * n : ℤ) : ZMod e) =
      ((c : ZMod e) * γ) * (l : ZMod e) ↔ (n : ZMod e) = γ * (l : ZMod e) := by
    simp only [Int.cast_mul, Int.cast_natCast]
    change (vc : ZMod e) * (n : ZMod e) = (vc : ZMod e) * γ * (l : ZMod e) ↔ _
    rw [mul_assoc]
    exact (incidenceInputUnitEquiv vc).injective.eq_iff
  have hcw : (c : ZMod m) * ((w / c : ℕ) : ZMod m) = (w : ZMod m) := by
    simpa only [Nat.cast_mul] using
      congrArg (fun n : ℕ => (n : ZMod m)) (Nat.mul_div_cancel' hc)
  have hphase (n l : ℤ) :
      PrimeGap186.reciprocalUnitPhase m ((A : ZMod m) * (l : ZMod m))
        ((e : ZMod m) * ((((c : ℤ) * n : ℤ) : ZMod m) +
          (B : ZMod m) * ((w * e : ℕ) : ZMod m))) =
      PrimeGap186.reciprocalUnitPhase m
        (((A : ZMod m) * ((uc⁻¹ : (ZMod m)ˣ) : ZMod m)) * (l : ZMod m))
        ((e : ZMod m) * ((n : ZMod m) +
          ((B * ((w / c : ℕ) : ℤ) : ℤ) : ZMod m) * (e : ZMod m))) := by
    have hden : (e : ZMod m) * ((((c : ℤ) * n : ℤ) : ZMod m) +
        (B : ZMod m) * ((w * e : ℕ) : ZMod m)) =
        (uc : ZMod m) * ((e : ZMod m) * ((n : ZMod m) +
          ((B * ((w / c : ℕ) : ℤ) : ℤ) : ZMod m) * (e : ZMod m))) := by
      simp only [uc, ZMod.coe_unitOfCoprime, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
      linear_combination -((B : ZMod m) * (e : ZMod m) ^ 2) * hcw
    rw [hden, incidenceReciprocalPhase_unit_denominator]
    congr 1
    ring
  unfold incidencePhysicalDivisorSector
  rw [incidenceDivisor_sum_reindex]
  unfold incidenceUnmaskedPhysicalRow
  simp only [Finset.mul_sum, Finset.ite_sum_zero, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro l _
  simp only [hcancel, hphase, ite_and, uc]

theorem incidencePhysicalEnergy_divisor_bound {m w e : ℕ}
    [NeZero m] [NeZero w] [NeZero e]
    (hwm : Nat.Coprime w m) (hwe : Nat.Coprime w e)
    (A B : ℤ) (Λ I : Finset ℤ) (a χ : ℤ → ℂ) :
    incidencePhysicalEnergy (m := m) (w := w) (e := e) A B Λ I a χ ≤
      (w.divisors.card : ℝ) * ∑ c ∈ w.divisors.attach,
        ∑ γ : ZMod e, ‖incidenceUnmaskedPhysicalRow
          ((A : ZMod m) * (((ZMod.unitOfCoprime c.1
            (hwm.of_dvd_left (Nat.dvd_of_mem_divisors c.2)))⁻¹ : (ZMod m)ˣ) : ZMod m))
          (B * ((w / c.1 : ℕ) : ℤ)) Λ
          ((I.filter (fun n => (c.1 : ℤ) ∣ n)).image (fun n => n / (c.1 : ℤ)))
          a (fun n => χ ((c.1 : ℤ) * n)) γ‖ ^ 2 := by
  have hrow (γ : ZMod e) := incidenceWeightedSum_energy_le w.divisors
    (fun c => ((ArithmeticFunction.moebius c : ℤ) : ℂ))
    (fun c => incidencePhysicalDivisorSector (m := m) (w := w) c A B Λ I a χ γ)
    (fun c _ => incidenceMoebius_norm_le_one c)
  simp only [← incidencePhysicalRow_moebius] at hrow
  unfold incidencePhysicalEnergy
  calc
    _ ≤ ∑ γ : ZMod e, (w.divisors.card : ℝ) * ∑ c ∈ w.divisors,
        ‖incidencePhysicalDivisorSector (m := m) (w := w) c A B Λ I a χ γ‖ ^ 2 :=
      Finset.sum_le_sum (fun γ _ => hrow γ)
    _ = (w.divisors.card : ℝ) * ∑ c ∈ w.divisors,
        ∑ γ : ZMod e, ‖incidencePhysicalDivisorSector (m := m) (w := w) c A B Λ I a χ γ‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ = _ := by
      congr 1
      rw [← Finset.sum_attach w.divisors]
      apply Finset.sum_congr rfl
      intro c _
      let vc : (ZMod e)ˣ := ZMod.unitOfCoprime c.1 (hwe.of_dvd_left (Nat.dvd_of_mem_divisors c.2))
      have he := (incidenceInputUnitEquiv vc).sum_comp (fun γ =>
        ‖incidencePhysicalDivisorSector (m := m) (w := w) c.1 A B Λ I a χ γ‖ ^ 2)
      rw [← he]
      apply Finset.sum_congr rfl
      intro γ _
      rw [show (incidenceInputUnitEquiv vc) γ = (c.1 : ZMod e) * γ from rfl,
        incidencePhysicalDivisorSector_reindex hwm hwe c.1 (Nat.dvd_of_mem_divisors c.2)]

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidencePhysicalRow_moebius
#print axioms PrimeGap182Audit.incidencePhysicalDivisorSector_reindex
#print axioms PrimeGap182Audit.incidencePhysicalEnergy_divisor_bound
