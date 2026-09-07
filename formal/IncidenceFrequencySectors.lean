import IncidenceSectorCoefficients

/-!+# The actual signed frequency-divisor sectors

The original frequencies have a fixed full m-supported factor w₂.
The unit mask modulo the row e is expanded by Möbius inversion before
taking norms, then the exact coefficient set is reindexed as λ=t w₂ a.
No unit restriction inside a complex sum is discarded.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators

theorem incidenceFrequencySectors_moebius (e w₂ : ℕ) [NeZero e] (he : 0 < e)
    (hwe : Nat.Coprime w₂ e) (Λ : Finset ℤ)
    (hΛ : ∀ l ∈ Λ, (w₂ : ℤ) ∣ l) (f : ℤ → ℂ) :
    (∑ l ∈ Λ, if IsUnit (l : ZMod e) then f l else 0) =
      ∑ t ∈ e.divisors, ((ArithmeticFunction.moebius t : ℤ) : ℂ) *
        ∑ a ∈ incidenceDividedCoefficientSet Λ (t * w₂),
          f (((t * w₂ : ℕ) : ℤ) * a) := by
  have hmask : (∑ l ∈ Λ, if IsUnit (l : ZMod e) then f l else 0) =
      ∑ t ∈ e.divisors, ((ArithmeticFunction.moebius t : ℤ) : ℂ) *
        ∑ l ∈ Λ, if (t : ℤ) ∣ l then f l else 0 := by
    convert incidenceUnitMask_sum e he Λ f using 1
    apply Finset.sum_congr rfl
    intro l _
    split_ifs <;> rfl
  rw [hmask]
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  rw [incidenceDividedCoefficient_sum]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l hl
  have htw : Nat.Coprime t w₂ :=
    (hwe.of_dvd_right (Nat.dvd_of_mem_divisors ht)).symm
  have hcop : IsCoprime (t : ℤ) (w₂ : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact htw.gcd_eq_one
  have hd : (t : ℤ) ∣ l ↔ ((t * w₂ : ℕ) : ℤ) ∣ l := by
    simp only [Nat.cast_mul]
    exact ⟨fun h => hcop.mul_dvd h (hΛ l hl),
      fun h => (dvd_mul_right (t : ℤ) (w₂ : ℤ)).trans h⟩
  simp only [hd]

theorem incidenceFrequencySectors_energy (e w₂ : ℕ) [NeZero e] (he : 0 < e)
    (hwe : Nat.Coprime w₂ e) (Λ : Finset ℤ)
    (hΛ : ∀ l ∈ Λ, (w₂ : ℤ) ∣ l) (f : ℤ → ℂ) :
    ‖∑ l ∈ Λ, if IsUnit (l : ZMod e) then f l else 0‖ ^ 2 ≤
      (e.divisors.card : ℝ) * ∑ t ∈ e.divisors,
        ‖∑ a ∈ incidenceDividedCoefficientSet Λ (t * w₂),
          f (((t * w₂ : ℕ) : ℤ) * a)‖ ^ 2 := by
  rw [incidenceFrequencySectors_moebius e w₂ he hwe Λ hΛ]
  exact incidenceWeightedSum_energy_le e.divisors _ _
    (fun t _ => incidenceMoebius_norm_le_one t)

theorem incidenceFrequencySectors_quotient_unit (Λ : Finset ℤ)
    (m t w₂ : ℕ) (ht : t ≠ 0) (hw : w₂ ≠ 0)
    (hΛ : ∀ l ∈ Λ, IsUnit ((l / (w₂ : ℤ) : ℤ) : ZMod m))
    (a : ℤ) (ha : a ∈ incidenceDividedCoefficientSet Λ (t * w₂)) :
    IsUnit (a : ZMod m) := by
  have h := hΛ _ ((incidenceDividedCoefficientSet_mem Λ (t * w₂)
    (mul_ne_zero ht hw) a).mp ha)
  have hwI : (w₂ : ℤ) ≠ 0 := by exact_mod_cast hw
  have hdiv : (((t * w₂ : ℕ) : ℤ) * a) / (w₂ : ℤ) = (t : ℤ) * a := by
    rw [show ((t * w₂ : ℕ) : ℤ) * a = (w₂ : ℤ) * ((t : ℤ) * a) by
      push_cast; ring, Int.mul_ediv_cancel_left _ hwI]
  rw [hdiv] at h
  simp only [Int.cast_mul, Int.cast_natCast] at h
  exact isUnit_of_mul_isUnit_right h

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceFrequencySectors_moebius
#print axioms PrimeGap182Audit.incidenceFrequencySectors_energy
#print axioms PrimeGap182Audit.incidenceFrequencySectors_quotient_unit
