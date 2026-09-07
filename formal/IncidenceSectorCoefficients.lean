import IncidenceOscillatoryModulus
import IncidenceNumeratorSupport

/-!
# Actual divisor-sector coefficients and their short support

The coefficient in a t-sector is c(t w₂ a). Its squared norm is
counted through the original coefficient set, and each original
nonzero index occurs at most its divisor count over all t.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators

def incidenceDividedCoefficientSet (Λ : Finset ℤ) (d : ℕ) : Finset ℤ :=
  (Λ.filter (fun l => (d : ℤ) ∣ l)).image (fun l => l / (d : ℤ))

theorem incidenceDividedCoefficientSet_mem (Λ : Finset ℤ) (d : ℕ) (hd : d ≠ 0) (a : ℤ) :
    a ∈ incidenceDividedCoefficientSet Λ d ↔ (d : ℤ) * a ∈ Λ := by
  have hdI : (d : ℤ) ≠ 0 := by exact_mod_cast hd
  simpa only [incidenceDividedCoefficientSet, Int.modEq_iff_dvd, sub_zero, zero_add] using
    incidenceProgressionIndex_mem (d : ℤ) 0 hdI Λ a

theorem incidenceDividedCoefficientSet_card (Λ : Finset ℤ) (d : ℕ) :
    (incidenceDividedCoefficientSet Λ d).card ≤ Λ.card :=
  Finset.card_image_le.trans (Finset.card_filter_le _ _)

theorem incidenceDividedCoefficient_sum {M : Type*} [AddCommMonoid M]
    (Λ : Finset ℤ) (d : ℕ) (f : ℤ → M) :
    (∑ a ∈ incidenceDividedCoefficientSet Λ d, f ((d : ℤ) * a)) =
      ∑ l ∈ Λ with (d : ℤ) ∣ l, f l := by
  unfold incidenceDividedCoefficientSet
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro l hl
    rw [Int.mul_ediv_cancel' (Finset.mem_filter.mp hl).2]
  · intro a ha b hb hab
    have ha' := Int.mul_ediv_cancel' (Finset.mem_filter.mp ha).2
    have hb' := Int.mul_ediv_cancel' (Finset.mem_filter.mp hb).2
    exact ha'.symm.trans ((congrArg (fun k : ℤ => (d : ℤ) * k) hab).trans hb')

theorem incidenceDividedCoefficient_isUnit (Λ : Finset ℤ) (d m : ℕ) (hd : d ≠ 0)
    (hΛ : ∀ l ∈ Λ, IsUnit (l : ZMod m)) (a : ℤ)
    (ha : a ∈ incidenceDividedCoefficientSet Λ d) : IsUnit (a : ZMod m) := by
  have h := hΛ _ ((incidenceDividedCoefficientSet_mem Λ d hd a).mp ha)
  simp only [Int.cast_mul, Int.cast_natCast] at h
  exact isUnit_of_mul_isUnit_right h

theorem incidenceDividedCoefficient_dyadic (Λ : Finset ℤ) (d : ℕ) (hd : 0 < d)
    (L : ℝ) (hΛ : ∀ l ∈ Λ, L ≤ |(l : ℝ)| ∧ |(l : ℝ)| ≤ 2 * L)
    (a : ℤ) (ha : a ∈ incidenceDividedCoefficientSet Λ d) :
    L / d ≤ |(a : ℝ)| ∧ |(a : ℝ)| ≤ 2 * (L / d) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have h := hΛ _ ((incidenceDividedCoefficientSet_mem Λ d hd.ne' a).mp ha)
  simp only [Int.cast_mul, Int.cast_natCast, abs_mul, abs_of_pos hdR] at h
  constructor
  · exact (div_le_iff₀ hdR).mpr (by nlinarith only [h.1])
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hdR).mpr
    nlinarith only [h.2]

theorem incidenceIntegerDyadic_card (A : Finset ℤ) (U : ℝ) (hU : 0 < U)
    (hA : ∀ a ∈ A, U ≤ |(a : ℝ)| ∧ |(a : ℝ)| ≤ 2 * U) : (A.card : ℝ) ≤ 6 * U := by
  by_cases hAE : A = ∅
  · simp only [hAE, Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hAE
  have hane : a ≠ 0 := by
    intro hz
    have h := (hA a ha).1
    simp only [hz, Int.cast_zero, abs_zero] at h
    exact hU.not_ge h
  have habs : (1 : ℝ) ≤ |(a : ℝ)| := by
    have hh : 1 ≤ a.natAbs := Nat.succ_le_iff.mpr (Int.natAbs_pos.mpr hane)
    have hhR : (1 : ℝ) ≤ (a.natAbs : ℝ) := by exact_mod_cast hh
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hhR
  have hcard := PrimeGap186.int_finset_card_le_of_mem_real_Icc A (-2 * U) (2 * U)
    (by linarith) (fun a ha => by
      have hh := (abs_le.mp (hA a ha).2)
      constructor <;> linarith)
  linarith [(hA a ha).2]

theorem incidenceSectorCoefficients_energy_sum (T : Finset ℕ) (Λ : Finset ℤ)
    (w₂ : ℕ) (c : ℤ → ℂ) (τ : ℝ)
    (hΛ0 : ∀ l ∈ Λ, l ≠ 0)
    (hτ : ∀ l ∈ Λ, (l.natAbs.divisors.card : ℝ) ≤ τ) :
    (∑ t ∈ T, ∑ a ∈ incidenceDividedCoefficientSet Λ (t * w₂),
      ‖c (((t * w₂ : ℕ) : ℤ) * a)‖ ^ 2) ≤ τ * ∑ l ∈ Λ, ‖c l‖ ^ 2 := by
  calc
    _ = ∑ t ∈ T, ∑ l ∈ Λ with ((t * w₂ : ℕ) : ℤ) ∣ l, ‖c l‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro t _
      exact incidenceDividedCoefficient_sum Λ (t * w₂) (fun l => ‖c l‖ ^ 2)
    _ ≤ ∑ t ∈ T, ∑ l ∈ Λ with t ∈ l.natAbs.divisors, ‖c l‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro t _
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro l hl
        obtain ⟨hl, hd⟩ := Finset.mem_filter.mp hl
        have ht : (t : ℤ) ∣ l := (show (t : ℤ) ∣ ((t * w₂ : ℕ) : ℤ) by
          simp only [Nat.cast_mul]; exact dvd_mul_right _ _).trans hd
        exact Finset.mem_filter.mpr ⟨hl, Nat.mem_divisors.mpr
          ⟨Int.natCast_dvd.mp ht, Int.natAbs_ne_zero.mpr (hΛ0 l hl)⟩⟩
      · intro l _ _
        exact sq_nonneg _
    _ ≤ _ := incidenceDivisorSectors_energy_le T Λ c τ hτ

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceDividedCoefficientSet_mem
#print axioms PrimeGap182Audit.incidenceDividedCoefficientSet_card
#print axioms PrimeGap182Audit.incidenceDividedCoefficient_sum
#print axioms PrimeGap182Audit.incidenceDividedCoefficient_isUnit
#print axioms PrimeGap182Audit.incidenceDividedCoefficient_dyadic
#print axioms PrimeGap182Audit.incidenceIntegerDyadic_card
#print axioms PrimeGap182Audit.incidenceSectorCoefficients_energy_sum
