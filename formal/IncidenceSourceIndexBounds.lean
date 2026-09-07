import IncidenceSourceCoefficients
import IncidenceRowPartition
import IncidenceEnergyRowSupport

/-! Actual heights and masses of the source row and coefficient index sets. -/

noncomputable section
namespace PrimeGap182Audit
open Classical
open scoped BigOperators

theorem incidenceRowDivisors_subset (D : Finset ℕ) (Dmax : ℕ)
    (hD : D ⊆ Finset.Icc 1 Dmax) :
    incidenceRowDivisors D ⊆ Finset.Icc 1 Dmax := by
  intro t ht
  obtain ⟨e, he, hte⟩ := Finset.mem_biUnion.mp ht
  exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hte,
    (Nat.le_of_dvd (Finset.mem_Icc.mp (hD he)).1 (Nat.dvd_of_mem_divisors hte)).trans
      (Finset.mem_Icc.mp (hD he)).2⟩

theorem incidenceSourceQuotientSet_height (J : Finset ℤ)
    (v₁ v₂ m w w₂ : ℕ) (Y : ℤ) (X : ℝ)
    (hheight : ∀ h ∈ incidenceSourceFrequencyBlock J v₁ v₂ m w w₂ Y,
      ((incidenceReducedFrequency v₁ v₂ h).natAbs : ℝ) ≤ X)
    (l : ℤ) (hl : l ∈ incidenceSourceQuotientSet J v₁ v₂ m w w₂ Y) :
    (l.natAbs : ℝ) ≤ X := by
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hl
  have hd := (Finset.mem_filter.mp hh).2.1
  dsimp only [incidenceQuotientFrequency]
  rw [Int.natAbs_ediv_of_dvd hd, Int.natAbs_natCast]
  exact (Nat.cast_le.mpr (Nat.div_le_self _ _)).trans (hheight h hh)

theorem incidenceDividedCoefficientSet_height (F : Finset ℤ) (d : ℕ) (X : ℝ)
    (hF : ∀ l ∈ F, l ≠ 0 ∧ (l.natAbs : ℝ) ≤ X)
    (a : ℤ) (ha : a ∈ incidenceDividedCoefficientSet F d) :
    a ≠ 0 ∧ (a.natAbs : ℝ) ≤ X := by
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hl, hd⟩ := Finset.mem_filter.mp hl
  have hmul := Int.mul_ediv_cancel' hd
  refine ⟨?_, ?_⟩
  · intro hz
    rw [hz, mul_zero] at hmul
    exact (hF l hl).1 hmul.symm
  · rw [Int.natAbs_ediv_of_dvd hd, Int.natAbs_natCast]
    exact (Nat.cast_le.mpr (Nat.div_le_self _ _)).trans (hF l hl).2

theorem incidenceSourceDividedCoefficientSet_card (J : Finset ℤ)
    (v₁ v₂ m w w₂ : ℕ) (Y : ℤ) (d : ℕ) (C H : ℝ)
    (_hCH : 0 ≤ C * H) (hJ : (J.card : ℝ) ≤ 5 * C * H) :
    ((incidenceDividedCoefficientSet
      (incidenceSourceQuotientSet J v₁ v₂ m w w₂ Y) d).card : ℝ) ≤
        25 * C ^ 2 * H ^ 2 := by
  have hsub : incidenceSourceFrequencyBlock J v₁ v₂ m w w₂ Y ⊆ J ×ˢ J :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  calc
    _ ≤ ((incidenceSourceQuotientSet J v₁ v₂ m w w₂ Y).card : ℝ) :=
      Nat.cast_le.mpr (incidenceDividedCoefficientSet_card _ _)
    _ ≤ ((incidenceSourceFrequencyBlock J v₁ v₂ m w w₂ Y).card : ℝ) :=
      Nat.cast_le.mpr Finset.card_image_le
    _ ≤ ((J ×ˢ J).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ = (J.card : ℝ) ^ 2 := by rw [Finset.card_product, Nat.cast_mul, pow_two]
    _ ≤ (5 * C * H) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hJ 2
    _ = _ := by ring

theorem incidenceSupportedRows_taylor_weight (Dmax w m J j : ℕ)
    (d₀ Δ₁ TD : ℝ) (hΔ₁ : 0 < Δ₁) (hTD : 1 ≤ TD) (hj : j ≤ J)
    (ψD : ℝ → ℝ) (hsD : Function.support ψD ⊆ Set.Icc 0 TD)
    (hψD : ∀ y, 0 ≤ ψD y ∧ ψD y ≤ 1)
    (e : ℕ) (he : e ∈ incidenceSupportedEnergyRows Dmax w m
      (fun d => ψD (((d : ℝ) - d₀) / Δ₁))) :
    let z := (((w : ℝ) * e - d₀) / Δ₁)
    0 ≤ ψD z * (z ^ j) ^ 2 ∧ ψD z * (z ^ j) ^ 2 ≤ TD ^ (2 * J) := by
  intro z
  have hlocal := incidenceSupportedEnergyRows_local Dmax w m d₀ Δ₁ 0 TD
    hΔ₁ le_rfl ψD hsD e he
  have hz0 : 0 ≤ z := div_nonneg (sub_nonneg.mpr hlocal.1) hΔ₁.le
  have hzTD : z ≤ TD := (div_le_iff₀ hΔ₁).mpr (by linarith only [hlocal.2.1])
  refine ⟨mul_nonneg (hψD z).1 (sq_nonneg _), ?_⟩
  calc
    ψD z * (z ^ j) ^ 2 ≤ (z ^ j) ^ 2 := mul_le_of_le_one_left (sq_nonneg _) (hψD z).2
    _ ≤ (TD ^ j) ^ 2 := pow_le_pow_left₀ (pow_nonneg hz0 _) (pow_le_pow_left₀ hz0 hzTD _) _
    _ = TD ^ (2 * j) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ _ := pow_le_pow_right₀ hTD (Nat.mul_le_mul_left 2 hj)

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceRowDivisors_subset
#print axioms PrimeGap182Audit.incidenceSourceQuotientSet_height
#print axioms PrimeGap182Audit.incidenceDividedCoefficientSet_height
#print axioms PrimeGap182Audit.incidenceSourceDividedCoefficientSet_card
#print axioms PrimeGap182Audit.incidenceSupportedRows_taylor_weight
