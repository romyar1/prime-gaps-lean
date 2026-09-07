import IncidenceFrequencyBlock

/-!
# Coefficients for the actual public source block

The public selector supplies H ≤ L q₀ V, rather than H ≤ V. The
fiber count below therefore retains q₀. Squaring the pointwise bound
retains q₀²; no stronger source-scale assumption is made.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators

theorem incidenceQuotientFrequency_fiber_card_le (H v₁ v₂ w₁ q₀ : ℕ)
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) (hq₀ : 1 ≤ q₀)
    (V L : ℝ) (hV : 0 < V) (hL : 1 ≤ L)
    (hHV : (H : ℝ) ≤ L * q₀ * V) (hVmax : V ≤ (max v₁ v₂ : ℕ))
    (S : Finset (ℤ × ℤ)) (hS : S ⊆ incidenceFrequencyWindow H)
    (hd : ∀ h ∈ S, (w₁ : ℤ) ∣ incidenceReducedFrequency v₁ v₂ h) (y : ℤ) :
    ((S.filter (fun h => incidenceQuotientFrequency w₁ v₁ v₂ h = y)).card : ℝ) ≤
      3 * L * q₀ * (Nat.gcd v₁ v₂ : ℝ) := by
  have hb := (PrimeGap186.secondary_frequency_symmetric_window_counts H v₁ v₂
    hv₁ hv₂).2.2.2 V hV hVmax ((w₁ : ℤ) * y)
  have hsub : S.filter (fun h => incidenceQuotientFrequency w₁ v₁ v₂ h = y) ⊆
      (incidenceFrequencyWindow H).filter
        (fun h => incidenceReducedFrequency v₁ v₂ h = (w₁ : ℤ) * y) := by
    intro h hh
    obtain ⟨hh, hy⟩ := Finset.mem_filter.mp hh
    refine Finset.mem_filter.mpr ⟨hS hh, ?_⟩
    rw [← incidenceQuotientFrequency_mul w₁ v₁ v₂ h (hd h hh), hy]
  have hc : ((S.filter (fun h => incidenceQuotientFrequency w₁ v₁ v₂ h = y)).card : ℝ) ≤
      1 + 2 * (Nat.gcd v₁ v₂ : ℝ) * H / V :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hb
  have hg : (1 : ℝ) ≤ Nat.gcd v₁ v₂ := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.gcd_pos_of_pos_left v₂ hv₁)
  have hq : (1 : ℝ) ≤ q₀ := by exact_mod_cast hq₀
  have hLq : 1 ≤ L * q₀ := one_le_mul_of_one_le_of_one_le hL hq
  have hLqg : 1 ≤ L * q₀ * (Nat.gcd v₁ v₂ : ℝ) :=
    one_le_mul_of_one_le_of_one_le hLq hg
  have hfrac : 2 * (Nat.gcd v₁ v₂ : ℝ) * H / V ≤
      2 * (Nat.gcd v₁ v₂ : ℝ) * (L * q₀) := by
    apply (div_le_iff₀ hV).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hHV
      (show 0 ≤ 2 * (Nat.gcd v₁ v₂ : ℝ) by positivity)]
  nlinarith only [hc, hfrac, hLqg]

theorem incidenceQuotientFrequency_coefficients (H v₁ v₂ w₁ q₀ : ℕ)
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) (hq₀ : 1 ≤ q₀)
    (V L : ℝ) (hV : 0 < V) (hL : 1 ≤ L)
    (hHV : (H : ℝ) ≤ L * q₀ * V) (hVmax : V ≤ (max v₁ v₂ : ℕ))
    (S : Finset (ℤ × ℤ)) (hS : S ⊆ incidenceFrequencyWindow H)
    (hd : ∀ h ∈ S, (w₁ : ℤ) ∣ incidenceReducedFrequency v₁ v₂ h)
    (a : ℤ × ℤ → ℂ) (B : ℝ) (hB : 0 ≤ B) (ha : ∀ h ∈ S, ‖a h‖ ≤ B) :
    (∀ y, ‖incidenceGroupedCoefficient S (incidenceQuotientFrequency w₁ v₁ v₂) a y‖ ≤
      3 * L * q₀ * (Nat.gcd v₁ v₂ : ℝ) * B) ∧
    (∀ Y : Finset ℤ, (∑ y ∈ Y,
      ‖incidenceGroupedCoefficient S (incidenceQuotientFrequency w₁ v₁ v₂) a y‖ ^ 2) ≤
        3 * L * q₀ * (Nat.gcd v₁ v₂ : ℝ) * B ^ 2 * S.card) := by
  have hf := incidenceQuotientFrequency_fiber_card_le H v₁ v₂ w₁ q₀
    hv₁ hv₂ hq₀ V L hV hL hHV hVmax S hS hd
  exact ⟨incidenceGroupedCoefficient_norm_le S _ a _ B hB hf ha,
    fun Y => incidenceGroupedCoefficient_energy_card_le S _ a Y _ B
      (by positivity) hf ha⟩

theorem incidenceSourceFrequencyBlock_subset (H : ℕ) (J : Finset ℤ)
    (hJ : J ⊆ (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (fun h => h ≠ 0))
    (v₁ v₂ m w₁ w₂ : ℕ) (Y : ℤ) :
    incidenceSourceFrequencyBlock J v₁ v₂ m w₁ w₂ Y ⊆ incidenceFrequencyWindow H := by
  intro h hh
  obtain ⟨hh₁, hh₂⟩ := Finset.mem_product.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).1
  exact Finset.mem_product.mpr ⟨hJ hh₁, hJ hh₂⟩

def incidenceSourceQuotientSet (J : Finset ℤ) (v₁ v₂ m w₁ w₂ : ℕ) (Y : ℤ) :
    Finset ℤ :=
  (incidenceSourceFrequencyBlock J v₁ v₂ m w₁ w₂ Y).image
    (incidenceQuotientFrequency w₁ v₁ v₂)

theorem incidenceSourceQuotientSet_properties (J : Finset ℤ) (v₁ v₂ m w₁ w₂ : ℕ)
    (hm : m ≠ 0) (hw : 0 < w₁) (hwm : Nat.Coprime w₁ m) (Y : ℤ)
    (l : ℤ) (hl : l ∈ incidenceSourceQuotientSet J v₁ v₂ m w₁ w₂ Y) :
    l ≠ 0 ∧ 0 < w₂ ∧ (w₂ : ℤ) ∣ l ∧ IsUnit ((l / (w₂ : ℤ) : ℤ) : ZMod m) ∧
      0 < |(Y : ℝ)| / w₁ ∧ |(Y : ℝ)| / w₁ ≤ |(l : ℝ)| ∧
      |(l : ℝ)| ≤ 2 * (|(Y : ℝ)| / w₁) := by
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hl
  have hp := incidenceSourceFrequencyBlock_quotient J v₁ v₂ m w₁ w₂ hm hw.ne' hwm Y h hh
  have hb := incidenceSourceFrequencyBlock_dyadic J v₁ v₂ m w₁ w₂ hw Y h hh
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hb⟩

theorem incidenceSourceFrequencyBlock_coefficients (H : ℕ) (J : Finset ℤ)
    (hJ : J ⊆ (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (fun h => h ≠ 0))
    (v₁ v₂ m w₁ w₂ q₀ : ℕ) (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) (hq₀ : 1 ≤ q₀)
    (V L : ℝ) (hV : 0 < V) (hL : 1 ≤ L)
    (hHV : (H : ℝ) ≤ L * q₀ * V) (hVmax : V ≤ (max v₁ v₂ : ℕ))
    (Y : ℤ) (a : ℤ × ℤ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ h ∈ incidenceSourceFrequencyBlock J v₁ v₂ m w₁ w₂ Y, ‖a h‖ ≤ B) :
    let S := incidenceSourceFrequencyBlock J v₁ v₂ m w₁ w₂ Y
    let c := incidenceGroupedCoefficient S (incidenceQuotientFrequency w₁ v₁ v₂) a
    (∀ l, ‖c l‖ ≤ 3 * L * q₀ * (Nat.gcd v₁ v₂ : ℝ) * B) ∧
    (∀ Λ : Finset ℤ, (∑ l ∈ Λ, ‖c l‖ ^ 2) ≤
      3 * L * q₀ * (Nat.gcd v₁ v₂ : ℝ) * B ^ 2 * S.card) := by
  exact incidenceQuotientFrequency_coefficients H v₁ v₂ w₁ q₀ hv₁ hv₂ hq₀
    V L hV hL hHV hVmax _ (incidenceSourceFrequencyBlock_subset H J hJ _ _ _ _ _ Y)
    (fun _ hh => (Finset.mem_filter.mp hh).2.1) a B hB ha

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceQuotientFrequency_fiber_card_le
#print axioms PrimeGap182Audit.incidenceQuotientFrequency_coefficients
#print axioms PrimeGap182Audit.incidenceSourceFrequencyBlock_subset
#print axioms PrimeGap182Audit.incidenceSourceQuotientSet_properties
#print axioms PrimeGap182Audit.incidenceSourceFrequencyBlock_coefficients
