import IncidenceFareyUniform

/-!
# Actual grouped Type II frequency coefficients

The coefficients below are the sums on the actual fibers of the reduced
frequency map. Their square norm is bounded before any source incidence
estimate. The source specialization uses the baseline's proved integer
fiber count, and the divisor-sector estimate counts each original index
by its actual number of positive divisors.
-/

noncomputable section

namespace PrimeGap182Audit

open scoped BigOperators

def incidenceGroupedCoefficient {ι κ : Type*} [DecidableEq κ]
    (S : Finset ι) (φ : ι → κ) (a : ι → ℂ) (y : κ) : ℂ :=
  ∑ h ∈ S with φ h = y, a h

theorem incidenceNormSum_sq_le {ι : Type*} (S : Finset ι) (a : ι → ℂ) :
    ‖∑ h ∈ S, a h‖ ^ 2 ≤ (S.card : ℝ) * ∑ h ∈ S, ‖a h‖ ^ 2 := by
  calc
    _ ≤ (∑ h ∈ S, ‖a h‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := sq_sum_le_card_mul_sum_sq

theorem incidenceGroupedCoefficient_norm_le {ι κ : Type*} [DecidableEq κ]
    (S : Finset ι) (φ : ι → κ) (a : ι → ℂ) (M L : ℝ)
    (hL : 0 ≤ L) (hM : ∀ y, ((S.filter (fun h => φ h = y)).card : ℝ) ≤ M)
    (ha : ∀ h ∈ S, ‖a h‖ ≤ L) (y : κ) :
    ‖incidenceGroupedCoefficient S φ a y‖ ≤ M * L := by
  calc
    _ ≤ ∑ h ∈ S with φ h = y, ‖a h‖ := norm_sum_le _ _
    _ ≤ ∑ _h ∈ S with φ _h = y, L :=
      Finset.sum_le_sum (fun h hh => ha h (Finset.mem_filter.mp hh).1)
    _ = ((S.filter (fun h => φ h = y)).card : ℝ) * L := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ M * L := mul_le_mul_of_nonneg_right (hM y) hL

theorem incidenceGroupedCoefficient_energy_le {ι κ : Type*} [DecidableEq κ]
    (S : Finset ι) (φ : ι → κ) (a : ι → ℂ) (Y : Finset κ) (M : ℝ)
    (hM : ∀ y, ((S.filter (fun h => φ h = y)).card : ℝ) ≤ M) :
    (∑ y ∈ Y, ‖incidenceGroupedCoefficient S φ a y‖ ^ 2) ≤
      M * ∑ h ∈ S, ‖a h‖ ^ 2 := by
  classical
  by_cases hY : Y = ∅
  · subst Y
    by_cases hS : S = ∅
    · simp [hS]
    · obtain ⟨h, hh⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      have hM0 : 0 ≤ M := (Nat.cast_nonneg _).trans (hM (φ h))
      simp only [Finset.sum_empty]
      positivity
  obtain ⟨y₀, _⟩ := Finset.nonempty_iff_ne_empty.mpr hY
  have hM0 : 0 ≤ M := (Nat.cast_nonneg _).trans (hM y₀)
  calc
    _ ≤ ∑ y ∈ Y, M * ∑ h ∈ S with φ h = y, ‖a h‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro y _
      exact (incidenceNormSum_sq_le (S.filter (fun h => φ h = y)) a).trans
        (mul_le_mul_of_nonneg_right (hM y) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    _ = M * ∑ h ∈ S with φ h ∈ Y, ‖a h‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_fiberwise_eq_sum_filter]
    _ ≤ M * ∑ h ∈ S, ‖a h‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => sq_nonneg _)) hM0

theorem incidenceGroupedCoefficient_energy_card_le {ι κ : Type*} [DecidableEq κ]
    (S : Finset ι) (φ : ι → κ) (a : ι → ℂ) (Y : Finset κ) (M L : ℝ)
    (hM0 : 0 ≤ M)
    (hM : ∀ y, ((S.filter (fun h => φ h = y)).card : ℝ) ≤ M)
    (ha : ∀ h ∈ S, ‖a h‖ ≤ L) :
    (∑ y ∈ Y, ‖incidenceGroupedCoefficient S φ a y‖ ^ 2) ≤
      M * L ^ 2 * S.card := by
  calc
    _ ≤ M * ∑ h ∈ S, ‖a h‖ ^ 2 := incidenceGroupedCoefficient_energy_le S φ a Y M hM
    _ ≤ M * ∑ _h ∈ S, L ^ 2 := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun h hh => pow_le_pow_left₀ (norm_nonneg _) (ha h hh) 2)) hM0
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

def incidenceFrequencyWindow (H : ℕ) : Finset (ℤ × ℤ) :=
  let J := (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (fun h => h ≠ 0)
  J.product J

def incidenceReducedFrequency (v₁ v₂ : ℕ) (h : ℤ × ℤ) : ℤ :=
  h.1 * ((v₂ / Nat.gcd v₁ v₂ : ℕ) : ℤ) -
    h.2 * ((v₁ / Nat.gcd v₁ v₂ : ℕ) : ℤ)

/-- The actual source frequency fibers have size at most three times
the gcd once the source scale dominates the frequency radius. -/
theorem incidenceFrequency_fiber_card_le (H v₁ v₂ : ℕ)
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) (V : ℝ) (hV : 0 < V)
    (hHV : (H : ℝ) ≤ V) (hVmax : V ≤ (max v₁ v₂ : ℕ))
    (S : Finset (ℤ × ℤ)) (hS : S ⊆ incidenceFrequencyWindow H) (y : ℤ) :
    ((S.filter (fun h => incidenceReducedFrequency v₁ v₂ h = y)).card : ℝ) ≤
      3 * (Nat.gcd v₁ v₂ : ℝ) := by
  have hb := (PrimeGap186.secondary_frequency_symmetric_window_counts H v₁ v₂
    hv₁ hv₂).2.2.2 V hV hVmax y
  have hg : (1 : ℝ) ≤ Nat.gcd v₁ v₂ := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.gcd_pos_of_pos_left v₂ hv₁)
  have hsub : S.filter (fun h => incidenceReducedFrequency v₁ v₂ h = y) ⊆
      (incidenceFrequencyWindow H).filter (fun h => incidenceReducedFrequency v₁ v₂ h = y) :=
    Finset.filter_subset_filter _ hS
  have hc : ((S.filter (fun h => incidenceReducedFrequency v₁ v₂ h = y)).card : ℝ) ≤
      1 + 2 * (Nat.gcd v₁ v₂ : ℝ) * H / V :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hb
  have hfrac : 2 * (Nat.gcd v₁ v₂ : ℝ) * H / V ≤ 2 * (Nat.gcd v₁ v₂ : ℝ) := by
    apply (div_le_iff₀ hV).mpr
    exact mul_le_mul_of_nonneg_left hHV (by positivity)
  linarith

theorem incidenceFrequency_coefficients (H v₁ v₂ : ℕ)
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) (V : ℝ) (hV : 0 < V)
    (hHV : (H : ℝ) ≤ V) (hVmax : V ≤ (max v₁ v₂ : ℕ))
    (S : Finset (ℤ × ℤ)) (hS : S ⊆ incidenceFrequencyWindow H)
    (a : ℤ × ℤ → ℂ) (L : ℝ) (hL : 0 ≤ L) (ha : ∀ h ∈ S, ‖a h‖ ≤ L) :
    (∀ y, ‖incidenceGroupedCoefficient S (incidenceReducedFrequency v₁ v₂) a y‖ ≤
      3 * (Nat.gcd v₁ v₂ : ℝ) * L) ∧
    (∀ Y : Finset ℤ, (∑ y ∈ Y,
      ‖incidenceGroupedCoefficient S (incidenceReducedFrequency v₁ v₂) a y‖ ^ 2) ≤
        3 * (Nat.gcd v₁ v₂ : ℝ) * L ^ 2 * S.card) := by
  have hM := incidenceFrequency_fiber_card_le H v₁ v₂ hv₁ hv₂ V hV hHV hVmax S hS
  exact ⟨incidenceGroupedCoefficient_norm_le S _ a _ L hL hM ha,
    fun Y => incidenceGroupedCoefficient_energy_card_le S _ a Y _ L
      (by positivity) hM ha⟩

/-- Expanding the coprimality condition by positive divisors counts each
nonzero source index at most its actual divisor count. -/
theorem incidenceDivisorSectors_energy_le (T : Finset ℕ) (Y : Finset ℤ)
    (c : ℤ → ℂ) (τ : ℝ)
    (hτ : ∀ y ∈ Y, (y.natAbs.divisors.card : ℝ) ≤ τ) :
    (∑ t ∈ T, ∑ y ∈ Y with t ∈ y.natAbs.divisors, ‖c y‖ ^ 2) ≤
      τ * ∑ y ∈ Y, ‖c y‖ ^ 2 := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  have hc : ((T.filter (fun t => t ∈ y.natAbs.divisors)).card : ℝ) ≤ τ :=
    (Nat.cast_le.mpr (Finset.card_le_card (by
      intro t ht
      exact (Finset.mem_filter.mp ht).2))).trans (hτ y hy)
  calc
    _ = ((T.filter (fun t => t ∈ y.natAbs.divisors)).card : ℝ) * ‖c y‖ ^ 2 := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ τ * ‖c y‖ ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)

#print axioms incidenceNormSum_sq_le
#print axioms incidenceGroupedCoefficient_norm_le
#print axioms incidenceGroupedCoefficient_energy_le
#print axioms incidenceGroupedCoefficient_energy_card_le
#print axioms incidenceFrequency_fiber_card_le
#print axioms incidenceFrequency_coefficients
#print axioms incidenceDivisorSectors_energy_le

end PrimeGap182Audit
