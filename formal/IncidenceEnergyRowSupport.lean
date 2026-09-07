import IncidenceEnergyRows

/-!
# Actual source row support and its finite mass

The support restriction is an exact equality for the weighted energy.
The smooth d profile then supplies every local Taylor interval bound.
-/

noncomputable section
namespace PrimeGap182Audit
open Classical
open scoped BigOperators

def incidenceSupportedEnergyRows (Dmax w m : ℕ) (ρ : ℕ → ℝ) : Finset ℕ :=
  (incidenceEnergyRows Dmax w m).filter (fun e => ρ (w * e) ≠ 0)

theorem incidenceEnergyRows_weighted_support (Dmax w m : ℕ) (ρ f : ℕ → ℝ) :
    (∑ e ∈ incidenceEnergyRows Dmax w m, ρ (w * e) * f e) =
      ∑ e ∈ incidenceSupportedEnergyRows Dmax w m ρ, ρ (w * e) * f e := by
  rw [incidenceSupportedEnergyRows, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : ρ (w * e) = 0
  · simp only [he, zero_mul, ne_self_iff_false, ite_false]
  · exact (ite_eq_left he).symm

theorem incidenceSupportedEnergyRows_mem (Dmax w m : ℕ) (ρ : ℕ → ℝ) (e : ℕ) :
    e ∈ incidenceSupportedEnergyRows Dmax w m ρ ↔
      0 < e ∧ e ≤ Dmax / w ∧ Nat.Coprime e w ∧ Nat.Coprime e m ∧ ρ (w * e) ≠ 0 := by
  simp only [incidenceSupportedEnergyRows, incidenceEnergyRows, Finset.mem_filter,
    Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨he, hmax⟩, hew, hem⟩, hρ⟩
    exact ⟨he, hmax, hew, hem, hρ⟩
  · rintro ⟨he, hmax, hew, hem, hρ⟩
    exact ⟨⟨⟨he, hmax⟩, hew, hem⟩, hρ⟩

theorem incidenceSupportedEnergyRows_local (Dmax w m : ℕ)
    (d₀ Δ₁ cD TD : ℝ) (hΔ₁ : 0 < Δ₁) (hcD : 0 ≤ cD)
    (ψD : ℝ → ℝ) (hsD : Function.support ψD ⊆ Set.Icc cD TD)
    (e : ℕ) (he : e ∈ incidenceSupportedEnergyRows Dmax w m
      (fun d => ψD (((d : ℝ) - d₀) / Δ₁))) :
    d₀ ≤ (w : ℝ) * e ∧ (w : ℝ) * e ≤ d₀ + TD * Δ₁ ∧
      |(w : ℝ) * e - d₀| ≤ TD * Δ₁ := by
  have hs := hsD ((incidenceSupportedEnergyRows_mem _ _ _ _ _).mp he).2.2.2.2
  simp only [Nat.cast_mul, Set.mem_Icc] at hs
  have hlo := (le_div_iff₀ hΔ₁).mp hs.1
  have hhi := (div_le_iff₀ hΔ₁).mp hs.2
  have hn : 0 ≤ (w : ℝ) * e - d₀ := (mul_nonneg hcD hΔ₁.le).trans hlo
  exact ⟨by linarith, by linarith, by simpa only [abs_of_nonneg hn] using hhi⟩

theorem incidenceFiniteRows_mass (Dmax w : ℕ) (D : Finset ℕ)
    (hD : D ⊆ Finset.Icc 1 (Dmax / w)) (ρ : ℕ → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hρ : ∀ e ∈ D, ρ e ≤ L) :
    (∑ e ∈ D, ρ e * (e : ℝ)) ≤ L * ((Dmax : ℝ) / w) ^ 2 := by
  have hcard : (D.card : ℝ) ≤ ((Dmax / w : ℕ) : ℝ) := by
    exact_mod_cast (Finset.card_le_card hD).trans_eq (by simp)
  have hcast : ((Dmax / w : ℕ) : ℝ) ≤ (Dmax : ℝ) / w := Nat.cast_div_le
  calc
    _ ≤ ∑ _e ∈ D, L * ((Dmax / w : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro e he
      exact mul_le_mul (hρ e he) (Nat.cast_le.mpr (Finset.mem_Icc.mp (hD he)).2)
        (Nat.cast_nonneg e) hL
    _ = (D.card : ℝ) * L * ((Dmax / w : ℕ) : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    _ ≤ ((Dmax / w : ℕ) : ℝ) * L * ((Dmax / w : ℕ) : ℝ) := by gcongr
    _ ≤ ((Dmax : ℝ) / w) * L * ((Dmax : ℝ) / w) := by gcongr
    _ = _ := by ring

theorem incidenceSupportedEnergyRows_mass (Dmax w m : ℕ) (ρ : ℕ → ℝ)
    (L : ℝ) (hL : 0 ≤ L) (hρ : ∀ d, ρ d ≤ L) :
    (∑ e ∈ incidenceSupportedEnergyRows Dmax w m ρ, ρ (w * e) * (e : ℝ)) ≤
      L * ((Dmax : ℝ) / w) ^ 2 := by
  apply incidenceFiniteRows_mass Dmax w _ _ (fun e => ρ (w * e)) L hL
    (fun e _ => hρ (w * e))
  intro e he
  have hh := (incidenceSupportedEnergyRows_mem Dmax w m ρ e).mp he
  exact Finset.mem_Icc.mpr ⟨hh.1, hh.2.1⟩

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceEnergyRows_weighted_support
#print axioms PrimeGap182Audit.incidenceSupportedEnergyRows_mem
#print axioms PrimeGap182Audit.incidenceSupportedEnergyRows_local
#print axioms PrimeGap182Audit.incidenceFiniteRows_mass
#print axioms PrimeGap182Audit.incidenceSupportedEnergyRows_mass
