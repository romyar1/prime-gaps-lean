import IncidencePositiveTaylor
import IncidencePhysicalFeatures

/-!
# Positive Taylor separation of the literal physical source energy

This theorem applies the actual two-factor Fourier Taylor expansion to
the original physical rows. The error uses a proved finite row bound,
while each main term is again an actual physical energy with fixed
coefficients. The source masks may remain in the row-dependent χ.
-/

noncomputable section
namespace PrimeGap182Audit
open Classical
open scoped BigOperators

set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem incidencePhysicalSourcePhi_positive_taylor (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ι : Type*) [DecidableEq ι] (Fset : Finset ι)
        (c T M H L d₀ Δ₁ D : ℝ)
        (_ : 0 < c) (_ : c ≤ T) (_ : 0 < M) (_ : 0 ≤ H) (_ : 0 ≤ L)
        (_ : 0 < d₀) (_ : 0 < Δ₁) (_ : 0 ≤ D)
        (ψ : ℝ → ℝ) (_ : Function.support ψ ⊆ Set.Icc c T) (_ : ∀ y, |ψ y| ≤ L)
        (r₁ q₀ u₁ v₁ v₂ q₂ : ℕ)
        (_ : 0 < r₁ * q₀ * u₁ * v₁ * q₂ ∧ 0 < r₁ * q₀ * u₁ * v₂ * q₂)
        (h : ι → Fin 2 → ℤ) (_ : ∀ a ∈ Fset, ∀ i, |(h a i : ℝ)| ≤ H),
      let R₁ := r₁ * q₀ * u₁ * v₁ * q₂
      let R₂ := r₁ * q₀ * u₁ * v₂ * q₂
      let F : ι → ℝ → ℂ := fun a d =>
        PrimeGap186.sourcePhiRealFactor ψ M R₁ (h a 0) d *
          star (PrimeGap186.sourcePhiRealFactor ψ M R₂ (h a 1) d)
      let S := Δ₁ / d₀ *
        (1 + T * M * H / d₀ * ((R₁ : ℝ)⁻¹ + (R₂ : ℝ)⁻¹))
      let coeff : ι → ℕ → ℂ := fun a j =>
        (Δ₁ ^ j / (j.factorial : ℝ)) • iteratedDeriv j (F a) d₀
      (∀ a ∈ Fset, ∀ j ≤ J, ‖coeff a j‖ ≤ C * (T * L) ^ 2 * S ^ j) ∧
      ∀ m w : ℕ, ∀ [NeZero m] [NeZero w], ∀ A B : ℤ,
      ∀ Drows : Finset ℕ, ∀ ρ : ℕ → ℝ, (∀ e ∈ Drows, 0 ≤ ρ e) →
      (∀ e ∈ Drows, d₀ ≤ (w : ℝ) * e ∧ (w : ℝ) * e ≤ d₀ + D * Δ₁) →
      ∀ I : Finset ℤ, ∀ ell : ι → ℤ, ∀ χ : ℕ → ℤ → ℂ, ∀ LN : ℝ,
      0 ≤ LN → (∀ e ∈ Drows, ∀ n ∈ I, ‖χ e n‖ ≤ LN) →
      (∑ e ∈ Drows, ρ e * incidencePhysicalEnergyOrZero (m := m) (w := w) e A B
        (Fset.image ell) I (incidenceGroupedCoefficient Fset ell (fun a => F a ((w : ℝ) * e))) (χ e)) ≤
        2 * (J + 1 : ℕ) *
          (∑ j ∈ Finset.range (J + 1), ∑ e ∈ Drows,
            (ρ e * ((((w : ℝ) * e - d₀) / Δ₁) ^ j) ^ 2) *
              incidencePhysicalEnergyOrZero (m := m) (w := w) e A B (Fset.image ell) I
                (incidenceGroupedCoefficient Fset ell (fun a => coeff a j)) (χ e)) +
        2 * (C * (T * L) ^ 2 * (D * S) ^ (J + 1)) ^ 2 *
          (((Fset.card : ℝ) * (I.card : ℝ) * LN) ^ 2 * ∑ e ∈ Drows, ρ e * (e : ℝ)) := by
  obtain ⟨C, hC, hTaylor⟩ := incidenceSourcePhi_positive_taylor J
  refine ⟨C, hC, ?_⟩
  intro ι _ Fset c T M H L d₀ Δ₁ D hc hcT hM hH hL hd₀ hΔ₁ hD ψ hsψ hψ
    r₁ q₀ u₁ v₁ v₂ q₂ hperiods h hh R₁ R₂ F S coeff
  have ht := hTaylor ι (ℕ × ℤ) Fset (∅ : Finset (ℕ × ℤ))
    c T M H L d₀ Δ₁ D hc hcT hM hH hL hd₀ hΔ₁ hD ψ hsψ hψ
    r₁ q₀ u₁ v₁ v₂ q₂ hperiods h hh
  refine ⟨ht.1, ?_⟩
  intro m w _ _ A B Drows ρ hρ hlocal I ell χ LN hLN hχ
  let Arow (p : ℕ × ℤ) (a : ι) : ℂ :=
    incidencePhysicalFeature (m := m) (w := w) p.1 A B I (χ p.1) p.2 (ell a)
  have hp := (hTaylor ι (ℕ × ℤ) Fset (incidenceOriginalRows Drows)
    c T M H L d₀ Δ₁ D hc hcT hM hH hL hd₀ hΔ₁ hD ψ hsψ hψ
    r₁ q₀ u₁ v₁ v₂ q₂ hperiods h hh).2
    (fun p => (w : ℝ) * p.1)
    (fun p hp => hlocal p.1 ((incidenceOriginalRows_mem Drows p).mp hp).1)
    (fun p => ρ p.1) (fun p hp => hρ p.1 ((incidenceOriginalRows_mem Drows p).mp hp).1) Arow
  have hleft := incidenceWeightedPhysicalEnergy_features (m := m) (w := w)
    A B Drows ρ Fset I ell (fun e a => F a ((w : ℝ) * e)) χ
  change _ = ∑ p ∈ incidenceOriginalRows Drows, ρ p.1 *
    ‖∑ a ∈ Fset, Arow p a * F a ((w : ℝ) * p.1)‖ ^ 2 at hleft
  rw [← hleft] at hp
  have hmain (j : ℕ) :
      (∑ p ∈ incidenceOriginalRows Drows,
        ρ p.1 * ((((w : ℝ) * p.1 - d₀) / Δ₁) ^ j) ^ 2 *
          ‖∑ a ∈ Fset, Arow p a * coeff a j‖ ^ 2) =
      ∑ e ∈ Drows, (ρ e * ((((w : ℝ) * e - d₀) / Δ₁) ^ j) ^ 2) *
        incidencePhysicalEnergyOrZero (m := m) (w := w) e A B (Fset.image ell) I
          (incidenceGroupedCoefficient Fset ell (fun a => coeff a j)) (χ e) := by
    exact (incidenceWeightedPhysicalEnergy_features (m := m) (w := w) A B Drows
      (fun e => ρ e * ((((w : ℝ) * e - d₀) / Δ₁) ^ j) ^ 2) Fset I ell
      (fun _ a => coeff a j) χ).symm
  change _ ≤ 2 * (J + 1 : ℕ) *
    (∑ j ∈ Finset.range (J + 1), ∑ p ∈ incidenceOriginalRows Drows,
      ρ p.1 * ((((w : ℝ) * p.1 - d₀) / Δ₁) ^ j) ^ 2 *
        ‖∑ a ∈ Fset, Arow p a * coeff a j‖ ^ 2) +
    2 * (C * (T * L) ^ 2 * (D * S) ^ (J + 1)) ^ 2 *
      ∑ p ∈ incidenceOriginalRows Drows, ρ p.1 * (∑ a ∈ Fset, ‖Arow p a‖) ^ 2 at hp
  simp_rw [hmain] at hp
  apply hp.trans
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left
    (incidencePhysicalFeature_remainder_mass (m := m) (w := w)
      A B Drows ρ hρ Fset I ell χ LN hLN hχ) (by positivity)

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidencePhysicalSourcePhi_positive_taylor
