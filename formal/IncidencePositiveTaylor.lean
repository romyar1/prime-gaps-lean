import IncidenceAmplitudeTaylor

/-!
# Positive energy after the actual two-factor Taylor expansion

The finite Taylor expansion is performed on the amplitude before its
absolute square. The remainder is bounded explicitly by the original
row masses. There is no assumption about positive four-factor Taylor
coefficients.
-/

noncomputable section
namespace PrimeGap182Audit
open Classical
open scoped BigOperators

set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem incidenceNorm_sq_le_twice (z w : ℂ) (E : ℝ) (hE : ‖z - w‖ ≤ E) :
    ‖z‖ ^ 2 ≤ 2 * ‖w‖ ^ 2 + 2 * E ^ 2 := by
  have hE0 := (norm_nonneg (z - w)).trans hE
  have hz : ‖z‖ ≤ E + ‖w‖ := by
    calc
      _ = ‖(z - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hE le_rfl
  have hs := pow_le_pow_left₀ (norm_nonneg z) hz 2
  nlinarith only [hs, sq_nonneg (E - ‖w‖)]

theorem incidencePositiveFiniteExpansion {ι κ : Type*} (Rows : Finset ι) (J : Finset κ)
    (ρ : ι → ℝ) (hρ : ∀ r ∈ Rows, 0 ≤ ρ r)
    (f : ι → ℂ) (u z : ι → κ → ℂ) (E : ι → ℝ)
    (hrem : ∀ r ∈ Rows, ‖f r - ∑ j ∈ J, u r j * z r j‖ ≤ E r) :
    (∑ r ∈ Rows, ρ r * ‖f r‖ ^ 2) ≤
      2 * (J.card : ℝ) * (∑ j ∈ J, ∑ r ∈ Rows, ρ r * ‖u r j‖ ^ 2 * ‖z r j‖ ^ 2) +
        2 * ∑ r ∈ Rows, ρ r * (E r) ^ 2 := by
  have hpoint (r : ι) (hr : r ∈ Rows) :
      ‖f r‖ ^ 2 ≤ 2 * (J.card : ℝ) * (∑ j ∈ J, ‖u r j‖ ^ 2 * ‖z r j‖ ^ 2) +
        2 * (E r) ^ 2 := by
    apply (incidenceNorm_sq_le_twice (f r) (∑ j ∈ J, u r j * z r j) (E r) (hrem r hr)).trans
    have hh := incidenceNormSum_sq_le J (fun j => u r j * z r j)
    simp only [norm_mul, mul_pow] at hh
    nlinarith only [hh]
  calc
    _ ≤ ∑ r ∈ Rows,
        (ρ r * (2 * (J.card : ℝ) * (∑ j ∈ J, ‖u r j‖ ^ 2 * ‖z r j‖ ^ 2) +
          2 * (E r) ^ 2)) :=
      Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (hpoint r hr) (hρ r hr))
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro r _
        ring
      · apply Finset.sum_congr rfl
        intro r _
        ring

theorem incidenceSourcePhi_positive_taylor (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ι κ : Type*) [DecidableEq ι] (I : Finset ι) (Rows : Finset κ)
        (c T M H L d₀ Δ₁ D : ℝ)
        (_ : 0 < c) (_ : c ≤ T) (_ : 0 < M) (_ : 0 ≤ H) (_ : 0 ≤ L)
        (_ : 0 < d₀) (_ : 0 < Δ₁) (_ : 0 ≤ D)
        (ψ : ℝ → ℝ) (_ : Function.support ψ ⊆ Set.Icc c T) (_ : ∀ y, |ψ y| ≤ L)
        (r₁ q₀ u₁ v₁ v₂ q₂ : ℕ)
        (_ : 0 < r₁ * q₀ * u₁ * v₁ * q₂ ∧ 0 < r₁ * q₀ * u₁ * v₂ * q₂)
        (h : ι → Fin 2 → ℤ) (_ : ∀ a ∈ I, ∀ i, |(h a i : ℝ)| ≤ H),
      let R₁ := r₁ * q₀ * u₁ * v₁ * q₂
      let R₂ := r₁ * q₀ * u₁ * v₂ * q₂
      let F : ι → ℝ → ℂ := fun a d =>
        PrimeGap186.sourcePhiRealFactor ψ M R₁ (h a 0) d *
          star (PrimeGap186.sourcePhiRealFactor ψ M R₂ (h a 1) d)
      let S := Δ₁ / d₀ *
        (1 + T * M * H / d₀ * ((R₁ : ℝ)⁻¹ + (R₂ : ℝ)⁻¹))
      let coeff : ι → ℕ → ℂ := fun a j =>
        (Δ₁ ^ j / (j.factorial : ℝ)) • iteratedDeriv j (F a) d₀
      (∀ a ∈ I, ∀ j ≤ J, ‖coeff a j‖ ≤ C * (T * L) ^ 2 * S ^ j) ∧
      ∀ d : κ → ℝ, (∀ r ∈ Rows, d₀ ≤ d r ∧ d r ≤ d₀ + D * Δ₁) →
      ∀ ρ : κ → ℝ, (∀ r ∈ Rows, 0 ≤ ρ r) → ∀ A : κ → ι → ℂ,
      (∑ r ∈ Rows, ρ r * ‖∑ a ∈ I, A r a * F a (d r)‖ ^ 2) ≤
        2 * (J + 1 : ℕ) *
          (∑ j ∈ Finset.range (J + 1), ∑ r ∈ Rows,
            ρ r * (((d r - d₀) / Δ₁) ^ j) ^ 2 * ‖∑ a ∈ I, A r a * coeff a j‖ ^ 2) +
        2 * (C * (T * L) ^ 2 * (D * S) ^ (J + 1)) ^ 2 *
          ∑ r ∈ Rows, ρ r * (∑ a ∈ I, ‖A r a‖) ^ 2 := by
  obtain ⟨C, hC, hTaylor⟩ := incidenceSourcePhi_twofold_taylor J
  refine ⟨C, hC, ?_⟩
  intro ι κ _ I Rows c T M H L d₀ Δ₁ D hc hcT hM hH hL hd₀ hΔ₁ hD ψ hsψ hψ
    r₁ q₀ u₁ v₁ v₂ q₂ hperiods h hh R₁ R₂ F S coeff
  have ht := hTaylor ι I c T M H L d₀ Δ₁ D hc hcT hM hH hL hd₀ hΔ₁ hD ψ hsψ hψ
    r₁ q₀ u₁ v₁ v₂ q₂ hperiods h hh
  refine ⟨ht.1, ?_⟩
  intro d hd ρ hρ A
  let χ : ℝ → ℝ := fun y => if y ∈ Set.Icc 0 (D * Δ₁) then 1 else 0
  have hχ : Function.support χ ⊆ Set.Icc 0 (D * Δ₁) := by
    intro y hy
    by_contra hn
    exact hy (ite_eq_right hn)
  let Berr := C * (T * L) ^ 2 * (D * S) ^ (J + 1)
  have hrem (r : κ) (hr : r ∈ Rows) :
      ‖(∑ a ∈ I, A r a * F a (d r)) -
        ∑ j ∈ Finset.range (J + 1),
          ((((d r - d₀) / Δ₁) ^ j : ℝ) : ℂ) * (∑ a ∈ I, A r a * coeff a j)‖ ≤
        Berr * ∑ a ∈ I, ‖A r a‖ := by
    have hχr : χ (d r - d₀) = 1 := by
      exact ite_eq_left (show d r - d₀ ∈ Set.Icc 0 (D * Δ₁) by
        constructor <;> linarith [(hd r hr).1, (hd r hr).2])
    have hb := ht.2 χ hχ (fun _ a => A r a) (d r)
    simpa only [hχr, Complex.ofReal_one, one_mul, abs_one] using hb
  have hp := incidencePositiveFiniteExpansion Rows (Finset.range (J + 1)) ρ hρ
    (fun r => ∑ a ∈ I, A r a * F a (d r))
    (fun r j => ((((d r - d₀) / Δ₁) ^ j : ℝ) : ℂ))
    (fun r j => ∑ a ∈ I, A r a * coeff a j)
    (fun r => Berr * ∑ a ∈ I, ‖A r a‖) hrem
  have herr : (2 : ℝ) * (∑ r ∈ Rows, ρ r * (Berr * ∑ a ∈ I, ‖A r a‖) ^ 2) =
      2 * Berr ^ 2 * ∑ r ∈ Rows, ρ r * (∑ a ∈ I, ‖A r a‖) ^ 2 := by
    conv_lhs => rw [Finset.mul_sum]
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [herr] at hp
  simpa only [Finset.card_range, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hp

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceNorm_sq_le_twice
#print axioms PrimeGap182Audit.incidencePositiveFiniteExpansion
#print axioms PrimeGap182Audit.incidenceSourcePhi_positive_taylor
