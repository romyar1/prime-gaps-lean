import IncidenceEnergyRowSupport

/-!
# Positive Taylor expansion of the original d-summed source block

All row restrictions follow from the original frequency gcd gate and the
support of ψD. The actual source numerator, including its two gcd masks,
is retained in each fixed-coefficient main term.
-/

noncomputable section
namespace PrimeGap182Audit
open Classical
open scoped BigOperators

set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem incidenceSourceNumerator_norm (r₁ q₀ u₁ v₁ v₂ q₂ d : ℕ)
    (ℓ : ℤ) (E : ZMod q₀ → Finset (ZMod q₀)) (ψN : ℝ → ℝ) (N LN : ℝ)
    (hLN : 0 ≤ LN) (hψN : ∀ y, |ψN y| ≤ LN) (n : ℤ) :
    ‖incidenceSourceNumerator r₁ q₀ u₁ v₁ v₂ q₂ d ℓ E ψN N n‖ ≤ LN := by
  unfold incidenceSourceNumerator
  split_ifs
  · simpa only [one_mul, Complex.norm_real, Real.norm_eq_abs] using hψN ((n : ℝ) / N)
  · simpa only [zero_mul, norm_zero] using hLN
  · simpa only [norm_zero] using hLN

theorem incidenceRawSource_positive_taylor (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Fset : Finset (ℤ × ℤ)) (c T M H LM LN d₀ Δ₁ TD : ℝ),
      0 < c → c ≤ T → 0 < M → 0 ≤ H → 0 ≤ LM → 0 ≤ LN →
      0 < d₀ → 0 < Δ₁ → 0 ≤ TD →
      ∀ ψM ψN ψD : ℝ → ℝ,
      Function.support ψM ⊆ Set.Icc c T → (∀ y, |ψM y| ≤ LM) →
      (∀ y, |ψN y| ≤ LN) → Function.support ψD ⊆ Set.Icc 0 TD →
      (∀ y, 0 ≤ ψD y ∧ ψD y ≤ 1) →
      ∀ r₁ q₀ u₁ v₁ v₂ q₂ : ℕ,
      0 < r₁ * q₀ * u₁ * v₁ * q₂ ∧ 0 < r₁ * q₀ * u₁ * v₂ * q₂ →
      (∀ h ∈ Fset, |(h.1 : ℝ)| ≤ H ∧ |(h.2 : ℝ)| ≤ H) →
      let R₁ := r₁ * q₀ * u₁ * v₁ * q₂
      let R₂ := r₁ * q₀ * u₁ * v₂ * q₂
      let F : (ℤ × ℤ) → ℝ → ℂ := fun h d =>
        PrimeGap186.sourcePhiRealFactor ψM M R₁ h.1 d *
          star (PrimeGap186.sourcePhiRealFactor ψM M R₂ h.2 d)
      let S := Δ₁ / d₀ *
        (1 + T * M * H / d₀ * ((R₁ : ℝ)⁻¹ + (R₂ : ℝ)⁻¹))
      let coeff : (ℤ × ℤ) → ℕ → ℂ := fun h j =>
        (Δ₁ ^ j / (j.factorial : ℝ)) • iteratedDeriv j (F h) d₀
      (∀ h ∈ Fset, ∀ j ≤ J, ‖coeff h j‖ ≤ C * (T * LM) ^ 2 * S ^ j) ∧
      ∀ m w Dmax : ℕ, ∀ [NeZero m] [NeZero w], Nat.Coprime w m →
      ∀ A B ℓ : ℤ, ∀ E : ZMod q₀ → Finset (ZMod q₀), ∀ N : ℝ,
      ∀ I : Finset ℤ, ∀ ell : ℤ × ℤ → ℤ,
      let ρ : ℕ → ℝ := fun d => ψD (((d : ℝ) - d₀) / Δ₁)
      let Rows := incidenceSupportedEnergyRows Dmax w m ρ
      (incidenceRawBlockEnergy m w Dmax r₁ q₀ u₁ v₁ v₂ q₂ A B ℓ E ψN N
        Fset I ell (fun d h => F h (d : ℝ)) ρ).re ≤
        2 * (J + 1 : ℕ) *
          (∑ j ∈ Finset.range (J + 1), ∑ e ∈ Rows,
            (ρ (w * e) * ((((w : ℝ) * e - d₀) / Δ₁) ^ j) ^ 2) *
              incidencePhysicalEnergyOrZero (m := m) (w := w) e A B (Fset.image ell) I
                (incidenceGroupedCoefficient Fset ell (fun h => coeff h j))
                (incidenceSourceNumerator r₁ q₀ u₁ v₁ v₂ q₂ (w * e) ℓ E ψN N)) +
        2 * (C * (T * LM) ^ 2 * (TD * S) ^ (J + 1)) ^ 2 *
          ((Fset.card : ℝ) * (I.card : ℝ) * LN) ^ 2 * ((Dmax : ℝ) / w) ^ 2 := by
  obtain ⟨C, hC, hTaylor⟩ := incidencePhysicalSourcePhi_positive_taylor J
  refine ⟨C, hC, ?_⟩
  intro Fset c T M H LM LN d₀ Δ₁ TD hc hcT hM hH hLM hLN hd₀ hΔ₁ hTD
    ψM ψN ψD hsM hMbound hNbound hsD hDbound r₁ q₀ u₁ v₁ v₂ q₂ hperiods
    hF R₁ R₂ F S coeff
  let pair (h : ℤ × ℤ) (i : Fin 2) : ℤ := if i = 0 then h.1 else h.2
  have hpair (h : ℤ × ℤ) (hh : h ∈ Fset) (i : Fin 2) : |(pair h i : ℝ)| ≤ H := by
    fin_cases i
    · exact (hF h hh).1
    · exact (hF h hh).2
  have ht := hTaylor (ℤ × ℤ) Fset c T M H LM d₀ Δ₁ TD hc hcT hM hH hLM hd₀ hΔ₁ hTD
    ψM hsM hMbound r₁ q₀ u₁ v₁ v₂ q₂ hperiods pair hpair
  refine ⟨ht.1, ?_⟩
  intro m w Dmax _ _ hwm A B ℓ E N I ell ρ Rows
  have hρ (e : ℕ) : 0 ≤ ρ (w * e) := (hDbound _).1
  have hp := ht.2 m w A B Rows (fun e => ρ (w * e)) (fun e _ => hρ e)
    (fun e he => (incidenceSupportedEnergyRows_local Dmax w m d₀ Δ₁ 0 TD hΔ₁
      le_rfl ψD hsD e he).imp_right And.left)
    I ell (fun e => incidenceSourceNumerator r₁ q₀ u₁ v₁ v₂ q₂ (w * e) ℓ E ψN N)
    LN hLN (fun e _ n _ => incidenceSourceNumerator_norm r₁ q₀ u₁ v₁ v₂ q₂
      (w * e) ℓ E ψN N LN hLN hNbound n)
  have hr := congrArg Complex.re (incidenceRawBlockEnergy_eq hwm Dmax r₁ q₀ u₁ v₁ v₂ q₂
    A B ℓ E ψN N Fset I ell (fun d h => F h (d : ℝ)) ρ)
  simp only [Complex.ofReal_re, Nat.cast_mul] at hr
  rw [incidenceEnergyRows_weighted_support] at hr
  rw [hr]
  apply hp.trans
  apply add_le_add le_rfl
  have hmass := incidenceSupportedEnergyRows_mass Dmax w m ρ 1 zero_le_one (fun d => (hDbound _).2)
  simp only [one_mul] at hmass
  calc
    _ ≤ 2 * (C * (T * LM) ^ 2 * (TD * S) ^ (J + 1)) ^ 2 *
        (((Fset.card : ℝ) * (I.card : ℝ) * LN) ^ 2 * ((Dmax : ℝ) / w) ^ 2) := by
      gcongr
    _ = _ := by ring

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceSourceNumerator_norm
#print axioms PrimeGap182Audit.incidenceRawSource_positive_taylor
