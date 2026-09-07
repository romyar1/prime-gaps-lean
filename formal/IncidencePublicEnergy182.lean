import IncidenceEnergyRows

/-!
# The public positive block energy is the actual raw incidence energy

The left side below is the literal energy expression in
`PrimeGap186.sourceSecondary_positive_block_cauchy`, including both gcd
gates and all four Fourier factors. The right side is the actual raw
energy used by the incidence estimates. Only finite sums, divisibility,
and complex conjugation are used; there is no analytic or finite-field
hypothesis. The outer cutoff and the inner interval are arbitrary, so
the public floor/ceiling cutoffs specialize without another limit step.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical PrimeGap186
open scoped BigOperators

set_option maxHeartbeats 1000000

theorem incidencePublicEnergy_eq_rawBlockEnergy
    (m w w₂ Dmax r₁ q₀ u₁ v₁ v₂ q₂ : ℕ)
    (A B ℓ Y : ℤ) (E : ZMod q₀ → Finset (ZMod q₀))
    (ψM ψN ψD : ℝ → ℝ) (M N Δ₁ d₀ : ℝ) (J I : Finset ℤ) :
    let g : ℕ := Nat.gcd v₁ v₂
    let φ : ℤ × ℤ → ℤ := fun h =>
      h.1 * ((v₂ / g : ℕ) : ℤ) - h.2 * ((v₁ / g : ℕ) : ℤ)
    let Freq : Finset (ℤ × ℤ) := (J ×ˢ J).filter
      (fun h => h.1 * (v₂ : ℤ) ≠ h.2 * (v₁ : ℤ))
    let supported : ℤ → ℕ := fun y =>
      ∏ p ∈ m.primeFactors, p ^ y.natAbs.factorization p
    let Fblock : ℕ → ℕ → ℤ → Finset (ℤ × ℤ) := fun w₁ w₂ Y =>
      Freq.filter (fun h =>
        (w₁ : ℤ) ∣ φ h ∧ supported (φ h) = w₂ ∧
        1 ≤ (φ h : ℝ) / (Y : ℝ) ∧ (φ h : ℝ) / (Y : ℝ) < 2)
    let R₁ : ℕ := r₁ * q₀ * u₁ * v₁ * q₂
    let R₂ : ℕ := r₁ * q₀ * u₁ * v₂ * q₂
    let Four : (ℤ × ℤ) → (ℤ × ℤ) → ℝ → ℂ := fun h h' d =>
      sourcePhiRealFactor ψM M R₁ h.1 d *
        star (sourcePhiRealFactor ψM M R₂ h.2 d) *
        star (sourcePhiRealFactor ψM M R₁ h'.1 d) *
        sourcePhiRealFactor ψM M R₂ h'.2 d
    let kernel : ℕ → ℕ → ℤ → ℤ → ℂ := fun w₁ d y y' =>
      ∑ n ∈ I, ∑ n' ∈ I,
        sourceSecondaryPairTerm m r₁ q₀ u₁ v₁ v₂ q₂ w₁
          A B ℓ E ψN N y y' ⊤ d n n'
    (∑ d ∈ Finset.Icc 1 Dmax,
      if w ∣ d ∧ Nat.Coprime (d / w) w then
        (ψD (((d : ℝ) - d₀) / Δ₁) : ℂ) *
          ∑ h ∈ Fblock w w₂ Y, ∑ h' ∈ Fblock w w₂ Y,
            if Int.gcd ((d / w : ℕ) : ℤ)
                (((m : ℤ) * φ h * φ h') / (w : ℤ) ^ 2) = 1 then
              kernel w d (φ h) (φ h') * Four h h' (d : ℝ)
            else 0
      else 0) =
      incidenceRawBlockEnergy m w Dmax r₁ q₀ u₁ v₁ v₂ q₂ A B ℓ E ψN N
        (incidenceSourceFrequencyBlock J v₁ v₂ m w w₂ Y) I
        (incidenceQuotientFrequency w v₁ v₂)
        (fun d h => sourcePhiRealFactor ψM M R₁ h.1 (d : ℝ) *
          star (sourcePhiRealFactor ψM M R₂ h.2 (d : ℝ)))
        (fun d => ψD (((d : ℝ) - d₀) / Δ₁)) := by
  intro g φ Freq supported Fblock R₁ R₂ Four kernel
  have hF : Fblock w w₂ Y = incidenceSourceFrequencyBlock J v₁ v₂ m w w₂ Y := by
    rfl
  have hφ (h : ℤ × ℤ) (hh : h ∈ Fblock w w₂ Y) :
      (w : ℤ) * incidenceQuotientFrequency w v₁ v₂ h = φ h := by
    have hd : (w : ℤ) ∣ φ h := (Finset.mem_filter.mp hh).2.1
    exact incidenceQuotientFrequency_mul w v₁ v₂ h hd
  unfold incidenceRawBlockEnergy
  rw [← hF]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs with hd
  · congr 1
    apply Finset.sum_congr rfl
    intro h hh
    apply Finset.sum_congr rfl
    intro h' hh'
    rw [hφ h hh, hφ h' hh']
    split_ifs
    · change kernel w d (φ h) (φ h') * Four h h' (d : ℝ) =
        kernel w d (φ h) (φ h') * _
      congr 1
      dsimp only [Four]
      simp only [star_mul, star_star]
      ring
    · rfl
  · rfl

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidencePublicEnergy_eq_rawBlockEnergy
