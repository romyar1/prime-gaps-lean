import TypeIIISignedRepartition

/-! Transfer of the public selected-factor Gram equality to entire signed profile blocks. -/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def selectedSignedGram (b : ℕ) (S : Finset ℕ+) (Rs : ℕ+ → Finset ℕ+)
    (a : ℤ) (M : Finset ℤ) (η : ℕ → ℂ) (α : ℤ → ℂ)
    (T H : ℝ) (ψ : ℝ → ℝ) : ℂ :=
  ∑ s ∈ S, ∑ r₁ ∈ Rs s, ∑ r₂ ∈ Rs s,
    (s : ℂ) * selectedSignedCorrelation b ((r₁ : ℕ) * (s : ℕ))
      ((r₂ : ℕ) * (s : ℕ)) ((s : ℕ) * Nat.lcm (r₁ : ℕ) (r₂ : ℕ))
      a M η α T H ψ

def selectedProfileMass (b : ℕ) (S : Finset ℕ+) (Rs : ℕ+ → Finset ℕ+)
    (a : ℤ) (M : Finset ℤ) (η : ℕ → ℂ) (α : ℤ → ℂ)
    (N : ℕ) (T H : ℝ) (ψ : ℝ → ℝ) : ℝ :=
  ∑ s ∈ S, ∑ r₁ ∈ Rs s, ∑ r₂ ∈ Rs s,
    (s : ℝ) * ‖selectedGcdProfile b s r₁ r₂ a M η α N T H ψ‖

/-- This is the literal `G₂` finite sum in
`PrimeGap186.typeIII_selected_factor_cauchy_correlation`. -/
theorem selectedSignedGram_expansion (b : ℕ) (S : Finset ℕ+)
    (Rs : ℕ+ → Finset ℕ+) (a : ℤ) (M : Finset ℤ)
    (η : ℕ → ℂ) (α : ℤ → ℂ) (T H : ℝ) (ψ : ℝ → ℝ) :
    selectedSignedGram b S Rs a M η α T H ψ =
      ∑ s ∈ S, ∑ r₁ ∈ Rs s, ∑ r₂ ∈ Rs s, ∑ m ∈ M, ∑ n ∈ M,
        if Int.gcd m ((b * (r₁ : ℕ) * (s : ℕ) : ℕ) : ℤ) = 1 ∧
            Int.gcd n ((b * (r₂ : ℕ) * (s : ℕ) : ℕ) : ℤ) = 1 then
          (s : ℂ) * (η (b * (r₁ : ℕ) * (s : ℕ)) *
            star (η (b * (r₂ : ℕ) * (s : ℕ)))) * (α m * star (α n)) *
            ∑ ℓ ∈ Finset.Icc ⌈-T * H⌉ ⌊T * H⌋,
              if IsUnit (ℓ : ZMod ((s : ℕ) * Nat.lcm (r₁ : ℕ) (r₂ : ℕ))) then
                (ψ ((ℓ : ℝ) / H) : ℂ) *
                  PrimeGap186.normalizedKloosterman3Mod ((r₁ : ℕ) * (s : ℕ))
                    (((a : ZMod ((r₁ : ℕ) * (s : ℕ))) *
                      (m : ZMod ((r₁ : ℕ) * (s : ℕ)))⁻¹) *
                      (ℓ : ZMod ((r₁ : ℕ) * (s : ℕ)))) *
                  star (PrimeGap186.normalizedKloosterman3Mod ((r₂ : ℕ) * (s : ℕ))
                    (((a : ZMod ((r₂ : ℕ) * (s : ℕ))) *
                      (n : ZMod ((r₂ : ℕ) * (s : ℕ)))⁻¹) *
                      (ℓ : ZMod ((r₂ : ℕ) * (s : ℕ)))))
              else 0
        else 0 := by
  simp only [selectedSignedGram, selectedSignedCorrelation, Finset.mul_sum,
    mul_ite, mul_zero, mul_assoc]

theorem selectedSignedGram_eq_profiles (b : ℕ) (S : Finset ℕ+)
    (Rs : ℕ+ → Finset ℕ+) (a : ℤ) (M : Finset ℤ)
    (η : ℕ → ℂ) (α : ℤ → ℂ) (N : ℕ)
    (hM : M ⊆ Finset.Ico 1 (1 + (N : ℤ)))
    (T H : ℝ) (ψ : ℝ → ℝ) :
    selectedSignedGram b S Rs a M η α T H ψ =
      ∑ s ∈ S, ∑ r₁ ∈ Rs s, ∑ r₂ ∈ Rs s,
        (s : ℂ) * selectedGcdProfile b s r₁ r₂ a M η α N T H ψ := by
  unfold selectedSignedGram
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro r₁ _
  apply Finset.sum_congr rfl
  intro r₂ _
  rw [selectedGcdProfile_eq_correlation b s r₁ r₂ a M η α N hM]

/-- The Gram equality transfers `T₂` directly to the norm of each whole signed
coefficient/frequency block. No entrywise positive majorant is used. -/
theorem selected_T2_le_profileMass (b : ℕ) (S : Finset ℕ+)
    (Rs : ℕ+ → Finset ℕ+) (a : ℤ) (M : Finset ℤ)
    (η : ℕ → ℂ) (α : ℤ → ℂ) (N : ℕ)
    (hM : M ⊆ Finset.Ico 1 (1 + (N : ℤ)))
    (T H : ℝ) (ψ : ℝ → ℝ) (T₂ : ℝ) (hT₂ : 0 ≤ T₂)
    (hGram : (T₂ : ℂ) = selectedSignedGram b S Rs a M η α T H ψ) :
    T₂ ≤ selectedProfileMass b S Rs a M η α N T H ψ := by
  rw [selectedSignedGram_eq_profiles b S Rs a M η α N hM] at hGram
  have hnorm : ‖(T₂ : ℂ)‖ = T₂ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT₂]
  rw [← hnorm, hGram]
  unfold selectedProfileMass
  apply (norm_sum_le S _).trans
  apply Finset.sum_le_sum
  intro s _
  apply (norm_sum_le (Rs s) _).trans
  apply Finset.sum_le_sum
  intro r₁ _
  apply (norm_sum_le (Rs s) _).trans
  apply Finset.sum_le_sum
  intro r₂ _
  simp only [norm_mul, Complex.norm_natCast, le_refl]

theorem selected_cauchy_le_profileMass (b : ℕ) (S : Finset ℕ+)
    (Rs : ℕ+ → Finset ℕ+) (a : ℤ) (M : Finset ℤ)
    (η : ℕ → ℂ) (α : ℤ → ℂ) (N : ℕ)
    (hM : M ⊆ Finset.Ico 1 (1 + (N : ℤ)))
    (T H : ℝ) (ψ : ℝ → ℝ) (C T₁ T₂ : ℝ) (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (hC : C ^ 2 ≤ T₁ * T₂)
    (hGram : (T₂ : ℂ) = selectedSignedGram b S Rs a M η α T H ψ) :
    C ^ 2 ≤ T₁ * selectedProfileMass b S Rs a M η α N T H ψ :=
  hC.trans (mul_le_mul_of_nonneg_left
    (selected_T2_le_profileMass b S Rs a M η α N hM T H ψ T₂ hT₂ hGram) hT₁)

#print axioms selectedSignedGram_expansion
#print axioms selectedSignedGram_eq_profiles
#print axioms selected_T2_le_profileMass
#print axioms selected_cauchy_le_profileMass

end

end PrimeGap182.TypeIII
