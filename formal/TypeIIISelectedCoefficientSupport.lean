import TypeIIISelectedGram

/-! Extending only the actual finite modulus coefficients by zero preserves the signed Gram mass. -/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def finiteModulusCoefficient (Q : Finset ℕ) (η : ℕ → ℂ) (q : ℕ) : ℂ :=
  if q ∈ Q then η q else 0

theorem finiteModulusCoefficient_norm_le (Q : Finset ℕ) (η : ℕ → ℂ) (E : ℝ)
    (hE : 0 ≤ E) (hη : ∀ q ∈ Q, ‖η q‖ ≤ E) (q : ℕ) :
    ‖finiteModulusCoefficient Q η q‖ ≤ E := by
  unfold finiteModulusCoefficient
  split_ifs with hq
  · exact hη q hq
  · simpa only [norm_zero] using hE

theorem selectedProfileMass_finiteModulusCoefficient (b : ℕ) (Sset : Finset ℕ+)
    (Rs : ℕ+ → Finset ℕ+) (a : ℤ) (M : Finset ℤ) (η : ℕ → ℂ) (α : ℤ → ℂ)
    (N : ℕ) (hM : M ⊆ Finset.Ico 1 (1 + (N : ℤ)))
    (Q : Finset ℕ) (hQ : ∀ s ∈ Sset, ∀ r ∈ Rs s, b * ((r : ℕ) * (s : ℕ)) ∈ Q)
    (T H : ℝ) (ψ : ℝ → ℝ) :
    selectedProfileMass b Sset Rs a M (finiteModulusCoefficient Q η) α N T H ψ =
      selectedProfileMass b Sset Rs a M η α N T H ψ := by
  unfold selectedProfileMass
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro r₁ hr₁
  apply Finset.sum_congr rfl
  intro r₂ hr₂
  rw [selectedGcdProfile_eq_correlation b s r₁ r₂ a M (finiteModulusCoefficient Q η) α N hM,
    selectedGcdProfile_eq_correlation b s r₁ r₂ a M η α N hM]
  simp only [selectedSignedCorrelation, finiteModulusCoefficient,
    ite_eq_left (hQ s hs r₁ hr₁), ite_eq_left (hQ s hs r₂ hr₂)]

/-- The selected analytic estimate's global coefficient bound follows from the exact
finite supported coefficient bound, without changing the selected signed sums. -/
theorem selectedProfileMass_bounded_reduction (b : ℕ) (Sset : Finset ℕ+)
    (Rs : ℕ+ → Finset ℕ+) (a : ℤ) (M : Finset ℤ) (η : ℕ → ℂ) (α : ℤ → ℂ)
    (N : ℕ) (hM : M ⊆ Finset.Ico 1 (1 + (N : ℤ)))
    (Q : Finset ℕ) (hQ : ∀ s ∈ Sset, ∀ r ∈ Rs s, b * ((r : ℕ) * (s : ℕ)) ∈ Q)
    (E : ℝ) (hE : 0 ≤ E) (hη : ∀ q ∈ Q, ‖η q‖ ≤ E)
    (T H : ℝ) (ψ : ℝ → ℝ) :
    ∃ η' : ℕ → ℂ, (∀ q : ℕ, ‖η' q‖ ≤ E) ∧
      selectedProfileMass b Sset Rs a M η' α N T H ψ =
        selectedProfileMass b Sset Rs a M η α N T H ψ :=
  ⟨finiteModulusCoefficient Q η, finiteModulusCoefficient_norm_le Q η E hE hη,
    selectedProfileMass_finiteModulusCoefficient b Sset Rs a M η α N hM Q hQ T H ψ⟩

#print axioms selectedProfileMass_finiteModulusCoefficient
#print axioms selectedProfileMass_bounded_reduction

end

end PrimeGap182.TypeIII
