import IncidenceMaskedOriginal

/-! The literal physical energy is zero when its frequency set is empty. -/

noncomputable section
namespace PrimeGap182Audit
open Classical
open scoped BigOperators

theorem incidencePhysicalEnergy_empty {m w e : ℕ}
    [NeZero m] [NeZero w] [NeZero e]
    (A B : ℤ) (I : Finset ℤ) (coeff χ : ℤ → ℂ) :
    incidencePhysicalEnergy (m := m) (w := w) (e := e) A B ∅ I coeff χ = 0 := by
  simp only [incidencePhysicalEnergy, incidencePhysicalRow, Finset.sum_empty,
    norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero]

theorem incidencePhysicalEnergyOrZero_empty {m w : ℕ} [NeZero m] [NeZero w]
    (e : ℕ) (A B : ℤ) (I : Finset ℤ) (coeff χ : ℤ → ℂ) :
    incidencePhysicalEnergyOrZero (m := m) (w := w) e A B ∅ I coeff χ = 0 := by
  by_cases he : e = 0
  · subst e
    simp only [incidencePhysicalEnergyOrZero, dite_true]
  · have : NeZero e := ⟨he⟩
    rw [incidencePhysicalEnergyOrZero_of_ne, incidencePhysicalEnergy_empty]

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidencePhysicalEnergy_empty
#print axioms PrimeGap182Audit.incidencePhysicalEnergyOrZero_empty
