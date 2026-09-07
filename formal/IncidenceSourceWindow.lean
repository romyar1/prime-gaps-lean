import IncidenceFarey
import IncidenceAffineWindow

/-!
# Actual reduced Type II source blocks

The source response is a finite sum over coefficient/numerator pairs, with
their actual modular quotient. It is identified with the incidence matrix
applied to the actual Farey coefficient vector before bounding its energy.
The arbitrary joint input weight includes all retained input pole masks.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators

theorem incidenceFiniteInput_response {ρ κ : Type*} [Fintype ρ] [DecidableEq ρ]
    (A : Finset ℤ) (I : ℤ → Finset κ) (r : ℤ → κ → ρ)
    (c : ℤ → ℂ) (β : ℤ → κ → ℂ) (K : ρ → ℂ) :
    (∑ b : ρ, K b * (∑ a ∈ A, c a * ∑ k ∈ I a,
      if r a k = b then β a k else 0)) =
        ∑ a ∈ A, c a * ∑ k ∈ I a, β a k * K (r a k) := by
  classical
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp [mul_ite, mul_comm, mul_left_comm]

theorem incidenceReindex_energy {ρ : Type*} [Fintype ρ]
    (e : ρ ≃ ρ) (c : ρ → ℂ) :
    incidenceVectorEnergy (fun b => c (e.symm b)) = incidenceVectorEnergy c := by
  exact e.symm.sum_comp (fun b => ‖c b‖ ^ 2)

theorem incidenceReindex_response {ρ : Type*} [Fintype ρ]
    (e : ρ ≃ ρ) (K c : ρ → ℂ) :
    (∑ b, K b * c (e.symm b)) = ∑ b, K (e b) * c b := by
  simpa only [e.symm_apply_apply] using (e.sum_comp (fun b => K b * c (e.symm b))).symm

def incidenceInputUnitEquiv {q : ℕ} (u : (ZMod q)ˣ) : ZMod q ≃ ZMod q where
  toFun b := (u : ZMod q) * b
  invFun b := ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * b
  left_inv b := by simp
  right_inv b := by simp

def incidenceSourceResponse {q : ℕ} [NeZero q] (AQ : ZMod q) (u : (ZMod q)ˣ)
    (d : ℕ) (r₀ : ℤ) (A : Finset ℤ) (I : ℤ → Finset ℤ) (B : ℤ)
    (c : ℤ → ℂ) (β : ℤ → ℤ → ℂ) (z : ℤ × ℤ) : ℂ :=
  ∑ a ∈ A, c a * ∑ k ∈ I a, β a k *
    incidenceMatrixMod AQ ((((d : ℤ) * z.1 + r₀ : ℤ) : ZMod q), (z.2 : ZMod q))
      ((u : ZMod q) * incidenceFareyResidue q B a k)

theorem incidenceSourceResponse_eq {q : ℕ} [NeZero q]
    (AQ : ZMod q) (u : (ZMod q)ˣ) (d : ℕ) (r₀ : ℤ)
    (A : Finset ℤ) (I : ℤ → Finset ℤ) (B : ℤ)
    (c : ℤ → ℂ) (β : ℤ → ℤ → ℂ) (z : ℤ × ℤ) :
    incidenceSourceResponse AQ u d r₀ A I B c β z =
      (incidenceMatrixMod AQ *ᵥ
        (fun b => incidenceFareyCoefficients (q := q) A I B c β
          ((incidenceInputUnitEquiv u).symm b)))
        ((((d : ℤ) * z.1 + r₀ : ℤ) : ZMod q), (z.2 : ZMod q)) := by
  rw [Matrix.mulVec, dotProduct, incidenceReindex_response]
  exact (incidenceFiniteInput_response A I (incidenceFareyResidue q B) c β
    (fun b => incidenceMatrixMod AQ
      ((((d : ℤ) * z.1 + r₀ : ℤ) : ZMod q), (z.2 : ZMod q))
      ((incidenceInputUnitEquiv u) b))).symm

set_option maxHeartbeats 800000 in
/-- The actual reduced source block is bounded by the window scale times
the sharp finite Farey factor. Every coefficient sum remains explicit. -/
theorem incidenceSourceWindow_bound (hK4 : AllIncidenceRankFourBounds)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ [NeZero q], Squarefree q →
      ∀ AQ : ZMod q, IsUnit AQ → ∀ u : (ZMod q)ˣ,
      ∀ d : ℕ, Nat.Coprime d q → ∀ r₀ : ℤ,
      ∀ E₁ E₂ e₀ γ₀ shear L : ℝ, 0 < E₁ → 0 < E₂ → 0 ≤ L →
      ∀ w : ℤ × ℤ → ℝ, (∀ z, 0 ≤ w z) → (∀ z, w z ≤ L) →
      (∀ z, w z ≠ 0 → |(z.1 : ℝ) - e₀| ≤ E₁ ∧
        |(z.2 : ℝ) - shear * (z.1 : ℝ) - γ₀| ≤ E₂) →
      ∀ A : Finset ℤ, ∀ I : ℤ → Finset ℤ, ∀ B : ℤ,
      ∀ U V τ : ℝ, 0 < U → 0 ≤ V →
      (∀ a ∈ A, U ≤ |(a : ℝ)| ∧ |(a : ℝ)| ≤ 2 * U ∧ IsUnit (a : ZMod q)) →
      (∀ a ∈ A, (a.natAbs.divisors.card : ℝ) ≤ τ) →
      ∀ center : ℤ → ℝ,
      (∀ a ∈ A, ∀ k ∈ I a, |(k : ℝ) - center a| ≤ V) →
      ∀ c : ℤ → ℂ, ∀ β : ℤ → ℤ → ℂ,
      (∀ a ∈ A, ∀ k ∈ I a, ‖β a k‖ ≤ 1) →
      (∑' z : ℤ × ℤ, w z * ‖incidenceSourceResponse AQ u d r₀ A I B c β z‖ ^ 2) ≤
        C * L * incidenceWindowScale η q E₁ E₂ *
          ((1 + 8 * U * V / (q : ℝ)) * ((A.card : ℝ) + 8 * V * τ)) *
            ∑ a ∈ A, ‖c a‖ ^ 2 := by
  obtain ⟨C, hC, hwindow⟩ := incidenceProgressionWindow_bound hK4 η hη
  refine ⟨C, hC, ?_⟩
  intro q _ hq AQ hAQ u d hd r₀ E₁ E₂ e₀ γ₀ shear L hE₁ hE₂ hL w hw0 hwL hwbox
    A I B U V τ hU hV hA hτ center hI c β hβ
  have hw := hwindow q hq AQ hAQ d hd r₀ E₁ E₂ e₀ γ₀ shear L hE₁ hE₂ hL
    w hw0 hwL hwbox
    (fun b => incidenceFareyCoefficients (q := q) A I B c β
      ((incidenceInputUnitEquiv u).symm b))
  simp only [← incidenceSourceResponse_eq, incidenceReindex_energy] at hw
  have hf := incidenceFarey_energy_le A I B U V τ hU hV hA hτ center hI c β hβ
  calc
    _ ≤ C * L * incidenceWindowScale η q E₁ E₂ *
        incidenceVectorEnergy (incidenceFareyCoefficients (q := q) A I B c β) := hw
    _ ≤ C * L * incidenceWindowScale η q E₁ E₂ *
        (((1 + 8 * U * V / (q : ℝ)) * ((A.card : ℝ) + 8 * V * τ)) *
          ∑ a ∈ A, ‖c a‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hf (by dsimp only [incidenceWindowScale]; positivity)
    _ = _ := by ring

#print axioms incidenceFiniteInput_response
#print axioms incidenceReindex_energy
#print axioms incidenceReindex_response
#print axioms incidenceSourceResponse_eq
#print axioms incidenceSourceWindow_bound

end PrimeGap182Audit
