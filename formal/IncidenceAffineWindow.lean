import IncidenceAffineModes
import IncidenceWindowFromModes

/-!
# The actual affine-progression incidence window used by the source transfer

The progression modulus is a unit modulo the oscillatory modulus. Its
reparametrization costs no factor in the mean or in the nonzero-mode error.
The source's potentially large real shear is retained without restriction.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι]

omit [NeZero q] in
theorem incidenceAffineRows_mulVec (R : Matrix (ZMod q × ZMod q) ι ℂ)
    (u : (ZMod q)ˣ) (t : ZMod q) (c : ι → ℂ) (z : ZMod q × ZMod q) :
    (incidenceAffineRows R u t *ᵥ c) z = (R *ᵥ c) ((u : ZMod q) * z.1 + t, z.2) := rfl

set_option maxHeartbeats 600000 in
theorem incidenceAffineShearedBox_bound (hK4 : AllIncidenceRankFourBounds)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ [NeZero q], Squarefree q →
      ∀ A : ZMod q, IsUnit A → ∀ u : (ZMod q)ˣ, ∀ t : ZMod q,
      ∀ E₁ E₂ e₀ γ₀ τ L : ℝ, 0 < E₁ → 0 < E₂ → 0 ≤ L →
      ∀ w : ℤ × ℤ → ℝ, (∀ z, 0 ≤ w z) → (∀ z, w z ≤ L) →
      (∀ z, w z ≠ 0 → |(z.1 : ℝ) - e₀| ≤ E₁ ∧
        |(z.2 : ℝ) - τ * (z.1 : ℝ) - γ₀| ≤ E₂) →
      ∀ c : ZMod q → ℂ,
        (∑' z : ℤ × ℤ, w z *
          ‖(incidenceMatrixMod A *ᵥ c)
            ((u : ZMod q) * (z.1 : ZMod q) + t, (z.2 : ZMod q))‖ ^ 2) ≤
          C * L * incidenceWindowScale η q E₁ E₂ * incidenceVectorEnergy c := by
  obtain ⟨C, hC, hwindow⟩ := incidenceShearedBox_from_modes η hη
  refine ⟨C, hC, ?_⟩
  intro q _ hq A hA u t E₁ E₂ e₀ γ₀ τ L hE₁ hE₂ hL w hw0 hwL hws c
  have hb := hwindow q (ZMod q) (incidenceAffineRows (incidenceMatrixMod A) u t)
    ((incidenceModalBounds_of_rankFour hK4 hq A hA).affine u t)
    E₁ E₂ e₀ γ₀ τ L hE₁ hE₂ hL w hw0 hwL hws c
  simpa only [incidenceAffineRows_mulVec, incidenceIntegerResidue] using hb

/-- The precise natural-modulus progression used in the source proof. -/
theorem incidenceProgressionWindow_bound (hK4 : AllIncidenceRankFourBounds)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ [NeZero q], Squarefree q →
      ∀ A : ZMod q, IsUnit A → ∀ d : ℕ, Nat.Coprime d q → ∀ t : ℤ,
      ∀ E₁ E₂ e₀ γ₀ τ L : ℝ, 0 < E₁ → 0 < E₂ → 0 ≤ L →
      ∀ w : ℤ × ℤ → ℝ, (∀ z, 0 ≤ w z) → (∀ z, w z ≤ L) →
      (∀ z, w z ≠ 0 → |(z.1 : ℝ) - e₀| ≤ E₁ ∧
        |(z.2 : ℝ) - τ * (z.1 : ℝ) - γ₀| ≤ E₂) →
      ∀ c : ZMod q → ℂ,
        (∑' z : ℤ × ℤ, w z *
          ‖(incidenceMatrixMod A *ᵥ c)
            (((((d : ℤ) * z.1 + t) : ℤ) : ZMod q), (z.2 : ZMod q))‖ ^ 2) ≤
          C * L * incidenceWindowScale η q E₁ E₂ * incidenceVectorEnergy c := by
  obtain ⟨C, hC, hwindow⟩ := incidenceAffineShearedBox_bound hK4 η hη
  refine ⟨C, hC, ?_⟩
  intro q _ hq A hA d hd t E₁ E₂ e₀ γ₀ τ L hE₁ hE₂ hL w hw0 hwL hws c
  have hb := hwindow q hq A hA (ZMod.unitOfCoprime d hd) (t : ZMod q)
    E₁ E₂ e₀ γ₀ τ L hE₁ hE₂ hL w hw0 hwL hws c
  simpa only [ZMod.coe_unitOfCoprime, Int.cast_add, Int.cast_mul, Int.cast_natCast] using hb

#print axioms incidenceAffineRows_mulVec
#print axioms incidenceAffineShearedBox_bound
#print axioms incidenceProgressionWindow_bound

end PrimeGap182Audit
