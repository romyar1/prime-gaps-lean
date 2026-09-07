import TypeIIIPhaseObstruction
import TypeIIIConstantField

/-!
# The scalar substitutions in Fu's local Fourier formula

Fu's published local-transform theorem is an external geometric input.
This file checks the subsequent changes of variables in fields, including
all choices of cubic and quadratic roots. The generic direction is the
actual transcendental element of `RatFunc k`; it is not a numerical sample.
No assertion about the inertia of the correlation sheaf is made here.
-/

noncomputable section
open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

variable {k : Type*} [Field k]

/-- The square of a radial coefficient after the quadratic radial cover. -/
def fuRadialPhaseSquare (α m γ : k) : RatFunc k :=
  RatFunc.C (4 * α / m) * (RatFunc.C γ - RatFunc.X) ^ 3 / RatFunc.X ^ 2

/-- Substituting q=γ/z in the Legendre-transform coefficient retains a
cubic zero in the angular variable. -/
theorem fu_phase_square_substitution {L : Type*} [Field L]
    (α m γ z : L) (hz : z ≠ 0) :
    4 * α * z / m * (γ / z - 1) ^ 3 =
      (4 * α / m) * (γ - z) ^ 3 / z ^ 2 := by
  field_simp

/-- The scalar whose product with sqrt(γ-z) is the required phase has
exactly the square dictated by the local Fourier substitution. -/
theorem radialPhaseScalar_sq_mul_linear (α m γ A : k)
    (hA : A ^ 2 = 4 * α / m) :
    (radialPhaseScalar A γ) ^ 2 * (RatFunc.C γ - RatFunc.X) =
      fuRadialPhaseSquare α m γ := by
  simp only [radialPhaseScalar, fuRadialPhaseSquare, div_pow, mul_pow, ← map_pow, hA]
  ring

section ConstantCubicRoots

variable {L : Type*} [Field L] [Algebra k L] [IsAlgClosed k]

/-- Over an algebraically closed constant field, every root of a cubic
with constant coefficients is constant. No branch choice is assumed. -/
theorem cubic_root_is_constant (x : L) (c : k)
    (hx : x ^ 3 = algebraMap k L c) :
    ∃ γ : k, γ ^ 3 = c ∧ algebraMap k L γ = x := by
  have hint : IsIntegral k x := by
    refine ⟨Polynomial.X ^ 3 - Polynomial.C c,
      Polynomial.monic_X_pow_sub_C c (by decide), ?_⟩
    change Polynomial.aeval x (Polynomial.X ^ 3 - Polynomial.C c) = 0
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hx, sub_self]
  obtain ⟨γ, hγ⟩ := exists_constant_of_isAlgebraic hint.isAlgebraic
  refine ⟨γ, ?_, hγ⟩
  apply (algebraMap k L).injective
  simpa only [map_pow, hγ] using hx

/-- The three possible generic cubic roots are precisely constant cubic
roots divided by the direction variable. This equivalence includes every
root in the ambient extension field. -/
theorem generic_cubic_roots_iff (c : k) (q z : L) (hz : z ≠ 0) :
    q ^ 3 = algebraMap k L c / z ^ 3 ↔
      ∃ γ : k, γ ^ 3 = c ∧ q = algebraMap k L γ / z := by
  constructor
  · intro hq
    have hpow : (q * z) ^ 3 = algebraMap k L c := by
      rw [mul_pow, hq, div_mul_cancel₀ _ (pow_ne_zero _ hz)]
    obtain ⟨γ, hγ, he⟩ := cubic_root_is_constant (q * z) c hpow
    exact ⟨γ, hγ, by rw [he, mul_div_cancel_right₀ q hz]⟩
  · rintro ⟨γ, hγ, rfl⟩
    rw [div_pow, ← map_pow, hγ]

end ConstantCubicRoots

section SquareRootCoordinates

variable {L : Type*} [Field L] [Algebra (RatFunc k) L] [IsAlgClosed k]

/-- Any coefficient with the square produced by Fu's formula belongs to
the independent-root scalar form used by the rectangle obstruction. -/
theorem fu_phase_has_radial_coordinates
    (h2 : (2 : k) ≠ 0) (α m γ : k) (hα : α ≠ 0) (hm : m ≠ 0)
    (β : L) (hβ : β ^ 2 = algebraMap (RatFunc k) L (fuRadialPhaseSquare α m γ)) :
    ∃ A : k, ∃ R : L, A ^ 2 = 4 * α / m ∧
      R ^ 2 = algebraMap (RatFunc k) L (RatFunc.C γ - RatFunc.X) ∧
      β = radialPhaseScalar A γ • R := by
  obtain ⟨A, hA⟩ := IsAlgClosed.exists_pow_nat_eq (4 * α / m) (by decide : 0 < (2 : ℕ))
  have hfour : (4 : k) ≠ 0 := by
    have h := pow_ne_zero 2 h2
    norm_num only [show (2 : k) ^ 2 = 4 by ring] at h
    exact h
  have hA0 : A ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hA
    exact (div_ne_zero (mul_ne_zero hfour hα) hm) hA.symm
  let a : L := algebraMap (RatFunc k) L (radialPhaseScalar A γ)
  have ha : a ≠ 0 := by
    simpa only [a, map_zero] using (algebraMap (RatFunc k) L).injective.ne
      (radialPhaseScalar_ne_zero hA0 γ)
  have hfactor : a ^ 2 * algebraMap (RatFunc k) L (RatFunc.C γ - RatFunc.X) =
      algebraMap (RatFunc k) L (fuRadialPhaseSquare α m γ) := by
    simpa only [a, map_mul, map_pow] using
      congrArg (algebraMap (RatFunc k) L) (radialPhaseScalar_sq_mul_linear α m γ A hA)
  refine ⟨A, β / a, hA, ?_, ?_⟩
  · rw [div_pow, hβ, ← hfactor]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ ha)
  · rw [Algebra.smul_def]
    change β = a * (β / a)
    field_simp

end SquareRootCoordinates

#print axioms fuRadialPhaseSquare
#print axioms fu_phase_square_substitution
#print axioms radialPhaseScalar_sq_mul_linear
#print axioms cubic_root_is_constant
#print axioms generic_cubic_roots_iff
#print axioms fu_phase_has_radial_coordinates

end PrimeGap182.TypeIII
