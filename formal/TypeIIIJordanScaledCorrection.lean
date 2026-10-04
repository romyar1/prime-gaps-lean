import Mathlib

/-!
# The correction trace under a unipotent change of tame Frobenius

This is linear algebra for the arithmetic identification in step 3 of the
cited Type III derivation. It computes the actual operator X ↦ D X D⁻¹ U
on the rank-three Jordan centralizer, for any U = 1 + aN + bN².
The resulting trace is independent of a and b. No sheaf identification,
local Fourier theorem or Type III estimate is assumed or concluded here.

Katz, GKM, Theorem 7.4.3 supplies the regular-unipotent zero model and its
invariant-line Frobenius. The separate geometric application must identify
its relative tame Frobenius with a unit U of this form.
-/

noncomputable section
open scoped Matrix
namespace PrimeGap182.TypeIII.ScaledJordanCorrection

variable {k : Type*} [Field k]

def toeplitz (v : Fin 3 → k) : Matrix (Fin 3) (Fin 3) k :=
  !![v 0, v 1, v 2; 0, v 0, v 1; 0, 0, v 0]

def diagonal (q : k) : Matrix (Fin 3) (Fin 3) k :=
  Matrix.diagonal ![1, q, q^2]

def unitShift (a b : k) : Matrix (Fin 3) (Fin 3) k :=
  toeplitz ![1, a, b]

/-- Both inverse products are verified, without assuming invertibility. -/
theorem unitShift_inverse (a b : k) :
    unitShift a b * unitShift (-a) (a^2-b) = 1 ∧
    unitShift (-a) (a^2-b) * unitShift a b = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [unitShift, toeplitz, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- Relative unipotent changes again have constant coefficient one. -/
theorem unitShift_relative (a b c d : k) :
    unitShift a b * unitShift (-c) (c^2-d) =
      unitShift (a-c) (b+c^2-d-a*c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitShift, toeplitz, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- The coordinate action of conjugation followed by the relative unit. -/
def coordinateMatrix (q a b : k) : Matrix (Fin 3) (Fin 3) k :=
  !![1, 0, 0; a, q⁻¹, 0; b, a*q⁻¹, q⁻¹^2]

theorem actual_operator_coordinates (q a b : k) (hq : q ≠ 0) (v : Fin 3 → k) :
    diagonal q * toeplitz v * diagonal q⁻¹ * unitShift a b =
      toeplitz ((coordinateMatrix q a b).mulVec v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal, toeplitz, unitShift, coordinateMatrix, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    field_simp [hq]

/-- Actual linear trace of the computed operator, not a stipulated value. -/
theorem coordinate_operator_trace (q a b : k) :
    LinearMap.trace k (Fin 3 → k) (Matrix.toLin' (coordinateMatrix q a b)) =
      1 + q⁻¹ + q⁻¹^2 := by
  rw [Matrix.trace_toLin'_eq]
  simp [Matrix.trace, coordinateMatrix, Fin.sum_univ_succ, add_assoc]

/-- The boundary correction survives every relative unipotent shift. -/
theorem trace_independent_of_tame_scaling (q a b c d : k) :
    LinearMap.trace k (Fin 3 → k)
      (Matrix.toLin' (coordinateMatrix q (a-c) (b+c^2-d-a*c))) =
    LinearMap.trace k (Fin 3 → k) (Matrix.toLin' (coordinateMatrix q 0 0)) := by
  rw [coordinate_operator_trace, coordinate_operator_trace]

end PrimeGap182.TypeIII.ScaledJordanCorrection

#print axioms PrimeGap182.TypeIII.ScaledJordanCorrection.unitShift_inverse
#print axioms PrimeGap182.TypeIII.ScaledJordanCorrection.unitShift_relative
#print axioms PrimeGap182.TypeIII.ScaledJordanCorrection.actual_operator_coordinates
#print axioms PrimeGap182.TypeIII.ScaledJordanCorrection.coordinate_operator_trace
#print axioms PrimeGap182.TypeIII.ScaledJordanCorrection.trace_independent_of_tame_scaling
