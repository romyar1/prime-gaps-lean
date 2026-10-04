import TypeIIIJordanScaledCorrection
import TypeIIIJordanCorrection

/-!
# Relative Frobenius on the actual Jordan centralizer

The two source Frobenius operators need not coincide. Their common
nilpotent-scaling law and normalized invariant-line eigenvalue force a
diagonal-times-unipotent normal form. We compute the actual relative
action X |-> F1 * X * F2^(-1), including the matrix inverse, and derive its
trace. No diagonal action on the completed boundary is assumed.

The geometric input still has to supply the single-source scaling and
invariant-line laws, and the naturality identifying the boundary action
with this relative action. These are not proved by the matrix calculation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Classical Matrix

namespace PrimeGap182.TypeIII.BoundaryFrobeniusNormalization

open ScaledJordanCorrection

variable {k : Type*} [Field k]

/-- A source Frobenius with invariant-line eigenvalue c. -/
def normalMatrix (q c a b : k) : Matrix (Fin 3) (Fin 3) k :=
  c • (diagonal q * unitShift a b)

/-- The single-source scaling law determines every matrix entry from
the invariant-line eigenvalue and the two remaining top-row entries. -/
theorem normal_form (q c : k) (hq : q ≠ 0) (hc : c ≠ 0)
    (F : Matrix (Fin 3) (Fin 3) k)
    (hN : F * jordanThree k = q⁻¹ • (jordanThree k * F)) (hline : F 0 0 = c) :
    F = normalMatrix q c (F 0 1 / c) (F 0 2 / c) := by
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) k => q • A) hN
  simp only [smul_smul, mul_inv_cancel₀ hq, one_smul] at h
  have h00 := congrArg (fun A => A 0 0) h
  have h10 := congrArg (fun A => A 1 0) h
  have h11 := congrArg (fun A => A 1 1) h
  have h01 := congrArg (fun A => A 0 1) h
  have h12 := congrArg (fun A => A 1 2) h
  have h02 := congrArg (fun A => A 0 2) h
  simp [jordanThree, Matrix.mul_apply, Fin.sum_univ_succ] at h00 h10 h11 h01 h12 h02
  have e10 : F 1 0 = 0 := h00.symm
  have e20 : F 2 0 = 0 := h10.symm
  have e21 : F 2 1 = 0 := by simpa [e10] using h11.symm
  have e11 : F 1 1 = q * c := by simpa [hline] using h01.symm
  have e12 : F 1 2 = q * F 0 1 := h02.symm
  have e22 : F 2 2 = q ^ 2 * c := by simpa [e11, pow_two, mul_assoc] using h12.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalMatrix, diagonal, unitShift, toeplitz, Matrix.diagonal_mul,
      hline, e10, e20, e21, e11, e12, e22] <;> field_simp [hc]

/-- The displayed inverse is verified against the source matrix. -/
theorem normalMatrix_mul_inverse (q c a b : k) (hq : q ≠ 0) (hc : c ≠ 0) :
    normalMatrix q c a b *
      (c⁻¹ • (unitShift (-a) (a ^ 2 - b) * diagonal q⁻¹)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalMatrix, diagonal, unitShift, toeplitz, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.vecMul_diagonal] <;>
    field_simp [hq, hc] <;> ring

theorem normalMatrix_inv (q c a b : k) (hq : q ≠ 0) (hc : c ≠ 0) :
    (normalMatrix q c a b)⁻¹ = c⁻¹ • (unitShift (-a) (a ^ 2 - b) * diagonal q⁻¹) :=
  Matrix.inv_eq_right_inv (normalMatrix_mul_inverse q c a b hq hc)

/-- The same invariant-line normalization c cancels from the relative
action. The remaining unipotent coefficients are fully retained. -/
theorem relative_action_coordinates (q c a b d e : k) (hq : q ≠ 0) (hc : c ≠ 0)
    (v : Fin 3 → k) :
    normalMatrix q c a b * jordanThreeCoordinates v * (normalMatrix q c d e)⁻¹ =
      jordanThreeCoordinates
        ((coordinateMatrix q ((a - d) / q) ((b + d ^ 2 - e - a * d) / q ^ 2)).mulVec v) := by
  rw [normalMatrix_inv q c d e hq hc]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalMatrix, diagonal, unitShift, toeplitz, jordanThreeCoordinates, coordinateMatrix,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.vecMul_diagonal] <;>
    field_simp [hq, hc] <;> ring

/-- The operator on the actual centralizer, constructed in its proved
coordinates. The following theorem identifies its literal matrix action. -/
def relativeOperator (q c : k) (F1 F2 : Matrix (Fin 3) (Fin 3) k) :
    jordanThreeCentralizer k →ₗ[k] jordanThreeCentralizer k :=
  jordanThreeCentralizerEquiv.conj (Matrix.toLin'
    (coordinateMatrix q ((F1 0 1 / c - F2 0 1 / c) / q)
      ((F1 0 2 / c + (F2 0 1 / c) ^ 2 - F2 0 2 / c - (F1 0 1 / c) * (F2 0 1 / c)) / q ^ 2)))

theorem relativeOperator_val (q c : k) (hq : q ≠ 0) (hc : c ≠ 0)
    (F1 F2 : Matrix (Fin 3) (Fin 3) k)
    (hN1 : F1 * jordanThree k = q⁻¹ • (jordanThree k * F1))
    (hN2 : F2 * jordanThree k = q⁻¹ • (jordanThree k * F2))
    (hl1 : F1 0 0 = c) (hl2 : F2 0 0 = c) (X : jordanThreeCentralizer k) :
    (relativeOperator q c F1 F2 X).val = F1 * X.val * F2⁻¹ := by
  obtain ⟨v, rfl⟩ := (jordanThreeCentralizerEquiv (k := k)).surjective X
  simp only [relativeOperator, LinearEquiv.conj_apply_apply,
    LinearEquiv.symm_apply_apply, jordanThreeCentralizerEquiv_val, Matrix.toLin'_apply]
  conv_rhs =>
    rw [normal_form q c hq hc F1 hN1 hl1, normal_form q c hq hc F2 hN2 hl2]
  exact (relative_action_coordinates q c _ _ _ _ hq hc v).symm

/-- The boundary trace is unchanged by either source's unipotent part.
The preceding theorem connects this trace to the actual relative action. -/
theorem relativeOperator_trace (q c : k) (F1 F2 : Matrix (Fin 3) (Fin 3) k) :
    LinearMap.trace k (jordanThreeCentralizer k) (relativeOperator q c F1 F2) =
      1 + q⁻¹ + q⁻¹ ^ 2 := by
  rw [relativeOperator, LinearMap.trace_conj', coordinate_operator_trace]

end PrimeGap182.TypeIII.BoundaryFrobeniusNormalization

#print axioms PrimeGap182.TypeIII.BoundaryFrobeniusNormalization.normal_form
#print axioms PrimeGap182.TypeIII.BoundaryFrobeniusNormalization.normalMatrix_mul_inverse
#print axioms PrimeGap182.TypeIII.BoundaryFrobeniusNormalization.normalMatrix_inv
#print axioms PrimeGap182.TypeIII.BoundaryFrobeniusNormalization.relative_action_coordinates
#print axioms PrimeGap182.TypeIII.BoundaryFrobeniusNormalization.relativeOperator
#print axioms PrimeGap182.TypeIII.BoundaryFrobeniusNormalization.relativeOperator_val
#print axioms PrimeGap182.TypeIII.BoundaryFrobeniusNormalization.relativeOperator_trace
