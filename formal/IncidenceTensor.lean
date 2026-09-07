import IncidencePrimeModes
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Euclidean norm bounds for actual tensor products and CRT reindexing

The tensor estimate follows from the contractivity of the two actual
star-algebra embeddings A ↦ A ⊗ I and B ↦ I ⊗ B. No tensor norm identity is
assumed. These finite matrix lemmas are independent of any arithmetic bound.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- An actual index equivalence preserves the Euclidean square-matrix norm. -/
theorem incidence_submatrix_equiv_norm (M : Matrix n n ℂ) (e : m ≃ n) :
    ‖M.submatrix e e‖ = ‖M‖ := by
  let φ : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix m m ℂ :=
    { Matrix.reindexAlgEquiv ℂ ℂ e.symm with
      map_smul' := fun _ _ => rfl
      map_star' := fun _ => rfl }
  exact StarAlgEquiv.norm_map φ M

/-- The first tensor embedding, including a possibly empty second index. -/
def incidenceTensorLeft : Matrix m m ℂ →⋆ₙₐ[ℂ] Matrix (m × n) (m × n) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix n n ℂ)
  map_zero' := Matrix.zero_kronecker _
  map_add' A B := Matrix.add_kronecker A B _
  map_mul' A B := by
    simpa only [one_mul] using
      Matrix.mul_kronecker_mul A B (1 : Matrix n n ℂ) (1 : Matrix n n ℂ)
  map_smul' c A := Matrix.smul_kronecker c A _
  map_star' A := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one]

/-- The second tensor embedding. -/
def incidenceTensorRight : Matrix n n ℂ →⋆ₙₐ[ℂ] Matrix (m × n) (m × n) ℂ where
  toFun B := (1 : Matrix m m ℂ) ⊗ₖ B
  map_zero' := Matrix.kronecker_zero _
  map_add' A B := Matrix.kronecker_add _ A B
  map_mul' A B := by
    simpa only [one_mul] using
      Matrix.mul_kronecker_mul (1 : Matrix m m ℂ) (1 : Matrix m m ℂ) A B
  map_smul' c A := Matrix.kronecker_smul c _ A
  map_star' A := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one]

theorem incidence_kronecker_norm_le (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    ‖A ⊗ₖ B‖ ≤ ‖A‖ * ‖B‖ := by
  have hA : ‖A ⊗ₖ (1 : Matrix n n ℂ)‖ ≤ ‖A‖ :=
    NonUnitalStarAlgHom.norm_apply_le (incidenceTensorLeft (n := n)) A
  have hB : ‖(1 : Matrix m m ℂ) ⊗ₖ B‖ ≤ ‖B‖ :=
    NonUnitalStarAlgHom.norm_apply_le (incidenceTensorRight (m := m)) B
  have hmul : A ⊗ₖ B = (A ⊗ₖ (1 : Matrix n n ℂ)) * ((1 : Matrix m m ℂ) ⊗ₖ B) := by
    simpa only [mul_one, one_mul] using
      Matrix.mul_kronecker_mul A (1 : Matrix m m ℂ) (1 : Matrix n n ℂ) B
  rw [hmul]
  exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hA hB (norm_nonneg _) (norm_nonneg _))

#print axioms incidence_submatrix_equiv_norm
#print axioms incidence_kronecker_norm_le

end PrimeGap182Audit
