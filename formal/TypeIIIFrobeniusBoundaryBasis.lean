import TypeIIIBoundaryFrobeniusNormalization
import TypeIIIGeometricCoreRank

/-!
# A boundary basis compatible with the existing Frobenius interface

The relative source action is triangular, not necessarily diagonal in
the original centralizer coordinates. An explicit invertible change of
basis identifies it with the standard Jordan-centralizer Frobenius when
1-q^(-1) and 1-q^(-2) are nonzero. These hold for finite-field cardinalities.
This permits reuse of the existing arithmetic boundary record without
assuming the two source Frobenius matrices coincide.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Classical Matrix

namespace PrimeGap182.TypeIII.FrobeniusBoundaryBasis

open ScaledJordanCorrection BoundaryFrobeniusNormalization

variable {k : Type*} [Field k]

def lowerMatrix (x y : k) : Matrix (Fin 3) (Fin 3) k := (unitShift x y).transpose

theorem lowerMatrix_inverse (x y : k) :
    lowerMatrix x y * lowerMatrix (-x) (x ^ 2 - y) = 1 ∧
      lowerMatrix (-x) (x ^ 2 - y) * lowerMatrix x y = 1 := by
  constructor
  · simpa only [lowerMatrix, ← Matrix.transpose_mul, Matrix.transpose_one] using
      congrArg Matrix.transpose (unitShift_inverse x y).2
  · simpa only [lowerMatrix, ← Matrix.transpose_mul, Matrix.transpose_one] using
      congrArg Matrix.transpose (unitShift_inverse x y).1

def firstBasisCoefficient (q a : k) : k := a / (1 - q⁻¹)
def secondBasisCoefficient (q a b : k) : k :=
  (b + a * q⁻¹ * firstBasisCoefficient q a) / (1 - q⁻¹ ^ 2)

def basisMatrix (q a b : k) : Matrix (Fin 3) (Fin 3) k :=
  lowerMatrix (firstBasisCoefficient q a) (secondBasisCoefficient q a b)

/-- This basis has an explicit inverse even before eigenvalue conditions
are imposed; those conditions are used only for its intertwining property. -/
def coordinateBasisEquiv (q a b : k) : (Fin 3 → k) ≃ₗ[k] (Fin 3 → k) :=
  Matrix.toLin'OfInv
    (lowerMatrix_inverse (firstBasisCoefficient q a) (secondBasisCoefficient q a b)).2
    (lowerMatrix_inverse (firstBasisCoefficient q a) (secondBasisCoefficient q a b)).1

theorem basisMatrix_intertwines (q a b : k)
    (h1 : 1 - q⁻¹ ≠ 0) (h2 : 1 - q⁻¹ ^ 2 ≠ 0) :
    coordinateMatrix q a b * basisMatrix q a b =
      basisMatrix q a b * coordinateMatrix q 0 0 := by
  have hx : (1 - q⁻¹) * firstBasisCoefficient q a = a :=
    mul_div_cancel₀ a h1
  have hy : (1 - q⁻¹ ^ 2) * secondBasisCoefficient q a b =
      b + a * q⁻¹ * firstBasisCoefficient q a :=
    mul_div_cancel₀ _ h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateMatrix, basisMatrix, lowerMatrix, unitShift, toeplitz,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    first | linear_combination -hx | linear_combination -hy | linear_combination -(q⁻¹) * hx

def centralizerBasisEquiv (q a b : k) : jordanThreeCentralizer k ≃ₗ[k] jordanThreeCentralizer k :=
  (jordanThreeCentralizerEquiv.symm.trans (coordinateBasisEquiv q a b)).trans
    jordanThreeCentralizerEquiv

/-- The exact Frobenius intertwining required by the old arithmetic
boundary interface, rather than just equality of traces. -/
theorem centralizerBasis_intertwines (q a b : k) (hq : q ≠ 0)
    (h1 : 1 - q⁻¹ ≠ 0) (h2 : 1 - q⁻¹ ^ 2 ≠ 0) :
    (jordanThreeCentralizerEquiv.conj (Matrix.toLin' (coordinateMatrix q a b))).comp
        (centralizerBasisEquiv q a b).toLinearMap =
      (centralizerBasisEquiv q a b).toLinearMap.comp (jordanThreeCentralizerConjugation q hq) := by
  rw [jordanThreeCentralizerConjugation_eq_conj q hq]
  have hd : Matrix.diagonal ![1, q⁻¹, q⁻¹ ^ 2] = coordinateMatrix q 0 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coordinateMatrix]
  rw [hd]
  apply LinearMap.ext
  intro X
  obtain ⟨v, rfl⟩ := (jordanThreeCentralizerEquiv (k := k)).surjective X
  simp only [LinearMap.comp_apply, centralizerBasisEquiv, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  change jordanThreeCentralizerEquiv
      (Matrix.toLin' (coordinateMatrix q a b) (Matrix.toLin' (basisMatrix q a b) v)) =
    jordanThreeCentralizerEquiv
      (Matrix.toLin' (basisMatrix q a b) (Matrix.toLin' (coordinateMatrix q 0 0) v))
  rw [← Matrix.toLin'_mul_apply, ← Matrix.toLin'_mul_apply, basisMatrix_intertwines q a b h1 h2]

/-- The eigenvalue separations hold for every integer cardinality greater
than one, in any characteristic-zero coefficient field. -/
theorem nat_eigenvalue_separation [CharZero k] (n : ℕ) (hn : 1 < n) :
    1 - (n : k)⁻¹ ≠ 0 ∧ 1 - (n : k)⁻¹ ^ 2 ≠ 0 := by
  have hzero : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  constructor
  · intro h
    have he := congrArg (fun x : k => x * n) (sub_eq_zero.mp h)
    have heq : (n : k) = 1 := by simpa [hzero] using he
    have : n = 1 := by exact_mod_cast heq
    omega
  · intro h
    have he := congrArg (fun x : k => x * (n : k) ^ 2) (sub_eq_zero.mp h)
    have heq : (n : k) ^ 2 = 1 := by
      simpa only [one_mul, ← mul_pow, inv_mul_cancel₀ hzero, one_pow] using he
    have : n ^ 2 = 1 := by exact_mod_cast heq
    nlinarith

section ExistingBoundaryInterface

open CategoryTheory PublishedPhysicalConstruction GeometricCoreRank
universe u v w
variable {Input : Type u} {C : Type v} [Category.{w} C] [Abelian C]
  (H : CohomologyData Input C) (F : C ⥤ ModuleCat.{v} ℂ) (Fr : F ⟶ F)
  (A : Input) (B : GeometricBoundaryModel H F A)
  (q a b : ℂ) (hq : q ≠ 0) (h1 : 1 - q⁻¹ ≠ 0) (h2 : 1 - q⁻¹ ^ 2 ≠ 0)
  (hFr : (Fr.app (H.compact A)).hom.comp B.boundary =
    B.boundary.comp (jordanThreeCentralizerEquiv.conj (Matrix.toLin' (coordinateMatrix q a b))))

/-- Rebase the existing geometric boundary injection to construct the
unchanged arithmetic interface. Its image and injectivity are preserved.
The remaining hFr premise is the geometric naturality of the actual
relative source action, not a diagonal-boundary assertion. -/
def originBoundaryOfRelativeAction : OriginBoundaryModel H F A Fr q hq where
  boundary := B.boundary.comp (centralizerBasisEquiv q a b).toLinearMap
  injective := B.injective.comp (centralizerBasisEquiv q a b).injective
  exact := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
    exact B.exact
  frobenius := by
    rw [← LinearMap.comp_assoc, hFr, LinearMap.comp_assoc,
      centralizerBasis_intertwines q a b hq h1 h2, ← LinearMap.comp_assoc]

end ExistingBoundaryInterface

end PrimeGap182.TypeIII.FrobeniusBoundaryBasis

#print axioms PrimeGap182.TypeIII.FrobeniusBoundaryBasis.lowerMatrix_inverse
#print axioms PrimeGap182.TypeIII.FrobeniusBoundaryBasis.coordinateBasisEquiv
#print axioms PrimeGap182.TypeIII.FrobeniusBoundaryBasis.basisMatrix_intertwines
#print axioms PrimeGap182.TypeIII.FrobeniusBoundaryBasis.centralizerBasisEquiv
#print axioms PrimeGap182.TypeIII.FrobeniusBoundaryBasis.centralizerBasis_intertwines
#print axioms PrimeGap182.TypeIII.FrobeniusBoundaryBasis.nat_eigenvalue_separation
#print axioms PrimeGap182.TypeIII.FrobeniusBoundaryBasis.originBoundaryOfRelativeAction
