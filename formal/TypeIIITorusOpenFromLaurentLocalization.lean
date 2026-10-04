import TypeIIIUniformComplexityFromCommonRealization
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# The actual torus open immersion from Laurent localization

The original quotient torus ring is already identified with the double
Laurent ring.  The actual two-coordinate map factors through localization
of the inner polynomial coefficient and localization of the outer variable.
This proves an open immersion of schemes over every field; no sheaf or QST
realization premise is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

namespace PrimeGap182.TypeIII.TorusOpenFromLaurentLocalization
open PhysicalTorusMorphism PhysicalTorusLaurent

variable (K : Type) [Field K]

/-- The first affine coordinate is the inner polynomial variable. -/
def doublePolynomialEquiv :
    MvPolynomial (Fin 2) K ≃ₐ[K] Polynomial (Polynomial K) :=
  ((MvPolynomial.renameEquiv K (Equiv.swap 0 1)).trans
    (MvPolynomial.finSuccEquiv K 1)).trans
      (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv K (Fin 1)))

theorem doublePolynomialEquiv_X_zero :
    doublePolynomialEquiv K (MvPolynomial.X 0) = Polynomial.C Polynomial.X := by
  simp only [doublePolynomialEquiv, AlgEquiv.trans_apply,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, Equiv.swap_apply_left]
  rw [show (1 : Fin 2) = (0 : Fin 1).succ from rfl, MvPolynomial.finSuccEquiv_X_succ]
  simp [MvPolynomial.uniqueAlgEquiv_apply]

theorem doublePolynomialEquiv_X_one :
    doublePolynomialEquiv K (MvPolynomial.X 1) = Polynomial.X := by
  simp [doublePolynomialEquiv, MvPolynomial.renameEquiv_apply,
    MvPolynomial.finSuccEquiv_apply]

/-- Localization of the inner coefficient variable, retaining the outer variable. -/
def innerMap : Polynomial (Polynomial K) →+* Polynomial (LaurentPolynomial K) :=
  Polynomial.mapRingHom Polynomial.toLaurent

theorem innerMap_isOpenImmersion :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (innerMap K))) := by
  let : Algebra (Polynomial (Polynomial K)) (Polynomial (LaurentPolynomial K)) :=
    Polynomial.algebra (Polynomial K) (LaurentPolynomial K)
  have : IsLocalization.Away (Polynomial.C (Polynomial.X : Polynomial K))
      (Polynomial (LaurentPolynomial K)) := by
    rw [IsLocalization.Away, ← Submonoid.map_powers]
    exact Polynomial.isLocalization (Submonoid.powers (Polynomial.X : Polynomial K))
      (LaurentPolynomial K)
  exact IsOpenImmersion.of_isLocalization (Polynomial.C (Polynomial.X : Polynomial K))

/-- Localization of the outer variable over the already localized coefficient ring. -/
def outerMap : Polynomial (LaurentPolynomial K) →+* DoubleLaurent K :=
  Polynomial.toLaurent

theorem outerMap_isOpenImmersion :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (outerMap K))) :=
  IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial (LaurentPolynomial K))

/-- The localization factorization sends the literal affine coordinates to
the original torus units, including both independent inverses. -/
theorem coordinateMap_factorization :
    (fromLaurent K).toRingHom.comp ((outerMap K).comp
      ((innerMap K).comp (doublePolynomialEquiv K).toRingHom)) =
      (MvPolynomial.aeval ![(xUnit K : TorusRing K), (yUnit K : TorusRing K)]).toRingHom := by
  ext i : 2
  · have hC : doublePolynomialEquiv K (MvPolynomial.C i) =
        Polynomial.C (Polynomial.C i) := (doublePolynomialEquiv K).commutes i
    simp [hC, innerMap, outerMap, fromLaurent_C, innerEvaluation_C]
  · fin_cases i
    · simp [RingHom.comp_apply, doublePolynomialEquiv_X_zero, innerMap, outerMap,
        fromLaurent_C, innerEvaluation_T]
    · simp [RingHom.comp_apply, doublePolynomialEquiv_X_one, innerMap, outerMap,
        fromLaurent_T]

theorem torusOpen_factorization :
    UniformComplexityFromCommonRealization.torusOpen K =
      Spec.map (CommRingCat.ofHom (fromLaurent K).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (outerMap K)) ≫
          Spec.map (CommRingCat.ofHom (innerMap K)) ≫
            Spec.map (CommRingCat.ofHom (doublePolynomialEquiv K).toRingHom) := by
  unfold UniformComplexityFromCommonRealization.torusOpen
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [coordinateMap_factorization K]

/-- The same torus coordinate map used by the original QST construction is open. -/
instance torusOpen_isOpenImmersion :
    IsOpenImmersion (UniformComplexityFromCommonRealization.torusOpen K) := by
  have : IsIso (CommRingCat.ofHom (fromLaurent K).toRingHom) :=
    inferInstanceAs (IsIso (torusLaurentEquiv K).symm.toRingEquiv.toCommRingCatIso.hom)
  have : IsIso (CommRingCat.ofHom (doublePolynomialEquiv K).toRingHom) :=
    inferInstanceAs (IsIso (doublePolynomialEquiv K).toRingEquiv.toCommRingCatIso.hom)
  have := innerMap_isOpenImmersion K
  have := outerMap_isOpenImmersion K
  rw [torusOpen_factorization K]
  infer_instance

/-- The affine presentation of `torus2` is induced from the plane presentation. -/
theorem torus2_affineEmbedding_factorization :
    UniformComplexityFromCommonRealization.torusOpen K ≫
      UniformComplexityFromCommonRealization.affineEmbedding K .plane =
        UniformComplexityFromCommonRealization.affineEmbedding K .torus2 := by
  exact Category.comp_id _

end PrimeGap182.TypeIII.TorusOpenFromLaurentLocalization
