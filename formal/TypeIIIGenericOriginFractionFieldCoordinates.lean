import TypeIIILocalOriginRulesFromUniversalNearbyTheorems
import TypeIIIGeometricOriginFromScalar

/-!
# The actual generic curve over its parameter fraction field

F is the fraction field of the ORIGINAL Laurent parameter ring. The actual
coefficient-localization ring map gives Gm_F -> genericCurve_K by Spec
contravariance. Every original parameter-unit scalar becomes an actual unit
scalar on Gm_F followed by the original inclusion into A1_K. SAME U composition
constructs the complete natural nearby comparison. No selected boundary-zero
recognition, published theorem input or inertia model is assumed here.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace PrimeGap182.TypeIII.GenericOriginFractionFieldCoordinates
open GenericCurvePullback GenericSourceSpecialization GeometricOriginFromScalar
open ExactInverseImagesToDerived

variable (K : Type) [Field K]

abbrev ParameterFractionField := FractionRing (ParameterRing K)

def parameterFractionUnit (c : (ParameterRing K)ˣ) : (ParameterFractionField K)ˣ :=
  Units.map (algebraMap (ParameterRing K) (ParameterFractionField K)) c

/-- Coefficient localization retains the original curve Laurent variable. -/
def genericFractionHom : GenericRing K →ₐ[K]
    ArithmeticSourceMaps.FiberRing (ParameterFractionField K) where
  toRingHom := LaurentPolynomial.eval₂
    ((LaurentPolynomial.C : ParameterFractionField K →+* _).comp
      (algebraMap (ParameterRing K) (ParameterFractionField K)))
    (PhysicalTorusLaurent.variableUnit (ParameterFractionField K))
  commutes' c := by
    change LaurentPolynomial.eval₂ _ _
      (LaurentPolynomial.C (algebraMap K (ParameterRing K) c)) = _
    rw [LaurentPolynomial.eval₂_C]
    change LaurentPolynomial.C
      (algebraMap (ParameterRing K) (ParameterFractionField K)
        (algebraMap K (ParameterRing K) c)) =
      LaurentPolynomial.C (algebraMap K (ParameterFractionField K) c)
    rw [← IsScalarTower.algebraMap_apply K (ParameterRing K) (ParameterFractionField K)]

theorem genericFractionHom_C (a : ParameterRing K) :
    genericFractionHom K (LaurentPolynomial.C a) =
      LaurentPolynomial.C (algebraMap (ParameterRing K) (ParameterFractionField K) a) :=
  LaurentPolynomial.eval₂_C _ _ a

theorem genericFractionHom_curveUnit :
    genericFractionHom K (curveUnit K : GenericRing K) =
      (PhysicalTorusLaurent.variableUnit (ParameterFractionField K) :
        ArithmeticSourceMaps.FiberRing (ParameterFractionField K)) := by
  change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.T 1) = _
  rw [LaurentPolynomial.eval₂_T, zpow_one]

theorem genericFraction_scalarHom (c : (ParameterRing K)ˣ) :
    (genericFractionHom K).comp (genericScalarHom K c) =
      (ArithmeticSourceMaps.scalarHom K (ParameterFractionField K)
        (parameterFractionUnit K c)).comp
        (ArithmeticSourceMaps.localInputHom K (ParameterFractionField K)) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  simp only [AlgHom.comp_apply, genericScalarHom, ArithmeticSourceMaps.localInputHom,
    MvPolynomial.aeval_X, map_mul]
  change genericFractionHom K (LaurentPolynomial.C (c : ParameterRing K)) *
    genericFractionHom K (curveUnit K : GenericRing K) =
    ArithmeticSourceMaps.scalarHom K (ParameterFractionField K) (parameterFractionUnit K c)
      (PhysicalTorusLaurent.variableUnit (ParameterFractionField K) :
        ArithmeticSourceMaps.FiberRing (ParameterFractionField K))
  rw [genericFractionHom_C, genericFractionHom_curveUnit]
  change _ = LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.T 1)
  rw [LaurentPolynomial.eval₂_T, zpow_one]
  rfl

def genericFractionMorphism :
    ArithmeticSourceMaps.fiberScheme (ParameterFractionField K) ⟶ genericScheme K :=
  Spec.map (CommRingCat.ofHom (genericFractionHom K).toRingHom)

/-- Actual generic scalar factorization, with Spec's correct direction. -/
theorem genericFraction_scalarMorphism (c : (ParameterRing K)ˣ) :
    genericFractionMorphism K ≫ genericScalarMorphism K c =
      ArithmeticSourceMaps.scalarMorphism (ParameterFractionField K) (ParameterFractionField K)
        (parameterFractionUnit K c) ≫
        ArithmeticSourceMaps.localInputMorphism K (ParameterFractionField K) := by
  dsimp only [genericFractionMorphism, genericScalarMorphism,
    ArithmeticSourceMaps.scalarMorphism, ArithmeticSourceMaps.localInputMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (genericFraction_scalarHom K c))

universe mu v
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (H : ∀ (E : Type) [Field E], Type v)
  [∀ (E : Type) [Field E], Group (H E)]
  (N : ∀ (E : Type) [Field E],
    C (ArithmeticSourceMaps.fiberScheme E) ⥤ FDRep ℂ (H E))

def genericZeroFunctor : C (genericScheme K) ⥤ FDRep ℂ (H (ParameterFractionField K)) :=
  U.pull (genericFractionMorphism K) ⋙ N (ParameterFractionField K)

def primitiveOriginFunctor : C (StartingSourceMaps.affineLine K) ⥤
    FDRep ℂ (H (ParameterFractionField K)) :=
  U.pull (ArithmeticSourceMaps.localInputMorphism K (ParameterFractionField K)) ⋙
    N (ParameterFractionField K)

/-- ALL original generic parameter scalars compare through the SAME actual U. -/
def genericScalarOriginIso (c : (ParameterRing K)ˣ) :
    U.pull (genericScalarMorphism K c) ⋙ genericZeroFunctor K C U H N ≅
      U.pull (ArithmeticSourceMaps.localInputMorphism K (ParameterFractionField K)) ⋙
        U.pull (ArithmeticSourceMaps.scalarMorphism (ParameterFractionField K) (ParameterFractionField K)
          (parameterFractionUnit K c)) ⋙ N (ParameterFractionField K) :=
  Functor.isoWhiskerRight (U.composition (genericFractionMorphism K) (genericScalarMorphism K c))
      (N (ParameterFractionField K)) ≪≫
    Functor.isoWhiskerRight
      (eqToIso (congrArg (fun f => U.pull f) (genericFraction_scalarMorphism K c)))
      (N (ParameterFractionField K)) ≪≫
    Functor.isoWhiskerRight
      (U.composition
        (ArithmeticSourceMaps.scalarMorphism (ParameterFractionField K) (ParameterFractionField K)
          (parameterFractionUnit K c))
        (ArithmeticSourceMaps.localInputMorphism K (ParameterFractionField K))).symm
      (N (ParameterFractionField K))

end PrimeGap182.TypeIII.GenericOriginFractionFieldCoordinates
