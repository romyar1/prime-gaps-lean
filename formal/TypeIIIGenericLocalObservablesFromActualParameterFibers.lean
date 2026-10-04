import TypeIIIGenericCurveRanksFromActualFractionPoint
import TypeIIIUniformSourceLocalObservablesFromParameterFibers
import TypeIIIGenericOriginFractionFieldCoordinates

/-!
Actual relative parameter points include every field algebra over the original
Laurent parameter ring. Their generic curve fibers retain the curve variable
and apply the actual parameter coefficient map. Generic ramification and Swan
observables use the SAME ordinary inverse images and local realization on
ALL those fibers. Pure is retained individually; no finite-field point purity
condition is substituted for purity over this infinite parameter field.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
namespace PrimeGap182.TypeIII.GenericLocalObservablesFromActualParameterFibers
open GenericCurvePullback GenericSourceSpecialization ExactInverseImagesToDerived
open PrimitiveRamificationFromGeneralKatzTheory NaturalSwanFromFiniteBreakProfile

variable (K : Type) [Field K]

structure ParameterPoint where
  coefficientField : Type
  [fieldStructure : Field coefficientField]
  [parameterAlgebra : Algebra (ParameterRing K) coefficientField]

attribute [instance] ParameterPoint.fieldStructure ParameterPoint.parameterAlgebra

instance pointBaseAlgebra (t : ParameterPoint K) : Algebra K t.coefficientField :=
  ((algebraMap (ParameterRing K) t.coefficientField).comp
    (algebraMap K (ParameterRing K))).toAlgebra

instance pointScalarTower (t : ParameterPoint K) :
    IsScalarTower K (ParameterRing K) t.coefficientField :=
  IsScalarTower.of_algebraMap_eq' rfl

def parameterPoint (E : Type) [Field E] [Algebra (ParameterRing K) E] : ParameterPoint K where
  coefficientField := E
  fieldStructure := inferInstance
  parameterAlgebra := inferInstance

/-- Coefficient base change on the SAME original Laurent curve ring. -/
def genericCoefficientHom (E : Type) [Field E] [Algebra (ParameterRing K) E] :
    GenericRing K →+* ArithmeticSourceMaps.FiberRing E :=
  LaurentPolynomial.eval₂
    ((LaurentPolynomial.C : E →+* _).comp (algebraMap (ParameterRing K) E))
    (PhysicalTorusLaurent.variableUnit E)

theorem genericCoefficientHom_C (E : Type) [Field E] [Algebra (ParameterRing K) E]
    (a : ParameterRing K) :
    genericCoefficientHom K E (LaurentPolynomial.C a) =
      LaurentPolynomial.C (algebraMap (ParameterRing K) E a) :=
  LaurentPolynomial.eval₂_C _ _ a

theorem genericCoefficientHom_curveUnit (E : Type) [Field E] [Algebra (ParameterRing K) E] :
    genericCoefficientHom K E (curveUnit K : GenericRing K) =
      (PhysicalTorusLaurent.variableUnit E : ArithmeticSourceMaps.FiberRing E) := by
  change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.T 1) = _
  rw [LaurentPolynomial.eval₂_T, zpow_one]

def genericCoefficientMorphism (E : Type) [Field E] [Algebra (ParameterRing K) E] :
    ArithmeticSourceMaps.fiberScheme E ⟶ genericScheme K :=
  Spec.map (CommRingCat.ofHom (genericCoefficientHom K E))

theorem fractionMorphism_eq :
    genericCoefficientMorphism K (GenericOriginFractionFieldCoordinates.ParameterFractionField K) =
      GenericOriginFractionFieldCoordinates.genericFractionMorphism K := rfl

theorem point_two_ne_zero (t : ParameterPoint K) (hK : (2 : K) ≠ 0) :
    (2 : t.coefficientField) ≠ 0 := by
  have h := (algebraMap K t.coefficientField).injective.ne hK
  simpa only [map_ofNat, map_zero] using h

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (L : ∀ X : Scheme, ObjectProperty (C X))
  (M : LocalRealization C)
  (Z : UniformSourceLocalObservablesFromParameterFibers.OriginProfiles C M)

def curveRestriction (t : ParameterPoint K) :
    C (genericScheme K) ⥤ C (ArithmeticSourceMaps.fiberScheme t.coefficientField) :=
  U.pull (genericCoefficientMorphism K t.coefficientField)

def infinityProfile (A : C (genericScheme K)) (t : ParameterPoint K) : BreakProfile :=
  M.profile t.coefficientField ((curveRestriction K C U t).obj A)

def genericTameZero (A : C (genericScheme K)) : Prop :=
  L (genericScheme K) A ∧ ∀ t : ParameterPoint K,
    wildTrivial (M.wildOrigin t.coefficientField)
      ((M.origin t.coefficientField).obj ((curveRestriction K C U t).obj A))

def genericBreaksLE (A : C (genericScheme K)) (s : ℚ) : Prop :=
  L (genericScheme K) A ∧ ∀ t : ParameterPoint K,
    ∀ r ∈ (infinityProfile K C U M A t).multiplicity.support, r ≤ s

def genericIsoclinic (A : C (genericScheme K)) (s : ℚ) : Prop :=
  L (genericScheme K) A ∧ ∀ t : ParameterPoint K,
    ∀ r ∈ (infinityProfile K C U M A t).multiplicity.support, r = s

def genericSwanZero (A : C (genericScheme K)) (t : ParameterPoint K) : ℕ :=
  naturalSwan (Z.profile t.coefficientField ((curveRestriction K C U t).obj A))

def genericSwanInfinity (A : C (genericScheme K)) (t : ParameterPoint K) : ℕ :=
  naturalSwan (infinityProfile K C U M A t)

variable (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)
  (pure : C (genericScheme K) → ℝ → Prop)

def genericObservables : CurveDataFromOperations.Observables
    (C (genericScheme K)) (ParameterPoint K) where
  Lisse := L (genericScheme K)
  Pure := pure
  rank := GenericCurveRanksFromActualFractionPoint.canonicalGenericCurveRank K C U G
  TameZero := genericTameZero K C U L M
  BreaksLE := genericBreaksLE K C U L M
  Isoclinic := genericIsoclinic K C U L M
  swanZero := genericSwanZero K C U M Z
  swanInfinity := genericSwanInfinity K C U M

end PrimeGap182.TypeIII.GenericLocalObservablesFromActualParameterFibers
