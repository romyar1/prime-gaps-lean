import TypeIIICoherentGenericSourceZeroFromGeneralOrigin03
import TypeIIIGeometricBoundaryFromFunctors
import TypeIIICurveDataFromOperations

/-!
# The generic boundary uses the SAME computed geometric zero functor

One all-schemes theory is fixed before p. ALL-field generic-curve ordinary
cohomology/observables and actual connecting maps are chosen once. GENERAL
localization, guarded dual restriction and positive-slope clauses concern
ALL eligible ordinary inputs, not the Kloosterman tensor recipe.

The zero functor is literally genericZero of that theory. BoundarySequence,
RestrictionData and ZeroFunctor are outputs, and the comparison to zero
is refl. The computed general-origin application supplies the primitive
local Kl and additive models on this SAME zero. There is no independent
zero functor, selected zero recognition or ZK/ZA premise.

Genuine six-operation/local trait interpretations and the listed general
operation laws are external published-theory premises. This source neither
constructs an adic model nor closes the endpoint or its uniform caps. NEW
staged source only; no elaboration/object claimed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.CoherentGenericZeroBoundaryFromGeneralLocalization06
open ExactInverseImagesToDerived PrimitiveRamificationFromGeneralKatzTheory
open PublishedPhysicalConstruction BoundaryFromSourceModels GeometricBoundaryFromFunctors
open OriginModelsFromSameComputedCoefficients CurveDataFromOperations
open CanonicalCurveInput PublishedMackey CanonicalSourceLocalData

universe mu v point
variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  [∀ X, MonoidalCategory (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (M : LocalRealization C)
  [∀ (E : Type) [Field E], (M.origin E).Monoidal]
  (Point : ∀ (K : Type) [Field K], Type point)
  (Obs : ∀ (K : Type) [Field K],
    Observables (C (GenericSourceSpecialization.genericScheme K)) (Point K))
  (dualInput : ∀ (K : Type) [Field K],
    (C (GenericSourceSpecialization.genericScheme K))ᵒᵖ ⥤ C (GenericSourceSpecialization.genericScheme K))
  (H : ∀ (K : Type) [Field K],
    CohomologyData (C (GenericSourceSpecialization.genericScheme K))
      (C (GenericCurvePullback.parameterScheme K)))
  (observer : ∀ (K : Type) [Field K],
    C (GenericCurvePullback.parameterScheme K) ⥤ ModuleCat ℂ)
  (Iinf : ∀ (K : Type) [Field K], Type v)
  [∀ (K : Type) [Field K], Group (Iinf K)]

/-- Ordinary geometric localization/dual laws for ALL fields and inputs.
The connecting map is the actual chosen localization map; no finished
BoundarySequence/RestrictionData/ZeroFunctor is a record field. -/
structure GeneralCurveBoundaryClauses where
  infinity : ∀ (K : Type) [Field K] (_h2 : (2 : K) ≠ 0),
    C (GenericSourceSpecialization.genericScheme K) ⥤ FDRep ℂ (Iinf K)
  dual : ∀ (K : Type) [Field K] (_h2 : (2 : K) ≠ 0)
      (A : C (GenericSourceSpecialization.genericScheme K)),
    (Obs K).Lisse A →
    Representation.Equiv
      ((genericZero C U M K).obj ((dualInput K).obj (Opposite.op A))).ρ
      (PublishedPhaseApplication.dualRepresentation ((genericZero C U M K).obj A)).ρ
  positiveSlope : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
      (A : C (GenericSourceSpecialization.genericScheme K)),
    (Obs K).Isoclinic A 1 → Representation.invariants ((infinity K h2).obj A).ρ = ⊥
  connecting : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
      (A : C (GenericSourceSpecialization.genericScheme K)),
    (Representation.invariants ((genericZero C U M K).obj A).ρ ×
      Representation.invariants ((infinity K h2).obj A).ρ) →ₗ[ℂ]
        (observer K).obj ((H K).compact A)
  connecting_injective : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
      (A : C (GenericSourceSpecialization.genericScheme K)),
    (Obs K).Lisse A → (Obs K).Isoclinic A 1 → Function.Injective (connecting K h2 A)
  connecting_exact : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
      (A : C (GenericSourceSpecialization.genericScheme K)),
    (Obs K).Lisse A → (Obs K).TameZero A → (Obs K).Isoclinic A 1 →
    LinearMap.range (connecting K h2 A) = LinearMap.ker ((observer K).map ((H K).comparison A)).hom

variable (laws : GeneralCurveBoundaryClauses C U M Point Obs dualInput H observer Iinf)
  (K : Type) [Field K] (h2 : (2 : K) ≠ 0)

include C U M Point Obs dualInput H observer Iinf laws K h2

/-- The zero field is the literal standard genericZero, before any source
or parameter is selected. All other fields are general theorem projections. -/
def computedBoundaryData : GeometricBoundaryFromFunctors.Data
    (G0 := M.originGroup (GenericOriginFractionFieldCoordinates.ParameterFractionField K))
    (Ginf := Iinf K) ((Obs K).curveData (dualInput K)) (H K) (observer K) (dualInput K) where
  zero := genericZero C U M K
  infinity := laws.infinity K h2
  dual := laws.dual K h2
  positiveSlope := laws.positiveSlope K h2
  toCompact := laws.connecting K h2
  injective := laws.connecting_injective K h2
  exact := laws.connecting_exact K h2

/-- Boundary space and connecting map are constructed together. -/
def computedBoundarySequence :=
  (computedBoundaryData C U M Point Obs dualInput H observer Iinf laws K h2).boundarySequence

/-- Tensor and dual restriction comparisons are derived from canonical
identity comparisons of ordinary tensor/internal dual and general laws. -/
def computedRestriction :=
  (computedBoundaryData C U M Point Obs dualInput H observer Iinf laws K h2).restriction
    (fun _ _ => Iso.refl _) (fun _ => Iso.refl _)

/-- The source-isomorphism transport uses the same zero, with refl comparison. -/
def computedZeroFunctor :=
  (computedBoundaryData C U M Point Obs dualInput H observer Iinf laws K h2).zeroFunctor
    (fun _ _ => Iso.refl _) (fun _ => Iso.refl _)

/-- Literal zero identification for every ordinary input; no model-recognition
predicate or selected family equality is an assumption. -/
theorem restriction_zero_literal (A : C (GenericSourceSpecialization.genericScheme K)) :
    (computedRestriction C U M Point Obs dualInput H observer Iinf laws K h2).zero A =
      (genericZero C U M K).obj A := rfl

end PrimeGap182.TypeIII.CoherentGenericZeroBoundaryFromGeneralLocalization06

#print axioms PrimeGap182.TypeIII.CoherentGenericZeroBoundaryFromGeneralLocalization06.computedBoundaryData
#print axioms PrimeGap182.TypeIII.CoherentGenericZeroBoundaryFromGeneralLocalization06.computedRestriction
#print axioms PrimeGap182.TypeIII.CoherentGenericZeroBoundaryFromGeneralLocalization06.computedZeroFunctor
#print axioms PrimeGap182.TypeIII.CoherentGenericZeroBoundaryFromGeneralLocalization06.restriction_zero_literal
