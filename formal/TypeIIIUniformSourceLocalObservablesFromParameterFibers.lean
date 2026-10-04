import TypeIIINaturalSwanFromFiniteBreakProfile
import TypeIIIScalarGenericSourceRankFromLissePoints
import TypeIIIScalarSourceSpecializationCoordinates

/-!
# Uniform globally-lisse source local observables on actual parameter fibers

Parameter points contain their actual coefficient field, algebra structure
and two units. Every local profile is taken after the original SAME-U source
specialization to that field's Gm. Tame/break/isoclinic predicates explicitly
require global source lissity and the local condition on EVERY parameter
fiber. Conductors use the natural sum of that SAME finite upper-break profile.
No fixed-point/generic rank constancy for arbitrary constructible objects,
vertical-support specialization law or selected source Swan equality is assumed.

One general local lisse-rank comparison identifies the infinity representation
dimension with the actual generic Gm coefficient dimension over every field.
The existing integral globally-lisse geometric/arithmetic point-rank law then
identifies EVERY specialized profile rank with generic source rank. One general
wild-trivial-origin break theorem gives tame support. These precise universal
local theorem/model applications derive the two original unguarded conductor
rules for the constructed, explicitly globally-lisse uniform predicates.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace PrimeGap182.TypeIII.UniformSourceLocalObservablesFromParameterFibers
open ExactInverseImagesToDerived RationalPointStalksFromUniversalFiber
open PrimitiveRamificationFromGeneralKatzTheory NaturalSwanFromFiniteBreakProfile
open GenericSourceRanksFromActualFractionPoint SourceRanksFromCommonFinitePoint
open ScalarGenericSourceRankFromLissePoints

variable (K : Type) [Field K]

/-- A genuine parameter fiber, including infinite generic coefficient fields. -/
structure ParameterPoint where
  coefficientField : Type
  [fieldStructure : Field coefficientField]
  [algebraStructure : Algebra K coefficientField]
  lambda : coefficientFieldˣ
  xi : coefficientFieldˣ

attribute [instance] ParameterPoint.fieldStructure ParameterPoint.algebraStructure

/-- Every actual field-extension unit pair gives its literal parameter point. -/
def parameterPoint (E : Type) [Field E] [Algebra K E] (lambda xi : Eˣ) : ParameterPoint K where
  coefficientField := E
  fieldStructure := inferInstance
  algebraStructure := inferInstance
  lambda := lambda
  xi := xi

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)
  (L : ∀ X : Scheme, ObjectProperty (C X))
  (M : LocalRealization C)

/-- The origin upper-break data is coupled to the SAME origin representation,
with actual dimension and local-isomorphism invariance. Its continuous
inertia/upper-numbering interpretation remains external model data. -/
structure OriginProfiles where
  profile : ∀ (E : Type) [Field E], C (ArithmeticSourceMaps.fiberScheme E) → BreakProfile
  dimension : ∀ (E : Type) [Field E] (A : C (ArithmeticSourceMaps.fiberScheme E)),
    (profile E A).rank = Module.finrank (PadicAlgCl 2) ((M.origin E).obj A)
  localIso : ∀ (E : Type) [Field E] (A B : C (ArithmeticSourceMaps.fiberScheme E)),
    ((M.origin E).obj A ≅ (M.origin E).obj B) →
      (profile E A).multiplicity = (profile E B).multiplicity

variable (Z : OriginProfiles C M)

/-- The source fiber is the actual existing coordinate specialization. -/
def sourceRestriction (t : ParameterPoint K) :
    C (StartingSourceMaps.sourceScheme K) ⥤ C (ArithmeticSourceMaps.fiberScheme t.coefficientField) :=
  U.pull (ArithmeticSourceMaps.specializationMorphism K t.coefficientField t.lambda t.xi)

/-- The infinity profile uses SAME-M after SAME-U at the literal parameter fiber. -/
def sourceInfinityProfile (A : C (StartingSourceMaps.sourceScheme K)) (t : ParameterPoint K) :
    BreakProfile := M.profile t.coefficientField ((sourceRestriction K C U t).obj A)

/-- Tame source families are globally lisse and wild-trivial on every actual fiber. -/
def sourceTameZero (A : C (StartingSourceMaps.sourceScheme K)) : Prop :=
  L (StartingSourceMaps.sourceScheme K) A ∧ ∀ t : ParameterPoint K,
    wildTrivial (M.wildOrigin t.coefficientField) ((M.origin t.coefficientField).obj
      ((sourceRestriction K C U t).obj A))

/-- Bounded-break source families are globally lisse with the uniform fiber bound. -/
def sourceBreaksLE (A : C (StartingSourceMaps.sourceScheme K)) (s : ℚ) : Prop :=
  L (StartingSourceMaps.sourceScheme K) A ∧ ∀ t : ParameterPoint K,
    ∀ r ∈ (sourceInfinityProfile K C U M A t).multiplicity.support, r ≤ s

/-- Isoclinic source families are globally lisse with the same slope on every fiber. -/
def sourceIsoclinic (A : C (StartingSourceMaps.sourceScheme K)) (s : ℚ) : Prop :=
  L (StartingSourceMaps.sourceScheme K) A ∧ ∀ t : ParameterPoint K,
    ∀ r ∈ (sourceInfinityProfile K C U M A t).multiplicity.support, r = s

/-- The zero conductor is computed from the actual origin profile of the same fiber. -/
def sourceSwanZero (A : C (StartingSourceMaps.sourceScheme K)) (t : ParameterPoint K) : ℕ :=
  naturalSwan (Z.profile t.coefficientField ((sourceRestriction K C U t).obj A))

/-- The infinity conductor is computed from the actual infinity profile of the same fiber. -/
def sourceSwanInfinity (A : C (StartingSourceMaps.sourceScheme K)) (t : ParameterPoint K) : ℕ :=
  naturalSwan (sourceInfinityProfile K C U M A t)

/-- All source local/numeric fields are computed on one genuine parameter-fiber model. -/
def sourceObservables : SourcePurityFromStalks.Observables
    (C (StartingSourceMaps.sourceScheme K)) (ParameterPoint K) where
  Lisse := L (StartingSourceMaps.sourceScheme K)
  rank := canonicalGenericSourceRank K C U G
  TameZero := sourceTameZero K C U L M
  BreaksLE := sourceBreaksLE K C U L M
  Isoclinic := sourceIsoclinic K C U L M
  swanZero := sourceSwanZero K C U M Z
  swanInfinity := sourceSwanInfinity K C U M

variable
  (originWildSupport : ∀ (E : Type) [Field E] (A : C (ArithmeticSourceMaps.fiberScheme E)),
    wildTrivial (M.wildOrigin E) ((M.origin E).obj A) →
      ∀ r ∈ (Z.profile E A).multiplicity.support, r = 0)

include originWildSupport in
/-- The original source tame-Swan rule follows for every actual parameter fiber. -/
theorem tame_swan (A : C (StartingSourceMaps.sourceScheme K))
    (hA : sourceTameZero K C U L M A) (t : ParameterPoint K) :
    sourceSwanZero K C U M Z A t = 0 :=
  naturalSwan_of_tame_support _ (originWildSupport t.coefficientField _ (hA.2 t))

variable (F : ArithmeticFibers C)
  (lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y), L Y A → L X ((U.pull f).obj A))
  (localGenericRank : ∀ (E : Type) [Field E] (A : C (ArithmeticSourceMaps.fiberScheme E)),
    L (ArithmeticSourceMaps.fiberScheme E) A →
      Module.finrank (PadicAlgCl 2) ((M.infinity E).obj A) =
        geometricPointRank C U G (QSTGenericFiberFromActualGenericPoint.GenericField E)
          (ArithmeticSourceMaps.fiberScheme E) (QSTGenericFiberFromActualGenericPoint.genericPoint E) A)
  (lisseGeometricArithmeticPointRank : ∀ (X : Scheme) [IsIntegral X]
    (A : C X), L X A → ∀ (Eg : Type) [Field Eg] (xg : Spec (.of Eg) ⟶ X)
      (Ea : Type) [Field Ea] [Fintype Ea] (xa : Spec (.of Ea) ⟶ X),
      geometricPointRank C U G Eg X xg A = pointRank C U F Ea X xa A)

include lissePull localGenericRank lisseGeometricArithmeticPointRank in
/-- Globally lisse source families have the computed generic rank on EVERY parameter profile. -/
theorem sourceInfinityProfile_rank [Fintype K]
    (A : C (StartingSourceMaps.sourceScheme K)) (hA : L (StartingSourceMaps.sourceScheme K) A)
    (t : ParameterPoint K) :
    (sourceInfinityProfile K C U M A t).rank = canonicalGenericSourceRank K C U G A := by
  let f := ArithmeticSourceMaps.specializationMorphism K t.coefficientField t.lambda t.xi
  let g := QSTGenericFiberFromActualGenericPoint.genericPoint t.coefficientField
  have hl := lissePull f A hA
  calc
    (sourceInfinityProfile K C U M A t).rank =
        Module.finrank (PadicAlgCl 2) ((M.infinity t.coefficientField).obj ((U.pull f).obj A)) :=
      M.profile_dimension t.coefficientField _
    _ = geometricPointRank C U G
        (QSTGenericFiberFromActualGenericPoint.GenericField t.coefficientField) _ g ((U.pull f).obj A) :=
      localGenericRank t.coefficientField _ hl
    _ = geometricPointRank C U G
        (QSTGenericFiberFromActualGenericPoint.GenericField t.coefficientField)
        (StartingSourceMaps.sourceScheme K) (g ≫ f) A :=
      ((G.fiber (QSTGenericFiberFromActualGenericPoint.GenericField t.coefficientField)).mapIso
        ((U.composition g f).app A)).toLinearEquiv.finrank_eq
    _ = pointRank C U F K _ (RationalPointStalks.curvePoint (K := K) (L := K) 1 1 1) A :=
      lisseGeometricArithmeticPointRank (StartingSourceMaps.sourceScheme K) A hA
        (QSTGenericFiberFromActualGenericPoint.GenericField t.coefficientField) (g ≫ f) K
          (RationalPointStalks.curvePoint (K := K) (L := K) 1 1 1)
    _ = canonicalGenericSourceRank K C U G A :=
      (source_generic_rank_at_unit C U F G L lisseGeometricArithmeticPointRank K A hA).symm

include lissePull localGenericRank lisseGeometricArithmeticPointRank in
/-- The original unguarded source slope-one-Swan rule holds for the explicitly uniform lisse predicate. -/
theorem slope_one_swan [Fintype K] (A : C (StartingSourceMaps.sourceScheme K))
    (hA : sourceIsoclinic K C U L M A 1) (t : ParameterPoint K) :
    sourceSwanInfinity K C U M A t = canonicalGenericSourceRank K C U G A :=
  (naturalSwan_of_isoclinic_one _ (hA.2 t)).trans
    (sourceInfinityProfile_rank K C U G L M F lissePull localGenericRank
      lisseGeometricArithmeticPointRank A hA.1 t)

end PrimeGap182.TypeIII.UniformSourceLocalObservablesFromParameterFibers
