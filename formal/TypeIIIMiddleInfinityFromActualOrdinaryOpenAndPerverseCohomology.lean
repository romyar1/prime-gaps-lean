import TypeIIIOrdinaryOpenExtensionsFromAdjunctions
import TypeIIIInfinityNearbyFromComputedPowerEmbedding
import TypeIIIMiddleInfinityFromPerverse
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
The middle infinity data is computed on the actual ordinary affine line and
its actual universal perverse heart. Ordinary j_* is the SAME right adjoint
in the existing open family; its restriction comparison follows from the
adjoint triple and the actual j_! unit isomorphism. No ordinary j_* exactness
or concentration of its derived direct image is assumed.

The one new universal MODEL comparison ranges over ALL standard bounded
complexes on ALL separated finite-type smooth curves and actual Gm open
charts, with two invertible. It identifies ordinary H^-1 of perverse H0
with ordinary H^-1 at the geometric generic stalk. Its BBD generic-lisse /
open t-exact interpretation, the supplied P/H0 and continuous nearby model
remain external. Punctual ordinary objects are allowed. They are not
asserted perverse after [1]; they disappear only at the generic stalk.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology
open ExactInverseImagesToDerived QSTCompactBridgeFromCompactifiedDerivedPushforward
open NativePerverseFromUniversalHeart PrimitiveRamificationFromGeneralKatzTheory
open InfinityNearbyFromComputedPowerEmbedding

universe mu

variable (E : Type) [Field E]

/-- The actual affine line structure morphism. -/
def lineStructure : StartingSourceMaps.affineLine E ⟶ Spec (.of E) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C : E →+* MvPolynomial (Fin 1) E))

/-- Polynomial generators with no relations give relative dimension one. -/
private def linePolynomialPresentation :
    Algebra.SubmersivePresentation E (MvPolynomial (Fin 1) E) (Fin 1) Empty where
  toPreSubmersivePresentation := {
    toPresentation := {
      toGenerators := Algebra.Generators.mvPolynomial E (Fin 1)
      relation := Empty.elim
      span_range_relation_eq_ker := by simp [Algebra.Generators.ker_mvPolynomial] }
    map := Empty.elim
    map_inj := Function.injective_of_subsingleton _ }
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp

instance lineStructure_smooth : SmoothOfRelativeDimension 1 (lineStructure E) := by
  let : Algebra.IsStandardSmoothOfRelativeDimension 1 E (MvPolynomial (Fin 1) E) :=
    (linePolynomialPresentation E).isStandardSmoothOfRelativeDimension (by
      simp [Algebra.Presentation.dimension])
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).2
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).2 inferInstance

instance lineStructure_locallyFiniteType : LocallyOfFiniteType (lineStructure E) := by
  let : Smooth (lineStructure E) := SmoothOfRelativeDimension.smooth 1 (lineStructure E)
  infer_instance

def linePresentation : FieldPresentation E (StartingSourceMaps.affineLine E) where
  structureMorphism := lineStructure E
  locallyFiniteType := inferInstance
  quasiCompact := inferInstance
  separated := inferInstance

instance linePresentation_smooth :
    SmoothOfRelativeDimension 1 (linePresentation E).structureMorphism :=
  inferInstanceAs (SmoothOfRelativeDimension 1 (lineStructure E))

/-- The original Laurent embedding is the actual Away-X localization. -/
instance localInput_isOpenImmersion :
    IsOpenImmersion (ArithmeticSourceMaps.localInputMorphism E E) := by
  have h : (ArithmeticSourceMaps.localInputHom E E).toRingHom =
      Polynomial.toLaurent.comp (MvPolynomial.uniqueAlgEquiv E (Fin 1)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [ArithmeticSourceMaps.localInputHom]
    · intro i
      simp [ArithmeticSourceMaps.localInputHom, MvPolynomial.uniqueAlgEquiv,
        Polynomial.toLaurent_X]
      rfl
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (ArithmeticSourceMaps.localInputHom E E).toRingHom))
  rw [h, CommRingCat.ofHom_comp, Spec.map_comp]
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Polynomial.toLaurent : Polynomial E →+* LaurentPolynomial E))) := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (Polynomial E) (LaurentPolynomial E))))
    exact IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial E)
  have : IsIso (CommRingCat.ofHom
      (MvPolynomial.uniqueAlgEquiv E (Fin 1)).toRingHom) :=
    inferInstanceAs (IsIso
      (MvPolynomial.uniqueAlgEquiv E (Fin 1)).toRingEquiv.toCommRingCatIso.hom)
  infer_instance

instance localInput_quasiCompact :
    QuasiCompact (ArithmeticSourceMaps.localInputMorphism E E) := inferInstance

/-- The same-field Gm structure is inherited through this literal open map. -/
def gmPresentation : FieldPresentation E (ArithmeticSourceMaps.fiberScheme E) where
  structureMorphism := ArithmeticSourceMaps.localInputMorphism E E ≫ lineStructure E
  locallyFiniteType := inferInstance
  quasiCompact := inferInstance
  separated := inferInstance

variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C)
local instance allSchemeLocalizations : ∀ X : Scheme,
    HasDerivedCategory.{mu} (C X) := fun _ => HasDerivedCategory.standard _

variable (F : OrdinaryOpenExtensionsFromAdjunctions.OrdinaryOpenFamily C U)

/-- In an adjoint triple, the existing left unit iso implies the right counit iso. -/
def pushRestrictionIso (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    {X Y : Scheme} (PX : FieldPresentation K X) (PY : FieldPresentation K Y)
    (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    (baseSquare : j ≫ PY.structureMorphism = PX.structureMorphism) :
    F.push K h2 PX PY j baseSquare ⋙ U.pull j ≅ 𝟭 (C X) := by
  let t : Adjunction.Triple (F.bang K h2 PX PY j baseSquare) (U.pull j)
      (F.push K h2 PX PY j baseSquare) :=
    ⟨F.bangAdj K h2 PX PY j baseSquare, F.pushAdj K h2 PX PY j baseSquare⟩
  letI := F.bangUnitIsIso K h2 PX PY j baseSquare
  letI : IsIso (F.pushAdj K h2 PX PY j baseSquare).counit :=
    t.isIso_unit_iff_isIso_counit.mp (inferInstance)
  exact asIso (F.pushAdj K h2 PX PY j baseSquare).counit

variable (P : ∀ X : Scheme, ObjectProperty (DerivedCategory (C X)))
  (H0 : ∀ X : Scheme, DerivedCategory (C X) ⥤ (P X).FullSubcategory)
  (M : LocalRealization C)

/-- Precisely universal curve/generic MODEL scope; its domain is ALL bounded complexes. -/
abbrev GenericPerverseCohomologyComparison :=
  ∀ (K : Type) [Field K] (_h2 : (2 : K) ≠ 0)
    {X : Scheme} (PX : FieldPresentation K X)
    [SmoothOfRelativeDimension 1 PX.structureMorphism]
    (w : ArithmeticSourceMaps.fiberScheme K ⟶ X)
    [IsOpenImmersion w] [QuasiCompact w]
    (_over : w ≫ PX.structureMorphism = (gmPresentation K).structureMorphism),
    (QSTAdmissibilityFromBoundedDerived.boundedProperty (C X)).ι ⋙ H0 X ⋙
      (P X).ι ⋙ U.ordinary X (-1) ⋙ U.pull w ⋙ nearbyInfinity C M K ≅
    (QSTAdmissibilityFromBoundedDerived.boundedProperty (C X)).ι ⋙
      U.ordinary X (-1) ⋙ U.pull w ⋙ nearbyInfinity C M K

/-- The actual standard bounded single0 followed by [1]. -/
def boundedSingleShiftOne (X : Scheme) : C X ⥤ Bounded C X :=
  (QSTAdmissibilityFromBoundedDerived.boundedProperty (C X)).lift
    (U.degreeZero X ⋙ shiftFunctor (DerivedCategory (C X)) (1 : ℤ))
    (fun A => QSTAdmissibilityFromBoundedDerived.shift_bounded _ _
      (QSTAdmissibilityFromBoundedDerived.single_bounded _ 0 A) 1)

def singleShiftOneHomology (X : Scheme) :
    U.degreeZero X ⋙ shiftFunctor (DerivedCategory (C X)) (1 : ℤ) ⋙
      U.ordinary X (-1) ≅ 𝟭 (C X) :=
  Functor.isoWhiskerLeft _
    ((DerivedCategory.homologyFunctor (C X) 0).shiftIso (1 : ℤ) (-1) 0 (by decide)) ≪≫
    DerivedCategory.singleFunctorCompHomologyFunctorIso (C X) 0

def perverseShift : C (StartingSourceMaps.affineLine E) ⥤
    (P (StartingSourceMaps.affineLine E)).FullSubcategory :=
  U.degreeZero _ ⋙ shiftFunctor _ (1 : ℤ) ⋙ H0 _

def ordinaryInfinity : C (StartingSourceMaps.affineLine E) ⥤ FDRep ℂ (M.infinityGroup E) :=
  U.pull (ArithmeticSourceMaps.localInputMorphism E E) ⋙ nearbyInfinity C M E

def perverseInfinity : (P (StartingSourceMaps.affineLine E)).FullSubcategory ⥤
    FDRep ℂ (M.infinityGroup E) :=
  (P _).ι ⋙ U.ordinary _ (-1) ⋙ U.pull (ArithmeticSourceMaps.localInputMorphism E E) ⋙
    nearbyInfinity C M E

variable (genericComparison : GenericPerverseCohomologyComparison C U P H0 M)

def shiftInfinityIso (h2 : (2 : E) ≠ 0) :
    perverseShift E C U P H0 ⋙ perverseInfinity E C U P M ≅
      ordinaryInfinity E C U M := by
  exact Functor.isoWhiskerLeft (boundedSingleShiftOne C U (StartingSourceMaps.affineLine E))
    (genericComparison E h2 (linePresentation E)
      (ArithmeticSourceMaps.localInputMorphism E E) rfl) ≪≫
    Functor.isoWhiskerRight
      (singleShiftOneHomology C U (StartingSourceMaps.affineLine E))
      (U.pull (ArithmeticSourceMaps.localInputMorphism E E) ⋙ nearbyInfinity C M E) ≪≫
    Functor.leftUnitor _

/-- Compute every original middle data role and both full natural comparisons. -/
def actualMiddleInfinity (h2 : (2 : E) ≠ 0) :
    MiddleInfinityFromPerverse.Data
      (Q := (P (StartingSourceMaps.affineLine E)).FullSubcategory) (nearbyInfinity C M E) where
  Ambient := C (StartingSourceMaps.affineLine E)
  ambientCategory := inferInstance
  ambientAbelian := inferInstance
  extend := F.push E h2 (gmPresentation E) (linePresentation E)
    (ArithmeticSourceMaps.localInputMorphism E E) rfl
  perverseShift := perverseShift E C U P H0
  ordinaryInfinity := ordinaryInfinity E C U M
  perverseInfinity := perverseInfinity E C U P M
  extension := Functor.isoWhiskerRight
    (pushRestrictionIso C U F E h2 (gmPresentation E) (linePresentation E)
      (ArithmeticSourceMaps.localInputMorphism E E) rfl) (nearbyInfinity C M E) ≪≫
    Functor.leftUnitor _
  shift := shiftInfinityIso E C U P H0 M genericComparison h2

theorem actualMiddleInfinity_ambient (h2 : (2 : E) ≠ 0) :
    (actualMiddleInfinity E C U F P H0 M genericComparison h2).Ambient =
      C (StartingSourceMaps.affineLine E) := rfl

theorem actualMiddleInfinity_middle (h2 : (2 : E) ≠ 0) :
    (actualMiddleInfinity E C U F P H0 M genericComparison h2).middle =
      F.push E h2 (gmPresentation E) (linePresentation E)
        (ArithmeticSourceMaps.localInputMorphism E E) rfl ⋙
        U.degreeZero _ ⋙ shiftFunctor _ (1 : ℤ) ⋙ H0 _ := rfl

/-- The original whole middle/infinity comparison on these literal computed roles. -/
def actualMiddleInfinityIso (h2 : (2 : E) ≠ 0) :
    (actualMiddleInfinity E C U F P H0 M genericComparison h2).middle ⋙
      perverseInfinity E C U P M ≅ nearbyInfinity C M E :=
  (actualMiddleInfinity E C U F P H0 M genericComparison h2).infinityComparison

end PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology

-- Declaration reports consumed by the repository-wide axiom audit.
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.lineStructure
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.lineStructure_smooth
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.lineStructure_locallyFiniteType
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.linePresentation
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.linePresentation_smooth
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.localInput_isOpenImmersion
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.localInput_quasiCompact
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.gmPresentation
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.pushRestrictionIso
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.GenericPerverseCohomologyComparison
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.boundedSingleShiftOne
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.singleShiftOneHomology
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.perverseShift
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.ordinaryInfinity
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.perverseInfinity
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.shiftInfinityIso
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.actualMiddleInfinity
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.actualMiddleInfinity_ambient
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.actualMiddleInfinity_middle
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.actualMiddleInfinityIso
