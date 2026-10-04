import TypeIIIQSTRealizationFromExactInverseImages
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# QST's bounded domain from the standard derived category

The admissible objects are literally the bounded objects for Mathlib's
canonical ordinary t-structure. Single complexes, shifts and ordinary
cohomology satisfy that property. Exact ordinary inverse image preserves
the SAME bounds, using the already constructed derived-cohomology comparison.
No separately selected bounded-domain predicate or closure laws are inputs.

The intended ordinary constructible adic interpretation of B/extra categories,
perverse/six-functor/QST laws and their common realization remain explicit.
This does not assert QST on all unbounded complexes or construct Inputs.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical ZeroObject

namespace PrimeGap182.TypeIII.QSTAdmissibilityFromBoundedDerived

universe v w dh mu

section StandardBounded
variable (C : Type v) [Category.{w} C] [Abelian C] [HasDerivedCategory.{dh} C]

abbrev boundedProperty : ObjectProperty (DerivedCategory C) :=
  (DerivedCategory.TStructure.t (C := C)).bounded

theorem single_bounded (n : ℤ) (X : C) :
    boundedProperty C ((DerivedCategory.singleFunctor C n).obj X) :=
  ⟨⟨n, inferInstance⟩, ⟨n, inferInstance⟩⟩

instance : (boundedProperty C).ContainsZero where
  exists_zero := ⟨(DerivedCategory.singleFunctor C 0).obj 0,
    (DerivedCategory.singleFunctor C 0).map_isZero (isZero_zero C), single_bounded C 0 0⟩

theorem shift_bounded (X : DerivedCategory C) (hX : boundedProperty C X) (n : ℤ) :
    boundedProperty C ((shiftFunctor (DerivedCategory C) n).obj X) :=
  (boundedProperty C).le_shift n X hX

variable {C} {C' : Type v} [Category.{w} C'] [Abelian C'] [HasDerivedCategory.{dh} C']
  (F : C ⥤ C') [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Exact ordinary inverse image preserves each ordinary cohomological
bound; the comparison is constructed on the same functor, for all degrees. -/
theorem exactFunctor_bounded (X : DerivedCategory C) (hX : boundedProperty C X) :
    boundedProperty C' (F.mapDerivedCategory.obj X) := by
  rcases hX with ⟨⟨lo, hlo⟩, ⟨hi, hhi⟩⟩
  refine ⟨⟨lo, (DerivedCategory.isGE_iff _ _).2 ?_⟩,
    ⟨hi, (DerivedCategory.isLE_iff _ _).2 ?_⟩⟩
  · intro n hn
    exact (F.map_isZero ((DerivedCategory.isGE_iff X lo).1 hlo n hn)).of_iso
      ((OriginRealizationFromExactInverseImages.exactDerivedCohomology F n).app X)
  · intro n hn
    exact (F.map_isZero ((DerivedCategory.isLE_iff X hi).1 hhi n hn)).of_iso
      ((OriginRealizationFromExactInverseImages.exactDerivedCohomology F n).app X)

end StandardBounded

section QSTDomain
open ExactInverseImagesToDerived QSTRealizationFromExactInverseImages

variable {K : Type} [Field K] (B : SourceInverseImageSystem.System.{0,mu} K)
  {J : Type} (extraScheme : J → Scheme) (extraObj : J → Type)
  [∀ j, Category.{mu} (extraObj j)] [∀ j, Abelian (extraObj j)]
  (plane : J) (hPlane : extraScheme plane = UniformComplexityFromCommonRealization.affinePlane K)
  (A : OrdinarySystem (extensionScheme extraScheme) (extensionObjects B extraObj))

local instance qstLocalizations :
    ∀ i, HasDerivedCategory.{mu} (qstObjects B extraObj plane i) :=
  fun _ => HasDerivedCategory.standard _

/-- All eight original QST-domain fields are supplied by the canonical
bounded t-structure and the SAME exact ordinary inverse images. -/
def admissibility : Admissibility.{0,mu} B extraScheme extraObj plane hPlane A where
  property i := boundedProperty (qstObjects B extraObj plane i)
  containsZero _i := inferInstance
  closedIso _i := inferInstance
  degreeZero _i X := single_bounded _ 0 X
  shift _i X hX n := shift_bounded _ X hX n
  ordinary _i X _hX n := single_bounded _ 0 ((DerivedCategory.homologyFunctor _ n).obj X)
  pull i j f X hX := exactFunctor_bounded
    ((qstSystem B extraScheme extraObj plane hPlane A).pull (i := i) (j := j) f) X hX

theorem admissibility_property (i : UniformComplexityFromCommonRealization.Space)
    (X : NativeDerived B extraObj plane i) :
    (admissibility B extraScheme extraObj plane hPlane A).property i X ↔
      (DerivedCategory.TStructure.t (C := qstObjects B extraObj plane i)).bounded X := Iff.rfl

end QSTDomain
end PrimeGap182.TypeIII.QSTAdmissibilityFromBoundedDerived

#print axioms PrimeGap182.TypeIII.QSTAdmissibilityFromBoundedDerived.single_bounded
#print axioms PrimeGap182.TypeIII.QSTAdmissibilityFromBoundedDerived.shift_bounded
#print axioms PrimeGap182.TypeIII.QSTAdmissibilityFromBoundedDerived.exactFunctor_bounded
#print axioms PrimeGap182.TypeIII.QSTAdmissibilityFromBoundedDerived.admissibility
#print axioms PrimeGap182.TypeIII.QSTAdmissibilityFromBoundedDerived.admissibility_property
