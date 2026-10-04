import TypeIIIQSTCompactBridgeFromCompactifiedDerivedPushforward
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
The compact realization uses the SAME standard bounded derived category,
ordinary single in degree zero, and compactification-defined derived bang.
All fields have carrier and hom universe mu. The ordinary compact-H1 law
is definitional, before choosing a prime or any Fourier source object.
No ordinary direct-image exactness or selected comparison is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

namespace PrimeGap182.TypeIII.BoundedCompactRealizationFromSameOperations
open QSTCompactBridgeFromCompactifiedDerivedPushforward

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)]
  [∀ X, Abelian (C X)]

local instance allSchemeLocalizations : ∀ X : Scheme,
    HasDerivedCategory.{mu} (C X) := fun _ => HasDerivedCategory.standard _

/-- The literal standard bounded category, with carrier universe mu. -/
abbrev CohomologyDerived (X : Scheme.{0}) : Type mu := Bounded C X

/-- The intrinsic hom-universe-mu category structure. -/
abbrev cohomologyDerivedCategory (X : Scheme.{0}) :
    Category.{mu} (CohomologyDerived C X) := inferInstance

/-- SAME existing ordinary degree-zero inclusion, without replacing the functor. -/
def ordinaryKernelRealization (X : Scheme.{0}) : C X ⥤ CohomologyDerived C X :=
  boundedDegreeZero C X

instance ordinaryKernelRealization_full (X : Scheme.{0}) :
    (ordinaryKernelRealization C X).Full := by
  unfold ordinaryKernelRealization boundedDegreeZero
  infer_instance

instance ordinaryKernelRealization_faithful (X : Scheme.{0}) :
    (ordinaryKernelRealization C X).Faithful := by
  unfold ordinaryKernelRealization boundedDegreeZero
  infer_instance

/-- Actual inverse on maps, from full faithfulness of ordinary single. -/
def ordinaryKernelRealizationFullyFaithful (X : Scheme.{0}) :
    (ordinaryKernelRealization C X).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

variable (O : Operations C) {X Y : Scheme.{0}} {f : X ⟶ Y}
  (c : Compactification f)

/-- SAME compactification bang followed by actual ordinary H1. -/
def genericCompactFirst : CohomologyDerived C X ⥤ C Y :=
  derivedBang C O c ⋙ cohomology C Y (1 : ℤ)

/-- This is the literal defining compact functor in cohomologyData. -/
def ordinaryCompactFirst :
    ordinaryKernelRealization C X ⋙ genericCompactFirst C O c ≅
      (cohomologyData C O c (1 : ℤ)).compact := Iso.refl _

end PrimeGap182.TypeIII.BoundedCompactRealizationFromSameOperations

-- Declaration reports consumed by the repository-wide axiom audit.
#print axioms PrimeGap182.TypeIII.BoundedCompactRealizationFromSameOperations.CohomologyDerived
#print axioms PrimeGap182.TypeIII.BoundedCompactRealizationFromSameOperations.cohomologyDerivedCategory
#print axioms PrimeGap182.TypeIII.BoundedCompactRealizationFromSameOperations.ordinaryKernelRealization
#print axioms PrimeGap182.TypeIII.BoundedCompactRealizationFromSameOperations.ordinaryKernelRealization_full
#print axioms PrimeGap182.TypeIII.BoundedCompactRealizationFromSameOperations.ordinaryKernelRealization_faithful
#print axioms PrimeGap182.TypeIII.BoundedCompactRealizationFromSameOperations.ordinaryKernelRealizationFullyFaithful
#print axioms PrimeGap182.TypeIII.BoundedCompactRealizationFromSameOperations.genericCompactFirst
#print axioms PrimeGap182.TypeIII.BoundedCompactRealizationFromSameOperations.ordinaryCompactFirst
