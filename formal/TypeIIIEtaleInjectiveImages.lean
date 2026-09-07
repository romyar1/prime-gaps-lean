import TypeIIIEtaleInverseImageStalk
import TypeIIIEtaleExtensionExact
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Injective objects under actual étale direct image and open restriction

The proved exact inverse-image functor is left adjoint to the original
direct-image functor. Consequently, direct image preserves injectives.
For a monomorphic étale object, the proved exact extension by zero is
left adjoint to the original restriction, so that restriction also
preserves injectives. These conclusions use the actual adjunctions;
injectivity preservation for arbitrary inverse image is not asserted.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory AlgebraicGeometry

namespace EtaleDirectImage

/-- The actual direct-image functor preserves injective module sheaves,
because its actual left adjoint preserves monomorphisms. -/
instance functor_preservesInjectiveObjects {X S : Scheme.{u}} (q : X ⟶ S)
    (E : Type u) [Ring E] : (functor q E).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (EtaleInverseImage.adjunction q E)

end EtaleDirectImage

namespace EtaleExtensionByZero

/-- Restriction to the actual open object preserves injectives, by
the established exactness of its actual extension-by-zero left adjoint. -/
instance restriction_preservesInjectiveObjects (S : Scheme.{u}) (U : S.Etale)
    [Mono U.hom] (E : Type u) [Ring E] :
    (restriction S U E).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (adjunction S U E)

end EtaleExtensionByZero

#print axioms EtaleDirectImage.functor_preservesInjectiveObjects
#print axioms EtaleExtensionByZero.restriction_preservesInjectiveObjects

end PrimeGap182.TypeIII
