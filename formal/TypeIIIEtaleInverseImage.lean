import TypeIIIEtaleDirectImage
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Actual inverse image on the small étale site

For any scheme morphism q : X → S, the existing actual direct image
preserves all limits of the coefficient universe. The small étale
module-sheaf categories are Grothendieck abelian, so the special adjoint
functor theorem supplies its left adjoint. This constructs inverse image
on the original sites, with its actual adjunction to the original q_*.

No adjoint, continuity, smallness, or geometric exactness premise is
supplied. Finite-limit preservation of this inverse image is proved
from actual geometric stalks in TypeIIIEtaleInverseImageStalk.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleInverseImage

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable {X S : Scheme.{u}} (q : X ⟶ S) (E : Type u) [Ring E]

/-- Actual direct image preserves all limits of the coefficient universe,
because its underlying presheaf functor is precomposition. -/
instance directImage_preservesLimits :
    PreservesLimitsOfSize.{u, u} (EtaleDirectImage.functor q E) where
  preservesLimitsOfShape {J} _ := by
    let : PreservesLimitsOfShape J
        (EtaleDirectImage.functor q E ⋙
          sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} E)) :=
      preservesLimitsOfShape_of_natIso
        (EtaleDirectImage.functorCompSheafToPresheafIso q E).symm
    exact preservesLimitsOfShape_of_reflects_of_preserves
      (EtaleDirectImage.functor q E)
      (sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} E))

/-- The actual right-adjoint property follows from completeness,
well-poweredness, and the proved coseparator of the Grothendieck category. -/
instance directImage_isRightAdjoint : (EtaleDirectImage.functor q E).IsRightAdjoint := by
  let : IsGrothendieckAbelian.{u}
      (Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) := inferInstance
  let : IsGrothendieckAbelian.{u}
      (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) := inferInstance
  exact isRightAdjoint_of_preservesLimits_of_isCoseparating.{u}
    (isCoseparator_coseparator _) _

/-- The same proved right-adjoint property for the literal site pushforward. -/
instance baseChangePushforward_isRightAdjoint :
    ((EtaleDirectImage.baseChange q).sheafPushforwardContinuous (ModuleCat.{u} E)
      S.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint :=
  directImage_isRightAdjoint q E

/-- The actual inverse image q^* on module sheaves. -/
def functor :
    Sheaf S.smallEtaleTopology (ModuleCat.{u} E) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u} E) :=
  (EtaleDirectImage.functor q E).leftAdjoint

/-- The constructed inverse image is left adjoint to the existing actual q_*. -/
def adjunction : functor q E ⊣ EtaleDirectImage.functor q E :=
  Adjunction.ofIsRightAdjoint _

/-- This inverse image is the actual site pullback for the base-change functor. -/
theorem functor_eq_sheafPullback :
    functor q E = (EtaleDirectImage.baseChange q).sheafPullback (ModuleCat.{u} E)
      S.smallEtaleTopology X.smallEtaleTopology := rfl

/-- The left-adjoint structure comes from the constructed adjunction. -/
instance functor_isLeftAdjoint : (functor q E).IsLeftAdjoint :=
  (adjunction q E).isLeftAdjoint

/-- Inverse image preserves all colimits of the coefficient universe. -/
instance functor_preservesColimits : PreservesColimitsOfSize.{u, u} (functor q E) :=
  (adjunction q E).leftAdjoint_preservesColimits

/-- In particular, the actual inverse image preserves finite colimits. -/
instance functor_preservesFiniteColimits : PreservesFiniteColimits (functor q E) := by
  let : PreservesColimitsOfSize.{0, 0} (functor q E) :=
    (adjunction q E).leftAdjoint_preservesColimits
  infer_instance

end PrimeGap182.TypeIII.EtaleInverseImage

#print axioms PrimeGap182.TypeIII.EtaleInverseImage.directImage_preservesLimits
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.directImage_isRightAdjoint
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.baseChangePushforward_isRightAdjoint
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.functor
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.adjunction
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.functor_eq_sheafPullback
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.functor_isLeftAdjoint
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.functor_preservesColimits
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.functor_preservesFiniteColimits
