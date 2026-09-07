import TypeIIIEtaleTowerDirectImage
import TypeIIIEtaleInjectiveImages
import TypeIIIRightDerivedPlusComposition

/-!
# Derived inverse limit and the original étale direct image

For the actual category of inverse systems of étale module sheaves, the
original inverse-limit functor and the original pointwise direct-image
functor both preserve injectives.  Their proved ordinary comparison thus
gives a comparison of their original bounded below right derived functors:

`Rq_* (Rlim T) ≅ Rlim (RQ T)`.

Here `RQ T` is a full derived object in the category of towers.  It is not
a tower obtained by selecting one cohomological degree.  The normalization
below retains the original limit-preservation map and both original pasted
derived units.  No proper base change, exactness of inverse limits, or
identification with adic cohomology is assumed.
-/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII.EtaleDerivedLimitDirectImage

open CategoryTheory CategoryTheory.Category AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (q : X ⟶ S) (E : Type u) [Ring E]

/-- The original total derived direct image commutes with the original total
derived limit when the direct image on towers is itself derived. -/
def iso :
    EtaleSheafTower.derivedPlus X E ⋙ (EtaleDirectImage.functor q E).rightDerivedFunctorPlus ≅
      (EtaleTowerDirectImage.functor q E).rightDerivedFunctorPlus ⋙
        EtaleSheafTower.derivedPlus S E :=
  (rightDerivedFunctorPlusCompIso (EtaleSheafTower.limitFunctor X E)
      (EtaleDirectImage.functor q E)).symm ≪≫
    rightDerivedFunctorPlusIso (EtaleTowerDirectImage.limitIso q E) ≪≫
    rightDerivedFunctorPlusCompIso (EtaleTowerDirectImage.functor q E)
      (EtaleSheafTower.limitFunctor S E)

/-- The derived interchange has the original ordinary limit comparison as its
normalization with respect to the original derived units. -/
theorem iso_hom_fac :
    rightDerivedFunctorPlusCompUnit (EtaleSheafTower.limitFunctor X E)
        (EtaleDirectImage.functor q E) ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh (iso q E).hom =
    Functor.whiskerRight (mapHomotopyCategoryPlusIso
        (EtaleTowerDirectImage.limitIso q E)).hom DerivedCategory.Plus.Qh ≫
      rightDerivedFunctorPlusCompUnit (EtaleTowerDirectImage.functor q E)
        (EtaleSheafTower.limitFunctor S E) := by
  let a := rightDerivedFunctorPlusCompIso (EtaleSheafTower.limitFunctor X E)
    (EtaleDirectImage.functor q E)
  let b := rightDerivedFunctorPlusIso (EtaleTowerDirectImage.limitIso q E)
  let c := rightDerivedFunctorPlusCompIso (EtaleTowerDirectImage.functor q E)
    (EtaleSheafTower.limitFunctor S E)
  have hcomp : a.hom ≫ (iso q E).hom = b.hom ≫ c.hom := by
    simp [iso, a, b, c]
  rw [← rightDerivedFunctorPlusCompIso_hom_fac, assoc,
    ← Functor.whiskerLeft_comp, hcomp, Functor.whiskerLeft_comp, ← assoc,
    rightDerivedFunctorPlusIso_hom_fac, assoc,
    rightDerivedFunctorPlusCompIso_hom_fac]

/-- The same normalization at an actual bounded below complex keeps all three
original comparison maps and the actual localization functor. -/
theorem iso_hom_fac_app (K : HomotopyCategory.Plus (EtaleSheafTower.Tower X E)) :
    (rightDerivedFunctorPlusCompUnit (EtaleSheafTower.limitFunctor X E)
        (EtaleDirectImage.functor q E)).app K ≫
      (iso q E).hom.app (DerivedCategory.Plus.Qh.obj K) =
    DerivedCategory.Plus.Qh.map
        ((mapHomotopyCategoryPlusIso (EtaleTowerDirectImage.limitIso q E)).hom.app K) ≫
      (rightDerivedFunctorPlusCompUnit (EtaleTowerDirectImage.functor q E)
        (EtaleSheafTower.limitFunctor S E)).app K := by
  exact congrArg (fun a => a.app K) (iso_hom_fac q E)

end PrimeGap182.TypeIII.EtaleDerivedLimitDirectImage

#print axioms PrimeGap182.TypeIII.EtaleDerivedLimitDirectImage.iso
#print axioms PrimeGap182.TypeIII.EtaleDerivedLimitDirectImage.iso_hom_fac
#print axioms PrimeGap182.TypeIII.EtaleDerivedLimitDirectImage.iso_hom_fac_app
