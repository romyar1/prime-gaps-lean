import TypeIIIKloostermanExtendedTower
import TypeIIIEtaleDerivedLimitDirectImage

/-!
# The full derived limit image of the original extended phase tower

The original extended coefficient tower is placed in degree zero in its
actual derived tower category. Its derived inverse limit is then sent
through the original full derived direct image of the proper projection.
The proved derived-limit/direct-image comparison identifies this object
with the derived inverse limit of the full derived tower direct image.

An explicit presentation uses the original chosen injective resolution
of the extended tower, mapped by the ordinary limit followed by the
ordinary direct image. Its comparison is normalized by the original
augmentation and the original pasted derived units. No injective
preservation for extension by zero is used: the sheaves were extended
before their tower was resolved.

The independently defined finite-coefficient extended tower gives the
same full derived object via its already proved actual tower isomorphism.
No cohomological degree is selected before taking the derived limit, and
no adic-cohomology identification, finiteness, concentration, proper base
change, or trace formula is asserted.
-/

noncomputable section

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category AlgebraicGeometry

section ResolutionComposition

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C]
  [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [EnoughInjectives D]
  [HasDerivedCategory.{w₂} D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasDerivedCategory.{w₃} E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  [F.PreservesInjectiveObjects]

/-- The original resolution augmentation normalizes the original derived composition comparison. -/
theorem rightDerivedPlusResolutionCompIso_augmentation {A : C} (I : InjectiveResolution A) :
    DerivedCategory.Plus.Q.map
        ((F ⋙ G).mapCochainComplexPlus.map (injectiveResolutionPlusAugmentation I)) ≫
      (rightDerivedPlusResolutionIso (F ⋙ G) I ≪≫
        (rightDerivedFunctorPlusCompIso F G).app
          ((DerivedCategory.Plus.singleFunctor C 0).obj A)).hom =
      (rightDerivedFunctorPlusCompUnit F G).app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj A) := by
  change _ ≫ ((rightDerivedPlusResolutionIso (F ⋙ G) I).hom ≫
    (rightDerivedFunctorPlusCompIso F G).hom.app
      ((DerivedCategory.Plus.singleFunctor C 0).obj A)) = _
  rw [← assoc, rightDerivedPlusResolutionIso_augmentation]
  exact congrArg (fun a => a.app ((HomotopyCategory.Plus.singleFunctor C 0).obj A))
    (rightDerivedFunctorPlusCompIso_hom_fac F G)

end ResolutionComposition

attribute [local instance] HasDerivedCategory.standard

variable (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell)

/-- The original extended tower, placed in degree zero in its actual derived category. -/
def kloostermanExtendedTowerSingle :
    DerivedCategory.Plus
      (EtaleSheafTower.Tower (kloostermanCompactificationScheme p)
        (TorsionCoefficientLimit p ell)) :=
  (DerivedCategory.Plus.singleFunctor
    (EtaleSheafTower.Tower (kloostermanCompactificationScheme p)
      (TorsionCoefficientLimit p ell)) 0).obj
        (kloostermanTorsionExtendedTower p ell hne)

/-- The full derived direct image of the actual derived inverse limit of the extended tower. -/
def kloostermanDerivedLimitImage :
    DerivedCategory.Plus
      (Sheaf (Spec (.of (Polynomial (ZMod p)))).smallEtaleTopology
        (ModuleCat.{0} (TorsionCoefficientLimit p ell))) :=
  (EtaleDirectImage.functor (kloostermanCompactificationProjection p)
      (TorsionCoefficientLimit p ell)).rightDerivedFunctorPlus.obj
    ((EtaleSheafTower.derivedPlus (kloostermanCompactificationScheme p)
      (TorsionCoefficientLimit p ell)).obj (kloostermanExtendedTowerSingle p ell hne))

/-- The comparison target derives the tower direct image before taking the full derived limit. -/
def kloostermanDerivedTowerLimit :
    DerivedCategory.Plus
      (Sheaf (Spec (.of (Polynomial (ZMod p)))).smallEtaleTopology
        (ModuleCat.{0} (TorsionCoefficientLimit p ell))) :=
  (EtaleSheafTower.derivedPlus (Spec (.of (Polynomial (ZMod p))))
      (TorsionCoefficientLimit p ell)).obj
    ((EtaleTowerDirectImage.functor (kloostermanCompactificationProjection p)
      (TorsionCoefficientLimit p ell)).rightDerivedFunctorPlus.obj
        (kloostermanExtendedTowerSingle p ell hne))

/-- The full derived objects are compared by the original derived interchange isomorphism. -/
def kloostermanDerivedLimitImageIso :
    kloostermanDerivedLimitImage p ell hne ≅ kloostermanDerivedTowerLimit p ell hne :=
  (EtaleDerivedLimitDirectImage.iso (kloostermanCompactificationProjection p)
    (TorsionCoefficientLimit p ell)).app (kloostermanExtendedTowerSingle p ell hne)

/-- The forward map is the same original comparison at the original degree-zero tower. -/
theorem kloostermanDerivedLimitImageIso_hom :
    (kloostermanDerivedLimitImageIso p ell hne).hom =
      (EtaleDerivedLimitDirectImage.iso (kloostermanCompactificationProjection p)
        (TorsionCoefficientLimit p ell)).hom.app (kloostermanExtendedTowerSingle p ell hne) := rfl

/-- The actual chosen resolution belongs to the category of already extended towers. -/
def kloostermanExtendedTowerInjectiveResolution :
    InjectiveResolution (kloostermanTorsionExtendedTower p ell hne) :=
  EtaleSheafTower.resolution (kloostermanCompactificationScheme p)
    (TorsionCoefficientLimit p ell) (kloostermanTorsionExtendedTower p ell hne)

/-- Apply the original ordinary limit and direct image to that entire resolution. -/
def kloostermanDerivedLimitResolutionComplex :
    CochainComplex.Plus
      (Sheaf (Spec (.of (Polynomial (ZMod p)))).smallEtaleTopology
        (ModuleCat.{0} (TorsionCoefficientLimit p ell))) :=
  (EtaleSheafTower.limitFunctor (kloostermanCompactificationScheme p)
      (TorsionCoefficientLimit p ell) ⋙
    EtaleDirectImage.functor (kloostermanCompactificationProjection p)
      (TorsionCoefficientLimit p ell)).mapCochainComplexPlus.obj
        (injectiveResolutionCochainPlus (kloostermanExtendedTowerInjectiveResolution p ell hne))

/-- The original resolution comparison followed by the original composition isomorphism. -/
def kloostermanDerivedLimitResolutionIso :
    DerivedCategory.Plus.Q.obj (kloostermanDerivedLimitResolutionComplex p ell hne) ≅
      kloostermanDerivedLimitImage p ell hne :=
  rightDerivedPlusResolutionIso
      (EtaleSheafTower.limitFunctor (kloostermanCompactificationScheme p)
          (TorsionCoefficientLimit p ell) ⋙
        EtaleDirectImage.functor (kloostermanCompactificationProjection p)
          (TorsionCoefficientLimit p ell))
      (kloostermanExtendedTowerInjectiveResolution p ell hne) ≪≫
    (rightDerivedFunctorPlusCompIso
      (EtaleSheafTower.limitFunctor (kloostermanCompactificationScheme p)
        (TorsionCoefficientLimit p ell))
      (EtaleDirectImage.functor (kloostermanCompactificationProjection p)
        (TorsionCoefficientLimit p ell))).app (kloostermanExtendedTowerSingle p ell hne)

/-- The explicit presentation retains both original comparison maps. -/
theorem kloostermanDerivedLimitResolutionIso_hom_original :
    (kloostermanDerivedLimitResolutionIso p ell hne).hom =
      (rightDerivedPlusResolutionIso
        (EtaleSheafTower.limitFunctor (kloostermanCompactificationScheme p)
            (TorsionCoefficientLimit p ell) ⋙
          EtaleDirectImage.functor (kloostermanCompactificationProjection p)
            (TorsionCoefficientLimit p ell))
        (kloostermanExtendedTowerInjectiveResolution p ell hne)).hom ≫
      (rightDerivedFunctorPlusCompIso
        (EtaleSheafTower.limitFunctor (kloostermanCompactificationScheme p)
          (TorsionCoefficientLimit p ell))
        (EtaleDirectImage.functor (kloostermanCompactificationProjection p)
          (TorsionCoefficientLimit p ell))).hom.app
            (kloostermanExtendedTowerSingle p ell hne) := rfl

/-- The original augmentation maps to the original pasted derived unit.
The inferred statement uses the two original factors of the preceding
`kloostermanDerivedLimitResolutionIso_hom_original` identity. -/
abbrev kloostermanDerivedLimitResolutionIso_augmentation :=
  rightDerivedPlusResolutionCompIso_augmentation
    (EtaleSheafTower.limitFunctor (kloostermanCompactificationScheme p)
      (TorsionCoefficientLimit p ell))
    (EtaleDirectImage.functor (kloostermanCompactificationProjection p)
      (TorsionCoefficientLimit p ell))
    (kloostermanExtendedTowerInjectiveResolution p ell hne)

/-- The actual finite-category tower comparison is placed in degree zero without changing its maps. -/
def kloostermanFiniteCoefficientExtendedTowerSingleIso :
    (DerivedCategory.Plus.singleFunctor
      (EtaleSheafTower.Tower (kloostermanCompactificationScheme p)
        (TorsionCoefficientLimit p ell)) 0).obj
          (kloostermanFiniteCoefficientExtendedTower p ell hne) ≅
      kloostermanExtendedTowerSingle p ell hne :=
  (DerivedCategory.Plus.singleFunctor
    (EtaleSheafTower.Tower (kloostermanCompactificationScheme p)
      (TorsionCoefficientLimit p ell)) 0).mapIso
        (kloostermanFiniteCoefficientExtendedTowerIso p ell hne)

/-- The same full derived construction starting from the independently extended finite-category tower. -/
def kloostermanFiniteCoefficientDerivedLimitImage :
    DerivedCategory.Plus
      (Sheaf (Spec (.of (Polynomial (ZMod p)))).smallEtaleTopology
        (ModuleCat.{0} (TorsionCoefficientLimit p ell))) :=
  (EtaleSheafTower.derivedPlus (kloostermanCompactificationScheme p)
      (TorsionCoefficientLimit p ell) ⋙
    (EtaleDirectImage.functor (kloostermanCompactificationProjection p)
      (TorsionCoefficientLimit p ell)).rightDerivedFunctorPlus).obj
        ((DerivedCategory.Plus.singleFunctor
          (EtaleSheafTower.Tower (kloostermanCompactificationScheme p)
            (TorsionCoefficientLimit p ell)) 0).obj
              (kloostermanFiniteCoefficientExtendedTower p ell hne))

/-- Mapping the already proved actual tower isomorphism identifies the two full derived images. -/
def kloostermanFiniteCoefficientDerivedLimitToOriginalIso :
    kloostermanFiniteCoefficientDerivedLimitImage p ell hne ≅
      kloostermanDerivedLimitImage p ell hne :=
  (EtaleSheafTower.derivedPlus (kloostermanCompactificationScheme p)
      (TorsionCoefficientLimit p ell) ⋙
    (EtaleDirectImage.functor (kloostermanCompactificationProjection p)
      (TorsionCoefficientLimit p ell)).rightDerivedFunctorPlus).mapIso
        (kloostermanFiniteCoefficientExtendedTowerSingleIso p ell hne)

/-- The forward map is the full derived composite applied to the original tower comparison. -/
theorem kloostermanFiniteCoefficientDerivedLimitToOriginalIso_hom :
    (kloostermanFiniteCoefficientDerivedLimitToOriginalIso p ell hne).hom =
      (EtaleSheafTower.derivedPlus (kloostermanCompactificationScheme p)
          (TorsionCoefficientLimit p ell) ⋙
        (EtaleDirectImage.functor (kloostermanCompactificationProjection p)
          (TorsionCoefficientLimit p ell)).rightDerivedFunctorPlus).map
            ((DerivedCategory.Plus.singleFunctor
              (EtaleSheafTower.Tower (kloostermanCompactificationScheme p)
                (TorsionCoefficientLimit p ell)) 0).map
                  (kloostermanFiniteCoefficientExtendedTowerIso p ell hne).hom) := rfl

/-- The finite-category comparison commutes with the same full derived interchange map. -/
theorem kloostermanFiniteCoefficientDerivedLimitToOriginalIso_interchange :
    (kloostermanFiniteCoefficientDerivedLimitToOriginalIso p ell hne).hom ≫
        (kloostermanDerivedLimitImageIso p ell hne).hom =
      (EtaleDerivedLimitDirectImage.iso (kloostermanCompactificationProjection p)
        (TorsionCoefficientLimit p ell)).hom.app
          ((DerivedCategory.Plus.singleFunctor
            (EtaleSheafTower.Tower (kloostermanCompactificationScheme p)
              (TorsionCoefficientLimit p ell)) 0).obj
                (kloostermanFiniteCoefficientExtendedTower p ell hne)) ≫
      ((EtaleTowerDirectImage.functor (kloostermanCompactificationProjection p)
          (TorsionCoefficientLimit p ell)).rightDerivedFunctorPlus ⋙
        EtaleSheafTower.derivedPlus (Spec (.of (Polynomial (ZMod p))))
          (TorsionCoefficientLimit p ell)).map
            (kloostermanFiniteCoefficientExtendedTowerSingleIso p ell hne).hom :=
  (EtaleDerivedLimitDirectImage.iso (kloostermanCompactificationProjection p)
    (TorsionCoefficientLimit p ell)).hom.naturality
      (kloostermanFiniteCoefficientExtendedTowerSingleIso p ell hne).hom

#print axioms rightDerivedPlusResolutionCompIso_augmentation
#print axioms kloostermanExtendedTowerSingle
#print axioms kloostermanDerivedLimitImage
#print axioms kloostermanDerivedTowerLimit
#print axioms kloostermanDerivedLimitImageIso
#print axioms kloostermanDerivedLimitImageIso_hom
#print axioms kloostermanExtendedTowerInjectiveResolution
#print axioms kloostermanDerivedLimitResolutionComplex
#print axioms kloostermanDerivedLimitResolutionIso
#print axioms kloostermanDerivedLimitResolutionIso_hom_original
#print axioms kloostermanDerivedLimitResolutionIso_augmentation
#print axioms kloostermanFiniteCoefficientExtendedTowerSingleIso
#print axioms kloostermanFiniteCoefficientDerivedLimitImage
#print axioms kloostermanFiniteCoefficientDerivedLimitToOriginalIso
#print axioms kloostermanFiniteCoefficientDerivedLimitToOriginalIso_hom
#print axioms kloostermanFiniteCoefficientDerivedLimitToOriginalIso_interchange

end PrimeGap182.TypeIII
