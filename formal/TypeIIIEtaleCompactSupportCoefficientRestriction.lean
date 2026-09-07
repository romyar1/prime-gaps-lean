import TypeIIIEtaleCoefficientDerivedDirectImage
import TypeIIIEtaleExtensionCoefficientRestriction

/-!
# Coefficient restriction for the original extended derived direct image

For an étale object U over X and q : X → S, combine the proved
coefficient comparison for the original extension with the proved
comparison for the original derived direct image.  The resulting
natural isomorphism concerns the literal composite Rⁿq_* j_! in the
original module-sheaf categories.

Its component formula retains both original maps.  In degree zero,
the full composite comparison commutes with the original resolution
augmentations and the ordinary comparison.  No properness or
monomorphy premise is needed for this coefficient comparison; when
U is the open of a proper model, it applies to that specific relative
compact-support construction.
-/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII.EtaleCompactSupportCoefficientRestriction

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry

variable {X S : Scheme.{u}} (q : X ⟶ S) (U : X.Etale)
  {E E' : Type u} [Ring E] [Ring E'] (r : E →+* E')

/-- The actual coefficient comparison for the original extended
derived direct image, with all associators specified. -/
def iso (n : ℕ) :
    (EtaleExtensionByZero.functor X U E' ⋙ EtaleDerivedDirectImage.functor q E' n) ⋙
        EtaleCoefficientRestriction.functor S r ≅
      EtaleCoefficientRestriction.functor U.left r ⋙
        (EtaleExtensionByZero.functor X U E ⋙ EtaleDerivedDirectImage.functor q E n) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (EtaleExtensionByZero.functor X U E')
      (EtaleCoefficientRestriction.derivedDirectImageIso q r n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (EtaleExtensionCoefficientRestriction.iso X U r)
      (EtaleDerivedDirectImage.functor q E n) ≪≫
    Functor.associator _ _ _

/-- On every original coefficient sheaf, first use the original
derived coefficient map on j_!F, then the higher direct image of the
original extension coefficient comparison. -/
theorem iso_hom_app (n : ℕ)
    (F : Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E')) :
    (iso q U r n).hom.app F =
      (EtaleCoefficientRestriction.derivedDirectImageMap q r n).app
          ((EtaleExtensionByZero.functor X U E').obj F) ≫
        (EtaleDerivedDirectImage.functor q E n).map
          ((EtaleExtensionCoefficientRestriction.iso X U r).hom.app F) := by
  simp [iso, EtaleCoefficientRestriction.derivedDirectImageIso_hom]

/-- The corresponding ordinary comparison uses the literal coefficient
square for q_* and the same original extension comparison. -/
def ordinaryIso :
    (EtaleExtensionByZero.functor X U E' ⋙ EtaleDirectImage.functor q E') ⋙
        EtaleCoefficientRestriction.functor S r ≅
      EtaleCoefficientRestriction.functor U.left r ⋙
        (EtaleExtensionByZero.functor X U E ⋙ EtaleDirectImage.functor q E) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (EtaleExtensionByZero.functor X U E')
      (EtaleCoefficientRestriction.directImageIso q r) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (EtaleExtensionCoefficientRestriction.iso X U r)
      (EtaleDirectImage.functor q E) ≪≫
    Functor.associator _ _ _

/-- The ordinary component retains the two original maps. -/
theorem ordinaryIso_hom_app
    (F : Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E')) :
    (ordinaryIso q U r).hom.app F =
      (EtaleCoefficientRestriction.directImageIso q r).hom.app
          ((EtaleExtensionByZero.functor X U E').obj F) ≫
        (EtaleDirectImage.functor q E).map
          ((EtaleExtensionCoefficientRestriction.iso X U r).hom.app F) := by
  simp [ordinaryIso]

/-- On every original coefficient sheaf, the full degree-zero
comparison intertwines the original augmentation maps. -/
theorem iso_zero_app
    (F : Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E')) :
    (EtaleCoefficientRestriction.functor S r).map
          ((EtaleDirectImage.functor q E').toRightDerivedZero.app
            ((EtaleExtensionByZero.functor X U E').obj F)) ≫
        (iso q U r 0).hom.app F =
      (ordinaryIso q U r).hom.app F ≫
        (EtaleDirectImage.functor q E).toRightDerivedZero.app
          ((EtaleExtensionByZero.functor X U E).obj
            ((EtaleCoefficientRestriction.functor U.left r).obj F)) := by
  have h₀ := NatTrans.congr_app
    (EtaleCoefficientRestriction.derivedDirectImageMap_zero q r)
    ((EtaleExtensionByZero.functor X U E').obj F)
  change (EtaleCoefficientRestriction.functor S r).map
      ((EtaleDirectImage.functor q E').toRightDerivedZero.app
        ((EtaleExtensionByZero.functor X U E').obj F)) ≫
      (EtaleCoefficientRestriction.derivedDirectImageMap q r 0).app
        ((EtaleExtensionByZero.functor X U E').obj F) =
    (EtaleCoefficientRestriction.directImageIso q r).hom.app
        ((EtaleExtensionByZero.functor X U E').obj F) ≫
      (EtaleDirectImage.functor q E).toRightDerivedZero.app
        ((EtaleCoefficientRestriction.functor X r).obj
          ((EtaleExtensionByZero.functor X U E').obj F)) at h₀
  rw [iso_hom_app, ordinaryIso_hom_app, ← assoc, h₀, assoc]
  have hη := (EtaleDirectImage.functor q E).toRightDerivedZero.naturality
    ((EtaleExtensionCoefficientRestriction.iso X U r).hom.app F)
  change (EtaleDirectImage.functor q E).map
      ((EtaleExtensionCoefficientRestriction.iso X U r).hom.app F) ≫
      (EtaleDirectImage.functor q E).toRightDerivedZero.app
        ((EtaleExtensionByZero.functor X U E).obj
          ((EtaleCoefficientRestriction.functor U.left r).obj F)) =
    (EtaleDirectImage.functor q E).toRightDerivedZero.app
        ((EtaleCoefficientRestriction.functor X r).obj
          ((EtaleExtensionByZero.functor X U E').obj F)) ≫
      (EtaleDerivedDirectImage.functor q E 0).map
        ((EtaleExtensionCoefficientRestriction.iso X U r).hom.app F) at hη
  exact (congrArg
    (fun z => (EtaleCoefficientRestriction.directImageIso q r).hom.app
      ((EtaleExtensionByZero.functor X U E').obj F) ≫ z) hη.symm).trans
        (assoc _ _ _).symm

/-- The full natural-transformation square in degree zero uses the
original augmentations of q_* on both existing extension functors. -/
theorem iso_zero :
    Functor.whiskerRight
        (Functor.whiskerLeft (EtaleExtensionByZero.functor X U E')
          (EtaleDirectImage.functor q E').toRightDerivedZero)
        (EtaleCoefficientRestriction.functor S r) ≫ (iso q U r 0).hom =
      (ordinaryIso q U r).hom ≫
        Functor.whiskerLeft (EtaleCoefficientRestriction.functor U.left r)
          (Functor.whiskerLeft (EtaleExtensionByZero.functor X U E)
            (EtaleDirectImage.functor q E).toRightDerivedZero) := by
  apply NatTrans.ext
  funext F
  exact iso_zero_app q U r F

#print axioms iso
#print axioms iso_hom_app
#print axioms ordinaryIso
#print axioms ordinaryIso_hom_app
#print axioms iso_zero_app
#print axioms iso_zero

end PrimeGap182.TypeIII.EtaleCompactSupportCoefficientRestriction
