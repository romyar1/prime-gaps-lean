import TypeIIIEtaleCoefficientCoextension
import TypeIIIEtaleRestrictionInverseImage
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Coefficient restriction and the original étale extension

The existing étale restriction is literal precomposition on the small
étale sites.  It therefore commutes with the actual objectwise coefficient
coextension by an identity comparison.  Conjugating that identity through
the original extension/restriction adjunctions and the original restricted
coefficient adjunctions gives a canonical comparison for extension.

The result uses the existing extension functor and existing coefficient
restriction on both sides.  It holds for every étale object; when its
structure map is monomorphic, this is the proved extension by zero.
No flatness or preservation of injective objects is required.
-/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII.EtaleExtensionCoefficientRestriction

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry

variable (S : Scheme.{u}) (U : S.Etale)
  {E E' : Type u} [Ring E] [Ring E'] (r : E →+* E')

/-- The two actual right-adjoint composites agree by literal
precomposition of the original objectwise coextension. -/
def coextensionRestrictionIso :
    EtaleCoefficientRestriction.coextension S r ⋙ EtaleExtensionByZero.restriction S U E' ≅
      EtaleExtensionByZero.restriction S U E ⋙
        EtaleCoefficientRestriction.coextension U.left r :=
  Iso.refl _

/-- The right-adjoint comparison is the identity on the original sheaf. -/
theorem coextensionRestrictionIso_hom_app
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :
    (coextensionRestrictionIso S U r).hom.app F =
      𝟙 ((EtaleExtensionByZero.restriction S U E').obj
        ((EtaleCoefficientRestriction.coextension S r).obj F)) := rfl

/-- Its inverse is the same original identity. -/
theorem coextensionRestrictionIso_inv_app
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :
    (coextensionRestrictionIso S U r).inv.app F =
      𝟙 ((EtaleCoefficientRestriction.coextension U.left r).obj
        ((EtaleExtensionByZero.restriction S U E).obj F)) := rfl

/-- The first composite uses the original extension followed by
the original coefficient restriction. -/
def extensionRestrictionAdjunction :
    EtaleExtensionByZero.functor S U E' ⋙ EtaleCoefficientRestriction.functor S r ⊣
      EtaleCoefficientRestriction.coextension S r ⋙ EtaleExtensionByZero.restriction S U E' :=
  (EtaleExtensionByZero.adjunction S U E').comp
    (EtaleCoefficientRestriction.restrictionCoextensionAdjunction S r)

/-- The second composite uses the original coefficient restriction
followed by the original extension. -/
def restrictionExtensionAdjunction :
    EtaleCoefficientRestriction.functor U.left r ⋙ EtaleExtensionByZero.functor S U E ⊣
      EtaleExtensionByZero.restriction S U E ⋙
        EtaleCoefficientRestriction.coextension U.left r :=
  (EtaleCoefficientRestriction.restrictionCoextensionAdjunction U.left r).comp
    (EtaleExtensionByZero.adjunction S U E)

/-- The original étale extension commutes with arbitrary restriction
of coefficient rings.  For a monomorphic étale object, this is the
actual extension-by-zero comparison. -/
def iso :
    EtaleExtensionByZero.functor S U E' ⋙ EtaleCoefficientRestriction.functor S r ≅
      EtaleCoefficientRestriction.functor U.left r ⋙ EtaleExtensionByZero.functor S U E :=
  ((conjugateIsoEquiv (extensionRestrictionAdjunction S U r)
    (restrictionExtensionAdjunction S U r)).symm (coextensionRestrictionIso S U r)).symm

/-- Conjugating back recovers precisely the original identity square
of coefficient coextension and étale restriction. -/
theorem iso_conjugate :
    conjugateIsoEquiv (extensionRestrictionAdjunction S U r)
      (restrictionExtensionAdjunction S U r) (iso S U r).symm =
        coextensionRestrictionIso S U r :=
  Equiv.apply_symm_apply _ _

/-- The forward comparison intertwines the two original composite units. -/
theorem unit_iso_hom
    (F : Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E')) :
    (restrictionExtensionAdjunction S U r).unit.app F ≫
        (coextensionRestrictionIso S U r).inv.app
          ((EtaleExtensionByZero.functor S U E).obj
            ((EtaleCoefficientRestriction.functor U.left r).obj F)) =
      (extensionRestrictionAdjunction S U r).unit.app F ≫
        (EtaleCoefficientRestriction.coextension S r ⋙
          EtaleExtensionByZero.restriction S U E').map ((iso S U r).hom.app F) :=
  unit_conjugateEquiv_symm (restrictionExtensionAdjunction S U r)
    (extensionRestrictionAdjunction S U r) (coextensionRestrictionIso S U r).inv F

/-- The inverse comparison intertwines the same original units
in the opposite direction. -/
theorem unit_iso_inv
    (F : Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E')) :
    (extensionRestrictionAdjunction S U r).unit.app F ≫
        (coextensionRestrictionIso S U r).hom.app
          ((EtaleCoefficientRestriction.functor S r).obj
            ((EtaleExtensionByZero.functor S U E').obj F)) =
      (restrictionExtensionAdjunction S U r).unit.app F ≫
        (EtaleExtensionByZero.restriction S U E ⋙
          EtaleCoefficientRestriction.coextension U.left r).map ((iso S U r).inv.app F) :=
  unit_conjugateEquiv_symm (extensionRestrictionAdjunction S U r)
    (restrictionExtensionAdjunction S U r) (coextensionRestrictionIso S U r).hom F

/-- The forward comparison also intertwines the original composite counits. -/
theorem iso_hom_counit
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :
    (EtaleExtensionByZero.functor S U E' ⋙ EtaleCoefficientRestriction.functor S r).map
          ((coextensionRestrictionIso S U r).inv.app G) ≫
        (extensionRestrictionAdjunction S U r).counit.app G =
      (iso S U r).hom.app
          ((EtaleCoefficientRestriction.coextension U.left r).obj
            ((EtaleExtensionByZero.restriction S U E).obj G)) ≫
        (restrictionExtensionAdjunction S U r).counit.app G :=
  conjugateEquiv_counit_symm (restrictionExtensionAdjunction S U r)
    (extensionRestrictionAdjunction S U r) (coextensionRestrictionIso S U r).inv G

/-- Ordinary transposition of the same map agrees under the canonical
comparison and the original identity square of right adjoints. -/
theorem homEquiv_compat
    (F : Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E'))
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u} E))
    (h : (EtaleExtensionByZero.functor S U E).obj
      ((EtaleCoefficientRestriction.functor U.left r).obj F) ⟶ G) :
    (extensionRestrictionAdjunction S U r).homEquiv F G ((iso S U r).hom.app F ≫ h) =
      (restrictionExtensionAdjunction S U r).homEquiv F G h ≫
        (coextensionRestrictionIso S U r).inv.app G := by
  simp only [Adjunction.homEquiv_unit]
  rw [assoc, (coextensionRestrictionIso S U r).inv.naturality h, ← assoc, unit_iso_hom]
  simp only [Functor.map_comp, assoc]

#print axioms coextensionRestrictionIso
#print axioms coextensionRestrictionIso_hom_app
#print axioms coextensionRestrictionIso_inv_app
#print axioms extensionRestrictionAdjunction
#print axioms restrictionExtensionAdjunction
#print axioms iso
#print axioms iso_conjugate
#print axioms unit_iso_hom
#print axioms unit_iso_inv
#print axioms iso_hom_counit
#print axioms homEquiv_compat

end PrimeGap182.TypeIII.EtaleExtensionCoefficientRestriction
