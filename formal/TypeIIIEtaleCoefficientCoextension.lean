import TypeIIIEtaleCoefficientRestriction
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Actual coefficient coextension on the small étale site

Coextension applies the existing module coextension functor to the
original section modules.  Its right-adjoint structure on modules
ensures that these presheaves are sheaves.  Restricting the original
objectwise adjunction through the full sheaf inclusions gives an
adjunction whose left adjoint is the existing coefficient restriction.

The unit, counit, and transposition formulas retain the original
module adjunction on every étale object.  The coefficient rings and
their homomorphism are arbitrary.
-/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII.EtaleCoefficientRestriction

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry

variable (S : Scheme.{u}) {E E' : Type u} [Ring E] [Ring E'] (r : E →+* E')

/-- The actual objectwise module coextension on the original small étale site. -/
def coextension :
    Sheaf S.smallEtaleTopology (ModuleCat.{u} E) ⥤
      Sheaf S.smallEtaleTopology (ModuleCat.{u} E') :=
  sheafCompose S.smallEtaleTopology (ModuleCat.coextendScalars r)

/-- At every étale object this is the original module coextension. -/
theorem coextension_obj_obj (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E))
    (U : S.Etaleᵒᵖ) :
    ((coextension S r).obj F).obj.obj U =
      (ModuleCat.coextendScalars r).obj (F.obj.obj U) := rfl

/-- Each morphism component is the original coextended module map. -/
theorem coextension_map_hom_app
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)} (f : F ⟶ G)
    (U : S.Etaleᵒᵖ) :
    ((coextension S r).map f).hom.app U =
      (ModuleCat.coextendScalars r).map (f.hom.app U) := rfl

/-- The original coefficient restriction is left adjoint to actual
objectwise coextension, by restricting the original module adjunction. -/
def restrictionCoextensionAdjunction : functor S r ⊣ coextension S r :=
  ((ModuleCat.restrictCoextendScalarsAdj r).whiskerRight S.Etaleᵒᵖ).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} E'))
    (fullyFaithfulSheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} E))
    (Iso.refl _) (Iso.refl _)

/-- The underlying unit is the original objectwise module-adjunction unit. -/
theorem restrictionCoextensionAdjunction_unit_app_hom
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E')) :
    ((restrictionCoextensionAdjunction S r).unit.app F).hom =
      ((ModuleCat.restrictCoextendScalarsAdj r).whiskerRight S.Etaleᵒᵖ).unit.app F.obj := by
  change (sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} E')).map
    ((restrictionCoextensionAdjunction S r).unit.app F) = _
  simp only [restrictionCoextensionAdjunction,
    Adjunction.map_restrictFullyFaithful_unit_app, Iso.refl_hom, NatTrans.id_app]
  rfl

/-- The underlying counit is the original objectwise module-adjunction counit. -/
theorem restrictionCoextensionAdjunction_counit_app_hom
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :
    ((restrictionCoextensionAdjunction S r).counit.app F).hom =
      ((ModuleCat.restrictCoextendScalarsAdj r).whiskerRight S.Etaleᵒᵖ).counit.app F.obj := by
  change (sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} E)).map
    ((restrictionCoextensionAdjunction S r).counit.app F) = _
  simp only [restrictionCoextensionAdjunction,
    Adjunction.map_restrictFullyFaithful_counit_app, Iso.refl_inv, NatTrans.id_app]
  rfl

/-- At each étale object, the unit is precisely the original module unit. -/
theorem restrictionCoextensionAdjunction_unit_app_hom_app
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E')) (U : S.Etaleᵒᵖ) :
    ((restrictionCoextensionAdjunction S r).unit.app F).hom.app U =
      (ModuleCat.restrictCoextendScalarsAdj r).unit.app (F.obj.obj U) := by
  rw [restrictionCoextensionAdjunction_unit_app_hom]
  exact Adjunction.whiskerRight_unit_app_app _ _ _ _

/-- At each étale object, the counit is precisely the original module counit. -/
theorem restrictionCoextensionAdjunction_counit_app_hom_app
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) (U : S.Etaleᵒᵖ) :
    ((restrictionCoextensionAdjunction S r).counit.app F).hom.app U =
      (ModuleCat.restrictCoextendScalarsAdj r).counit.app (F.obj.obj U) := by
  rw [restrictionCoextensionAdjunction_counit_app_hom]
  exact Adjunction.whiskerRight_counit_app_app _ _ _ _

/-- Transposition of an actual sheaf map is the original module
transposition on each section module. -/
theorem restrictionCoextensionAdjunction_homEquiv_app
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E'))
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u} E))
    (f : (functor S r).obj F ⟶ G) (U : S.Etaleᵒᵖ) :
    ((restrictionCoextensionAdjunction S r).homEquiv F G f).hom.app U =
      (ModuleCat.restrictCoextendScalarsAdj r).homEquiv (F.obj.obj U) (G.obj.obj U)
        (f.hom.app U) := by
  simp only [Adjunction.homEquiv_unit]
  change ((restrictionCoextensionAdjunction S r).unit.app F).hom.app U ≫
    (ModuleCat.coextendScalars r).map (f.hom.app U) = _
  rw [restrictionCoextensionAdjunction_unit_app_hom_app]

/-- Coextension is a right adjoint through this original restricted adjunction. -/
instance coextension_isRightAdjoint : (coextension S r).IsRightAdjoint :=
  (restrictionCoextensionAdjunction S r).isRightAdjoint

/-- The original coefficient restriction is a left adjoint to that coextension. -/
instance functor_isLeftAdjoint : (functor S r).IsLeftAdjoint :=
  (restrictionCoextensionAdjunction S r).isLeftAdjoint

/-- All small colimits are preserved by the original coefficient restriction. -/
instance functor_preservesColimits : PreservesColimitsOfSize.{u, u} (functor S r) :=
  (restrictionCoextensionAdjunction S r).leftAdjoint_preservesColimits

#print axioms coextension
#print axioms coextension_obj_obj
#print axioms coextension_map_hom_app
#print axioms restrictionCoextensionAdjunction
#print axioms restrictionCoextensionAdjunction_unit_app_hom
#print axioms restrictionCoextensionAdjunction_counit_app_hom
#print axioms restrictionCoextensionAdjunction_unit_app_hom_app
#print axioms restrictionCoextensionAdjunction_counit_app_hom_app
#print axioms restrictionCoextensionAdjunction_homEquiv_app
#print axioms coextension_isRightAdjoint
#print axioms functor_isLeftAdjoint
#print axioms functor_preservesColimits

end PrimeGap182.TypeIII.EtaleCoefficientRestriction
