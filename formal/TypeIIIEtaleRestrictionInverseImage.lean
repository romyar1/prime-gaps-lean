import TypeIIIEtaleExtensionByZero
import TypeIIIEtaleInverseImage
import TypeIIIEtaleInjectiveImages
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Restriction to an étale object is the actual inverse image

Postcomposition with an étale structure morphism is left adjoint to
the actual base-change functor on small étale sites.  Its continuity
follows from the literal slice-site equivalence and the slice forgetful
functor.  The induced sheaf adjunction therefore identifies the existing
restriction functor with the already constructed inverse image.

The comparison is the unique isomorphism of left adjoints to the original
direct image, and its unit and counit compatibility are retained.  No
proper base-change or cohomology comparison is assumed or asserted.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleRestrictionInverseImage

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

variable (S : Scheme.{u}) (U : S.Etale)

set_option backward.isDefEq.respectTransparency.types false in
/-- Postcomposition with the actual étale structure map. -/
def postcomposition : U.left.Etale ⥤ S.Etale :=
  MorphismProperty.Over.map (P := @AlgebraicGeometry.Etale) ⊤ U.prop

/-- Postcomposition keeps the original scheme. -/
theorem postcomposition_obj_left (V : U.left.Etale) :
    ((postcomposition S U).obj V).left = V.left := rfl

/-- Its structure map is the original composite to the base. -/
theorem postcomposition_obj_hom (V : U.left.Etale) :
    ((postcomposition S U).obj V).hom = V.hom ≫ U.hom := rfl

/-- Its action on an arrow keeps the underlying scheme map. -/
theorem postcomposition_map_left {V W : U.left.Etale} (f : V ⟶ W) :
    ((postcomposition S U).map f).left = f.left := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The same functor is literal passage to the slice followed by forgetting. -/
def postcompositionIsoSlice :
    postcomposition S U ≅ etaleToSlice S U ⋙ Over.forget U := Iso.refl _

/-- Continuity follows from the actual slice topology, without a
representable-flatness assumption on postcomposition. -/
instance postcomposition_isContinuous :
    (postcomposition S U).IsContinuous U.left.smallEtaleTopology S.smallEtaleTopology :=
  Functor.isContinuous_comp' (postcompositionIsoSlice S U).symm
    U.left.smallEtaleTopology (S.smallEtaleTopology.over U) S.smallEtaleTopology

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual site postcomposition/base-change adjunction. -/
def postcompositionAdjunction :
    postcomposition S U ⊣ EtaleDirectImage.baseChange U.hom :=
  MorphismProperty.Over.mapPullbackAdj (@AlgebraicGeometry.Etale) ⊤ U.hom U.prop trivial

variable (E : Type u) [Ring E]

set_option backward.isDefEq.respectTransparency.types false in
/-- The existing restriction is actual presheaf precomposition. -/
def restrictionIsoPushforward :
    EtaleExtensionByZero.restriction S U E ≅
      (postcomposition S U).sheafPushforwardContinuous (ModuleCat.{u} E)
        U.left.smallEtaleTopology S.smallEtaleTopology := Iso.refl _

/-- Restriction is left adjoint to the original étale direct image. -/
def restrictionAdjunction :
    EtaleExtensionByZero.restriction S U E ⊣ EtaleDirectImage.functor U.hom E :=
  ((postcompositionAdjunction S U).sheafPushforwardContinuous
    (E := ModuleCat.{u} E) U.left.smallEtaleTopology S.smallEtaleTopology).ofNatIsoLeft
      (restrictionIsoPushforward S U E).symm

/-- On sections, its unit is restriction along the actual site counit. -/
theorem restrictionAdjunction_unit_app_hom_app
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) (V : S.Etale) :
    ((restrictionAdjunction S U E).unit.app F).hom.app (op V) =
      F.obj.map ((postcompositionAdjunction S U).counit.app V).op := by
  change F.obj.map ((postcompositionAdjunction S U).counit.app V).op ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- On sections, its counit is restriction along the actual site unit. -/
theorem restrictionAdjunction_counit_app_hom_app
    (F : Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E)) (V : U.left.Etale) :
    ((restrictionAdjunction S U E).counit.app F).hom.app (op V) =
      F.obj.map ((postcompositionAdjunction S U).unit.app V).op := by
  change (𝟙 _) ≫ F.obj.map ((postcompositionAdjunction S U).unit.app V).op = _
  exact Category.id_comp _

/-- The actual restriction/inverse-image comparison, by uniqueness of
left adjoints to the unchanged direct image. -/
def iso : EtaleExtensionByZero.restriction S U E ≅ EtaleInverseImage.functor U.hom E :=
  (restrictionAdjunction S U E).leftAdjointUniq (EtaleInverseImage.adjunction U.hom E)

/-- The comparison intertwines the two actual units. -/
theorem iso_unit (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :
    (restrictionAdjunction S U E).unit.app F ≫
      (EtaleDirectImage.functor U.hom E).map ((iso S U E).hom.app F) =
      (EtaleInverseImage.adjunction U.hom E).unit.app F :=
  Adjunction.unit_leftAdjointUniq_hom_app
    (restrictionAdjunction S U E) (EtaleInverseImage.adjunction U.hom E) F

/-- The comparison intertwines the two actual counits. -/
theorem iso_counit (F : Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E)) :
    (iso S U E).hom.app ((EtaleDirectImage.functor U.hom E).obj F) ≫
      (EtaleInverseImage.adjunction U.hom E).counit.app F =
      (restrictionAdjunction S U E).counit.app F :=
  Adjunction.leftAdjointUniq_hom_app_counit
    (restrictionAdjunction S U E) (EtaleInverseImage.adjunction U.hom E) F

/-- The existing extension from an étale object is left adjoint to
the unchanged inverse image along its structure map. -/
def extensionAdjunction :
    EtaleExtensionByZero.functor S U E ⊣ EtaleInverseImage.functor U.hom E :=
  (EtaleExtensionByZero.adjunction S U E).ofNatIsoRight (iso S U E)

/-- For a monomorphic étale object, actual inverse image preserves
injectives through the proved restriction comparison. -/
instance inverseImage_preservesInjectiveObjects [Mono U.hom] :
    (EtaleInverseImage.functor U.hom E).PreservesInjectiveObjects where
  injective_obj {F} hF :=
    Injective.of_iso ((iso S U E).app F)
      ((EtaleExtensionByZero.restriction S U E).injective_obj_of_injective hF)

/-- The same consequence for an actual monomorphic étale scheme map. -/
instance inverseImage_preservesInjectiveObjects_of_etale_mono
    {X T : Scheme.{u}} (j : X ⟶ T) [Etale j] [Mono j]
    (E : Type u) [Ring E] : (EtaleInverseImage.functor j E).PreservesInjectiveObjects := by
  let : Mono (Scheme.Etale.mk j).hom := inferInstanceAs (Mono j)
  exact inverseImage_preservesInjectiveObjects T (Scheme.Etale.mk j) E

end PrimeGap182.TypeIII.EtaleRestrictionInverseImage

#print axioms PrimeGap182.TypeIII.EtaleRestrictionInverseImage.postcomposition
#print axioms PrimeGap182.TypeIII.EtaleRestrictionInverseImage.postcomposition_obj_left
#print axioms PrimeGap182.TypeIII.EtaleRestrictionInverseImage.postcomposition_obj_hom
#print axioms PrimeGap182.TypeIII.EtaleRestrictionInverseImage.postcomposition_map_left
#print axioms PrimeGap182.TypeIII.EtaleRestrictionInverseImage.postcompositionIsoSlice
#print axioms PrimeGap182.TypeIII.EtaleRestrictionInverseImage.postcomposition_isContinuous
#print axioms PrimeGap182.TypeIII.EtaleRestrictionInverseImage.postcompositionAdjunction
#print axioms PrimeGap182.TypeIII.EtaleRestrictionInverseImage.restrictionIsoPushforward
#print axioms PrimeGap182.TypeIII.EtaleRestrictionInverseImage.restrictionAdjunction
#print axioms PrimeGap182.TypeIII.EtaleRestrictionInverseImage.restrictionAdjunction_unit_app_hom_app
#print axioms PrimeGap182.TypeIII.EtaleRestrictionInverseImage.restrictionAdjunction_counit_app_hom_app
#print axioms PrimeGap182.TypeIII.EtaleRestrictionInverseImage.iso
#print axioms PrimeGap182.TypeIII.EtaleRestrictionInverseImage.iso_unit
#print axioms PrimeGap182.TypeIII.EtaleRestrictionInverseImage.iso_counit
#print axioms PrimeGap182.TypeIII.EtaleRestrictionInverseImage.extensionAdjunction
#print axioms PrimeGap182.TypeIII.EtaleRestrictionInverseImage.inverseImage_preservesInjectiveObjects
#print axioms PrimeGap182.TypeIII.EtaleRestrictionInverseImage.inverseImage_preservesInjectiveObjects_of_etale_mono
