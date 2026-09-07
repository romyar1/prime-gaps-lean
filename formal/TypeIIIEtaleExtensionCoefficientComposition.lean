import TypeIIIEtaleCoefficientRestrictionComposition
import TypeIIIEtaleExtensionCoefficientRestriction

/-!
# Composition of the original extension coefficient comparisons

The existing extension/coefficient comparison is characterized using
the original extension adjunction unit.  That characterization proves
composition coherence with the original coefficient-restriction
composition isomorphism.  All extension and restriction functors and
both comparison maps are the previously constructed ones.
-/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII.EtaleExtensionCoefficientRestriction

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry

variable (S : Scheme.{u}) (U : S.Etale)

section OneMap

variable {E E' : Type u} [Ring E] [Ring E'] (r : E →+* E')

/-- The original coefficient-adjunction unit commutes with the actual
étale restriction, since both use the same original section modules. -/
theorem restriction_coextensionUnit
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E')) :
    (EtaleExtensionByZero.restriction S U E').map
        ((EtaleCoefficientRestriction.restrictionCoextensionAdjunction S r).unit.app F) =
      (EtaleCoefficientRestriction.restrictionCoextensionAdjunction U.left r).unit.app
        ((EtaleExtensionByZero.restriction S U E').obj F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  change ((EtaleCoefficientRestriction.restrictionCoextensionAdjunction S r).unit.app F).hom.app
      ((EtaleRestrictionInverseImage.postcomposition S U).op.obj V) = _
  rw [EtaleCoefficientRestriction.restrictionCoextensionAdjunction_unit_app_hom_app,
    EtaleCoefficientRestriction.restrictionCoextensionAdjunction_unit_app_hom_app]
  rfl

/-- The inverse of the original comparison is characterized by the
original extension unit, without a supplied comparison or coherence premise. -/
theorem iso_inv_unit
    (F : Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E')) :
    (EtaleExtensionByZero.adjunction S U E).unit.app
          ((EtaleCoefficientRestriction.functor U.left r).obj F) ≫
        (EtaleExtensionByZero.restriction S U E).map ((iso S U r).inv.app F) =
      (EtaleCoefficientRestriction.functor U.left r).map
        ((EtaleExtensionByZero.adjunction S U E').unit.app F) := by
  apply Equiv.injective
    ((EtaleCoefficientRestriction.restrictionCoextensionAdjunction U.left r).homEquiv F _)
  have h := unit_iso_inv S U r F
  erw [coextensionRestrictionIso_hom_app, Category.comp_id] at h
  simp only [extensionRestrictionAdjunction, restrictionExtensionAdjunction,
    Adjunction.comp_unit_app, Functor.comp_map, assoc] at h
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← h, restriction_coextensionUnit]
  exact (EtaleCoefficientRestriction.restrictionCoextensionAdjunction U.left r).unit.naturality
    ((EtaleExtensionByZero.adjunction S U E').unit.app F)

end OneMap

section Composition

variable {E₀ E₁ E₂ : Type u} [Ring E₀] [Ring E₁] [Ring E₂]
  (f : E₀ →+* E₁) (g : E₁ →+* E₂) (gf : E₀ →+* E₂) (hgf : gf = g.comp f)

/-- Étale restriction retains the original coefficient-composition map. -/
theorem restriction_compIso'_hom_app
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E₂)) :
    (EtaleExtensionByZero.restriction S U E₀).map
        ((EtaleCoefficientRestriction.compIso' S f g gf hgf).hom.app F) =
      (EtaleCoefficientRestriction.compIso' U.left f g gf hgf).hom.app
        ((EtaleExtensionByZero.restriction S U E₂).obj F) := by
  apply Sheaf.hom_ext
  ext V x
  rfl

/-- The same compatibility holds for the inverse composition map. -/
theorem restriction_compIso'_inv_app
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E₂)) :
    (EtaleExtensionByZero.restriction S U E₀).map
        ((EtaleCoefficientRestriction.compIso' S f g gf hgf).inv.app F) =
      (EtaleCoefficientRestriction.compIso' U.left f g gf hgf).inv.app
        ((EtaleExtensionByZero.restriction S U E₂).obj F) := by
  apply Sheaf.hom_ext
  ext V x
  rfl

/-- The inverse of the original extension comparison respects successive
coefficient restrictions and the actual composition isomorphism. -/
theorem iso_inv_comp'
    (F : Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E₂)) :
    (EtaleExtensionByZero.functor S U E₀).map
          ((EtaleCoefficientRestriction.compIso' U.left f g gf hgf).inv.app F) ≫
        (iso S U gf).inv.app F =
      (iso S U f).inv.app ((EtaleCoefficientRestriction.functor U.left g).obj F) ≫
        (EtaleCoefficientRestriction.functor S f).map ((iso S U g).inv.app F) ≫
        (EtaleCoefficientRestriction.compIso' S f g gf hgf).inv.app
          ((EtaleExtensionByZero.functor S U E₂).obj F) := by
  apply ((EtaleExtensionByZero.adjunction S U E₀).homEquiv _ _).injective
  have hη := (EtaleExtensionByZero.adjunction S U E₀).unit.naturality
    ((EtaleCoefficientRestriction.compIso' U.left f g gf hgf).inv.app F)
  simp only [Functor.id_map, Functor.comp_map] at hη
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  calc
    _ = (EtaleCoefficientRestriction.compIso' U.left f g gf hgf).inv.app F ≫
        (EtaleCoefficientRestriction.functor U.left gf).map
          ((EtaleExtensionByZero.adjunction S U E₂).unit.app F) := by
      erw [← assoc, ← hη, assoc, iso_inv_unit]
    _ = (EtaleCoefficientRestriction.functor U.left f).map
          ((EtaleCoefficientRestriction.functor U.left g).map
            ((EtaleExtensionByZero.adjunction S U E₂).unit.app F)) ≫
        (EtaleCoefficientRestriction.compIso' U.left f g gf hgf).inv.app
          ((EtaleExtensionByZero.restriction S U E₂).obj
            ((EtaleExtensionByZero.functor S U E₂).obj F)) :=
      ((EtaleCoefficientRestriction.compIso' U.left f g gf hgf).inv.naturality
        ((EtaleExtensionByZero.adjunction S U E₂).unit.app F)).symm
    _ = _ := by
      erw [← iso_inv_unit S U g F, Functor.map_comp,
        ← iso_inv_unit S U f ((EtaleCoefficientRestriction.functor U.left g).obj F),
        ← restriction_compIso'_inv_app S U f g gf hgf
          ((EtaleExtensionByZero.functor S U E₂).obj F)]
      rfl

/-- The original forward comparisons satisfy composition coherence
with the actual coefficient-restriction comparison for the specified composite. -/
theorem iso_comp'
    (F : Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E₂)) :
    (EtaleCoefficientRestriction.compIso' S f g gf hgf).hom.app
          ((EtaleExtensionByZero.functor S U E₂).obj F) ≫
        (EtaleCoefficientRestriction.functor S f).map ((iso S U g).hom.app F) ≫
        (iso S U f).hom.app ((EtaleCoefficientRestriction.functor U.left g).obj F) =
      (iso S U gf).hom.app F ≫
        (EtaleExtensionByZero.functor S U E₀).map
          ((EtaleCoefficientRestriction.compIso' U.left f g gf hgf).hom.app F) := by
  let e₁ := (EtaleCoefficientRestriction.compIso' S f g gf hgf).app
      ((EtaleExtensionByZero.functor S U E₂).obj F) ≪≫
    (EtaleCoefficientRestriction.functor S f).mapIso ((iso S U g).app F) ≪≫
    (iso S U f).app ((EtaleCoefficientRestriction.functor U.left g).obj F)
  let e₂ := (iso S U gf).app F ≪≫
    (EtaleExtensionByZero.functor S U E₀).mapIso
      ((EtaleCoefficientRestriction.compIso' U.left f g gf hgf).app F)
  have h : e₁.inv = e₂.inv := (iso_inv_comp' S U f g gf hgf F).symm
  exact congrArg Iso.hom (Iso.ext_inv h)

/-- Successive original extension comparisons agree with the original
comparison for the literal composite ring homomorphism. -/
theorem iso_comp
    (F : Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E₂)) :
    (EtaleCoefficientRestriction.compIso S f g).hom.app
          ((EtaleExtensionByZero.functor S U E₂).obj F) ≫
        (EtaleCoefficientRestriction.functor S f).map ((iso S U g).hom.app F) ≫
        (iso S U f).hom.app ((EtaleCoefficientRestriction.functor U.left g).obj F) =
      (iso S U (g.comp f)).hom.app F ≫
        (EtaleExtensionByZero.functor S U E₀).map
          ((EtaleCoefficientRestriction.compIso U.left f g).hom.app F) :=
  iso_comp' S U f g (g.comp f) rfl F

end Composition

#print axioms restriction_coextensionUnit
#print axioms iso_inv_unit
#print axioms restriction_compIso'_hom_app
#print axioms restriction_compIso'_inv_app
#print axioms iso_inv_comp'
#print axioms iso_comp'
#print axioms iso_comp

end PrimeGap182.TypeIII.EtaleExtensionCoefficientRestriction
