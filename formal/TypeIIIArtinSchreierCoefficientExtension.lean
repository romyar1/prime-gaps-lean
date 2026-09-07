import TypeIIIArtinSchreierCoefficientMaps
import TypeIIISplitImageTransport
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Sites.Adjunction

/-!
# Actual extension of coefficients for the Artin--Schreier sheaves

Coefficient extension is the sheafification of pointwise tensor extension,
with its actual adjunction to coefficient restriction. The free sheaf
comparison is induced by the free-module adjunction and sheafification.
All objects are the original sheaves on the original small étale site.

The actual free coefficient map is the adjoint transpose of this comparison.
Its proved projector square transports the original split character image
to the target image. Consequently the canonical tensor-extension map of
character sheaves is an isomorphism for every character-compatible ring map
with p invertible in both rings. The proof uses the actual split projectors
and needs no flatness assumption. Cohomology is not asserted here.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ChangeOfRings

section FreeModules

variable {E E' : Type u} [CommRing E] [CommRing E'] (r : E →+* E')

/-- Extending a free module gives the free module on the same generators,
by uniqueness of the actual free-forgetful adjunction. -/
def freeModuleCoefficientExtensionIso :
    ModuleCat.free E ⋙ ModuleCat.extendScalars r ≅ ModuleCat.free E' := by
  let adj₁ := (ModuleCat.adj E).comp (ModuleCat.extendRestrictScalarsAdj r)
  let adj₂ : ModuleCat.free E' ⊣
      ModuleCat.restrictScalars r ⋙ forget (ModuleCat.{u} E) := ModuleCat.adj E'
  exact adj₁.leftAdjointUniq adj₂

/-- The tensor-extension isomorphism has exactly the original free
coefficient map as its adjoint transpose. -/
theorem freeModuleCoefficientExtensionIso_mate (X : Type u) :
    (ModuleCat.extendRestrictScalarsAdj r).homEquiv _ _
        ((freeModuleCoefficientExtensionIso r).hom.app X) =
      (freeModuleCoefficientMap r).app X := by
  apply ModuleCat.free_hom_ext
  intro x
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((ModuleCat.adj E).comp (ModuleCat.extendRestrictScalarsAdj r))
    (show ModuleCat.free E' ⊣
      ModuleCat.restrictScalars r ⋙ forget (ModuleCat.{u} E) from ModuleCat.adj E') X
  have hx := congrArg (fun g => g x) h
  change (ModuleCat.extendRestrictScalarsAdj r).homEquiv _ _
    ((freeModuleCoefficientExtensionIso r).hom.app X) (ModuleCat.freeMk x) =
      ModuleCat.freeMk (R := E') x at hx
  exact hx.trans (freeModuleCoefficientMap_generator r X x).symm

/-- The actual free-module comparison preserves each tensor generator. -/
theorem freeModuleCoefficientExtensionIso_one_tmul (X : Type u) (x : X) :
    (freeModuleCoefficientExtensionIso r).hom.app X
        ((1 : E') ⊗ₜ[E,r] (ModuleCat.freeMk (R := E) x)) =
      ModuleCat.freeMk (R := E') x := by
  have h := congrArg (fun g => g (ModuleCat.freeMk (R := E) x))
    (freeModuleCoefficientExtensionIso_mate r X)
  exact h.trans (freeModuleCoefficientMap_generator r X x)

end FreeModules

section SheafExtension

variable (R : Type u) [CommRing R]
  {E E' : Type u} [CommRing E] [CommRing E'] (r : E →+* E')

/-- Actual sheafification of tensor extension on the small étale site. -/
abbrev etaleModuleCoefficientExtension :
    Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E) ⥤
      Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E') :=
  Sheaf.composeAndSheafify (Spec (.of R)).smallEtaleTopology
    (ModuleCat.extendScalars r)

/-- The actual coefficient-extension and coefficient-restriction adjunction. -/
def etaleModuleCoefficientAdjunction :
    etaleModuleCoefficientExtension R r ⊣ etaleModuleCoefficientRestriction R r :=
  Sheaf.adjunction (Spec (.of R)).smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj r)

end SheafExtension

variable (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] (f : R)
  {E E' : Type u} [CommRing E] [CommRing E'] (r : E →+* E')

/-- The free presheaf comparison uses the same representable cover. -/
def artinSchreierFreePresheafCoefficientExtensionIso :
    artinSchreierFreePresheaf p f E ⋙ ModuleCat.extendScalars r ≅
      artinSchreierFreePresheaf p f E' :=
  Functor.isoWhiskerLeft (shrinkYoneda.{u}.obj (artinSchreierEtaleObject p f))
    (freeModuleCoefficientExtensionIso r)

/-- The original free representable sheaf commutes with actual tensor
extension and sheafification. -/
def artinSchreierFreeSheafCoefficientExtensionIso :
    (etaleModuleCoefficientExtension R r).obj (artinSchreierFreeSheaf p f E) ≅
      artinSchreierFreeSheaf p f E' :=
  (presheafToSheafCompComposeAndSheafifyIso (Spec (.of R)).smallEtaleTopology
      (ModuleCat.extendScalars r)).app (artinSchreierFreePresheaf p f E) ≪≫
    (presheafToSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E')).mapIso
      (artinSchreierFreePresheafCoefficientExtensionIso p f r)

set_option backward.isDefEq.respectTransparency.types false in
/-- The free-sheaf tensor comparison is induced by the actual free-presheaf
comparison, with both sheafification units retained. -/
theorem artinSchreierFreeSheafCoefficientExtensionIso_presheaf :
    Functor.whiskerRight
        (toSheafify (Spec (.of R)).smallEtaleTopology (artinSchreierFreePresheaf p f E))
        (ModuleCat.extendScalars r) ≫
      toSheafify (Spec (.of R)).smallEtaleTopology
        (sheafify (Spec (.of R)).smallEtaleTopology
          (artinSchreierFreePresheaf p f E) ⋙ ModuleCat.extendScalars r) ≫
      (artinSchreierFreeSheafCoefficientExtensionIso p f r).hom.hom =
    (artinSchreierFreePresheafCoefficientExtensionIso p f r).hom ≫
      toSheafify (Spec (.of R)).smallEtaleTopology (artinSchreierFreePresheaf p f E') := by
  rw [← Category.assoc]
  erw [toSheafify_naturality]
  rw [Category.assoc]
  let e := (presheafToSheafCompComposeAndSheafifyIso
    (Spec (.of R)).smallEtaleTopology (ModuleCat.extendScalars r)).app
      (artinSchreierFreePresheaf p f E)
  change toSheafify (Spec (.of R)).smallEtaleTopology
      (artinSchreierFreePresheaf p f E ⋙ ModuleCat.extendScalars r) ≫
        (e.inv.hom ≫ (e.hom.hom ≫ sheafifyMap (Spec (.of R)).smallEtaleTopology
          (artinSchreierFreePresheafCoefficientExtensionIso p f r).hom)) = _
  have he : e.inv.hom ≫ e.hom.hom = 𝟙 _ := congrArg (fun g => g.hom) e.inv_hom_id
  rw [← Category.assoc e.inv.hom e.hom.hom, he, Category.id_comp]
  exact (toSheafify_naturality _ _).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual free-sheaf tensor comparison is adjoint to the previously
constructed coefficient map on the original free sheaves. -/
theorem artinSchreierFreeSheafCoefficientExtensionIso_mate :
    (etaleModuleCoefficientAdjunction R r).homEquiv _ _
        (artinSchreierFreeSheafCoefficientExtensionIso p f r).hom =
      artinSchreierFreeSheafCoefficientMap p f r := by
  rw [Adjunction.homEquiv_unit]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _
    ((etaleModuleCoefficientRestriction R r).obj
      (artinSchreierFreeSheaf p f E')).property
  rw [artinSchreierFreeSheafCoefficientMap_unit]
  change toSheafify (Spec (.of R)).smallEtaleTopology (artinSchreierFreePresheaf p f E) ≫
    (((etaleModuleCoefficientAdjunction R r).unit.app (artinSchreierFreeSheaf p f E)).hom ≫
      Functor.whiskerRight (artinSchreierFreeSheafCoefficientExtensionIso p f r).hom.hom
        (ModuleCat.restrictScalars r)) = _
  dsimp only [etaleModuleCoefficientAdjunction]
  rw [Sheaf.adjunction_unit_app_hom]
  apply NatTrans.ext
  funext X
  apply ModuleCat.free_hom_ext
  intro x
  have h := congrArg (fun η => η.app X ((1 : E') ⊗ₜ[E,r] (ModuleCat.freeMk (R := E) x)))
    (artinSchreierFreeSheafCoefficientExtensionIso_presheaf p f r)
  change (artinSchreierFreeSheafCoefficientExtensionIso p f r).hom.hom.app X
      ((toSheafify (Spec (.of R)).smallEtaleTopology
        (sheafify (Spec (.of R)).smallEtaleTopology
          (artinSchreierFreePresheaf p f E) ⋙ ModuleCat.extendScalars r)).app X
          ((1 : E') ⊗ₜ[E,r]
            ((toSheafify (Spec (.of R)).smallEtaleTopology
              (artinSchreierFreePresheaf p f E)).app X (ModuleCat.freeMk (R := E) x)))) =
    (toSheafify (Spec (.of R)).smallEtaleTopology (artinSchreierFreePresheaf p f E')).app X
      ((freeModuleCoefficientExtensionIso r).hom.app _
        ((1 : E') ⊗ₜ[E,r] (ModuleCat.freeMk (R := E) x))) at h
  rw [freeModuleCoefficientExtensionIso_one_tmul] at h
  change (artinSchreierFreeSheafCoefficientExtensionIso p f r).hom.hom.app X
      ((toSheafify (Spec (.of R)).smallEtaleTopology
        (sheafify (Spec (.of R)).smallEtaleTopology
          (artinSchreierFreePresheaf p f E) ⋙ ModuleCat.extendScalars r)).app X
          ((1 : E') ⊗ₜ[E,r]
            ((toSheafify (Spec (.of R)).smallEtaleTopology
              (artinSchreierFreePresheaf p f E)).app X (ModuleCat.freeMk (R := E) x)))) =
    (toSheafify (Spec (.of R)).smallEtaleTopology (artinSchreierFreePresheaf p f E')).app X
      ((freeModuleCoefficientMap r).app _ (ModuleCat.freeMk (R := E) x))
  rw [freeModuleCoefficientMap_generator]
  exact h

section CharacterImages

variable [Invertible (p : E)] [Invertible (p : E')]
  (ψ : AddChar (ZMod p) E) (ψ' : AddChar (ZMod p) E')
  (hψ : ∀ a, r (ψ a) = ψ' a)

include hψ

/-- Actual tensor extension intertwines the actual character projectors.
The compatibility follows by transposing the proved coefficient-map square. -/
theorem artinSchreierRingCharacterSheafAverage_extension :
    (etaleModuleCoefficientExtension R r).map
        (artinSchreierRingCharacterSheafAverage p f E ψ) ≫
      (artinSchreierFreeSheafCoefficientExtensionIso p f r).hom =
    (artinSchreierFreeSheafCoefficientExtensionIso p f r).hom ≫
      artinSchreierRingCharacterSheafAverage p f E' ψ' := by
  apply ((etaleModuleCoefficientAdjunction R r).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    artinSchreierFreeSheafCoefficientExtensionIso_mate]
  exact artinSchreierRingCharacterSheafAverage_coefficientMap p f ψ ψ' r hψ

/-- The original character sheaf commutes with actual tensor extension.
Its proved split projector supplies the comparison without flatness. -/
def artinSchreierRingCharacterSheafCoefficientExtensionIso :
    (etaleModuleCoefficientExtension R r).obj
        (artinSchreierRingCharacterImageSheaf p f E ψ) ≅
      artinSchreierRingCharacterImageSheaf p f E' ψ' :=
  splitRetractTransportIso (etaleModuleCoefficientExtension R r)
    (Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E ψ))
    (artinSchreierRingCharacterSheafRetraction p f E ψ)
    (artinSchreierRingCharacterSheafInclusion_comp_retraction p f E ψ)
    (Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E' ψ'))
    (artinSchreierRingCharacterSheafRetraction p f E' ψ')
    (artinSchreierRingCharacterSheafInclusion_comp_retraction p f E' ψ')
    (artinSchreierFreeSheafCoefficientExtensionIso p f r)
    (by
      rw [artinSchreierRingCharacterSheafRetraction_comp_inclusion,
        artinSchreierRingCharacterSheafRetraction_comp_inclusion]
      exact artinSchreierRingCharacterSheafAverage_extension p f r ψ ψ' hψ)

/-- The isomorphism is the adjoint transpose of the already constructed
map between the actual character images. -/
theorem artinSchreierRingCharacterSheafCoefficientExtensionIso_mate :
    (etaleModuleCoefficientAdjunction R r).homEquiv _ _
        (artinSchreierRingCharacterSheafCoefficientExtensionIso p f r ψ ψ' hψ).hom =
      artinSchreierRingCharacterSheafCoefficientMap p f ψ ψ' r := by
  change (etaleModuleCoefficientAdjunction R r).homEquiv _ _
      ((etaleModuleCoefficientExtension R r).map
        (Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E ψ)) ≫
          (artinSchreierFreeSheafCoefficientExtensionIso p f r).hom ≫
            artinSchreierRingCharacterSheafRetraction p f E' ψ') = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    artinSchreierFreeSheafCoefficientExtensionIso_mate]
  rfl

/-- The canonical tensor-reduction map itself is an isomorphism. -/
theorem artinSchreierRingCharacterSheafCoefficientExtension_isIso :
    IsIso (((etaleModuleCoefficientAdjunction R r).homEquiv _ _).symm
      (artinSchreierRingCharacterSheafCoefficientMap p f ψ ψ' r)) := by
  rw [← artinSchreierRingCharacterSheafCoefficientExtensionIso_mate p f r ψ ψ' hψ,
    Equiv.symm_apply_apply]
  infer_instance

end CharacterImages

#print axioms freeModuleCoefficientExtensionIso
#print axioms freeModuleCoefficientExtensionIso_mate
#print axioms freeModuleCoefficientExtensionIso_one_tmul
#print axioms etaleModuleCoefficientExtension
#print axioms etaleModuleCoefficientAdjunction
#print axioms artinSchreierFreePresheafCoefficientExtensionIso
#print axioms artinSchreierFreeSheafCoefficientExtensionIso
#print axioms artinSchreierFreeSheafCoefficientExtensionIso_presheaf
#print axioms artinSchreierFreeSheafCoefficientExtensionIso_mate
#print axioms artinSchreierRingCharacterSheafAverage_extension
#print axioms artinSchreierRingCharacterSheafCoefficientExtensionIso
#print axioms artinSchreierRingCharacterSheafCoefficientExtensionIso_mate
#print axioms artinSchreierRingCharacterSheafCoefficientExtension_isIso

end PrimeGap182.TypeIII
