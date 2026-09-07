import TypeIIIHenselianEtaleScheme
import TypeIIIEtaleClosedFieldSections
import TypeIIIEtaleCohomology

/-!
# Exact global sections over a strictly henselian local ring

For a henselian local ring with separably closed residue field, the
identity étale object pointed by the actual residue morphism is an
initial neighborhood of that geometric point.  The unique morphism
to each neighborhood is the scheme section constructed by the proved
henselian lifting theorem, with no section or uniqueness hypothesis.

The original germ at this identity neighborhood is therefore an
isomorphism.  It identifies the actual geometric stalk with the
existing global-sections functor.  Exactness is transferred from the
actual stalk functor; no new cohomology functor is introduced here.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.StrictHenselianEtaleSections

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing
open HenselianEtaleScheme

variable (R : Type u) [CommRing R] [HenselianLocalRing R] [IsSepClosed (ResidueField R)]

/-- The actual residue point in the fiber of the identity étale object. -/
def identitySection :
    (Scheme.pointSmallEtale (residueSpec R)).fiber.obj
      (Scheme.Etale.mk (𝟙 (Spec (.of R)))) :=
  Over.homMk (residueSpec R) (by simp)

/-- The identity étale object with its specified residue-field point. -/
def identityNeighborhood : (Scheme.pointSmallEtale (residueSpec R)).fiber.Elements :=
  ⟨Scheme.Etale.mk (𝟙 (Spec (.of R))), identitySection R⟩

/-- The actual scheme section gives a morphism from the identity object
to the original étale neighborhood. -/
def pointedSection (U : (Spec (.of R)).Etale)
    (t : (Scheme.pointSmallEtale (residueSpec R)).fiber.obj U) :
    Scheme.Etale.mk (𝟙 (Spec (.of R))) ⟶ U := by
  let : Etale U.hom := U.prop
  exact MorphismProperty.Over.homMk
    (sectionLift R U.hom t.left t.w) (sectionLift_over R U.hom t.left t.w)

/-- Its underlying scheme section lifts exactly the specified residue morphism. -/
theorem pointedSection_residue (U : (Spec (.of R)).Etale)
    (t : (Scheme.pointSmallEtale (residueSpec R)).fiber.obj U) :
    residueSpec R ≫ (pointedSection R U t).left = t.left := by
  let : Etale U.hom := U.prop
  exact sectionLift_residue R U.hom t.left t.w

/-- The constructed neighborhood morphism carries the original identity
fiber element to the specified geometric point of the neighborhood. -/
theorem pointedSection_fiber (U : (Spec (.of R)).Etale)
    (t : (Scheme.pointSmallEtale (residueSpec R)).fiber.obj U) :
    (Scheme.pointSmallEtale (residueSpec R)).fiber.map
        (pointedSection R U t) (identitySection R) = t := by
  apply Over.OverMorphism.ext
  exact pointedSection_residue R U t

set_option backward.isDefEq.respectTransparency false in
/-- Every pointed étale neighborhood receives a unique map from the
actual identity neighborhood, by the proved scheme lifting theorem. -/
def identityNeighborhood_isInitial : IsInitial (identityNeighborhood R) := by
  refine IsInitial.ofUniqueHom
    (fun V => ⟨pointedSection R V.1 V.2, pointedSection_fiber R V.1 V.2⟩) ?_
  intro V m
  apply Subtype.ext
  apply MorphismProperty.Over.Hom.ext
  let : Etale V.1.hom := V.1.prop
  apply section_ext R V.1.hom _ _
  · exact MorphismProperty.Over.w m.1
  · exact MorphismProperty.Over.w (pointedSection R V.1 V.2)
  · have hm := congrArg (fun f => f.left) m.2
    change residueSpec R ≫ m.1.left = V.2.left at hm
    rw [pointedSection_residue]
    exact hm

variable (E : Type u) [Ring E]

set_option backward.isDefEq.respectTransparency false in
/-- The original germ natural transformation at the identity
neighborhood is invertible, because this object is initial. -/
instance identityGermNatTrans_isIso :
    IsIso ((Scheme.pointSmallEtale (residueSpec R)).toPresheafFiberNatTrans
      (A := ModuleCat.{u} E) (Scheme.Etale.mk (𝟙 (Spec (.of R))))
      (identitySection R)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro P
  let hc := (Scheme.pointSmallEtale (residueSpec R)).isColimitPresheafFiberCocone P
  exact hc.isIso_ι_app_of_isTerminal (op (identityNeighborhood R))
    (identityNeighborhood_isInitial R).op

/-- The actual presheaf fiber equals evaluation at the identity étale object. -/
def presheafFiberIso :
    (Scheme.pointSmallEtale (residueSpec R)).presheafFiber (A := ModuleCat.{u} E) ≅
      (evaluation (Spec (.of R)).Etaleᵒᵖ (ModuleCat.{u} E)).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of R))))) :=
  (asIso ((Scheme.pointSmallEtale (residueSpec R)).toPresheafFiberNatTrans
    (A := ModuleCat.{u} E) (Scheme.Etale.mk (𝟙 (Spec (.of R))))
    (identitySection R))).symm

/-- The inverse comparison is literally the original germ map. -/
theorem presheafFiberIso_inv_app (P : (Spec (.of R)).Etaleᵒᵖ ⥤ ModuleCat.{u} E) :
    (presheafFiberIso R E).inv.app P =
      (Scheme.pointSmallEtale (residueSpec R)).toPresheafFiber
        (Scheme.Etale.mk (𝟙 (Spec (.of R)))) (identitySection R) P := rfl

set_option backward.isDefEq.respectTransparency false in
/-- An arbitrary germ corresponds to restriction along its actual,
uniquely constructed henselian section. -/
theorem toPresheafFiber_presheafFiberIso_hom (U : (Spec (.of R)).Etale)
    (t : (Scheme.pointSmallEtale (residueSpec R)).fiber.obj U)
    (P : (Spec (.of R)).Etaleᵒᵖ ⥤ ModuleCat.{u} E) :
    (Scheme.pointSmallEtale (residueSpec R)).toPresheafFiber
        (A := ModuleCat.{u} E) U t P ≫ (presheafFiberIso R E).hom.app P =
      P.map (pointedSection R U t).op := by
  have hw := (Scheme.pointSmallEtale (residueSpec R)).toPresheafFiber_w
    (A := ModuleCat.{u} E) (pointedSection R U t) (identitySection R) P
  rw [pointedSection_fiber] at hw
  rw [← hw, Category.assoc, ← presheafFiberIso_inv_app, Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- The actual geometric stalk is naturally isomorphic to the
unchanged global-sections functor on Spec R. -/
def stalkIso :
    (Scheme.pointSmallEtale (residueSpec R)).sheafFiber (A := ModuleCat.{u} E) ≅
      EtaleCohomology.sections (Spec (.of R)) E :=
  Functor.isoWhiskerLeft (sheafToPresheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E))
    (presheafFiberIso R E)

/-- The inverse sheaf comparison is the same actual identity-neighborhood germ. -/
theorem stalkIso_inv_app
    (F : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)) :
    (stalkIso R E).inv.app F =
      (Scheme.pointSmallEtale (residueSpec R)).toPresheafFiber
        (Scheme.Etale.mk (𝟙 (Spec (.of R)))) (identitySection R) F.obj := rfl

/-- The comparison of each sheaf germ with global sections uses the
actual section of that original étale neighborhood. -/
theorem toPresheafFiber_stalkIso_hom (U : (Spec (.of R)).Etale)
    (t : (Scheme.pointSmallEtale (residueSpec R)).fiber.obj U)
    (F : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)) :
    (Scheme.pointSmallEtale (residueSpec R)).toPresheafFiber
        (A := ModuleCat.{u} E) U t F.obj ≫ (stalkIso R E).hom.app F =
      F.obj.map (pointedSection R U t).op :=
  toPresheafFiber_presheafFiberIso_hom R E U t F.obj

/-- Actual global sections over the strictly henselian local ring
preserve finite colimits, as the proved stalk comparison shows. -/
instance sections_preservesFiniteColimits :
    PreservesFiniteColimits (EtaleCohomology.sections (Spec (.of R)) E) :=
  preservesFiniteColimits_of_natIso (stalkIso R E)

/-- Together with the existing finite-limit preservation, this gives
exactness of the same global-sections functor. -/
instance sections_preservesHomology :
    (EtaleCohomology.sections (Spec (.of R)) E).PreservesHomology := by
  infer_instance

/-- Every actual short exact sequence remains short exact on global
sections over the strictly henselian local ring. -/
theorem sections_map_shortExact
    (T : ShortComplex (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)))
    (hT : T.ShortExact) :
    (T.map (EtaleCohomology.sections (Spec (.of R)) E)).ShortExact :=
  hT.map_of_exact _

#print axioms identitySection
#print axioms identityNeighborhood
#print axioms pointedSection
#print axioms pointedSection_residue
#print axioms pointedSection_fiber
#print axioms identityNeighborhood_isInitial
#print axioms identityGermNatTrans_isIso
#print axioms presheafFiberIso
#print axioms presheafFiberIso_inv_app
#print axioms toPresheafFiber_presheafFiberIso_hom
#print axioms stalkIso
#print axioms stalkIso_inv_app
#print axioms toPresheafFiber_stalkIso_hom
#print axioms sections_preservesFiniteColimits
#print axioms sections_preservesHomology
#print axioms sections_map_shortExact

end PrimeGap182.TypeIII.StrictHenselianEtaleSections
