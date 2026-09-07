import TypeIIIEtaleInverseImageStalk
import Mathlib.CategoryTheory.Sites.Point.Presheaf

/-!
# The identity geometric stalk over a separably closed field

The actual identity geometric point of `Spec Ω` has an initial étale
neighborhood: the identity étale object with its identity section.
Consequently the original germ map identifies its presheaf fiber with
evaluation at that object.  Restricting this comparison to sheaves
identifies the actual stalk with global sections.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleClosedFieldSections

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- The identity section in the actual fiber of the identity étale object. -/
def identitySection :
    (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.obj
      (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) :=
  Over.homMk (𝟙 (Spec (.of Ω))) (by simp)

/-- The actual identity étale neighborhood with its identity geometric section. -/
def identityNeighborhood :
    (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.Elements :=
  ⟨Scheme.Etale.mk (𝟙 (Spec (.of Ω))), identitySection Ω⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every pointed étale neighborhood receives a unique map from the identity neighborhood. -/
def identityNeighborhood_isInitial : IsInitial (identityNeighborhood Ω) := by
  refine IsInitial.ofUniqueHom (fun V => ?_) ?_
  · refine ⟨MorphismProperty.Over.Hom.mk V.2 trivial, ?_⟩
    change (𝟙 _) ≫ V.2 = V.2
    exact Category.id_comp _
  · intro V m
    apply Subtype.ext
    apply MorphismProperty.Over.Hom.ext
    have hm := m.2
    change (𝟙 _) ≫ (Scheme.Etale.forget (Spec (.of Ω))).map m.1 = V.2 at hm
    rw [Category.id_comp] at hm
    exact congrArg (fun f => f.left) hm

variable (E : Type u) [Ring E]

set_option backward.isDefEq.respectTransparency false in
/-- The original germ at the identity neighborhood is a natural isomorphism. -/
instance identityGermNatTrans_isIso :
    IsIso ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiberNatTrans
      (A := ModuleCat.{u} E) (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
      (identitySection Ω)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro P
  exact ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).isColimitPresheafFiberCocone P).isIso_ι_app_of_isTerminal
      (op (identityNeighborhood Ω))
      (identityNeighborhood_isInitial Ω).op

/-- The actual identity-point presheaf fiber is evaluation on the identity étale object. -/
def presheafFiberIso :
    (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).presheafFiber (A := ModuleCat.{u} E) ≅
      (evaluation (Spec (.of Ω)).Etaleᵒᵖ (ModuleCat.{u} E)).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))) :=
  (asIso ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiberNatTrans
    (A := ModuleCat.{u} E) (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
    (identitySection Ω))).symm

/-- The inverse comparison is the existing germ map, without a new choice of comparison. -/
theorem presheafFiberIso_inv_app (P : (Spec (.of Ω)).Etaleᵒᵖ ⥤ ModuleCat.{u} E) :
    (presheafFiberIso Ω E).inv.app P =
      (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
        (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) (identitySection Ω) P := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Any germ is evaluated by restricting its section along the actual geometric section. -/
@[reassoc]
theorem toPresheafFiber_presheafFiberIso_hom
    (U : (Spec (.of Ω)).Etale)
    (t : (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.obj U)
    (P : (Spec (.of Ω)).Etaleᵒᵖ ⥤ ModuleCat.{u} E) :
    (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
        (A := ModuleCat.{u} E) U t P ≫
        (presheafFiberIso Ω E).hom.app P =
      P.map (MorphismProperty.Over.Hom.mk
        (A := Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) (B := U) t trivial).op := by
  have ht : (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.map
      (MorphismProperty.Over.Hom.mk
        (A := Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) (B := U) t trivial) (identitySection Ω) = t := by
    change (𝟙 _) ≫ t = t
    exact Category.id_comp _
  have hw := (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber_w
    (A := ModuleCat.{u} E)
    (MorphismProperty.Over.Hom.mk
      (A := Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) (B := U) t trivial) (identitySection Ω) P
  rw [ht] at hw
  rw [← hw, Category.assoc, ← presheafFiberIso_inv_app, Iso.inv_hom_id_app]
  erw [Category.comp_id]

/-- The actual identity geometric stalk is evaluation at the terminal étale object. -/
def stalkIso :
    (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber (A := ModuleCat.{u} E) ≅
      sheafToPresheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u} E) ⋙
        (evaluation (Spec (.of Ω)).Etaleᵒᵖ (ModuleCat.{u} E)).obj
          (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))) :=
  Functor.isoWhiskerLeft (sheafToPresheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u} E))
    (presheafFiberIso Ω E)

/-- The inverse sheaf comparison is the original germ at the identity section. -/
theorem stalkIso_inv_app
    (F : Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u} E)) :
    (stalkIso Ω E).inv.app F =
      (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
        (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) (identitySection Ω) F.obj := rfl

set_option backward.isDefEq.respectTransparency false in
/-- On any actual étale neighborhood, the sheaf comparison restricts along its geometric section. -/
@[reassoc]
theorem toPresheafFiber_stalkIso_hom
    (U : (Spec (.of Ω)).Etale)
    (t : (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.obj U)
    (F : Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u} E)) :
    (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
        (A := ModuleCat.{u} E) U t F.obj ≫ (stalkIso Ω E).hom.app F =
      F.obj.map (MorphismProperty.Over.Hom.mk
        (A := Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) (B := U) t trivial).op :=
  toPresheafFiber_presheafFiberIso_hom Ω E U t F.obj

/-- Global sections over the separably closed field preserve finite limits. -/
instance sections_preservesFiniteLimits :
    PreservesFiniteLimits
      (sheafToPresheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u} E) ⋙
        (evaluation (Spec (.of Ω)).Etaleᵒᵖ (ModuleCat.{u} E)).obj
          (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))) :=
  preservesFiniteLimits_of_natIso (stalkIso Ω E)

/-- Global sections over the separably closed field preserve finite colimits. -/
instance sections_preservesFiniteColimits :
    PreservesFiniteColimits
      (sheafToPresheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u} E) ⋙
        (evaluation (Spec (.of Ω)).Etaleᵒᵖ (ModuleCat.{u} E)).obj
          (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))) :=
  preservesFiniteColimits_of_natIso (stalkIso Ω E)

/-- These actual global sections are additive. -/
instance sections_additive :
    (sheafToPresheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u} E) ⋙
      (evaluation (Spec (.of Ω)).Etaleᵒᵖ (ModuleCat.{u} E)).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))).Additive := by
  infer_instance

/-- The proved exactness implies preservation of homology. -/
instance sections_preservesHomology :
    (sheafToPresheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u} E) ⋙
      (evaluation (Spec (.of Ω)).Etaleᵒᵖ (ModuleCat.{u} E)).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))).PreservesHomology := by
  infer_instance

/-- Every actual short exact sequence remains short exact on global sections over this field. -/
theorem sections_map_shortExact
    (T : ShortComplex (Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u} E)))
    (hT : T.ShortExact) :
    (T.map
      (sheafToPresheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u} E) ⋙
        (evaluation (Spec (.of Ω)).Etaleᵒᵖ (ModuleCat.{u} E)).obj
          (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))))).ShortExact :=
  hT.map_of_exact _

#print axioms identitySection
#print axioms identityNeighborhood
#print axioms identityNeighborhood_isInitial
#print axioms identityGermNatTrans_isIso
#print axioms presheafFiberIso
#print axioms presheafFiberIso_inv_app
#print axioms toPresheafFiber_presheafFiberIso_hom
#print axioms stalkIso
#print axioms stalkIso_inv_app
#print axioms toPresheafFiber_stalkIso_hom
#print axioms sections_preservesFiniteLimits
#print axioms sections_preservesFiniteColimits
#print axioms sections_additive
#print axioms sections_preservesHomology
#print axioms sections_map_shortExact

end PrimeGap182.TypeIII.EtaleClosedFieldSections
