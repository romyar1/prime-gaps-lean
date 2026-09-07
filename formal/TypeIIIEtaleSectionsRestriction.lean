import TypeIIIEtaleInverseImageStalk
import TypeIIIEtaleCohomology
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Original restriction of sections and its geometric germs

Restriction along an arbitrary scheme morphism is the actual inverse-image
unit followed by the original direct-image comparison for global sections.
Its compatibility with germs is proved using the actual skyscraper
adjunction: the comapped point's skyscraper is the direct image of the
original point's skyscraper.  No stalk-comparison premise is imposed.

The final equality lemma is ordinary separatedness of an actual module
sheaf on a covering family, expressed for elements of its section modules.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleSectionsRestriction

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry Opposite

variable {Z X : Scheme.{u}} (i : Z ⟶ X) (E : Type u) [Ring E]

/-- The original restriction on global sections, through the actual
inverse-image unit and the original direct-image section comparison. -/
def map :
    EtaleCohomology.sections X E ⟶
      EtaleInverseImage.functor i E ⋙ EtaleCohomology.sections Z E :=
  (EtaleCohomology.sections X E).leftUnitor.inv ≫
    Functor.whiskerRight (EtaleInverseImage.adjunction i E).unit
      (EtaleCohomology.sections X E) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (EtaleInverseImage.functor i E)
      (EtaleCohomology.directImageIso i E).hom

/-- The component retains precisely the original unit and comparison. -/
theorem map_app (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) :
    (map i E).app F =
      (EtaleCohomology.sections X E).map
          ((EtaleInverseImage.adjunction i E).unit.app F) ≫
        (EtaleCohomology.directImageIso i E).hom.app
          ((EtaleInverseImage.functor i E).obj F) := by
  simp only [map, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Equality after restriction already holds under the literal unit
component, because the remaining section comparison is an isomorphism. -/
theorem unit_component_eq_of_map_eq
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E))
    (s t : (EtaleCohomology.sections X E).obj F)
    (h : (map i E).app F s = (map i E).app F t) :
    ((EtaleInverseImage.adjunction i E).unit.app F).hom.app
        (op (EtaleCohomology.terminalObject X)) s =
      ((EtaleInverseImage.adjunction i E).unit.app F).hom.app
        (op (EtaleCohomology.terminalObject X)) t := by
  let e := (EtaleCohomology.directImageIso i E).app
    ((EtaleInverseImage.functor i E).obj F)
  have h' : e.hom ((EtaleCohomology.sections X E).map
      ((EtaleInverseImage.adjunction i E).unit.app F) s) =
      e.hom ((EtaleCohomology.sections X E).map
        ((EtaleInverseImage.adjunction i E).unit.app F) t) := by
    rw [map_app] at h
    change e.hom ((EtaleCohomology.sections X E).map
        ((EtaleInverseImage.adjunction i E).unit.app F) s) =
      e.hom ((EtaleCohomology.sections X E).map
        ((EtaleInverseImage.adjunction i E).unit.app F) t) at h
    exact h
  have he := congrArg (fun x => e.inv x) h'
  change (EtaleCohomology.sections X E).map
      ((EtaleInverseImage.adjunction i E).unit.app F) s =
    (EtaleCohomology.sections X E).map
      ((EtaleInverseImage.adjunction i E).unit.app F) t
  simpa only [ModuleCat.inv_hom_apply] using he

section Germs

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Z)

set_option backward.isDefEq.respectTransparency false in
/-- The original skyscraper unit transposed along the actual inverse-image
adjunction.  The two target skyscrapers agree by literal precomposition. -/
def comapSkyscraperLift (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) :
    (EtaleInverseImage.functor i E).obj F ⟶
      (Scheme.pointSmallEtale s).skyscraperSheaf
        ((EtaleInverseImage.geometricPointComap i s).sheafFiber
          (A := ModuleCat.{u} E) |>.obj F) :=
  ((EtaleInverseImage.adjunction i E).homEquiv F _).symm
    ((EtaleInverseImage.geometricPointComap i s).skyscraperSheafAdjunction.unit.app F)

set_option backward.isDefEq.respectTransparency false in
/-- The transposed map factors the original skyscraper unit through the
original inverse-image unit. -/
theorem unit_comapSkyscraperLift
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) :
    (EtaleInverseImage.adjunction i E).unit.app F ≫
        (EtaleDirectImage.functor i E).map (comapSkyscraperLift i E s F) =
      (EtaleInverseImage.geometricPointComap i s).skyscraperSheafAdjunction.unit.app F :=
  ((EtaleInverseImage.adjunction i E).homEquiv F _).apply_symm_apply _

/-- Evaluation of the transposed skyscraper map at a pointed étale
neighborhood, with values in the original comapped-point stalk. -/
def comapGermLift (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E))
    (U : X.Etale) (t : (EtaleInverseImage.geometricPointComap i s).fiber.obj U) :
    ((EtaleInverseImage.functor i E).obj F).obj.obj
        (op ((EtaleDirectImage.baseChange i).obj U)) ⟶
      (EtaleInverseImage.geometricPointComap i s).sheafFiber.obj F :=
  (comapSkyscraperLift i E s F).hom.app (op ((EtaleDirectImage.baseChange i).obj U)) ≫
    Pi.π _ t

set_option backward.isDefEq.respectTransparency false in
/-- The factorization gives the original colimit germ, with its literal
normalization and pointed-neighborhood index. -/
theorem unit_comapGermLift (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E))
    (U : X.Etale) (t : (EtaleInverseImage.geometricPointComap i s).fiber.obj U) :
    ((EtaleInverseImage.adjunction i E).unit.app F).hom.app (op U) ≫
        comapGermLift i E s F U t =
      (EtaleInverseImage.geometricPointComap i s).toPresheafFiber U t F.obj := by
  let Ψ := EtaleInverseImage.geometricPointComap i s
  have h := congrArg (fun f => f.hom.app (op U))
    (unit_comapSkyscraperLift i E s F)
  have hπ := congrArg (fun f => f ≫ Pi.π
    (fun _ : Ψ.fiber.obj U => Ψ.sheafFiber.obj F) t) h
  change ((EtaleInverseImage.adjunction i E).unit.app F).hom.app (op U) ≫
      (comapSkyscraperLift i E s F).hom.app
        (op ((EtaleDirectImage.baseChange i).obj U)) ≫ Pi.π _ t = _
  rw [← assoc]
  trans (Ψ.skyscraperSheafAdjunction.unit.app F).hom.app (op U) ≫ Pi.π _ t
  · exact hπ
  · rw [← Ψ.skyscraperSheafAdjunction.homEquiv_id F]
    erw [Ψ.skyscraperSheafAdjunction_homEquiv_apply_hom]
    erw [Ψ.skyscraperPresheafHomEquiv_app_π, comp_id]
    rfl

/-- Equality under an original unit component implies equality of the
original germs, without postulating a compatible stalk isomorphism. -/
theorem comapGerm_eq_of_unit_component_eq
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E))
    (U : X.Etale) (t : (EtaleInverseImage.geometricPointComap i s).fiber.obj U)
    (a b : F.obj.obj (op U))
    (h : ((EtaleInverseImage.adjunction i E).unit.app F).hom.app (op U) a =
      ((EtaleInverseImage.adjunction i E).unit.app F).hom.app (op U) b) :
    (EtaleInverseImage.geometricPointComap i s).toPresheafFiber U t F.obj a =
      (EtaleInverseImage.geometricPointComap i s).toPresheafFiber U t F.obj b := by
  have ha := congrArg (fun f => f a) (unit_comapGermLift i E s F U t)
  have hb := congrArg (fun f => f b) (unit_comapGermLift i E s F U t)
  exact ha.symm.trans ((congrArg (comapGermLift i E s F U t) h).trans hb)

end Germs

section Cover

omit i in
/-- Elements of an actual module sheaf agree if they agree on an actual
covering family.  This is sheaf separatedness using free rank-one maps. -/
theorem section_ext_of_cover
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E))
    {U : X.Etale} {ι : Type*} {V : ι → X.Etale} (f : ∀ j, V j ⟶ U)
    (hf : Sieve.ofArrows V f ∈ X.smallEtaleTopology U)
    (s t : F.obj.obj (op U))
    (h : ∀ j, F.obj.map (f j).op s = F.obj.map (f j).op t) : s = t := by
  let a : ModuleCat.of E E ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton E _ s)
  let b : ModuleCat.of E E ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton E _ t)
  have hab : a = b := F.property.hom_ext_ofArrows f hf (fun j => by
    apply ConcreteCategory.hom_ext
    intro r
    change F.obj.map (f j).op (r • s) = F.obj.map (f j).op (r • t)
    simp only [map_smul, h j])
  have hab₁ := congrArg (fun f => f (1 : E)) hab
  change (1 : E) • s = (1 : E) • t at hab₁
  simpa only [one_smul] using hab₁

end Cover

#print axioms map
#print axioms map_app
#print axioms unit_component_eq_of_map_eq
#print axioms comapSkyscraperLift
#print axioms unit_comapSkyscraperLift
#print axioms comapGermLift
#print axioms unit_comapGermLift
#print axioms comapGerm_eq_of_unit_component_eq
#print axioms section_ext_of_cover

end PrimeGap182.TypeIII.EtaleSectionsRestriction
