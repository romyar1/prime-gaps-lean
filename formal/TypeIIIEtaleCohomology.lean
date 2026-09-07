import TypeIIIEtaleDerivedDirectImage
import TypeIIIInjectiveResolutionAdditivity
import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# Actual global sections and their derived functors on the small étale site

The identity étale object is terminal.  Evaluation there is the actual
global-sections functor, naturally identified with the right adjoint of
the constant-sheaf functor.  Its right derived functors are computed by
the existing injective resolutions of actual module sheaves.

The final comparison identifies global sections after actual direct
image with global sections on the source.  It uses the second projection
of the literal pullback of the identity.  It asserts neither proper base
change nor a comparison with adic cohomology.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleCohomology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

variable (S : Scheme.{u})

/-- The original scheme, regarded as its identity étale object. -/
def terminalObject : S.Etale := Scheme.Etale.mk (𝟙 S)

set_option backward.isDefEq.respectTransparency false in
/-- Every étale object has its unique structural map to the identity object. -/
def terminal_isTerminal : IsTerminal (terminalObject S) := by
  refine IsTerminal.ofUniqueHom
    (fun U => MorphismProperty.Over.homMk U.hom (by
      change U.hom ≫ 𝟙 S = U.hom
      exact Category.comp_id _)) ?_
  intro U f
  apply MorphismProperty.Over.Hom.ext
  have h := MorphismProperty.Over.w f
  change f.left ≫ 𝟙 S = U.hom at h
  exact (Category.comp_id f.left).symm.trans h

variable (E : Type u) [Ring E]

/-- Global sections are literal evaluation of the actual sheaf at the identity étale object. -/
def sections : Sheaf S.smallEtaleTopology (ModuleCat.{u} E) ⥤ ModuleCat.{u} E :=
  sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} E) ⋙
    (evaluation S.Etaleᵒᵖ (ModuleCat.{u} E)).obj (op (Scheme.Etale.mk (𝟙 S)))

/-- The value is the original module of sections over the scheme itself. -/
theorem sections_obj (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :
    (sections S E).obj F = F.obj.obj (op (terminalObject S)) := rfl

/-- The map on sections is the original component of the sheaf morphism. -/
theorem sections_map {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)} (f : F ⟶ G) :
    (sections S E).map f = f.hom.app (op (terminalObject S)) := rfl

/-- These literal sections coincide naturally with the right adjoint of constant sheaves. -/
def gammaIso :
    Sheaf.Γ S.smallEtaleTopology (ModuleCat.{u} E) ≅ sections S E :=
  Sheaf.ΓNatIsoSheafSections S.smallEtaleTopology (ModuleCat.{u} E)
    (terminal_isTerminal S)

/-- Actual global sections preserve finite limits. -/
instance sections_preservesFiniteLimits : PreservesFiniteLimits (sections S E) := by
  dsimp only [sections]
  infer_instance

/-- Actual global sections are additive. -/
instance sections_additive : (sections S E).Additive := by
  dsimp only [sections]
  infer_instance

/-- Étale cohomology with fixed ring coefficients is the actual right derived functor of sections. -/
def functor (n : ℕ) :
    Sheaf S.smallEtaleTopology (ModuleCat.{u} E) ⥤ ModuleCat.{u} E :=
  (sections S E).rightDerived n

/-- This cohomology is computed by the existing actual injective resolution. -/
def objIsoHomology (n : ℕ) (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :
    (functor S E n).obj F ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} E) (ComplexShape.up ℕ) n).obj
        (((sections S E).mapHomologicalComplex _).obj
          (EtaleDerivedDirectImage.resolution S E F).cocomplex) :=
  (EtaleDerivedDirectImage.resolution S E F).isoRightDerivedObj (sections S E) n

/-- The canonical degree-zero identification with the same global sections. -/
def zeroIso : functor S E 0 ≅ sections S E :=
  (sections S E).rightDerivedZeroIsoSelf

/-- Its inverse is the canonical map from the original resolution augmentation. -/
theorem zeroIso_inv : (zeroIso S E).inv = (sections S E).toRightDerivedZero := rfl

/-- Each actual right derived global-sections functor is additive. -/
instance functor_additive (n : ℕ) : (functor S E n).Additive := by
  dsimp only [functor]
  infer_instance

/-- Actual injective sheaves have zero higher global cohomology. -/
theorem isZero_obj_injective_succ (n : ℕ)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) [Injective F] :
    IsZero ((functor S E (n + 1)).obj F) :=
  (sections S E).isZero_rightDerived_obj_injective_succ n F

section DirectImage

variable {X S : Scheme.{u}} (q : X ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- The actual base change of the identity object is the identity object by its second projection. -/
def baseChangeTerminalIso :
    (EtaleDirectImage.baseChange q).obj (terminalObject S) ≅ terminalObject X :=
  MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 S) q)) (by
    change pullback.snd (𝟙 S) q ≫ 𝟙 X = pullback.snd (𝟙 S) q
    exact Category.comp_id _)

/-- The forward comparison is literally the second scheme projection. -/
theorem baseChangeTerminalIso_hom_left :
    (baseChangeTerminalIso q).hom.left = pullback.snd (𝟙 S) q := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Global sections after actual direct image are canonically global sections on the source. -/
def directImageIso (q : X ⟶ S) (E : Type u) [Ring E] :
    EtaleDirectImage.functor q E ⋙ sections S E ≅ sections X E :=
  NatIso.ofComponents
    (fun F => F.obj.mapIso (baseChangeTerminalIso q).symm.op)
    (fun f => (f.hom.naturality (baseChangeTerminalIso q).inv.op).symm)

/-- The section comparison uses the inverse of the original second projection. -/
theorem directImageIso_hom_app (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) :
    (directImageIso q E).hom.app F = F.obj.map (baseChangeTerminalIso q).inv.op := rfl

/-- Its inverse is restriction along the original second projection. -/
theorem directImageIso_inv_app (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) :
    (directImageIso q E).inv.app F = F.obj.map (baseChangeTerminalIso q).hom.op := rfl

end DirectImage

#print axioms terminalObject
#print axioms terminal_isTerminal
#print axioms sections
#print axioms sections_obj
#print axioms sections_map
#print axioms gammaIso
#print axioms sections_preservesFiniteLimits
#print axioms sections_additive
#print axioms functor
#print axioms objIsoHomology
#print axioms zeroIso
#print axioms zeroIso_inv
#print axioms functor_additive
#print axioms isZero_obj_injective_succ
#print axioms baseChangeTerminalIso
#print axioms baseChangeTerminalIso_hom_left
#print axioms directImageIso
#print axioms directImageIso_hom_app
#print axioms directImageIso_inv_app

end PrimeGap182.TypeIII.EtaleCohomology
