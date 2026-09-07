import TypeIIIEtaleDirectImage
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Identity and composition for actual small étale direct image

The comparison maps are induced by the actual canonical isomorphisms
of scheme pullbacks.  A commuting square of scheme morphisms therefore
gives an isomorphism of the two composed direct-image functors.  No
functor-commutation isomorphism is supplied as a hypothesis.

The cartesian-square specialization uses the actual scheme pullback and
its proved commutativity.  This is a comparison of composed direct
images, not an invertibility assertion for an inverse-image base-change
mate or for a derived base-change morphism.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleDirectImage

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Base change by the identity is identified with the identity by the actual first projection. -/
def baseChangeIdIso (S : Scheme.{u}) : baseChange (𝟙 S) ≅ 𝟭 S.Etale :=
  NatIso.ofComponents
    (fun U => MorphismProperty.Over.isoMk
      (asIso (pullback.fst U.hom (𝟙 S))) (by
        change pullback.fst U.hom (𝟙 S) ≫ U.hom = pullback.snd U.hom (𝟙 S)
        simpa only [Category.comp_id] using (pullback.condition (f := U.hom) (g := 𝟙 S))))
    (by
      intro U V f
      apply MorphismProperty.Over.Hom.ext
      change pullback.lift _ _ _ ≫ pullback.fst V.hom (𝟙 S) =
        pullback.fst U.hom (𝟙 S) ≫ f.left
      rw [pullback.lift_fst])

/-- The identity comparison is literally the first projection of the scheme pullback. -/
theorem baseChangeIdIso_hom_app_left (S : Scheme.{u}) (U : S.Etale) :
    ((baseChangeIdIso S).hom.app U).left = pullback.fst U.hom (𝟙 S) := rfl

section Composition

variable {X S T : Scheme.{u}} (q : X ⟶ S) (r : S ⟶ T)

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual base change by a composite agrees with the iterated scheme pullback. -/
def baseChangeCompIso :
    baseChange (q ≫ r) ≅ baseChange r ⋙ baseChange q :=
  MorphismProperty.Over.pullbackComp (P := @AlgebraicGeometry.Etale) (Q := ⊤) q r

set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison preserves the actual projection to the original étale object. -/
theorem baseChangeCompIso_hom_fst_fst (U : T.Etale) :
    ((baseChangeCompIso q r).hom.app U).left ≫
        pullback.fst (pullback.snd U.hom r) q ≫ pullback.fst U.hom r =
      pullback.fst U.hom (q ≫ r) :=
  MorphismProperty.Over.pullbackComp_left_fst_fst q r U

end Composition

section Congruence

variable {X S : Scheme.{u}} {q r : X ⟶ S} (h : q = r)

set_option backward.isDefEq.respectTransparency.types false in
/-- Equality of the original scheme maps induces the actual pullback comparison. -/
def baseChangeCongrIso : baseChange q ≅ baseChange r :=
  MorphismProperty.Over.pullbackCongr (P := @AlgebraicGeometry.Etale) (Q := ⊤) h

set_option backward.isDefEq.respectTransparency.types false in
/-- The equality-induced comparison preserves the actual projection. -/
theorem baseChangeCongrIso_hom_fst (U : S.Etale) :
    ((baseChangeCongrIso h).hom.app U).left ≫ pullback.fst U.hom r =
      pullback.fst U.hom q :=
  MorphismProperty.Over.pullbackCongr_hom_app_left_fst h U

end Congruence

section Square

variable {X' X S' S : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
  (f' : X' ⟶ S') (g' : X' ⟶ X) (h : g' ≫ f = f' ≫ g)

/-- A commuting scheme square gives the actual comparison of iterated base-change categories. -/
def baseChangeSquareIso :
    baseChange f ⋙ baseChange g' ≅ baseChange g ⋙ baseChange f' :=
  (baseChangeCompIso g' f).symm ≪≫ baseChangeCongrIso h ≪≫ baseChangeCompIso f' g

end Square

section Sheaves

/-- Actual direct image by the identity is canonically the identity functor. -/
def idIso (S : Scheme.{u}) (E : Type u) [Ring E] : functor (𝟙 S) E ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (baseChangeIdIso S) (ModuleCat.{u} E)
    S.smallEtaleTopology

end Sheaves

section SheafComposition

variable {X S T : Scheme.{u}} (q : X ⟶ S) (r : S ⟶ T) (E : Type u) [Ring E]

/-- Composition of actual direct images agrees with direct image by the original composite. -/
def compIso : functor q E ⋙ functor r E ≅ functor (q ≫ r) E :=
  Functor.sheafPushforwardContinuousComp' (baseChangeCompIso q r).symm
    (ModuleCat.{u} E) T.smallEtaleTopology S.smallEtaleTopology X.smallEtaleTopology

/-- On sections, this comparison is restriction along the canonical composite-pullback map. -/
theorem compIso_hom_app_hom_app
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) (U : T.Etale) :
    ((compIso q r E).hom.app F).hom.app (op U) =
      F.obj.map ((baseChangeCompIso q r).hom.app U).op := rfl

/-- The inverse section map uses the inverse of that same canonical pullback comparison. -/
theorem compIso_inv_app_hom_app
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) (U : T.Etale) :
    ((compIso q r E).inv.app F).hom.app (op U) =
      F.obj.map ((baseChangeCompIso q r).inv.app U).op := rfl

end SheafComposition

section SheafCongruence

variable {X S : Scheme.{u}} {q r : X ⟶ S} (h : q = r) (E : Type u) [Ring E]

/-- Equality of scheme maps induces the canonical isomorphism of actual direct images. -/
def congrIso : functor q E ≅ functor r E :=
  Functor.sheafPushforwardContinuousIso (baseChangeCongrIso h) (ModuleCat.{u} E)
    S.smallEtaleTopology X.smallEtaleTopology

/-- Its section map is induced by the actual equality comparison of scheme pullbacks. -/
theorem congrIso_hom_app_hom_app
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) (U : S.Etale) :
    ((congrIso h E).hom.app F).hom.app (op U) =
      F.obj.map ((baseChangeCongrIso h).inv.app U).op := rfl

end SheafCongruence

section SheafSquare

variable {X' X S' S : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
  (f' : X' ⟶ S') (g' : X' ⟶ X) (h : g' ≫ f = f' ≫ g) (E : Type u) [Ring E]

/-- The two composed direct images of a commuting square are canonically isomorphic. -/
def squareIso : functor g' E ⋙ functor f E ≅ functor f' E ⋙ functor g E :=
  compIso g' f E ≪≫ congrIso h E ≪≫ (compIso f' g E).symm

end SheafSquare

section ActualPullback

variable {X S' S : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (E : Type u) [Ring E]

/-- Specialization to the actual cartesian scheme square, with its commutativity discharged. -/
def pullbackSquareIso :
    functor (pullback.fst f g) E ⋙ functor f E ≅
      functor (pullback.snd f g) E ⋙ functor g E :=
  squareIso f g (pullback.snd f g) (pullback.fst f g)
    (pullback.condition (f := f) (g := g)) E

end ActualPullback

end PrimeGap182.TypeIII.EtaleDirectImage

#print axioms PrimeGap182.TypeIII.EtaleDirectImage.baseChangeIdIso
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.baseChangeIdIso_hom_app_left
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.baseChangeCompIso
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.baseChangeCompIso_hom_fst_fst
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.baseChangeCongrIso
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.baseChangeCongrIso_hom_fst
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.baseChangeSquareIso
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.idIso
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.compIso
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.compIso_hom_app_hom_app
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.compIso_inv_app_hom_app
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.congrIso
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.congrIso_hom_app_hom_app
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.squareIso
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.pullbackSquareIso
