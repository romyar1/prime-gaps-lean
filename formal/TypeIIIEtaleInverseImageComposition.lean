import TypeIIIEtaleInverseImage
import TypeIIIEtaleDirectImageComposition
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Composition of actual inverse images and the canonical base-change map

The existing inverse images are the proved left adjoints to the actual
small étale direct images.  Conjugation of their actual identity and
composition comparisons constructs the corresponding inverse-image
isomorphisms.

For a commuting scheme square, the actual direct-image square has a
mate g^* q_* → q'_* g'^*.  The component formula displays its unit,
the canonical direct-image comparison, and its counit.  The cartesian
specialization uses the literal scheme pullback.  No invertibility of
this mate, derived base-change theorem, or fiber-cohomology comparison
is asserted.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleInverseImage

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section Identity

variable (S : Scheme.{u}) (E : Type u) [Ring E]

/-- The actual identity inverse image, obtained from its proved adjunction. -/
def idIso : functor (𝟙 S) E ≅ 𝟭 _ :=
  ((conjugateIsoEquiv (adjunction (𝟙 S) E) (Adjunction.id (C :=
      Sheaf S.smallEtaleTopology (ModuleCat.{u} E)))).symm
    (EtaleDirectImage.idIso S E)).symm

/-- This isomorphism is conjugate to the actual direct-image identity comparison. -/
theorem idIso_conjugate :
    conjugateIsoEquiv (adjunction (𝟙 S) E)
        (Adjunction.id (C := Sheaf S.smallEtaleTopology (ModuleCat.{u} E)))
        (idIso S E).symm = EtaleDirectImage.idIso S E :=
  Equiv.apply_symm_apply _ _

end Identity

section Composition

variable {X S T : Scheme.{u}} (q : X ⟶ S) (r : S ⟶ T) (E : Type u) [Ring E]

/-- The composition of the actual inverse images is inverse image by the original composite. -/
def compIso : functor r E ⋙ functor q E ≅ functor (q ≫ r) E :=
  ((conjugateIsoEquiv ((adjunction r E).comp (adjunction q E))
      (adjunction (q ≫ r) E)).symm (EtaleDirectImage.compIso q r E)).symm

/-- The comparison uses the actual direct-image composition under the proved adjunctions. -/
theorem compIso_conjugate :
    conjugateIsoEquiv ((adjunction r E).comp (adjunction q E))
        (adjunction (q ≫ r) E) (compIso q r E).symm =
      EtaleDirectImage.compIso q r E :=
  Equiv.apply_symm_apply _ _

end Composition

section Congruence

variable {X S : Scheme.{u}} {q r : X ⟶ S} (h : q = r) (E : Type u) [Ring E]

/-- Equality of the original scheme maps gives the corresponding inverse-image comparison. -/
def congrIso : functor q E ≅ functor r E :=
  ((conjugateIsoEquiv (adjunction q E) (adjunction r E)).symm
    (EtaleDirectImage.congrIso h E)).symm

end Congruence

section Square

variable {X' X S' S : Scheme.{u}} (q : X ⟶ S) (g : S' ⟶ S)
  (q' : X' ⟶ S') (g' : X' ⟶ X) (h : g' ≫ q = q' ≫ g) (E : Type u) [Ring E]

/-- The two ordinary inverse-image composites of a commuting scheme square are isomorphic. -/
def squareIso : functor q E ⋙ functor g' E ≅ functor g E ⋙ functor q' E :=
  compIso g' q E ≪≫ congrIso h E ≪≫ (compIso q' g E).symm

/-- The actual base-change morphism, defined as the mate under the constructed adjunctions. -/
def baseChangeMap :
    EtaleDirectImage.functor q E ⋙ functor g E ⟶
      functor g' E ⋙ EtaleDirectImage.functor q' E :=
  ((mateEquiv (adjunction g' E) (adjunction g E)).symm
    (TwoSquare.mk _ _ _ _ (EtaleDirectImage.squareIso q g q' g' h E).hom)).natTrans

/-- Its component is the actual unit, square comparison, and counit composite. -/
theorem baseChangeMap_app (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) :
    (baseChangeMap q g q' g' h E).app F =
      (functor g E).map ((EtaleDirectImage.functor q E).map
        ((adjunction g' E).unit.app F)) ≫
      (functor g E).map ((EtaleDirectImage.squareIso q g q' g' h E).hom.app
        ((functor g' E).obj F)) ≫
      (adjunction g E).counit.app
        ((EtaleDirectImage.functor q' E).obj ((functor g' E).obj F)) := by
  simp [baseChangeMap, mateEquiv]

/-- Taking its mate recovers the original, proved direct-image square. -/
theorem baseChangeMap_mate :
    mateEquiv (adjunction g' E) (adjunction g E)
        (TwoSquare.mk _ _ _ _ (baseChangeMap q g q' g' h E)) =
      TwoSquare.mk _ _ _ _ (EtaleDirectImage.squareIso q g q' g' h E).hom :=
  Equiv.apply_symm_apply _ _

end Square

section ActualPullback

variable {X S' S : Scheme.{u}} (q : X ⟶ S) (g : S' ⟶ S) (E : Type u) [Ring E]

/-- Base change for the actual cartesian scheme square, with commutativity discharged. -/
def pullbackBaseChangeMap :
    EtaleDirectImage.functor q E ⋙ functor g E ⟶
      functor (pullback.fst q g) E ⋙ EtaleDirectImage.functor (pullback.snd q g) E :=
  baseChangeMap q g (pullback.snd q g) (pullback.fst q g)
    (pullback.condition (f := q) (g := g)) E

/-- The cartesian specialization uses the same actual unit and counit. -/
theorem pullbackBaseChangeMap_app
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) :
    (pullbackBaseChangeMap q g E).app F =
      (functor g E).map ((EtaleDirectImage.functor q E).map
        ((adjunction (pullback.fst q g) E).unit.app F)) ≫
      (functor g E).map ((EtaleDirectImage.pullbackSquareIso q g E).hom.app
        ((functor (pullback.fst q g) E).obj F)) ≫
      (adjunction g E).counit.app
        ((EtaleDirectImage.functor (pullback.snd q g) E).obj
          ((functor (pullback.fst q g) E).obj F)) :=
  baseChangeMap_app q g (pullback.snd q g) (pullback.fst q g)
    (pullback.condition (f := q) (g := g)) E F

end ActualPullback

end PrimeGap182.TypeIII.EtaleInverseImage

#print axioms PrimeGap182.TypeIII.EtaleInverseImage.idIso
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.idIso_conjugate
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.compIso
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.compIso_conjugate
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.congrIso
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.squareIso
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.baseChangeMap
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.baseChangeMap_app
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.baseChangeMap_mate
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.pullbackBaseChangeMap
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.pullbackBaseChangeMap_app
