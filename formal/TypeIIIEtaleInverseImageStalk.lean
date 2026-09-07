import TypeIIIEtaleInverseImage
import TypeIIIAlgebraicallyClosedEtalePoints
import Mathlib.CategoryTheory.Sites.Point.Comap
import Mathlib.CategoryTheory.Sites.Point.Category
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Geometric stalks and exactness of actual étale inverse image

For q : X → S and a separably closed geometric point s of X, the
pullback universal property identifies the fiber of U ×[S] X at s
with the fiber of U at s ≫ q. This proves the necessary initial
smallness and identifies the actual site points. The canonical
adjunction comparison then gives (q^* F)_s ≅ F_(s ≫ q).

The actual conservative family of geometric points proves finite-limit
preservation. Together with the constructed left adjunction this gives
exact inverse image on module sheaves for any coefficient ring.
No stalk, smallness, adjunction, or exactness premise is supplied.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleInverseImage

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Classical

variable {X S : Scheme.{u}} (q : X ⟶ S)

section GeometricPoint

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)

set_option backward.isDefEq.respectTransparency false in
/-- Actual points of the fiber product over s are precisely points of
the original étale neighborhood over the composed geometric point. -/
def geometricFiberEquiv (U : S.Etale) :
    (EtaleDirectImage.baseChange q ⋙ (Scheme.pointSmallEtale s).fiber).obj U ≃
      (Scheme.pointSmallEtale (s ≫ q)).fiber.obj U where
  toFun t := Over.homMk (t.left ≫ pullback.fst U.hom q) (by
    have ht : t.left ≫ pullback.snd U.hom q = s := Over.w t
    change (t.left ≫ pullback.fst U.hom q) ≫ U.hom = s ≫ q
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht])
  invFun t := Over.homMk (pullback.lift t.left s (Over.w t)) (by
    change pullback.lift t.left s (Over.w t) ≫ pullback.snd U.hom q = s
    simp)
  left_inv t := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp
    · have ht : t.left ≫ pullback.snd U.hom q = s := Over.w t
      simpa using ht.symm
  right_inv t := by
    apply Over.OverMorphism.ext
    simp

/-- The forward geometric comparison is the actual first projection. -/
theorem geometricFiberEquiv_left (U : S.Etale)
    (t : (EtaleDirectImage.baseChange q ⋙ (Scheme.pointSmallEtale s).fiber).obj U) :
    (geometricFiberEquiv q s U t).left = t.left ≫ pullback.fst U.hom q := rfl

/-- The inverse geometric comparison is the actual pullback lift. -/
theorem geometricFiberEquiv_symm_left (U : S.Etale)
    (t : (Scheme.pointSmallEtale (s ≫ q)).fiber.obj U) :
    ((geometricFiberEquiv q s U).symm t).left =
      pullback.lift t.left s (Over.w t) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The pullback comparison is natural in the actual étale neighborhood. -/
def geometricFiberIso :
    EtaleDirectImage.baseChange q ⋙ (Scheme.pointSmallEtale s).fiber ≅
      (Scheme.pointSmallEtale (s ≫ q)).fiber :=
  NatIso.ofComponents (fun U => (geometricFiberEquiv q s U).toIso) (by
    intro U V f
    apply ConcreteCategory.hom_ext
    intro t
    apply Over.OverMorphism.ext
    change (t.left ≫ ((EtaleDirectImage.baseChange q).map f).left) ≫
        pullback.fst V.hom q =
      (t.left ≫ pullback.fst U.hom q) ≫ f.left
    simp [EtaleDirectImage.baseChange, MorphismProperty.Over.pullback])

/-- The actual categories indexing geometric fibers are equivalent. -/
def geometricFiberElementsEquiv :
    (EtaleDirectImage.baseChange q ⋙ (Scheme.pointSmallEtale s).fiber).Elements ≌
      (Scheme.pointSmallEtale (s ≫ q)).fiber.Elements :=
  (CategoryOfElements.structuredArrowEquivalence _).trans
    ((StructuredArrow.mapNatIso (geometricFiberIso q s)).trans
      (CategoryOfElements.structuredArrowEquivalence _).symm)

/-- Initial smallness comes from the existing composed geometric point,
transported through the proved category-of-elements equivalence. -/
instance geometricFiber_initiallySmall :
    InitiallySmall.{u}
      (EtaleDirectImage.baseChange q ⋙ (Scheme.pointSmallEtale s).fiber).Elements :=
  initiallySmall_of_initial_of_initiallySmall (geometricFiberElementsEquiv q s).inverse

/-- The actual comapped point of the original small étale site. -/
def geometricPointComap : GrothendieckTopology.Point.{u} S.smallEtaleTopology :=
  (Scheme.pointSmallEtale s).comap (EtaleDirectImage.baseChange q)
    (EtaleDirectImage.baseChange_coverPreserving q)

/-- The comapped site point is the actual composed geometric point;
the opposite variance of point morphisms is included explicitly. -/
def geometricPointComapIso :
    geometricPointComap q s ≅ Scheme.pointSmallEtale (s ≫ q) where
  hom := ⟨(geometricFiberIso q s).inv⟩
  inv := ⟨(geometricFiberIso q s).hom⟩
  hom_inv_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (geometricFiberIso q s).hom_inv_id
  inv_hom_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (geometricFiberIso q s).inv_hom_id

end GeometricPoint

section Stalks

variable (E : Type u) [Ring E]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)

/-- The actual isomorphism of site points induces the corresponding
isomorphism on module-valued stalk functors. -/
def geometricPointComapStalkIso :
    (geometricPointComap q s).sheafFiber (A := ModuleCat.{u} E) ≅
      (Scheme.pointSmallEtale (s ≫ q)).sheafFiber where
  hom := (geometricPointComapIso q s).inv.sheafFiber
  inv := (geometricPointComapIso q s).hom.sheafFiber
  hom_inv_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, Iso.hom_inv_id,
      GrothendieckTopology.Point.Hom.sheafFiber_id]
  inv_hom_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, Iso.inv_hom_id,
      GrothendieckTopology.Point.Hom.sheafFiber_id]

/-- The actual inverse-image stalk is the stalk at the composed
geometric point, via the proved site adjunction and pullback diagram. -/
def stalkIso :
    functor q E ⋙ (Scheme.pointSmallEtale s).sheafFiber ≅
      (Scheme.pointSmallEtale (s ≫ q)).sheafFiber :=
  ((Scheme.pointSmallEtale s).sheafFiberComapIso (EtaleDirectImage.baseChange q)
      (EtaleDirectImage.baseChange_coverPreserving q) (ModuleCat.{u} E)).symm ≪≫
    geometricPointComapStalkIso q E s

/-- Inverse image followed by an actual geometric stalk preserves
finite limits, by its identification with the composed geometric stalk. -/
theorem stalkComposite_preservesFiniteLimits :
    PreservesFiniteLimits (functor q E ⋙ (Scheme.pointSmallEtale s).sheafFiber) :=
  preservesFiniteLimits_of_natIso (stalkIso q E s).symm

end Stalks

section Exactness

variable (E : Type u) [Ring E]

/-- Actual inverse image preserves finite limits, detected by the
proved conservative family of algebraically closed geometric points. -/
instance functor_preservesFiniteLimits : PreservesFiniteLimits (functor q E) where
  preservesFiniteLimits J _ _ := by
    constructor
    intro K
    refine ⟨fun {c} hc => ⟨?_⟩⟩
    apply ((algebraicClosureEtalePoints_isConservative X).jointlyReflectIsomorphisms
      (ModuleCat.{u} E)).jointlyReflectsLimit
    intro Φ
    apply Classical.choice
    rcases Φ with ⟨_, ⟨s⟩⟩
    let : PreservesFiniteLimits
        (functor q E ⋙ (algebraicClosureEtalePoint X s).sheafFiber) :=
      stalkComposite_preservesFiniteLimits q E (algebraicClosureEtalePointMap X s)
    exact ⟨isLimitOfPreserves
      (functor q E ⋙ (algebraicClosureEtalePoint X s).sheafFiber) hc⟩

/-- The actual inverse-image functor is additive. -/
instance functor_additive : (functor q E).Additive := by
  let : HasFiniteProducts (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) := inferInstance
  let : HasBinaryProducts (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :=
    hasLimitsOfShape_discrete (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) WalkingPair
  exact Functor.additive_of_preserves_binary_products
    (C := Sheaf S.smallEtaleTopology (ModuleCat.{u} E))
    (D := Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) (functor q E)

/-- The proved finite-limit and finite-colimit preservation imply
preservation of homology for the actual inverse image. -/
instance functor_preservesHomology : (functor q E).PreservesHomology := inferInstance

/-- Every actual short exact sequence remains short exact under inverse image. -/
theorem map_shortExact
    (T : ShortComplex (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)))
    (hT : T.ShortExact) : (T.map (functor q E)).ShortExact :=
  hT.map_of_exact (functor q E)

end Exactness

end PrimeGap182.TypeIII.EtaleInverseImage

#print axioms PrimeGap182.TypeIII.EtaleInverseImage.geometricFiberEquiv
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.geometricFiberEquiv_left
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.geometricFiberEquiv_symm_left
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.geometricFiberIso
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.geometricFiberElementsEquiv
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.geometricFiber_initiallySmall
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.geometricPointComap
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.geometricPointComapIso
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.geometricPointComapStalkIso
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.stalkIso
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.stalkComposite_preservesFiniteLimits
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.functor_preservesFiniteLimits
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.functor_additive
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.functor_preservesHomology
#print axioms PrimeGap182.TypeIII.EtaleInverseImage.map_shortExact
