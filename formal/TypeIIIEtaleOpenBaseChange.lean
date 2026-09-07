import TypeIIIEtaleRestrictionInverseImage
import TypeIIIEtaleInverseImageComposition
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# The actual base-change map along an open immersion

For a monomorphic étale base change, the existing canonical mate is
an isomorphism.  The proof uses its original unit/comparison/counit
formula.  After identifying inverse image with literal restriction,
the relevant unit maps are restrictions along actual pullback
projections that admit inverses.  Their factorization through the
pulled-back open is given by a literal scheme pullback lift.

The result holds for modules over any coefficient ring and for an
arbitrary original scheme morphism.  It asserts ordinary open base
change; it makes no proper base-change or fiber-cohomology claim.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace PrimeGap182.TypeIII.EtaleOpenBaseChange

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

section PullbackFactor

variable {V U S : Scheme.{u}} (f : V ⟶ S) (j : U ⟶ S) [Mono j]

/-- Pulling a monomorphism back along a map that factors through it
gives an invertible first projection. -/
theorem pullback_fst_isIso_of_factor (a : V ⟶ U) (ha : a ≫ j = f) :
    IsIso (pullback.fst f j) := by
  subst f
  infer_instance

end PullbackFactor

section SiteAdjunction

variable (S : Scheme.{u}) (U : S.Etale) [Mono U.hom]

set_option backward.isDefEq.respectTransparency.types false in
/-- At an étale object whose structure map factors through the open,
the actual postcomposition/base-change counit is an isomorphism. -/
theorem postcomposition_counit_isIso_of_factor (V : S.Etale)
    (a : V.left ⟶ U.left) (ha : a ≫ U.hom = V.hom) :
    IsIso ((EtaleRestrictionInverseImage.postcompositionAdjunction S U).counit.app V) := by
  let : IsIso (pullback.fst V.hom U.hom) :=
    pullback_fst_isIso_of_factor V.hom U.hom a ha
  let : IsIso ((Scheme.Etale.forget S ⋙ Over.forget S).map
      ((EtaleRestrictionInverseImage.postcompositionAdjunction S U).counit.app V)) := by
    change IsIso (pullback.fst V.hom U.hom)
    infer_instance
  exact isIso_of_reflects_iso _ (Scheme.Etale.forget S ⋙ Over.forget S)

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual site unit is invertible for a monomorphic étale structure map. -/
theorem postcomposition_unit_isIso (V : U.left.Etale) :
    IsIso ((EtaleRestrictionInverseImage.postcompositionAdjunction S U).unit.app V) := by
  let η := (EtaleRestrictionInverseImage.postcompositionAdjunction S U).unit.app V
  have hη : η.left ≫ pullback.fst (V.hom ≫ U.hom) U.hom = 𝟙 V.left := by
    change pullback.lift _ _ _ ≫ pullback.fst _ _ = 𝟙 _
    exact pullback.lift_fst _ _ _
  have hηiso : IsIso η.left := by
    refine ⟨⟨pullback.fst (V.hom ≫ U.hom) U.hom, hη, ?_⟩⟩
    apply (cancel_mono (pullback.fst (V.hom ≫ U.hom) U.hom)).mp
    simp only [Category.assoc, hη, Category.id_comp]
    exact Category.comp_id _
  let : IsIso ((Scheme.Etale.forget U.left ⋙ Over.forget U.left).map η) := hηiso
  exact isIso_of_reflects_iso η (Scheme.Etale.forget U.left ⋙ Over.forget U.left)

variable (E : Type u) [Ring E]

/-- Literal open restriction followed by direct image has an invertible counit. -/
theorem restriction_counit_isIso
    (F : Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E)) :
    IsIso ((EtaleRestrictionInverseImage.restrictionAdjunction S U E).counit.app F) := by
  let α := (EtaleRestrictionInverseImage.restrictionAdjunction S U E).counit.app F
  let : ∀ V : U.left.Etaleᵒᵖ, IsIso (α.hom.app V) := fun V => by
    change IsIso (((EtaleRestrictionInverseImage.restrictionAdjunction S U E).counit.app
      F).hom.app (op V.unop))
    rw [EtaleRestrictionInverseImage.restrictionAdjunction_counit_app_hom_app]
    let : IsIso ((EtaleRestrictionInverseImage.postcompositionAdjunction S U).unit.app
      V.unop) := postcomposition_unit_isIso S U V.unop
    exact F.obj.map_isIso _
  exact (ObjectProperty.isIso_hom_iff α).mp (NatIso.isIso_of_isIso_app α.hom)

/-- The original inverse-image/direct-image adjunction has the same
invertible counit, through the proved comparison of its actual left adjoints. -/
theorem inverseImage_counit_isIso
    (F : Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E)) :
    IsIso ((EtaleInverseImage.adjunction U.hom E).counit.app F) := by
  let : IsIso ((EtaleRestrictionInverseImage.restrictionAdjunction S U E).counit.app F) :=
    restriction_counit_isIso S U E F
  apply (isIso_comp_left_iff
    ((EtaleRestrictionInverseImage.iso S U E).hom.app
      ((EtaleDirectImage.functor U.hom E).obj F)) _).mp
  rw [EtaleRestrictionInverseImage.iso_counit]
  infer_instance

end SiteAdjunction

section CartesianSquare

variable {X S' S : Scheme.{u}} (q : X ⟶ S) (g : S' ⟶ S)

/-- A neighborhood over the new base gives a literal lift of its
pullback to the original source into the cartesian source. -/
def neighborhoodLift (V : S'.Etale) :
    pullback (V.hom ≫ g) q ⟶ pullback q g :=
  pullback.lift (pullback.snd (V.hom ≫ g) q)
    (pullback.fst (V.hom ≫ g) q ≫ V.hom) (by
      simpa only [Category.assoc] using
        (pullback.condition (f := V.hom ≫ g) (g := q)).symm)

/-- The lift factors the unchanged structure map to the original source. -/
theorem neighborhoodLift_fst (V : S'.Etale) :
    neighborhoodLift q g V ≫ pullback.fst q g = pullback.snd (V.hom ≫ g) q :=
  pullback.lift_fst _ _ _

variable [Etale g] [Mono g] (E : Type u) [Ring E]

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual restriction-unit becomes invertible after direct image
and restriction to the open base, by the explicit neighborhood lift. -/
theorem restricted_directImage_restrictionUnit_isIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) :
    IsIso ((EtaleExtensionByZero.restriction S (Scheme.Etale.mk g) E).map
      ((EtaleDirectImage.functor q E).map
        ((EtaleRestrictionInverseImage.restrictionAdjunction X
          (Scheme.Etale.mk (pullback.fst q g)) E).unit.app F))) := by
  let U := Scheme.Etale.mk g
  let U' := Scheme.Etale.mk (pullback.fst q g)
  let : Mono U'.hom := inferInstanceAs (Mono (pullback.fst q g))
  let α := (EtaleExtensionByZero.restriction S U E).map
    ((EtaleDirectImage.functor q E).map
      ((EtaleRestrictionInverseImage.restrictionAdjunction X U' E).unit.app F))
  let : ∀ V : S'.Etaleᵒᵖ, IsIso (α.hom.app V) := fun V => by
    change IsIso (((EtaleRestrictionInverseImage.restrictionAdjunction X U' E).unit.app
      F).hom.app (op ((EtaleDirectImage.baseChange q).obj
        ((EtaleRestrictionInverseImage.postcomposition S U).obj V.unop))))
    rw [EtaleRestrictionInverseImage.restrictionAdjunction_unit_app_hom_app]
    let : IsIso ((EtaleRestrictionInverseImage.postcompositionAdjunction X U').counit.app
        ((EtaleDirectImage.baseChange q).obj
          ((EtaleRestrictionInverseImage.postcomposition S U).obj V.unop))) :=
      postcomposition_counit_isIso_of_factor X U' _ (neighborhoodLift q g V.unop)
        (neighborhoodLift_fst q g V.unop)
    exact F.obj.map_isIso _
  exact (ObjectProperty.isIso_hom_iff α).mp (NatIso.isIso_of_isIso_app α.hom)

set_option backward.isDefEq.respectTransparency.types false in
/-- The same assertion for the unchanged inverse-image unit, using
its proved compatibility with the literal restriction unit. -/
theorem restricted_directImage_inverseImageUnit_isIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) :
    IsIso ((EtaleExtensionByZero.restriction S (Scheme.Etale.mk g) E).map
      ((EtaleDirectImage.functor q E).map
        ((EtaleInverseImage.adjunction (pullback.fst q g) E).unit.app F))) := by
  change IsIso ((EtaleExtensionByZero.restriction S (Scheme.Etale.mk g) E).map
    ((EtaleDirectImage.functor q E).map
      ((EtaleInverseImage.adjunction (Scheme.Etale.mk (pullback.fst q g)).hom E).unit.app F)))
  rw [← EtaleRestrictionInverseImage.iso_unit X (Scheme.Etale.mk (pullback.fst q g)) E F]
  simp only [Functor.map_comp]
  let := restricted_directImage_restrictionUnit_isIso q g E F
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- The first factor of the existing canonical base-change map is
invertible; its functors and its unit are the original ones. -/
theorem inverseImage_directImage_unit_isIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) :
    IsIso ((EtaleInverseImage.functor g E).map
      ((EtaleDirectImage.functor q E).map
        ((EtaleInverseImage.adjunction (pullback.fst q g) E).unit.app F))) :=
  (NatIso.isIso_map_iff (EtaleRestrictionInverseImage.iso S (Scheme.Etale.mk g) E) _).mp
    (restricted_directImage_inverseImageUnit_isIso q g E F)

set_option backward.isDefEq.respectTransparency.types false in
/-- Every component of the existing cartesian base-change mate is an isomorphism. -/
theorem pullbackBaseChangeMap_app_isIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) :
    IsIso ((EtaleInverseImage.pullbackBaseChangeMap q g E).app F) := by
  rw [EtaleInverseImage.pullbackBaseChangeMap_app]
  let := inverseImage_directImage_unit_isIso q g E F
  let : Mono (Scheme.Etale.mk g).hom := inferInstanceAs (Mono g)
  let : IsIso ((EtaleInverseImage.adjunction g E).counit.app
      ((EtaleDirectImage.functor (pullback.snd q g) E).obj
        ((EtaleInverseImage.functor (pullback.fst q g) E).obj F))) :=
    inverseImage_counit_isIso S (Scheme.Etale.mk g) E _
  infer_instance

/-- Open base change holds for the existing actual natural transformation. -/
instance pullbackBaseChangeMap_isIso :
    IsIso (EtaleInverseImage.pullbackBaseChangeMap q g E) := by
  let : ∀ F, IsIso ((EtaleInverseImage.pullbackBaseChangeMap q g E).app F) :=
    pullbackBaseChangeMap_app_isIso q g E
  exact NatIso.isIso_of_isIso_app _

/-- The actual open base-change isomorphism, with the original mate as its forward map. -/
def pullbackBaseChangeIso :
    EtaleDirectImage.functor q E ⋙ EtaleInverseImage.functor g E ≅
      EtaleInverseImage.functor (pullback.fst q g) E ⋙
        EtaleDirectImage.functor (pullback.snd q g) E :=
  asIso (EtaleInverseImage.pullbackBaseChangeMap q g E)

/-- The isomorphism does not replace the previously constructed comparison map. -/
theorem pullbackBaseChangeIso_hom :
    (pullbackBaseChangeIso q g E).hom = EtaleInverseImage.pullbackBaseChangeMap q g E := rfl

end CartesianSquare

end PrimeGap182.TypeIII.EtaleOpenBaseChange

#print axioms PrimeGap182.TypeIII.EtaleOpenBaseChange.pullback_fst_isIso_of_factor
#print axioms PrimeGap182.TypeIII.EtaleOpenBaseChange.postcomposition_counit_isIso_of_factor
#print axioms PrimeGap182.TypeIII.EtaleOpenBaseChange.postcomposition_unit_isIso
#print axioms PrimeGap182.TypeIII.EtaleOpenBaseChange.restriction_counit_isIso
#print axioms PrimeGap182.TypeIII.EtaleOpenBaseChange.inverseImage_counit_isIso
#print axioms PrimeGap182.TypeIII.EtaleOpenBaseChange.neighborhoodLift
#print axioms PrimeGap182.TypeIII.EtaleOpenBaseChange.neighborhoodLift_fst
#print axioms PrimeGap182.TypeIII.EtaleOpenBaseChange.restricted_directImage_restrictionUnit_isIso
#print axioms PrimeGap182.TypeIII.EtaleOpenBaseChange.restricted_directImage_inverseImageUnit_isIso
#print axioms PrimeGap182.TypeIII.EtaleOpenBaseChange.inverseImage_directImage_unit_isIso
#print axioms PrimeGap182.TypeIII.EtaleOpenBaseChange.pullbackBaseChangeMap_app_isIso
#print axioms PrimeGap182.TypeIII.EtaleOpenBaseChange.pullbackBaseChangeMap_isIso
#print axioms PrimeGap182.TypeIII.EtaleOpenBaseChange.pullbackBaseChangeIso
#print axioms PrimeGap182.TypeIII.EtaleOpenBaseChange.pullbackBaseChangeIso_hom
