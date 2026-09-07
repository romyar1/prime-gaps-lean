import TypeIIISheafTowerDerivedLimit
import TypeIIIEtaleInverseImageStalk
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Direct images of actual small étale sheaf towers

For a scheme morphism q, the tower direct-image functor applies the
existing q_* at every level. Its left adjoint applies the existing q^*
at every level, using the whiskering of their original adjunction.
The proved exactness of q^* gives exactness on towers, so tower q_*
preserves injective objects.

The original categorical inverse limit commutes with the original q_*.
The comparison is Mathlib's limit-preservation isomorphism, and its
composition with each original limit projection is q_* applied to that
projection. All functors and maps are the existing ones on the actual
small étale module-sheaf categories.

No properness hypothesis, proper base change, exactness of inverse
limits, or identification with adic cohomology is used or asserted.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleTowerDirectImage

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

variable {X S : Scheme.{u}} (q : X ⟶ S) (E : Type u) [Ring E]

/-- Apply the original étale direct image at each level of the actual tower. -/
def functor : EtaleSheafTower.Tower X E ⥤ EtaleSheafTower.Tower S E :=
  (Functor.whiskeringRight ℕᵒᵖ
    (Sheaf X.smallEtaleTopology (ModuleCat.{u} E))
    (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))).obj
      (EtaleDirectImage.functor q E)

/-- Apply the original étale inverse image at each level of the actual tower. -/
def inverseFunctor : EtaleSheafTower.Tower S E ⥤ EtaleSheafTower.Tower X E :=
  (Functor.whiskeringRight ℕᵒᵖ
    (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))
    (Sheaf X.smallEtaleTopology (ModuleCat.{u} E))).obj
      (EtaleInverseImage.functor q E)

/-- The tower object is literally composition with the existing direct image. -/
@[simp] theorem functor_obj (T : EtaleSheafTower.Tower X E) :
    (functor q E).obj T = T ⋙ EtaleDirectImage.functor q E := rfl

/-- The level map is the existing direct image of the original tower map. -/
@[simp] theorem functor_map_app {T T' : EtaleSheafTower.Tower X E}
    (a : T ⟶ T') (n : ℕᵒᵖ) :
    ((functor q E).map a).app n = (EtaleDirectImage.functor q E).map (a.app n) := rfl

/-- The inverse-image tower is literally composition with the existing inverse image. -/
@[simp] theorem inverseFunctor_obj (T : EtaleSheafTower.Tower S E) :
    (inverseFunctor q E).obj T = T ⋙ EtaleInverseImage.functor q E := rfl

/-- The inverse-image level map retains the original map and original q^*. -/
@[simp] theorem inverseFunctor_map_app {T T' : EtaleSheafTower.Tower S E}
    (a : T ⟶ T') (n : ℕᵒᵖ) :
    ((inverseFunctor q E).map a).app n =
      (EtaleInverseImage.functor q E).map (a.app n) := rfl

/-- The tower adjunction is the whiskering of the original sheaf adjunction. -/
def adjunction : inverseFunctor q E ⊣ functor q E :=
  (EtaleInverseImage.adjunction q E).whiskerRight ℕᵒᵖ

/-- The pointwise direct image is a right adjoint on the actual tower categories. -/
instance functor_isRightAdjoint : (functor q E).IsRightAdjoint :=
  (adjunction q E).isRightAdjoint

/-- The pointwise inverse image is the corresponding left adjoint. -/
instance inverseFunctor_isLeftAdjoint : (inverseFunctor q E).IsLeftAdjoint :=
  (adjunction q E).isLeftAdjoint

/-- Finite limits of towers are preserved by the original pointwise inverse image. -/
instance inverseFunctor_preservesFiniteLimits : PreservesFiniteLimits (inverseFunctor q E) where
  preservesFiniteLimits J _ _ := by
    change PreservesLimitsOfShape J
      ((Functor.whiskeringRight ℕᵒᵖ
        (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} E))).obj
          (EtaleInverseImage.functor q E))
    infer_instance

/-- Finite colimits of towers are also preserved by the original pointwise inverse image. -/
instance inverseFunctor_preservesFiniteColimits : PreservesFiniteColimits (inverseFunctor q E) where
  preservesFiniteColimits J _ _ := by
    change PreservesColimitsOfShape J
      ((Functor.whiskeringRight ℕᵒᵖ
        (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} E))).obj
          (EtaleInverseImage.functor q E))
    infer_instance

/-- Additivity is inherited from the original inverse image level by level. -/
instance inverseFunctor_additive : (inverseFunctor q E).Additive :=
  inferInstanceAs (((Functor.whiskeringRight ℕᵒᵖ
    (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))
    (Sheaf X.smallEtaleTopology (ModuleCat.{u} E))).obj
      (EtaleInverseImage.functor q E)).Additive)

/-- Actual monomorphisms of towers remain monomorphisms under pointwise q^*. -/
instance inverseFunctor_preservesMonomorphisms :
    (inverseFunctor q E).PreservesMonomorphisms :=
  inferInstanceAs (((Functor.whiskeringRight ℕᵒᵖ
    (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))
    (Sheaf X.smallEtaleTopology (ModuleCat.{u} E))).obj
      (EtaleInverseImage.functor q E)).PreservesMonomorphisms)

/-- The actual pointwise inverse image preserves homology in the tower category. -/
instance inverseFunctor_preservesHomology :
    (inverseFunctor q E).PreservesHomology := inferInstance

/-- Original short exact sequences of towers remain short exact under pointwise q^*. -/
theorem inverseFunctor_map_shortExact (T : ShortComplex (EtaleSheafTower.Tower S E))
    (hT : T.ShortExact) : (T.map (inverseFunctor q E)).ShortExact :=
  hT.map_of_exact (inverseFunctor q E)

/-- Additivity is inherited from the original direct image level by level. -/
instance functor_additive : (functor q E).Additive :=
  inferInstanceAs (((Functor.whiskeringRight ℕᵒᵖ
    (Sheaf X.smallEtaleTopology (ModuleCat.{u} E))
    (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))).obj
      (EtaleDirectImage.functor q E)).Additive)

/-- Pointwise direct image preserves all limits in the coefficient universe. -/
instance functor_preservesLimits : PreservesLimitsOfSize.{u, u} (functor q E) :=
  (adjunction q E).rightAdjoint_preservesLimits

/-- In particular, the actual pointwise direct image is left exact. -/
instance functor_preservesFiniteLimits : PreservesFiniteLimits (functor q E) where
  preservesFiniteLimits J _ _ := by
    change PreservesLimitsOfShape J
      ((Functor.whiskeringRight ℕᵒᵖ
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} E))
        (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))).obj
          (EtaleDirectImage.functor q E))
    infer_instance

/-- The actual tower direct image preserves injectives because its proved left adjoint is exact. -/
instance functor_preservesInjectiveObjects : (functor q E).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (adjunction q E)

/-- The original inverse limit commutes with the original direct image. -/
def limitIso :
    EtaleSheafTower.limitFunctor X E ⋙ EtaleDirectImage.functor q E ≅
      functor q E ⋙ EtaleSheafTower.limitFunctor S E :=
  preservesLimitNatIso (EtaleDirectImage.functor q E)

/-- Its component is the original canonical limit-preservation map. -/
@[simp] theorem limitIso_hom_app (T : EtaleSheafTower.Tower X E) :
    (limitIso q E).hom.app T = (preservesLimitIso (EtaleDirectImage.functor q E) T).hom := rfl

/-- The comparison followed by a literal limit projection is q_* of that original projection. -/
theorem limitIso_hom_π (T : EtaleSheafTower.Tower X E) (n : ℕ) :
    (limitIso q E).hom.app T ≫ limit.π ((functor q E).obj T) (op n) =
      (EtaleDirectImage.functor q E).map (limit.π T (op n)) :=
  preservesLimitIso_hom_π (EtaleDirectImage.functor q E) T (op n)

/-- The inverse comparison retains the same original limit projections. -/
theorem limitIso_inv_π (T : EtaleSheafTower.Tower X E) (n : ℕ) :
    (limitIso q E).inv.app T ≫ (EtaleDirectImage.functor q E).map (limit.π T (op n)) =
      limit.π ((functor q E).obj T) (op n) :=
  preservesLimitIso_inv_π (EtaleDirectImage.functor q E) T (op n)

/-- The projection identity also holds for the original natural projection transformations. -/
theorem limitIso_hom_projection (n : ℕ) :
    (limitIso q E).hom ≫
        Functor.whiskerLeft (functor q E) (EtaleSheafTower.projection S E n) =
      Functor.whiskerRight (EtaleSheafTower.projection X E n) (EtaleDirectImage.functor q E) := by
  apply NatTrans.ext
  funext T
  exact limitIso_hom_π q E T n

#print axioms functor
#print axioms inverseFunctor
#print axioms functor_obj
#print axioms functor_map_app
#print axioms inverseFunctor_obj
#print axioms inverseFunctor_map_app
#print axioms adjunction
#print axioms functor_isRightAdjoint
#print axioms inverseFunctor_isLeftAdjoint
#print axioms inverseFunctor_preservesFiniteLimits
#print axioms inverseFunctor_preservesFiniteColimits
#print axioms inverseFunctor_additive
#print axioms inverseFunctor_preservesMonomorphisms
#print axioms inverseFunctor_preservesHomology
#print axioms inverseFunctor_map_shortExact
#print axioms functor_additive
#print axioms functor_preservesLimits
#print axioms functor_preservesFiniteLimits
#print axioms functor_preservesInjectiveObjects
#print axioms limitIso
#print axioms limitIso_hom_app
#print axioms limitIso_hom_π
#print axioms limitIso_inv_π
#print axioms limitIso_hom_projection

end PrimeGap182.TypeIII.EtaleTowerDirectImage
