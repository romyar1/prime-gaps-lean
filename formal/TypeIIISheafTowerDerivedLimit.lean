import TypeIIIEtaleDerivedDirectImage
import TypeIIIRightDerivedPlusTriangulated
import Mathlib.CategoryTheory.Generator.Presheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Derived inverse limits of actual small étale sheaf towers

The category of natural-number inverse systems of module sheaves on the
original small étale site is Grothendieck abelian. Its injective resolutions
therefore come from the existing enough-injectives construction.

The limit functor is the original categorical limit, with the original
projections and constant-functor adjunction. Since the constant functor
preserves monomorphisms, this limit functor preserves injective objects.
Its ordinary and bounded below right derived functors use the existing
injective resolutions and derived units.

No exactness of inverse limits, Mittag--Leffler assertion, commutation with
cohomology, or identification with an adic or pro-étale category is asserted.
-/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII.EtaleSheafTower

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry Opposite

variable (S : Scheme.{u}) (E : Type u) [Ring E]

/-- The actual category of inverse systems of module sheaves on the small étale site. -/
abbrev Tower := ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u} E)

/-- Natural transformations remain small in the coefficient universe. -/
instance tower_locallySmall : LocallySmall.{u} (Tower S E) where
  hom_small F G := by
    let : LocallySmall.{u} (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :=
      (EtaleDerivedDirectImage.isGrothendieckAbelian S E).locallySmall
    apply small_of_injective.{u}
      (f := fun (α : F ⟶ G) => (α.app : ∀ n : ℕᵒᵖ, F.obj n ⟶ G.obj n))
    intro α β h
    exact NatTrans.ext h

/-- The existing presheaf separator and pointwise exact filtered colimits
give the actual tower category its Grothendieck structure. -/
instance tower_isGrothendieckAbelian : IsGrothendieckAbelian.{u} (Tower S E) where
  ab5OfSize := ⟨fun _ _ _ => inferInstance⟩
  hasSeparator := by
    let : IsGrothendieckAbelian.{u} (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :=
      EtaleDerivedDirectImage.isGrothendieckAbelian S E
    let : HasColimitsOfSize.{u, u} (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :=
      IsGrothendieckAbelian.hasColimits (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))
    let : HasSeparator (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :=
      (EtaleDerivedDirectImage.isGrothendieckAbelian S E).hasSeparator
    let : HasCoproducts.{0} (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) := fun J =>
      HasColimitsOfShape.of_small.{u, u}
        (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) (Discrete J)
    exact Presheaf.hasSeparator ℕ (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))

/-- The Grothendieck-category construction supplies actual injective presentations. -/
theorem enoughInjectives : EnoughInjectives (Tower S E) := inferInstance

/-- Every original tower has an injective resolution in the actual tower category. -/
theorem hasInjectiveResolutions : HasInjectiveResolutions (Tower S E) := inferInstance

/-- The original categorical inverse limit of sheaf-valued towers. -/
def limitFunctor : Tower S E ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u} E) := lim

/-- Its objects are the original categorical limits. -/
@[simp] theorem limitFunctor_obj (T : Tower S E) :
    (limitFunctor S E).obj T = limit T := rfl

/-- Its maps are the original maps induced between those limits. -/
@[simp] theorem limitFunctor_map {T T' : Tower S E} (f : T ⟶ T') :
    (limitFunctor S E).map f = limMap f := rfl

/-- The adjunction is Mathlib's original constant-functor/limit adjunction. -/
def limitAdjunction :
    (Functor.const ℕᵒᵖ : Sheaf S.smallEtaleTopology (ModuleCat.{u} E) ⥤ Tower S E) ⊣
      limitFunctor S E := constLimAdj

/-- The counit's components are the original limit projections. -/
@[simp] theorem limitAdjunction_counit_app_app (T : Tower S E) (n : ℕ) :
    ((limitAdjunction S E).counit.app T).app (op n) = limit.π T (op n) := rfl

/-- The natural projection from the original limit to level n. -/
def projection (n : ℕ) :
    limitFunctor S E ⟶
      (evaluation ℕᵒᵖ (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))).obj (op n) :=
  lim.π (op n)

/-- Each natural projection is the original categorical limit projection. -/
@[simp] theorem projection_app (n : ℕ) (T : Tower S E) :
    (projection S E n).app T = limit.π T (op n) := rfl

/-- Original maps of towers commute with the original projections. -/
theorem projection_naturality (n : ℕ) {T T' : Tower S E} (f : T ⟶ T') :
    (limitFunctor S E).map f ≫ limit.π T' (op n) =
      limit.π T (op n) ≫ f.app (op n) :=
  limMap_π f (op n)

/-- The original limit projections respect every transition in the tower. -/
theorem projection_transition (T : Tower S E) {m n : ℕ} (hmn : m ≤ n) :
    limit.π T (op n) ≫ T.map (homOfLE hmn).op = limit.π T (op m) :=
  limit.w T (homOfLE hmn).op

/-- The actual limit functor preserves all limits in the coefficient universe. -/
instance limitFunctor_preservesLimits : PreservesLimitsOfSize.{u, u} (limitFunctor S E) :=
  (limitAdjunction S E).rightAdjoint_preservesLimits

/-- In particular, the actual inverse limit is left exact. -/
instance limitFunctor_preservesFiniteLimits : PreservesFiniteLimits (limitFunctor S E) :=
  inferInstanceAs (PreservesFiniteLimits (lim (J := ℕᵒᵖ)
    (C := Sheaf S.smallEtaleTopology (ModuleCat.{u} E))))

/-- Additivity follows from the original finite-product preservation. -/
instance limitFunctor_additive : (limitFunctor S E).Additive where
  map_add := by
    intro T T' f g
    apply limit.hom_ext
    intro n
    simp only [limitFunctor_map, Preadditive.add_comp, limMap_π, NatTrans.app_add,
      Preadditive.comp_add]

/-- The original exact constant functor is left adjoint to the actual limit,
so the actual limit sends injective towers to injective sheaves. -/
instance limitFunctor_preservesInjectiveObjects :
    (limitFunctor S E).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (limitAdjunction S E)

/-- The original adjunction unit has the identity as every constant-tower projection. -/
@[simp] theorem limitAdjunction_unit_app_π
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) (n : ℕ) :
    (limitAdjunction S E).unit.app F ≫
        limit.π ((Functor.const ℕᵒᵖ).obj F) (op n) = 𝟙 F :=
  limit.lift_π _ _

/-- An actual injective resolution of the original tower. -/
def resolution (T : Tower S E) : InjectiveResolution T :=
  CategoryTheory.injectiveResolution T

/-- The original nth right derived functor of the actual categorical limit. -/
def derived (n : ℕ) : Tower S E ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u} E) :=
  (limitFunctor S E).rightDerived n

/-- This definition uses the original injective-resolution and homology functors. -/
theorem derived_eq_resolution_homology (n : ℕ) :
    derived S E n =
      CategoryTheory.injectiveResolutions (Tower S E) ⋙
        (limitFunctor S E).mapHomotopyCategory (.up ℕ) ⋙
        HomotopyCategory.homologyFunctor
          (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) (.up ℕ) n := rfl

/-- Computation by the same chosen injective resolution of the original tower. -/
def derivedObjIsoHomology (n : ℕ) (T : Tower S E) :
    (derived S E n).obj T ≅
      (((limitFunctor S E).mapHomologicalComplex (.up ℕ)).obj
        (resolution S E T).cocomplex).homology n :=
  (resolution S E T).isoRightDerivedObj (limitFunctor S E) n

/-- Left exactness gives the canonical degree-zero comparison with the original limit. -/
def zeroIso : derived S E 0 ≅ limitFunctor S E :=
  (limitFunctor S E).rightDerivedZeroIsoSelf

/-- The inverse of the zero comparison is the original augmentation transformation. -/
theorem zeroIso_inv :
    (zeroIso S E).inv = (limitFunctor S E).toRightDerivedZero := rfl

/-- The positive derived limits of an actual injective tower vanish. -/
theorem isZero_derived_obj_injective_succ (n : ℕ) (T : Tower S E) [Injective T] :
    IsZero ((derived S E (n + 1)).obj T) :=
  (limitFunctor S E).isZero_rightDerived_obj_injective_succ n T

attribute [local instance] HasDerivedCategory.standard

/-- The existing total right derived limit on the actual bounded below derived categories. -/
def derivedPlus :
    DerivedCategory.Plus (Tower S E) ⥤
      DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :=
  (limitFunctor S E).rightDerivedFunctorPlus

/-- The total derived limit retains Mathlib's original derived unit. -/
def derivedPlusUnit :
    (limitFunctor S E).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ derivedPlus S E :=
  (limitFunctor S E).rightDerivedFunctorPlusUnit

/-- The original unit and original augmentation compute the total derived limit
using the same nonnegative injective resolution. -/
def derivedPlusResolutionIso (T : Tower S E) :
    DerivedCategory.Plus.Q.obj
        ((limitFunctor S E).mapCochainComplexPlus.obj
          (injectiveResolutionCochainPlus (resolution S E T))) ≅
      (derivedPlus S E).obj ((DerivedCategory.Plus.singleFunctor (Tower S E) 0).obj T) :=
  rightDerivedPlusResolutionIso (limitFunctor S E) (resolution S E T)

/-- The ordinary derived limits are the homology of the actual total derived limit,
on towers placed in degree zero. -/
def derivedPlusHomologyIso (n : ℕ) :
    derived S E n ≅
      DerivedCategory.Plus.singleFunctor (Tower S E) 0 ⋙ derivedPlus S E ⋙
        DerivedCategory.Plus.homologyFunctor
          (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) (n : ℤ) :=
  rightDerivedPlusComparisonIso (limitFunctor S E) n

/-- The degree-zero comparison matches the original total-derived unit,
with its canonical source identification. -/
theorem derivedPlusHomologyIso_zero_unit (T : Tower S E) :
    (zeroIso S E).inv.app T ≫ (derivedPlusHomologyIso S E 0).hom.app T =
      rightDerivedPlusZeroUnit (limitFunctor S E) T :=
  rightDerivedPlusComparisonIso_zero_unit (limitFunctor S E) T

end PrimeGap182.TypeIII.EtaleSheafTower

#print axioms PrimeGap182.TypeIII.EtaleSheafTower.Tower
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.tower_locallySmall
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.tower_isGrothendieckAbelian
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.enoughInjectives
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.hasInjectiveResolutions
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.limitFunctor
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.limitFunctor_obj
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.limitFunctor_map
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.limitAdjunction
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.limitAdjunction_counit_app_app
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.projection
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.projection_app
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.projection_naturality
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.projection_transition
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.limitFunctor_preservesLimits
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.limitFunctor_preservesFiniteLimits
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.limitFunctor_additive
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.limitFunctor_preservesInjectiveObjects
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.limitAdjunction_unit_app_π
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.resolution
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.derived
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.derived_eq_resolution_homology
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.derivedObjIsoHomology
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.zeroIso
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.zeroIso_inv
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.isZero_derived_obj_injective_succ
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.derivedPlus
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.derivedPlusUnit
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.derivedPlusResolutionIso
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.derivedPlusHomologyIso
#print axioms PrimeGap182.TypeIII.EtaleSheafTower.derivedPlusHomologyIso_zero_unit
