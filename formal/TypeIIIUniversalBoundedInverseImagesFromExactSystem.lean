import TypeIIIQSTBoundedTensorFromUniversalDerivedMonoidal

/-!
# Actual bounded inverse images from one universal exact system

All functors are restrictions of U's actual standard derived inverse image.
Exactness gives boundedness at every scheme and object. Strong monoidality
of these actual derived functors is a general six-functor theorem parameter;
the bounded tensor/unit comparisons are computed from its actual isomorphisms.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory
namespace PrimeGap182.TypeIII.UniversalBoundedInverseImagesFromExactSystem
open ExactInverseImagesToDerived QSTAdmissibilityFromBoundedDerived
open QSTBoundedTensorFromUniversalDerivedMonoidal
universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)]
  [∀ X, Abelian (C X)] [∀ X, MonoidalCategory (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
local instance allSchemeLocalizations : ∀ X : Scheme, HasDerivedCategory.{mu} (C X) :=
  fun _ => HasDerivedCategory.standard _
variable [∀ X, MonoidalCategory (DerivedCategory (C X))]
  (laws : BoundedTensorLaws C)

abbrev BoundedObj (X : Scheme) := (boundedProperty (C X)).FullSubcategory
abbrev boundedMonoidal (X : Scheme) : MonoidalCategory (BoundedObj C X) := by
  letI := boundedIsMonoidal C laws X
  exact ObjectProperty.fullMonoidalSubcategory _
def tensor (X : Scheme) (K L : BoundedObj C X) : BoundedObj C X := by
  letI := boundedMonoidal C laws X
  exact K ⊗ L

def unit (X : Scheme) : BoundedObj C X := by
  letI := boundedMonoidal C laws X
  exact 𝟙_ (BoundedObj C X)

/-- Literal lift of the SAME actual derived inverse image. -/
def pull {X Y : Scheme} (f : X ⟶ Y) : BoundedObj C Y ⥤ BoundedObj C X :=
  (boundedProperty (C X)).lift
    ((boundedProperty (C Y)).ι ⋙ U.derivedPull f)
    (fun K => exactFunctor_bounded (U.pull f) K.obj K.property)

omit [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  [∀ X, MonoidalCategory (DerivedCategory (C X))]
  [∀ X, MonoidalCategory (C X)] in
/-- The underlying object uses the actual derived inverse image. -/
theorem pull_obj {X Y : Scheme} (f : X ⟶ Y) (K : BoundedObj C Y) :
    ((pull C U f).obj K).obj = (U.derivedPull f).obj K.obj := rfl

variable [∀ {X Y : Scheme} (f : X ⟶ Y), (U.derivedPull f).Monoidal]

/-- ALL morphisms and ALL bounded objects have the computed tensor comparison. -/
def pullTensorIso {X Y : Scheme} (f : X ⟶ Y) (K L : BoundedObj C Y) :
    (pull C U f).obj (tensor C laws Y K L) ≅
      tensor C laws X ((pull C U f).obj K) ((pull C U f).obj L) :=
  (boundedProperty (C X)).isoMk
    (Functor.Monoidal.μIso (U.derivedPull f) K.obj L.obj).symm

/-- ALL morphisms have the computed unit comparison on the SAME bounded domain. -/
def pullUnitIso {X Y : Scheme} (f : X ⟶ Y) :
    (pull C U f).obj (unit C laws Y) ≅ unit C laws X :=
  (boundedProperty (C X)).isoMk (Functor.Monoidal.εIso (U.derivedPull f)).symm

end PrimeGap182.TypeIII.UniversalBoundedInverseImagesFromExactSystem
#print axioms PrimeGap182.TypeIII.UniversalBoundedInverseImagesFromExactSystem.pull
#print axioms PrimeGap182.TypeIII.UniversalBoundedInverseImagesFromExactSystem.pull_obj
#print axioms PrimeGap182.TypeIII.UniversalBoundedInverseImagesFromExactSystem.pullTensorIso
#print axioms PrimeGap182.TypeIII.UniversalBoundedInverseImagesFromExactSystem.pullUnitIso
