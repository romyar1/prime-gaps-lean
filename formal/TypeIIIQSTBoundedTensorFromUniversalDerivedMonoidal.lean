import TypeIIIQSTPerverseBackgroundFromUniversalHeart
import Mathlib.CategoryTheory.Monoidal.Subcategory

/-!
# Actual bounded tensor from the same universal derived monoidal category

The ordinary categories, inverse images and universal perverse hearts are
fixed before the prime. The additional general data are a monoidal structure
on the SAME standard derived categories at ALL schemes, with tensor and unit
preserving bounded objects. The canonical bounded full subcategories inherit
that actual structure. Their tensor, unit, tensor-isomorphism transport and
left-unit comparison construct four QST background fields.

No completed Background, special sign, construction bound or Type III
inequality is assumed. The six-functor/adic interpretation and compatibility
of this derived tensor with the original ordinary tensor remain explicit.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.QSTBoundedTensorFromUniversalDerivedMonoidal
open ExactInverseImagesToDerived CanonicalPrimeFramework
open NativePerverseFromUniversalHeart QSTRealizationFromExactInverseImages

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)]
  [∀ X, Abelian (C X)] [∀ X, MonoidalCategory (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]

local instance allSchemeLocalizations : ∀ X : Scheme, HasDerivedCategory.{mu} (C X) :=
  fun _ => HasDerivedCategory.standard _

variable [∀ X, MonoidalCategory (DerivedCategory (C X))]

/-- General closure at every scheme and every bounded derived object. -/
structure BoundedTensorLaws where
  tensor : ∀ X (K L : DerivedCategory (C X)),
    QSTAdmissibilityFromBoundedDerived.boundedProperty (C X) K →
    QSTAdmissibilityFromBoundedDerived.boundedProperty (C X) L →
    QSTAdmissibilityFromBoundedDerived.boundedProperty (C X) (K ⊗ L)
  unit : ∀ X, QSTAdmissibilityFromBoundedDerived.boundedProperty (C X)
    (𝟙_ (DerivedCategory (C X)))

variable (laws : BoundedTensorLaws C)

abbrev boundedIsMonoidal (X : Scheme) :
    (QSTAdmissibilityFromBoundedDerived.boundedProperty (C X)).IsMonoidal where
  prop_unit := laws.unit X
  prop_tensor := laws.tensor X

variable (P : ∀ X : Scheme.{0}, ObjectProperty (DerivedCategory (C X)))
  [∀ X, (P X).IsClosedUnderIsomorphisms] [∀ X, (P X).ContainsZero]
  [∀ X, Abelian (Heart C P X)]
  (perverseBounded : ∀ X (K : DerivedCategory (C X)), P X K →
    QSTAdmissibilityFromBoundedDerived.boundedProperty (C X) K)
  (p : ℕ) [Fact p.Prime]

local instance commonLocalizations : ∀ i,
    HasDerivedCategory.{mu} (extensionObjects (primeSource C U p) (extraOrdinary C p) i) :=
  fun _ => HasDerivedCategory.standard _

local notation "T" => QSTPerverseBackgroundFromUniversalHeart.domain C U p

/-- The literal QST bounded category inherits the ALL-scheme derived tensor. -/
abbrev nativeDerivedMonoidal (i : UniformComplexityFromCommonRealization.Space) :
    MonoidalCategory (NativeDerived (primeSource C U p) (extraOrdinary C p)
      QSTPerverseBackgroundFromUniversalHeart.planeIndex i) := by
  cases i <;> exact (inferInstanceAs (MonoidalCategory (DerivedCategory (C _))))

local instance qstNativeDerivedMonoidal (i : UniformComplexityFromCommonRealization.Space) :
    MonoidalCategory (NativeDerived (primeSource C U p) (extraOrdinary C p)
      QSTPerverseBackgroundFromUniversalHeart.planeIndex i) := nativeDerivedMonoidal C U p i

/-- The literal QST bounded category inherits the ALL-scheme derived tensor. -/
abbrev boundedMonoidal (i : UniformComplexityFromCommonRealization.Space) :
    MonoidalCategory (Obj (primeSource C U p) T i) := by
  letI : ∀ X : Scheme,
      (QSTAdmissibilityFromBoundedDerived.boundedProperty (C X)).IsMonoidal :=
    fun X => boundedIsMonoidal C laws X
  cases i <;> change MonoidalCategory ((QSTAdmissibilityFromBoundedDerived.boundedProperty
    (C _)).FullSubcategory)
  all_goals exact ObjectProperty.fullMonoidalSubcategory _

/-- Actual tensor on the canonical bounded domain. -/
def tensor (i : UniformComplexityFromCommonRealization.Space)
    (K L : Obj (primeSource C U p) T i) : Obj (primeSource C U p) T i := by
  letI := boundedMonoidal C U laws p i
  exact K ⊗ L

/-- Actual unit on the same domain. -/
def unit (i : UniformComplexityFromCommonRealization.Space) :
    Obj (primeSource C U p) T i := by
  letI := boundedMonoidal C U laws p i
  exact 𝟙_ (Obj (primeSource C U p) T i)

/-- ALL actual isomorphisms transport through that tensor. -/
def tensorIso (i : UniformComplexityFromCommonRealization.Space)
    {K K' L L' : Obj (primeSource C U p) T i} (e : K ≅ K') (f : L ≅ L') :
    tensor C U laws p i K L ≅ tensor C U laws p i K' L' := by
  letI := boundedMonoidal C U laws p i
  exact e ⊗ᵢ f

/-- The actual inherited left unitor. -/
def tensorUnit (i : UniformComplexityFromCommonRealization.Space)
    (K : Obj (primeSource C U p) T i) :
    tensor C U laws p i (unit C U laws p i) K ≅ K := by
  letI := boundedMonoidal C U laws p i
  exact λ_ K

/-- Underlying objects are the SAME all-scheme derived tensor. -/
theorem tensor_obj (i : UniformComplexityFromCommonRealization.Space)
    (K L : Obj (primeSource C U p) T i) :
    (tensor C U laws p i K L).obj = K.obj ⊗ L.obj := by
  cases i <;> rfl

/-- The inherited unit is the SAME all-scheme derived unit. -/
theorem unit_obj (i : UniformComplexityFromCommonRealization.Space) :
    (unit C U laws p i).obj = 𝟙_ (NativeDerived (primeSource C U p) (extraOrdinary C p)
      QSTPerverseBackgroundFromUniversalHeart.planeIndex i) := by
  cases i <;> rfl


include C U laws P perverseBounded p

/-- Construct eight QST fields: four universal-heart fields and four
inherited bounded-tensor fields; every other operation remains separate. -/
def backgroundConstructor
    (complexity : ∀ i, Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) i → ℕ)
    (GeometricConstantRankOne : ∀ i, Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) i → Prop)
    (embeddingComplexity : UniformComplexityFromCommonRealization.Space → ℕ)
    (mapComplexity : ∀ {i j}, (UniformComplexityFromCommonRealization.scheme (ZMod p) i ⟶ UniformComplexityFromCommonRealization.scheme (ZMod p) j) → ℕ)
    (twist : ∀ i, Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) i → ℤ → Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) i)
    (verdier : ∀ i, Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) i → Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) i)
    (push : ∀ {i j}, (UniformComplexityFromCommonRealization.scheme (ZMod p) i ⟶ UniformComplexityFromCommonRealization.scheme (ZMod p) j) → Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) i → Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) j)
    (openZero : ∀ {i j}, (UniformComplexityFromCommonRealization.scheme (ZMod p) i ⟶ UniformComplexityFromCommonRealization.scheme (ZMod p) j) → QSTPerverseBackgroundFromUniversalHeart.perverseHeart C P p i ⥤ QSTPerverseBackgroundFromUniversalHeart.perverseHeart C P p j)
    (openDirect : ∀ {i j}, (UniformComplexityFromCommonRealization.scheme (ZMod p) i ⟶ UniformComplexityFromCommonRealization.scheme (ZMod p) j) → QSTPerverseBackgroundFromUniversalHeart.perverseHeart C P p i ⥤ QSTPerverseBackgroundFromUniversalHeart.perverseHeart C P p j)
    (openSupport : ∀ {i j} (f : UniformComplexityFromCommonRealization.scheme (ZMod p) i ⟶ UniformComplexityFromCommonRealization.scheme (ZMod p) j), openZero f ⟶ openDirect f)
    (Induced : ∀ {i j}, (UniformComplexityFromCommonRealization.scheme (ZMod p) i ⟶ UniformComplexityFromCommonRealization.scheme (ZMod p) j) → Prop)
    (gmGenericFiber : Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) .gm → ModuleCat.{0} ℂ)
    [gmGenericFinite : ∀ X, FiniteDimensional ℂ (gmGenericFiber X)]
    (affineZero : Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) .gm → Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) .line)
    (affineMiddle : Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) .gm → Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) .line)
    (Hypergeometric : Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) .gm → ℕ → Prop)
    (NontrivialArtinSchreier : Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) .line → Prop) :
    Background (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) where
  complexity := complexity
  GeometricConstantRankOne := GeometricConstantRankOne
  embeddingComplexity := embeddingComplexity
  mapComplexity := mapComplexity
  tensor := tensor C U laws p
  unit := unit C U laws p
  tensorIso := tensorIso C U laws p
  tensorUnit := tensorUnit C U laws p
  twist := twist
  verdier := verdier
  push := push
  Perv := QSTPerverseBackgroundFromUniversalHeart.perverseHeart C P p
  perverseCategory := fun _ => inferInstance
  perverseAbelian := fun _ => inferInstance
  perverse := QSTPerverseBackgroundFromUniversalHeart.heartInclusion C U P perverseBounded p
  openZero := openZero
  openDirect := openDirect
  openSupport := openSupport
  Induced := Induced
  gmGenericFiber := gmGenericFiber
  gmGenericFinite := gmGenericFinite
  affineZero := affineZero
  affineMiddle := affineMiddle
  Hypergeometric := Hypergeometric
  NontrivialArtinSchreier := NontrivialArtinSchreier

end PrimeGap182.TypeIII.QSTBoundedTensorFromUniversalDerivedMonoidal

#print axioms PrimeGap182.TypeIII.QSTBoundedTensorFromUniversalDerivedMonoidal.boundedMonoidal
#print axioms PrimeGap182.TypeIII.QSTBoundedTensorFromUniversalDerivedMonoidal.tensor
#print axioms PrimeGap182.TypeIII.QSTBoundedTensorFromUniversalDerivedMonoidal.unit
#print axioms PrimeGap182.TypeIII.QSTBoundedTensorFromUniversalDerivedMonoidal.tensorIso
#print axioms PrimeGap182.TypeIII.QSTBoundedTensorFromUniversalDerivedMonoidal.tensorUnit
#print axioms PrimeGap182.TypeIII.QSTBoundedTensorFromUniversalDerivedMonoidal.tensor_obj
#print axioms PrimeGap182.TypeIII.QSTBoundedTensorFromUniversalDerivedMonoidal.unit_obj
#print axioms PrimeGap182.TypeIII.QSTBoundedTensorFromUniversalDerivedMonoidal.backgroundConstructor
