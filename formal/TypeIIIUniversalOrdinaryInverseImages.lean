import TypeIIINativeAuxiliarySchemes

/-!
# Restrict one universal ordinary inverse-image system

The categories are literally C of the actual schemes, with one ambient
category/abelian/monoidal family on ALL schemes. The same universally
exact ordinary pullback supplies the original source system and the
OriginPole extension including all four NativeAuxiliary schemes.
OriginalPullAgreement is constructed, never a premise.

The all-scheme sheaf-category, ordinary inverse-image and tensor
interpretation remains explicit general published-framework scope.
This does not construct adic foundations or a complete Inputs family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

namespace PrimeGap182.TypeIII.UniversalOrdinaryInverseImages
open ExactInverseImagesToDerived

universe mu
variable (C : Scheme → Type)
  [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  [∀ X, MonoidalCategory (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]

/-- Restrict the ONE universal system to the exact original source
scheme list, including every arithmetic fiber index. -/
def sourceSystem (K : Type) [Field K] : SourceInverseImageSystem.System.{0,mu} K where
  Obj i := C (SourceInverseImageSystem.scheme K i)
  category i := inferInstanceAs (Category.{mu} (C (SourceInverseImageSystem.scheme K i)))
  abelian i := inferInstanceAs (Abelian (C (SourceInverseImageSystem.scheme K i)))
  monoidal i := inferInstanceAs (MonoidalCategory (C (SourceInverseImageSystem.scheme K i)))
  pull f := U.pull f
  identity i := U.identity (SourceInverseImageSystem.scheme K i)
  composition f g := U.composition f g
  pullMonoidal f := inferInstanceAs ((U.pull f).Monoidal)
  pullAdditive f := inferInstanceAs ((U.pull f).Additive)
  pullLimits f := inferInstanceAs (PreservesFiniteLimits (U.pull f))
  pullColimits f := inferInstanceAs (PreservesFiniteColimits (U.pull f))

/-- The original category structure is the intrinsic universal one. -/
theorem sourceCategory (K : Type) [Field K] (i : SourceInverseImageSystem.Space K) :
    (sourceSystem C U K).category i =
      (inferInstance : Category.{mu} (C (SourceInverseImageSystem.scheme K i))) := rfl

theorem sourceMonoidal (K : Type) [Field K] (i : SourceInverseImageSystem.Space K) :
    (sourceSystem C U K).monoidal i =
      (inferInstance : MonoidalCategory (C (SourceInverseImageSystem.scheme K i))) := rfl

variable (K k : Type) [Field K] [Field k]

abbrev nativeOrdinary (i : OriginRealizationFromExactInverseImages.Index) : Type :=
  C (OriginRealizationFromExactInverseImages.scheme k i)

abbrev localOrdinary : Type := C (FourierSourceMaps.localScheme k)

abbrev auxiliaryOrdinary (i : NativeAuxiliarySchemes.Space) : Type :=
  C (NativeAuxiliarySchemes.scheme K k i)

abbrev extraScheme : OriginPoleFromExactInverseImages.Extra NativeAuxiliarySchemes.Space → Scheme :=
  OriginPoleFromExactInverseImages.extraScheme k (NativeAuxiliarySchemes.scheme K k)

abbrev extraOrdinary : OriginPoleFromExactInverseImages.Extra NativeAuxiliarySchemes.Space → Type :=
  OriginPoleFromExactInverseImages.extraObjects (nativeOrdinary C k) (localOrdinary C k)
    (auxiliaryOrdinary C K k)

local instance : ∀ i, Category.{mu} (nativeOrdinary C k i) := fun _ => inferInstance
local instance : ∀ i, Abelian (nativeOrdinary C k i) := fun _ => inferInstance
local instance : ∀ i, Category.{mu} (auxiliaryOrdinary C K k i) := fun _ => inferInstance
local instance : ∀ i, Abelian (auxiliaryOrdinary C K k i) := fun _ => inferInstance

/-- Every old/new category is the literal category of its actual scheme.
Only case analysis is needed; no category equivalence is supplied. -/
theorem commonObjects (i : SourceInverseImageSystem.Space K ⊕
    OriginPoleFromExactInverseImages.Extra NativeAuxiliarySchemes.Space) :
    extensionObjects (sourceSystem C U K) (extraOrdinary C K k) i =
      C (extensionScheme (extraScheme K k) i) := by
  rcases i with i | (i | (i | i)) <;> rfl

/-- The ONE extended ordinary system on old/native/trait/auxiliary
actual schemes, restricted from U without new pullback choices. -/
def ordinaryA : OrdinarySystem (extensionScheme (extraScheme K k))
    (extensionObjects (sourceSystem C U K) (extraOrdinary C K k)) where
  pull {i j} f := by
    rcases i with i | (i | (i | i)) <;>
      rcases j with j | (j | (j | j)) <;> exact U.pull f
  identity i := by
    rcases i with i | (i | (i | i)) <;> exact U.identity _
  composition {i j l} f g := by
    rcases i with i | (i | (i | i)) <;>
      rcases j with j | (j | (j | j)) <;>
        rcases l with l | (l | (l | l)) <;> exact U.composition f g
  additive {i j} f := by
    rcases i with i | (i | (i | i)) <;>
      rcases j with j | (j | (j | j)) <;> exact inferInstanceAs ((U.pull f).Additive)
  limits {i j} f := by
    rcases i with i | (i | (i | i)) <;>
      rcases j with j | (j | (j | j)) <;>
        exact inferInstanceAs (PreservesFiniteLimits (U.pull f))
  colimits {i j} f := by
    rcases i with i | (i | (i | i)) <;>
      rcases j with j | (j | (j | j)) <;>
        exact inferInstanceAs (PreservesFiniteColimits (U.pull f))

/-- Original pull agreement is reflexivity on every actual original
map, constructed from the two restrictions of the SAME universal U. -/
theorem originalAgreement : OriginalPullAgreement (sourceSystem C U K)
    (extraScheme K k) (extraOrdinary C K k) (ordinaryA C U K k) :=
  ⟨fun _ => rfl⟩

end PrimeGap182.TypeIII.UniversalOrdinaryInverseImages

#print axioms PrimeGap182.TypeIII.UniversalOrdinaryInverseImages.sourceSystem
#print axioms PrimeGap182.TypeIII.UniversalOrdinaryInverseImages.commonObjects
#print axioms PrimeGap182.TypeIII.UniversalOrdinaryInverseImages.ordinaryA
#print axioms PrimeGap182.TypeIII.UniversalOrdinaryInverseImages.originalAgreement
