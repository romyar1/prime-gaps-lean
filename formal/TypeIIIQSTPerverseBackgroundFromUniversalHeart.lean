import TypeIIINativePerverseFromUniversalHeart
import TypeIIIQSTAdmissibilityFromBoundedDerived

/-!
# QST perverse categories from the same universal heart

The ordinary C/U and universal perverse property P are fixed before the
prime. QST admissibility is the already constructed canonical bounded
domain. Its perverse categories and their inclusion are the SAME universal
hearts at the exact arithmetic schemes; general perverse boundedness
supplies their inclusion in this domain. Every other QST background
operation is separately curried on these fixed categories, with its actual
dependent type. No whole Background or Inputs is an argument.

General perverse boundedness and universal heart abelianness remain
published-framework parameters. Six operations, complexity and their
geometric interpretation are still separately exposed. No foundations
or complete compatible Type III family are constructed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace PrimeGap182.TypeIII.QSTPerverseBackgroundFromUniversalHeart
open ExactInverseImagesToDerived CanonicalPrimeFramework
open NativePerverseFromUniversalHeart QSTRealizationFromExactInverseImages

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)]
  [∀ X, Abelian (C X)] [∀ X, MonoidalCategory (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]

local instance allSchemeLocalizations : ∀ X : Scheme, HasDerivedCategory.{mu} (C X) :=
  fun _ => HasDerivedCategory.standard _

variable (P : ∀ X : Scheme.{0}, ObjectProperty (DerivedCategory (C X)))
  [∀ X, (P X).IsClosedUnderIsomorphisms] [∀ X, (P X).ContainsZero]
  [∀ X, Abelian (Heart C P X)]
  (perverseBounded : ∀ X (K : DerivedCategory (C X)), P X K →
    QSTAdmissibilityFromBoundedDerived.boundedProperty (C X) K)
  (p : ℕ) [Fact p.Prime]

local instance commonLocalizations : ∀ i,
    HasDerivedCategory.{mu} (extensionObjects (primeSource C U p) (extraOrdinary C p) i) :=
  fun _ => HasDerivedCategory.standard _

abbrev planeIndex : OriginPoleFromExactInverseImages.Extra NativeAuxiliarySchemes.Space :=
  Sum.inr (Sum.inr NativeAuxiliarySchemes.Space.arithmeticPlane)

/-- The SAME literal arithmetic QST domain used by the current root. -/
def domain := QSTAdmissibilityFromBoundedDerived.admissibility (primeSource C U p)
  (OriginPoleFromExactInverseImages.extraScheme (AlgebraicClosure (ZMod p))
    (NativeAuxiliarySchemes.scheme (ZMod p) (AlgebraicClosure (ZMod p))))
  (extraOrdinary C p) planeIndex rfl (primeCommon C U p)

abbrev perverseHeart (i : UniformComplexityFromCommonRealization.Space) :=
  Heart C P (UniformComplexityFromCommonRealization.scheme (ZMod p) i)

/-- Universal perverse boundedness includes the actual SAME heart in the
already constructed bounded domain, with its intrinsic underlying object. -/
def heartInclusion (i : UniformComplexityFromCommonRealization.Space) :
    perverseHeart C P p i ⥤ Obj (primeSource C U p) (domain C U p) i := by
  cases i <;> exact ((domain C U p).property _).lift (P _).ι
    (fun K => perverseBounded _ K.obj K.property)


include C U P perverseBounded p

/-- Assign four perverse background fields intrinsically and expose all
other general operations separately on those SAME objects/categories. -/
def backgroundConstructor
    (complexity : ∀ i, Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) i → ℕ)
    (GeometricConstantRankOne : ∀ i, Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) i → Prop)
    (embeddingComplexity : UniformComplexityFromCommonRealization.Space → ℕ)
    (mapComplexity : ∀ {i j}, (UniformComplexityFromCommonRealization.scheme (ZMod p) i ⟶ UniformComplexityFromCommonRealization.scheme (ZMod p) j) → ℕ)
    (tensor : ∀ i, Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) i → Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) i → Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) i)
    (unit : ∀ i, Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) i)
    (tensorIso : ∀ i {X X' Y Y' : Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) i}, (X ≅ X') → (Y ≅ Y') → (tensor i X Y ≅ tensor i X' Y'))
    (tensorUnit : ∀ i X, tensor i (unit i) X ≅ X)
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
  tensor := tensor
  unit := unit
  tensorIso := tensorIso
  tensorUnit := tensorUnit
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

end PrimeGap182.TypeIII.QSTPerverseBackgroundFromUniversalHeart

#print axioms PrimeGap182.TypeIII.QSTPerverseBackgroundFromUniversalHeart.heartInclusion
#print axioms PrimeGap182.TypeIII.QSTPerverseBackgroundFromUniversalHeart.backgroundConstructor
