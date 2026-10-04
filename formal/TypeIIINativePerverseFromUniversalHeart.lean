import TypeIIICanonicalPrimeFramework
import TypeIIIPerverseLinearPullbackFromExactInverseImages

/-!
# Native perverse objects from one universal heart property

The all-scheme ordinary C/U and one object property P on their actual
standard derived categories are fixed before the prime. Native curve and
full-plane admissibility are restrictions of P. Their perverse categories
are literally the same universal full subcategories, with the same
universal abelian structures; no alternative heart/category is selected.

P's perverse, bounded-constructible and continuous-adic interpretation,
its general zero/isomorphism properties and universal heart abelianness
remain framework parameters. Universal scheme-isomorphism pull closure,
when supplied, restricts to the actual native inverse images. Neither a
t-structure nor any whole compatible Inputs family is constructed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace PrimeGap182.TypeIII.NativePerverseFromUniversalHeart
open ExactInverseImagesToDerived CanonicalPrimeFramework

universe mu
variable (C : Scheme → Type)
  [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  [∀ X, MonoidalCategory (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]

local instance allSchemeLocalizations : ∀ X : Scheme,
    HasDerivedCategory.{mu} (C X) := fun _ => HasDerivedCategory.standard _

variable (P : ∀ X : Scheme, ObjectProperty (DerivedCategory (C X)))
  [∀ X, (P X).IsClosedUnderIsomorphisms]
  [∀ X, (P X).ContainsZero]

abbrev Heart (X : Scheme) := (P X).FullSubcategory

variable (p : ℕ) [Fact p.Prime]

local instance commonLocalizations : ∀ i,
    HasDerivedCategory.{mu} (extensionObjects (primeSource C U p) (extraOrdinary C p) i) :=
  fun _ => HasDerivedCategory.standard _

abbrev curveScheme : Scheme :=
  OriginRealizationFromExactInverseImages.scheme (AlgebraicClosure (ZMod p)) .curve

abbrev planeScheme : Scheme :=
  OriginRealizationFromExactInverseImages.scheme (AlgebraicClosure (ZMod p)) .plane

/-- Construct the old native admissibility, not a new premise record. -/
def nativeAdmissibility :
    PerverseLinearPullbackFromExactInverseImages.Admissibility (primeCommon C U p) where
  curve := P (curveScheme p)
  plane := P (planeScheme p)
  curveIso := inferInstance
  planeIso := inferInstance
  planeZero := inferInstance

theorem curveProperty : (nativeAdmissibility C U P p).curve = P (curveScheme p) := rfl
theorem planeProperty : (nativeAdmissibility C U P p).plane = P (planeScheme p) := rfl

theorem curveHeart :
    PerverseLinearPullbackFromExactInverseImages.CurveObj (nativeAdmissibility C U P p) =
      Heart C P (curveScheme p) := rfl

theorem planeHeart :
    PerverseLinearPullbackFromExactInverseImages.Obj (nativeAdmissibility C U P p) =
      Heart C P (planeScheme p) := rfl

/-- The category on native perverse objects is the intrinsic full
subcategory category, not another category structure. -/
theorem curveCategory :
    (inferInstance : Category.{mu}
      (PerverseLinearPullbackFromExactInverseImages.CurveObj (nativeAdmissibility C U P p))) =
    (inferInstance : Category.{mu} (Heart C P (curveScheme p))) := rfl

theorem planeCategory :
    (inferInstance : Category.{mu}
      (PerverseLinearPullbackFromExactInverseImages.Obj (nativeAdmissibility C U P p))) =
    (inferInstance : Category.{mu} (Heart C P (planeScheme p))) := rfl

section Abelian
variable [heartAbelian : ∀ X : Scheme, Abelian (Heart C P X)]

@[instance_reducible]
def curveAbelian : Abelian
    (PerverseLinearPullbackFromExactInverseImages.CurveObj (nativeAdmissibility C U P p)) :=
  heartAbelian (curveScheme p)

@[instance_reducible]
def planeAbelian : Abelian
    (PerverseLinearPullbackFromExactInverseImages.Obj (nativeAdmissibility C U P p)) :=
  heartAbelian (planeScheme p)

theorem curveAbelianUsesHeart : curveAbelian C U P p = heartAbelian (curveScheme p) := rfl
theorem planeAbelianUsesHeart : planeAbelian C U P p = heartAbelian (planeScheme p) := rfl

end Abelian

/-- The perverse-category comparisons are actual identity equivalences. -/
def curveEquivalence :
    PerverseLinearPullbackFromExactInverseImages.CurveObj (nativeAdmissibility C U P p) ≌
      Heart C P (curveScheme p) := CategoryTheory.Equivalence.refl

def planeEquivalence :
    PerverseLinearPullbackFromExactInverseImages.Obj (nativeAdmissibility C U P p) ≌
      Heart C P (planeScheme p) := CategoryTheory.Equivalence.refl

theorem curveInclusionUsesHeart : (nativeAdmissibility C U P p).curve.ι =
    (P (curveScheme p)).ι := rfl

theorem planeInclusionUsesHeart : (nativeAdmissibility C U P p).plane.ι =
    (P (planeScheme p)).ι := rfl

variable (isoPullHeart : ∀ {X Y : Scheme} (e : X ≅ Y)
    (K : DerivedCategory (C Y)), P Y K → P X ((U.derivedPull e.hom).obj K))

include isoPullHeart in
/-- Restrict general ALL-scheme isomorphism pull closure to the actual
native full plane; the functor is the SAME exact U-derived pull. -/
theorem nativePlaneIsoPull : ∀
    (e : RankTwoFourierKernelCoordinates.planeScheme (AlgebraicClosure (ZMod p)) ≅
      RankTwoFourierKernelCoordinates.planeScheme (AlgebraicClosure (ZMod p)))
    (K : (OriginPoleFromExactInverseImages.nativeSystem (primeCommon C U p)).Derived .plane),
    (nativeAdmissibility C U P p).plane K →
      (nativeAdmissibility C U P p).plane
        (((primeCommon C U p).derivedPull
          (i := OriginPoleFromExactInverseImages.nativeIndex .plane)
          (j := OriginPoleFromExactInverseImages.nativeIndex .plane) e.hom).obj K) := by
  intro e K hK
  exact isoPullHeart e K hK

include isoPullHeart in
theorem nativeCurveIsoPull : ∀ (e : curveScheme p ≅ curveScheme p)
    (K : (primeNative C U p).Derived .curve),
    (nativeAdmissibility C U P p).curve K →
      (nativeAdmissibility C U P p).curve
        (((primeNative C U p).derivedPull (i := .curve) (j := .curve) e.hom).obj K) := by
  intro e K hK
  exact isoPullHeart e K hK

/-- C/U/P are fixed before every prime in this family application. -/
def nativeAdmissibilityFamily : ∀ p : ℕ, ∀ (_ : Fact p.Prime),
    PerverseLinearPullbackFromExactInverseImages.Admissibility (primeCommon C U p) :=
  fun p _ => nativeAdmissibility C U P p

end PrimeGap182.TypeIII.NativePerverseFromUniversalHeart

#print axioms PrimeGap182.TypeIII.NativePerverseFromUniversalHeart.nativeAdmissibility
#print axioms PrimeGap182.TypeIII.NativePerverseFromUniversalHeart.planeEquivalence
#print axioms PrimeGap182.TypeIII.NativePerverseFromUniversalHeart.nativePlaneIsoPull
#print axioms PrimeGap182.TypeIII.NativePerverseFromUniversalHeart.nativeAdmissibilityFamily
