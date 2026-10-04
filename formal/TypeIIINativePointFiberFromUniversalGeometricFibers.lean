import TypeIIINativePerverseFromUniversalHeart
import TypeIIINativeSurfaceFromGeometricStalks

/-!
# The native point fiber from one all-field ordinary coefficient fiber

The ordinary categories and one geometric coefficient-fiber family are
fixed before the prime. Restriction at the actual geometric spectrum
constructs the nativePointFiber and inherits its four ordinary functor
structures. Finite-dimensionality of every ordinary coefficient fiber
proves the finite half of the actual native point-cohomology laws.

The constructible/adic interpretation, the general ordinary coefficient
fibers and their exactness/faithfulness remain explicit general framework
parameters. The perverse point-amplitude theorem remains separate. No
whole native StalkLaws or Inputs record is a parameter.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace PrimeGap182.TypeIII.NativePointFiberFromUniversalGeometricFibers
open ExactInverseImagesToDerived CanonicalPrimeFramework
open NativePerverseFromUniversalHeart NativeSurfaceFromGeometricStalks

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]

/-- Ordinary constructible geometric coefficient fibers on every field,
with their usual general functor structures, fixed before prime choice. -/
structure GeometricFibers where
  fiber : ∀ (E : Type) [Field E], C (Spec (.of E)) ⥤ ModuleCat.{mu} ℂ
  [additive : ∀ (E : Type) [Field E], (fiber E).Additive]
  [faithful : ∀ (E : Type) [Field E], (fiber E).Faithful]
  [limits : ∀ (E : Type) [Field E], PreservesFiniteLimits (fiber E)]
  [colimits : ∀ (E : Type) [Field E], PreservesFiniteColimits (fiber E)]
  finite : ∀ (E : Type) [Field E] A, FiniteDimensional ℂ ((fiber E).obj A)

attribute [instance] GeometricFibers.additive GeometricFibers.faithful
  GeometricFibers.limits GeometricFibers.colimits

variable (F : GeometricFibers C) (p : ℕ) [Fact p.Prime]

/-- The literal ordinary fiber on the SAME native geometric spectrum. -/
def nativePointFiber : extraOrdinary C p (Sum.inr (Sum.inr NativeAuxiliarySchemes.Space.geometricPoint)) ⥤
    ModuleCat.{mu} ℂ := F.fiber (AlgebraicClosure (ZMod p))

instance nativeAdditive : (nativePointFiber C F p).Additive :=
  F.additive (AlgebraicClosure (ZMod p))
instance nativeFaithful : (nativePointFiber C F p).Faithful :=
  F.faithful (AlgebraicClosure (ZMod p))
instance nativeLimits : PreservesFiniteLimits (nativePointFiber C F p) :=
  F.limits (AlgebraicClosure (ZMod p))
instance nativeColimits : PreservesFiniteColimits (nativePointFiber C F p) :=
  F.colimits (AlgebraicClosure (ZMod p))

local instance allSchemeLocalizations : ∀ X : Scheme, HasDerivedCategory.{mu} (C X) :=
  fun _ => HasDerivedCategory.standard _

variable [∀ X, MonoidalCategory (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (P : ∀ X : Scheme.{0}, ObjectProperty (DerivedCategory (C X)))
  [∀ X, (P X).IsClosedUnderIsomorphisms] [∀ X, (P X).ContainsZero]

/-- EVERY actual native point cohomology is finite because its ordinary
cohomology is evaluated by the one finite ordinary coefficient fiber. -/
theorem nativePointCohomology_finite
    (Q : PerverseLinearPullbackFromExactInverseImages.Obj (nativeAdmissibility C U P p))
    (z : AlgebraicClosure (ZMod p) × AlgebraicClosure (ZMod p)) (n : ℤ) :
    FiniteDimensional ℂ (pointCohomology (nativeAdmissibility C U P p)
      NativeAuxiliarySchemes.Space.geometricPoint rfl (nativePointFiber C F p) Q z n) := by
  exact F.finite (AlgebraicClosure (ZMod p)) _

end PrimeGap182.TypeIII.NativePointFiberFromUniversalGeometricFibers

#print axioms PrimeGap182.TypeIII.NativePointFiberFromUniversalGeometricFibers.nativePointFiber
#print axioms PrimeGap182.TypeIII.NativePointFiberFromUniversalGeometricFibers.nativePointCohomology_finite
