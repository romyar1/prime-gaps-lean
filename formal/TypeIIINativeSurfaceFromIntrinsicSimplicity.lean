import TypeIIINativeSurfaceFromGeometricStalks
import Mathlib.CategoryTheory.Simple

/-!
# Intrinsic simplicity on the same native perverse objects

The selected constituent list, purity and complexity remain observables.
Simple is ACTUAL categorical Simple on the fixed native full subcategory,
so its nonzero identity is a theorem rather than a supplied predicate law.
The native bounded-perverse/adic interpretation remains explicit framework
scope; this does not reconstruct a heart or a common input family.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

namespace PrimeGap182.TypeIII.NativeSurfaceFromIntrinsicSimplicity
open ExactInverseImagesToDerived OriginPoleFromExactInverseImages
open PerverseLinearPullbackFromExactInverseImages NativeSurfaceFromGeometricStalks

universe mu
variable {K0 k J : Type} [Field K0] [Field k]
  {B : SourceInverseImageSystem.System.{0,mu} K0}
  {otherScheme : J → Scheme}
  {NC : OriginRealizationFromExactInverseImages.Index → Type}
  [∀ i, Category.{mu} (NC i)] [∀ i, Abelian (NC i)]
  {LC : Type} [Category.{mu} LC] [Abelian LC]
  {OC : J → Type} [∀ i, Category.{mu} (OC i)] [∀ i, Abelian (OC i)]
  {A : OrdinarySystem (extensionScheme (extraScheme k otherScheme))
    (extensionObjects B (extraObjects NC LC OC))}

local instance nativeLocalizations : ∀ i, HasDerivedCategory.{mu} (NC i) :=
  fun i => HasDerivedCategory.standard (NC i)

variable (D : Admissibility A) (constituents : Obj D → List (Obj D))
  (Pure : Obj D → Prop) (complexity : Obj D → ℕ)

def observables : RemainingObservables D where
  constituents := constituents
  Pure := Pure
  Simple := CategoryTheory.Simple
  complexity := complexity

theorem simple_iff (Q : Obj D) :
    (observables D constituents Pure complexity).Simple Q ↔ CategoryTheory.Simple Q := Iff.rfl

theorem constituents_eq : (observables D constituents Pure complexity).constituents =
    constituents := rfl

theorem pure_eq : (observables D constituents Pure complexity).Pure = Pure := rfl

theorem complexity_eq : (observables D constituents Pure complexity).complexity = complexity := rfl

end PrimeGap182.TypeIII.NativeSurfaceFromIntrinsicSimplicity

#print axioms PrimeGap182.TypeIII.NativeSurfaceFromIntrinsicSimplicity.observables
#print axioms PrimeGap182.TypeIII.NativeSurfaceFromIntrinsicSimplicity.simple_iff
