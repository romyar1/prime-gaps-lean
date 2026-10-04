import TypeIIINativeLocalSupportFromGeometricDimensions

/-!
# Native coefficient transport with actual categorical isomorphism

The isomorphism predicate is Nonempty(P ≅ Q) on the SAME native perverse
category, never a selected relation. Actual point inverse image and ordinary
cohomology give geomDim_isomorphic. Only coefficient/dilation operations and
their other five general support/dimension laws remain parameters.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

namespace PrimeGap182.TypeIII.NativeCoefficientTransportFromIsomorphisms
open ExactInverseImagesToDerived OriginPoleFromExactInverseImages
open PerverseLinearPullbackFromExactInverseImages NativeSurfaceFromGeometricStalks
open PublishedSupportRules

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

variable (D : Admissibility A) (point : J)
  (hPoint : otherScheme point = pointScheme k)
  {E : Type} [Field E] (fiber : OC point ⥤ ModuleCat.{mu} E)
  (O : RemainingObservables D)
  (coefficientOp : Obj D → Obj D) (dilateOp : kˣ → Obj D → Obj D)

/-- The OTHER five general laws, on actual native objects/dimensions.
The first is a Jordan–Hölder support law under genuine native isomorphism.
No completed CoefficientTransport or arbitrary Isomorphic predicate occurs. -/
structure RemainingTransportLaws : Prop where
  supports_isomorphic : ∀ {Q R : Obj D}, Nonempty (Q ≅ R) →
    (surfaceData D point hPoint fiber O).constituentSupports Q =
      (surfaceData D point hPoint fiber O).constituentSupports R
  supports_coefficient : ∀ Q,
    (surfaceData D point hPoint fiber O).constituentSupports (coefficientOp Q) =
      (surfaceData D point hPoint fiber O).constituentSupports Q
  supports_dilate : ∀ a Q,
    (surfaceData D point hPoint fiber O).constituentSupports (dilateOp a Q) =
      (fun Z : Set (k × k) => (planeDilation a) ⁻¹' Z) ''
        (surfaceData D point hPoint fiber O).constituentSupports Q
  geomDim_coefficient : ∀ Q z i,
    (surfaceData D point hPoint fiber O).geomDim (coefficientOp Q) z i =
      (surfaceData D point hPoint fiber O).geomDim Q z i
  geomDim_dilate : ∀ a Q z i,
    (surfaceData D point hPoint fiber O).geomDim (dilateOp a Q) z i =
      (surfaceData D point hPoint fiber O).geomDim Q (planeDilation a z) i

variable {D point hPoint fiber O coefficientOp dilateOp}
  (L : RemainingTransportLaws D point hPoint fiber O coefficientOp dilateOp)

/-- Construct the original transport record with the intrinsic native
isomorphism predicate and derived point-dimension invariance. -/
def RemainingTransportLaws.transport : CoefficientTransport (surfaceData D point hPoint fiber O) where
  Isomorphic Q R := Nonempty (Q ≅ R)
  coefficient := coefficientOp
  dilate := dilateOp
  supports_isomorphic := L.supports_isomorphic
  supports_coefficient := L.supports_coefficient
  supports_dilate := L.supports_dilate
  geomDim_isomorphic h z i := geometricDimension_iso D point hPoint fiber (Classical.choice h) z i
  geomDim_coefficient := L.geomDim_coefficient
  geomDim_dilate := L.geomDim_dilate

/-- The exact predicate needed to use any constructive native Iso. -/
theorem RemainingTransportLaws.isomorphic_iff (Q R : Obj D) :
    L.transport.Isomorphic Q R ↔ Nonempty (Q ≅ R) := Iff.rfl

/-- Native Iso introduction needs no coefficient realization premise. -/
theorem RemainingTransportLaws.isomorphic_of_iso {Q R : Obj D} (e : Q ≅ R) :
    L.transport.Isomorphic Q R := ⟨e⟩

end PrimeGap182.TypeIII.NativeCoefficientTransportFromIsomorphisms

#print axioms PrimeGap182.TypeIII.NativeCoefficientTransportFromIsomorphisms.RemainingTransportLaws.transport
#print axioms PrimeGap182.TypeIII.NativeCoefficientTransportFromIsomorphisms.RemainingTransportLaws.isomorphic_iff
#print axioms PrimeGap182.TypeIII.NativeCoefficientTransportFromIsomorphisms.RemainingTransportLaws.isomorphic_of_iso
