import TypeIIIPerverseLinearPullbackFromExactInverseImages

/-!
# A concrete published theory on the native perverse objects

This constructor fixes Obj, CurveObj and FourierData to the admissible
native full-plane/curve objects and the actual linear inverse image [1].
The nine remaining surface, coefficient, support and stalk framework
arguments are explicit and typed on those SAME objects. No TheoryData or
root Inputs record is an assumption. The origin application is constructed
from actual native radial inverse image, ordinary H^-2 and ONE ordinary
wild functor. The original AS source and its canonical base-field map are
retained by the common origin/Pole constructor.

OtherLocalRules remains the nine precisely guarded general rules for
support/isomorphism, Fourier constituents, profiles, phases and inverse
point/line transforms. BBD, QST, support classification/degrees, rational
stalk and trace-weight rules retain their own published domains. None is
certified for a complete common continuous constructible Q2-adic model
here. Perverse interpretation, p != 2, the ordinary wild realization,
the original AS membership dictionary and profile/phase dictionaries are
still explicit realization scope. This builds the theory interface from
those fixed native operations, not the entire residual source family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

namespace PrimeGap182.TypeIII.TheoryFromNativePerverseInverseImages

open ExactInverseImagesToDerived OriginPoleFromExactInverseImages
open PerverseLinearPullbackFromExactInverseImages
open LinearRadialPhaseFromPoleTransport

universe mu e g

variable {p : ℕ} [Fact p.Prime] {J : Type}
  {B : SourceInverseImageSystem.System.{0,mu} (ZMod p)}
  {otherScheme : J → Scheme}
  {NC : OriginRealizationFromExactInverseImages.Index → Type}
  [∀ i, Category.{mu} (NC i)] [∀ i, Abelian (NC i)]
  {LC : Type} [Category.{mu} LC] [Abelian LC]
  {OC : J → Type} [∀ i, Category.{mu} (OC i)] [∀ i, Abelian (OC i)]
  {A : OrdinarySystem (extensionScheme (extraScheme (AlgebraicClosure (ZMod p)) otherScheme))
    (extensionObjects B (extraObjects NC LC OC))}
  (D : Admissibility A)
  (smooth : SmoothPullbackLaw D)
  (ops : Operations D)
  (surface : PublishedSupportRules.SurfaceData (AlgebraicClosure (ZMod p)) (Obj D))
  (bbd : PublishedSupportRules.BBDRules surface)
  (qst : PublishedSupportRules.QSTRules surface)
  (classification : PublishedSupportRules.SupportClassification surface)
  (degrees : PublishedSupportRules.OrdinarySupportDegreeRules surface)
  (coefficient : PublishedSupportRules.CoefficientTransport surface)
  (otherLocalRules : OtherLocalRules (F := fourierData smooth ops) surface coefficient)
  (realization : PublishedSupportRules.RationalStalkRealization p surface)
  (traceWeights : PublishedStalkCertificate.TraceWeightRules p surface realization
    (fourierData smooth ops).fourier)

/-- All three object/operation selections are constructed. The remaining
nine general framework arguments are explicit on the fixed native model. -/
def theoryData : TheoryData.{mu,mu} p where
  Obj := Obj D
  CurveObj := CurveObj D
  data := surface
  bbd := bbd
  qst := qst
  classification := classification
  degrees := degrees
  coefficient := coefficient
  fourier := fourierData smooth ops
  otherLocalRules := otherLocalRules
  realization := realization
  traceWeights := traceWeights

variable {E : Type e} [Field E] {G : Type g} [Group G]
  (W : OrdinaryWild (E := E) (G := G) A)

/-- No specific linear or radial comparison is assumed: both come from
the native object definitions in the perverse adapter. -/
def origin : DerivedOrigin
    (theoryData D smooth ops surface bbd qst classification degrees coefficient
      otherLocalRules realization traceWeights).fourier (radial (D := D) W) :=
  OriginalObjects.nativeOrigin W (originalObjects smooth ops W)

variable (as : B.Obj .line)
  (PD : PublishedPhaseApplication.PhaseData (AlgebraicClosure (ZMod p)) E G)
  (recognition : ASRecognition W as PD)
  (profile : ∀ P, (fourierData smooth ops).HasSimpleRadialPhases P ↔
    PD.HasProfile (radial (D := D) W P))
  (phases : ∀ P, (fourierData smooth ops).phases P =
    PD.phases (radial (D := D) W P))

/-- The original theory is assembled from the concrete native model,
the original AS line and separate general/profile realization arguments. -/
def publishedTheory : PublishedTypeIII.Theory.{mu,mu} p :=
  (theoryData D smooth ops surface bbd qst classification degrees coefficient
    otherLocalRules realization traceWeights).toTheory
    (radial (D := D) W) as PD
    (OriginalObjects.nativeOrigin W (originalObjects smooth ops W))
    (OriginalObjects.toPole W (originalObjects smooth ops W) recognition) profile phases

end PrimeGap182.TypeIII.TheoryFromNativePerverseInverseImages

#print axioms PrimeGap182.TypeIII.TheoryFromNativePerverseInverseImages.theoryData
#print axioms PrimeGap182.TypeIII.TheoryFromNativePerverseInverseImages.origin
#print axioms PrimeGap182.TypeIII.TheoryFromNativePerverseInverseImages.publishedTheory
