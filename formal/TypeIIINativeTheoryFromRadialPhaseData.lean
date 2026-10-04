import TypeIIITheoryFromNativePerverseInverseImages

/-!
# Native radial observables from the same PhaseData

Only Fourier and inverse operations on the exact native perverse plane
objects are selected. The radial representation is the actual native
radial inverse image, ordinary H^-2, and the SAME shared ordinary wild
functor W. Its profile and phase set are defined by ONE PhaseData PD.
Thus the former radialInertia, radialProfile and radialPhases choices
are no longer independent parameters of this constructor; both profile
and phase dictionaries are reflexive equalities.

The nine general surface/coefficient/support/stalk arguments remain
explicit on the fixed native objects and these constructed observables.
No whole TheoryData or Inputs is a premise. The canonical Fourier
operation is still a general operation parameter: this module does not
construct it from the full AS kernel or prove its published laws.
Perverse/continuous constructible Q2-adic realization with p != 2,
ordinary original-J group transport, and original AS recognition remain
explicit framework scope; no complete common input family is certified.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

namespace PrimeGap182.TypeIII.NativeTheoryFromRadialPhaseData

open ExactInverseImagesToDerived OriginPoleFromExactInverseImages
open PerverseLinearPullbackFromExactInverseImages LinearRadialPhaseFromPoleTransport

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
  (fourierOp inverseOp : Obj D → Obj D)
  {E : Type e} [Field E] {G : Type g} [Group G]
  (W : OrdinaryWild (E := E) (G := G) A)
  (PD : PublishedPhaseApplication.PhaseData (AlgebraicClosure (ZMod p)) E G)

/-- Both radial observables are defined from the SAME native radial
H^-2 representation and PD; only Fourier and inverse remain selections. -/
def operations : Operations D where
  fourier := fourierOp
  inverse := inverseOp
  HasSimpleRadialPhases P := PD.HasProfile (radial (D := D) W P)
  phases P := PD.phases (radial (D := D) W P)

/-- The general profile dictionary is an identity for every native object. -/
theorem profile (P : Obj D) :
    (operations D fourierOp inverseOp W PD).HasSimpleRadialPhases P ↔
      PD.HasProfile (radial (D := D) W P) := Iff.rfl

/-- The FULL phase set, including coefficient0 when present, is the same
set by definition, without selecting or losing any branch. -/
theorem phases (P : Obj D) :
    (operations D fourierOp inverseOp W PD).phases P =
      PD.phases (radial (D := D) W P) := rfl

variable (smooth : SmoothPullbackLaw D)
  (surface : PublishedSupportRules.SurfaceData (AlgebraicClosure (ZMod p)) (Obj D))
  (bbd : PublishedSupportRules.BBDRules surface)
  (qst : PublishedSupportRules.QSTRules surface)
  (classification : PublishedSupportRules.SupportClassification surface)
  (degrees : PublishedSupportRules.OrdinarySupportDegreeRules surface)
  (coefficient : PublishedSupportRules.CoefficientTransport surface)
  (otherLocalRules : OtherLocalRules
    (F := fourierData smooth (operations D fourierOp inverseOp W PD)) surface coefficient)
  (realization : PublishedSupportRules.RationalStalkRealization p surface)
  (traceWeights : PublishedStalkCertificate.TraceWeightRules p surface realization
    (fourierData smooth (operations D fourierOp inverseOp W PD)).fourier)

/-- The native theory data has no arbitrary radial observables, object
types, linear pullback, or supplied whole theory record. -/
def theoryData : TheoryData.{mu,mu} p :=
  TheoryFromNativePerverseInverseImages.theoryData D smooth
    (operations D fourierOp inverseOp W PD) surface bbd qst classification degrees
    coefficient otherLocalRules realization traceWeights

variable (as : B.Obj .line) (recognition : ASRecognition W as PD)

/-- Compose the existing fixed-native theory constructor with the
reflexive profile/phase dictionaries and original AS recognition. -/
def publishedTheory : PublishedTypeIII.Theory.{mu,mu} p :=
  TheoryFromNativePerverseInverseImages.publishedTheory D smooth
    (operations D fourierOp inverseOp W PD) surface bbd qst classification degrees
    coefficient otherLocalRules realization traceWeights W as PD recognition
    (profile D fourierOp inverseOp W PD) (phases D fourierOp inverseOp W PD)

end PrimeGap182.TypeIII.NativeTheoryFromRadialPhaseData

#print axioms PrimeGap182.TypeIII.NativeTheoryFromRadialPhaseData.operations
#print axioms PrimeGap182.TypeIII.NativeTheoryFromRadialPhaseData.profile
#print axioms PrimeGap182.TypeIII.NativeTheoryFromRadialPhaseData.phases
#print axioms PrimeGap182.TypeIII.NativeTheoryFromRadialPhaseData.theoryData
#print axioms PrimeGap182.TypeIII.NativeTheoryFromRadialPhaseData.publishedTheory
