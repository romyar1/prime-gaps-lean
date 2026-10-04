import TypeIIICoherentGeneralOpenCompactKernelApplication01
import TypeIIIRelativeAffineFourierKernelRestrictionFromInverseImages
import TypeIIICoherentNormalizedFourierCompactInfinity03
import TypeIIIFourierNormalizationMaps

/-!
# Actual ordinary j-star AS kernel and normalized affine compact fiber

Reuse the existing GENERAL smooth SOURCE/open base-change and lisse
projection application on the literal AS kernel. The SAME U compositor
and kernel coordinate equations give its punctured recipe. Apply the
SAME compact cohomology and radial observer to obtain the original affine
comparison, and compose the computed normalized perverse-origin diagram.

The target retains A1 compact cohomology of ordinary j-star. It is NOT
identified with Gm compact cohomology: the degree-zero boundary term is
retained, so rank-nine compact is not exchanged with rank-six middle.
No selected source comparison, FC, profile, rank or bound is an input.
GENERAL theory semantics and actual radial observer eligibility remain
external. No coherent adic model or Type III completion is asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.OriginalAffineKernelFromPublishedOpenCompact03

open PublishedPhaseApplication GenericSourceSpecialization FourierSourceMaps
open GenericRelativeAffineLineCoordinates RelativeAffineFourierKernelFromActualCoordinates
open OrdinaryOpenExtensionsFromAdjunctions QSTCompactBridgeFromCompactifiedDerivedPushforward
open OrdinaryFourierKernelExtensionFromGeneralSmoothBaseChange
open ActualRelativeFourierKernelExtensionFromPublishedOpenTheorems
open CoherentNormalizedFourierCompactInfinity03 FourierNormalizationMaps
open CoherentGeneralOpenCompactKernelApplication01

universe mu u v w z a b
variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)]
  [∀ X, Abelian (C X)] [∀ X, MonoidalCategory (C X)]
  (U : ExactInverseImagesToDerived.OrdinarySystem (fun X : Scheme => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (O : Operations C) (F : OrdinaryOpenFamily C U)
  (lisse : ∀ X : Scheme, ObjectProperty (C X))
  (smoothOpen : UniversalSmoothOpenBaseChange C U F)
  (lisseProjection : UniversalLisseOpenProjection C U F lisse)
  (lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y),
    lisse Y A → lisse X ((U.pull f).obj A))
  (compactBaseChange : UniversalCompactBaseChange C U O)

variable (K : Type) [Field K] (h2 : (2 : PhaseField K) ≠ 0)
  (c : Compactification (relativeProjection K))
  {Outer : Type u} [Group Outer]

local instance allSchemeLocalizations : ∀ X : Scheme, HasDerivedCategory.{mu} (C X) :=
  fun _ => HasDerivedCategory.standard _

section PositiveKernelExtension
include smoothOpen lisseProjection lissePull

/-- The exact ordinary extension on ALL source objects. The AS line's
only guard is its genuine globally smooth lissity. The open restriction
uses the existing literal kernel equation and U compositor. -/
def positiveKernelExtension (as : C (StartingSourceMaps.affineLine K))
    (hAS : lisse (StartingSourceMaps.affineLine K) as) :
    F.push (PhaseField K) h2
        (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.gmPresentation (PhaseField K))
        (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.linePresentation (PhaseField K))
        (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K)) rfl ⋙
      RelativeAffineFourierKernelRestrictionFromInverseImages.kernelFunctor K C U as ≅
    RelativeAffineFourierKernelRestrictionFromInverseImages.puncturedKernelFunctor K C U as ⋙
      relativeOpenExtend C U F K h2 :=
  CoherentGeneralOpenCompactKernelApplication01.sourceExtension C U F lisse
      smoothOpen lisseProjection K h2 ((U.pull (kernelMorphism K)).obj as)
      (lissePull _ as hAS) ≪≫
    Functor.isoWhiskerRight
      (CoherentGeneralOpenCompactKernelApplication01.positiveKernelIso C U K as)
      (relativeOpenExtend C U F K h2)

end PositiveKernelExtension

/-- The full-source degree-one compact recipe is defined literally from
the SAME kernel, retained compactification and coefficient observer. -/
def observedFullCompactFunctor (as : C (StartingSourceMaps.affineLine K))
    (observer : C (GenericCurvePullback.parameterScheme K) ⥤ FDRep ℂ Outer) :
    C (StartingSourceMaps.affineLine (PhaseField K)) ⥤ FDRep ℂ Outer :=
  RelativeAffineFourierKernelRestrictionFromInverseImages.kernelFunctor K C U as ⋙
    (cohomologyData C O c 1).compact ⋙ observer

/-- The original affine compact recipe includes SAME ordinary relative
j-star before compact cohomology; it keeps the zero-stalk quotient. -/
def observedAffineFunctor (observer : C (GenericCurvePullback.parameterScheme K) ⥤ FDRep ℂ Outer) :
    C (genericScheme K) ⥤ FDRep ℂ Outer :=
  relativeOpenExtend C U F K h2 ⋙
    (cohomologyData C O c 1).compact ⋙ observer

section ObservedOriginalAffine
include smoothOpen lisseProjection lissePull

/-- Apply compact cohomology and the SAME radial observer to the computed
ALL-source ordinary kernel extension. No final fiber isomorphism premise. -/
def observedOriginalAffineIso (as : C (StartingSourceMaps.affineLine K))
    (hAS : lisse (StartingSourceMaps.affineLine K) as)
    (observer : C (GenericCurvePullback.parameterScheme K) ⥤ FDRep ℂ Outer) (A : C (localScheme K)) :
    (observedFullCompactFunctor C U O K c as observer).obj
      ((F.push (PhaseField K) h2
        (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.gmPresentation (PhaseField K))
        (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.linePresentation (PhaseField K))
        (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K)) rfl).obj A) ≅
    (observedAffineFunctor C U O F K h2 c observer).obj
      ((RelativeAffineFourierKernelRestrictionFromInverseImages.puncturedKernelFunctor K C U as).obj A) :=
  ((cohomologyData C O c 1).compact ⋙ observer).mapIso
    ((positiveKernelExtension C U F lisse smoothOpen lisseProjection lissePull K h2 as hAS).app A)

end ObservedOriginalAffine

/-- The scale observer is the literal frequency pullback xi=T^2/s
followed by ONE chosen genuine radial observer. -/
def scaledObserver (s : (PhaseField K)ˣ)
    (observer : C (GenericCurvePullback.parameterScheme K) ⥤ FDRep ℂ Outer) :
    C (GenericCurvePullback.parameterScheme K) ⥤ FDRep ℂ Outer :=
  U.pull (frequencyMorphism K s) ⋙ observer

/-- This punctured recipe uses exactly the original additive source map,
not an independently chosen kernel: local specialization tensor AS(T^2*x/s). -/
def normalizedPuncturedKernelFunctor (as : C (StartingSourceMaps.affineLine K))
    (s : (PhaseField K)ˣ) : C (localScheme K) ⥤ C (genericScheme K) :=
  U.pull (projectionMorphism K) ⋙ tensorRight ((U.pull (additiveMorphism K s)).obj as)

/-- U compositors, monoidality and the already-proved coordinate equations
compute the whole ALL-source normalized AS kernel transport. -/
def normalizedPuncturedKernelIso (as : C (StartingSourceMaps.affineLine K))
    (s : (PhaseField K)ˣ) :
    RelativeAffineFourierKernelRestrictionFromInverseImages.puncturedKernelFunctor K C U as ⋙
      U.pull (curveMorphism K s) ≅ normalizedPuncturedKernelFunctor C U K as s :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (U.pull (projectionMorphism K))
      (Functor.Monoidal.commTensorRight (U.pull (curveMorphism K s))
        ((U.pull (universalKernelMorphism K)).obj as)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (U.composition (curveMorphism K s) (projectionMorphism K) ≪≫
        eqToIso (congrArg (fun f => U.pull f) (curve_projection K s))) _ ≪≫
    Functor.isoWhiskerLeft (U.pull (projectionMorphism K))
      ((tensoringRight (C (genericScheme K))).mapIso
        ((U.composition (curveMorphism K s) (universalKernelMorphism K) ≪≫
          eqToIso (congrArg (fun f => U.pull f) (curve_kernel K s))).app as))

section NormalizedOrigin
variable {Perv : Type v} [Category.{w} Perv]
  {Derived : Type z} [Category.{a} Derived]
  {I : Type b} [Group I]
  {LF : PublishedLocalConstruction.LocalFourierData K ℂ I Outer}
  (underlying : Perv ⥤ Derived)
  (N : CurveNormalizationOperations
    (Ord := C (StartingSourceMaps.affineLine (PhaseField K))) underlying)
  (S : StandardFiniteOriginOperations (LF := LF) underlying)

/-- Precisely GENERAL Fourier/truncation/point cohomology laws on the
literal full-kernel compact recipe. The observer family is the ONE actual
standard radial pullback/generic inertia operation at every nonzero scale.
No normalized origin/affine comparison or selected correlation occurs. -/
structure ObservedFourierCurveRules (as : C (StartingSourceMaps.affineLine K)) where
  radialObserver : C (GenericCurvePullback.parameterScheme K) ⥤ FDRep ℂ Outer
  ordinaryInfinity : C (StartingSourceMaps.affineLine (PhaseField K)) ⥤ FDRep ℂ I
  fourierFiber : ∀ (s : PhaseField K) (hs : s ≠ 0),
    (N.shiftOne ⋙ S.radialFourier s hs) ⋙ S.originGenericMinusOne ≅
      observedFullCompactFunctor C U O K c as (scaledObserver (C := C) (U := U) (K := K) (Units.mk0 s hs) radialObserver)
  compactQuotientIsIso : ∀ (s : PhaseField K) (hs : s ≠ 0) A,
    IsIso ((observedFullCompactFunctor C U O K c as (scaledObserver (C := C) (U := U) (K := K) (Units.mk0 s hs) radialObserver)).map
      (N.quotientMap.app A))
  infinityFiber : N.shiftOne ⋙ S.infinityGenericMinusOne ≅ ordinaryInfinity
  infinityQuotientIsIso : ∀ A, IsIso (ordinaryInfinity.map (N.quotientMap.app A))

/-- The per-scale observer is computed from one observer and literal U frequency pullback. -/
def ObservedFourierCurveRules.observer
    {as : C (StartingSourceMaps.affineLine K)}
    (R : ObservedFourierCurveRules C U O K c underlying N S as)
    (s : PhaseField K) (hs : s ≠ 0) : C (GenericCurvePullback.parameterScheme K) ⥤ FDRep ℂ Outer :=
  scaledObserver (C := C) (U := U) (K := K) (Units.mk0 s hs) R.radialObserver

/-- The compact field is the literal SAME full AS recipe, not another
chosen functor later identified only at the selected family. -/
def ObservedFourierCurveRules.curveFiberRules
    {as : C (StartingSourceMaps.affineLine K)}
    (R : ObservedFourierCurveRules C U O K c underlying N S as) : GeneralCurveFiberRules N S where
  compactDegreeOne s hs := observedFullCompactFunctor C U O K c as (ObservedFourierCurveRules.observer (C := C) (U := U) (O := O) (K := K) (c := c)
      (underlying := underlying) (N := N) (S := S) (R := R) s hs)
  ordinaryInfinity := R.ordinaryInfinity
  fourierFiber s hs := R.fourierFiber s hs
  compactQuotientIsIso s hs A := R.compactQuotientIsIso s hs A
  infinityFiber := R.infinityFiber
  infinityQuotientIsIso A := R.infinityQuotientIsIso A

include smoothOpen lisseProjection lissePull

/-- The normalized perverse origin is compared to the original SAME
ordinary affine compact cohomology recipe. Its zero-stalk quotient remains
present throughout; no Gm compact-rank replacement occurs. -/
def normalizedOriginToOriginalAffineIso
    (as : C (StartingSourceMaps.affineLine K))
    (hAS : lisse (StartingSourceMaps.affineLine K) as)
    (R : ObservedFourierCurveRules C U O K c underlying N S as)
    (s : PhaseField K) (hs : s ≠ 0) (A : C (localScheme K)) :
    (normalizedData N S).origin s hs
      ((F.push (PhaseField K) h2
        (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.gmPresentation (PhaseField K))
        (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.linePresentation (PhaseField K))
        (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K)) rfl).obj A) ≅
    (observedAffineFunctor C U O F K h2 c (ObservedFourierCurveRules.observer (C := C) (U := U) (O := O) (K := K) (c := c)
      (underlying := underlying) (N := N) (S := S) (R := R) s hs)).obj
      ((RelativeAffineFourierKernelRestrictionFromInverseImages.puncturedKernelFunctor K C U as).obj A) :=
  normalizedOriginCompactIso N S (R.curveFiberRules) s hs _ ≪≫
    observedOriginalAffineIso C U O F lisse smoothOpen lisseProjection lissePull K h2 c as hAS
      (ObservedFourierCurveRules.observer (C := C) (U := U) (O := O) (K := K) (c := c)
      (underlying := underlying) (N := N) (S := S) (R := R) s hs) A

/-- Expose the equivariant fiber on the same constructed objects. -/
def normalizedOriginToOriginalAffineEquiv
    (as : C (StartingSourceMaps.affineLine K))
    (hAS : lisse (StartingSourceMaps.affineLine K) as)
    (R : ObservedFourierCurveRules C U O K c underlying N S as)
    (s : PhaseField K) (hs : s ≠ 0) (A : C (localScheme K)) :
    Representation.Equiv
      ((normalizedData N S).origin s hs
        ((F.push (PhaseField K) h2
          (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.gmPresentation (PhaseField K))
          (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.linePresentation (PhaseField K))
          (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K)) rfl).obj A)).ρ
      ((observedAffineFunctor C U O F K h2 c (ObservedFourierCurveRules.observer (C := C) (U := U) (O := O) (K := K) (c := c)
      (underlying := underlying) (N := N) (S := S) (R := R) s hs)).obj
        ((RelativeAffineFourierKernelRestrictionFromInverseImages.puncturedKernelFunctor K C U as).obj A)).ρ :=
  TensorListRepresentation.equivOfIso
    (normalizedOriginToOriginalAffineIso C U O F lisse smoothOpen lisseProjection lissePull
      K h2 c underlying N S as hAS R s hs A)

section LiteralFrequencyBridge
include compactBaseChange smoothOpen lisseProjection lissePull

/-- Apply GENERAL compact BC on the PROVED frequency square, then the
computed source/AS kernel transport. This removes arbitrary scale observer
and generic-additive-source comparison cuts on the actual recipe. -/
def normalizedOriginToLiteralASAffineIso
    (as : C (StartingSourceMaps.affineLine K))
    (hAS : lisse (StartingSourceMaps.affineLine K) as)
    (R : ObservedFourierCurveRules C U O K c underlying N S as)
    (s : PhaseField K) (hs : s ≠ 0) (A : C (localScheme K)) :
    (normalizedData N S).origin s hs
      ((F.push (PhaseField K) h2
        (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.gmPresentation (PhaseField K))
        (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.linePresentation (PhaseField K))
        (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K)) rfl).obj A) ≅
    (observedAffineFunctor C U O F K h2 c R.radialObserver).obj
      ((normalizedPuncturedKernelFunctor C U K as (Units.mk0 s hs)).obj A) :=
  normalizedOriginToOriginalAffineIso C U O F lisse smoothOpen lisseProjection lissePull
      K h2 c underlying N S as hAS R s hs A ≪≫
    R.radialObserver.mapIso
      (CoherentGeneralOpenCompactKernelApplication01.positiveBaseChange
        C U O F lisse smoothOpen lisseProjection lissePull compactBaseChange K h2 c
        (frequencyMorphism K (Units.mk0 s hs)) (curveMorphism K (Units.mk0 s hs))
        (normalizationSquare_isPullback K (Units.mk0 s hs)) (curve_projection K (Units.mk0 s hs))
        as hAS A) ≪≫
    (observedAffineFunctor C U O F K h2 c R.radialObserver).mapIso
      ((normalizedPuncturedKernelIso C U K as (Units.mk0 s hs)).app A)

/-- The literal original-coordinate comparison preserves the SAME radial
inertia action; expose its equivariant form for the finite-origin caller. -/
def normalizedOriginToLiteralASAffineEquiv
    (as : C (StartingSourceMaps.affineLine K))
    (hAS : lisse (StartingSourceMaps.affineLine K) as)
    (R : ObservedFourierCurveRules C U O K c underlying N S as)
    (s : PhaseField K) (hs : s ≠ 0) (A : C (localScheme K)) :
    Representation.Equiv
      ((normalizedData N S).origin s hs
        ((F.push (PhaseField K) h2
          (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.gmPresentation (PhaseField K))
          (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.linePresentation (PhaseField K))
          (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K)) rfl).obj A)).ρ
      ((observedAffineFunctor C U O F K h2 c R.radialObserver).obj
        ((normalizedPuncturedKernelFunctor C U K as (Units.mk0 s hs)).obj A)).ρ :=
  TensorListRepresentation.equivOfIso
    (normalizedOriginToLiteralASAffineIso
      (C := C) (U := U) (O := O) (F := F) (lisse := lisse)
      (smoothOpen := smoothOpen) (lisseProjection := lisseProjection) (lissePull := lissePull)
      (compactBaseChange := compactBaseChange) (K := K) (h2 := h2) (c := c)
      (underlying := underlying) (N := N) (S := S)
      (as := as) (hAS := hAS) (R := R) (s := s) (hs := hs) (A := A))

end LiteralFrequencyBridge

end NormalizedOrigin
end PrimeGap182.TypeIII.OriginalAffineKernelFromPublishedOpenCompact03

#print axioms PrimeGap182.TypeIII.OriginalAffineKernelFromPublishedOpenCompact03.positiveKernelExtension
#print axioms PrimeGap182.TypeIII.OriginalAffineKernelFromPublishedOpenCompact03.observedOriginalAffineIso
#print axioms PrimeGap182.TypeIII.OriginalAffineKernelFromPublishedOpenCompact03.ObservedFourierCurveRules.curveFiberRules
#print axioms PrimeGap182.TypeIII.OriginalAffineKernelFromPublishedOpenCompact03.normalizedOriginToOriginalAffineIso
#print axioms PrimeGap182.TypeIII.OriginalAffineKernelFromPublishedOpenCompact03.normalizedOriginToOriginalAffineEquiv

#print axioms PrimeGap182.TypeIII.OriginalAffineKernelFromPublishedOpenCompact03.normalizedPuncturedKernelIso
#print axioms PrimeGap182.TypeIII.OriginalAffineKernelFromPublishedOpenCompact03.normalizedOriginToLiteralASAffineIso

#print axioms PrimeGap182.TypeIII.OriginalAffineKernelFromPublishedOpenCompact03.normalizedOriginToLiteralASAffineEquiv
