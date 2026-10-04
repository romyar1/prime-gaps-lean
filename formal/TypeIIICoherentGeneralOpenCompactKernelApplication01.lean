import TypeIIIActualRelativeFourierKernelExtensionFromPublishedOpenTheorems
import TypeIIIGenericRelativeAffineParameterBaseChangeCoordinates

/-!
# GENERAL ordinary-open / compact-support kernel application

The ordinary open push is the SAME U.pull right adjoint, directly in
its actual PhaseField presentation. The compact operation retains its
SAME certificate c. Only GENERAL all-smooth-open/lisse-projection and
all-Cartesian compact-support laws are supplied. Every selected source,
parameter self-map and AS kernel is computed from actual coordinates.
No CanonicalPrimeInputs aggregate, native Fourier object, finished family
comparison, Type III profile, rank or bound is imported or assumed.

The genuine constructible continuous-adic interpretation and the guarded
general six-operations laws remain external. This is an application of
published general laws, not a construction of an adic foundation.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory MonoidalCategory
namespace PrimeGap182.TypeIII.CoherentGeneralOpenCompactKernelApplication01
open PublishedPhaseApplication GenericSourceSpecialization GenericCurvePullback FourierSourceMaps
open GenericRelativeAffineLineCoordinates RelativeAffineFourierKernelFromActualCoordinates
open GenericRelativeAffineParameterBaseChangeCoordinates
open OrdinaryOpenExtensionsFromAdjunctions QSTCompactBridgeFromCompactifiedDerivedPushforward
open OrdinaryFourierKernelExtensionFromGeneralSmoothBaseChange
open ActualRelativeFourierKernelExtensionFromPublishedOpenTheorems
open QSTAdmissibilityFromBoundedDerived

universe mu
variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  [∀ X, MonoidalCategory (C X)]
  (U : ExactInverseImagesToDerived.OrdinarySystem (fun X : Scheme => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (O : Operations C)

local instance allSchemeLocalizations : ∀ X : Scheme, HasDerivedCategory.{mu} (C X) :=
  fun _ => HasDerivedCategory.standard _

/-- The published GENERAL proper-support comparison on ALL valid guarded
compactifications and ALL genuine Cartesian squares. The actual derived
bang and bounded inverse images are the SAME fixed operators; this does
not supply the selected kernel comparison or its degree-one consequence. -/
abbrev UniversalCompactBaseChange :=
  ∀ {X Y X' Y' : Scheme} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (g : X' ⟶ X) (h : Y' ⟶ Y) (_square : IsPullback g f' f h),
    derivedBang C O c ⋙ UniversalBoundedInverseImagesFromExactSystem.pull C U h ≅
      UniversalBoundedInverseImagesFromExactSystem.pull C U g ⋙ derivedBang C O c'

variable (F : OrdinaryOpenFamily C U)
  (L : ∀ X : Scheme, ObjectProperty (C X))
  (smoothOpen : UniversalSmoothOpenBaseChange C U F)
  (lisseProjection : UniversalLisseOpenProjection C U F L)
  (lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y),
    L Y A → L X ((U.pull f).obj A))
  (compactBaseChange : UniversalCompactBaseChange C U O)
  (K : Type) [Field K] (h2 : (2 : PhaseField K) ≠ 0)
  (c : Compactification (relativeProjection K))

/-- The actual relative ordinary j-star, chosen ONCE from the same U and
actual PhaseField presentation. Its definition uses no compactification
or alternative field-presentation comparison. -/
def relativeOpenExtend : C (genericScheme K) ⥤ C (relativeAffineScheme K) :=
  F.push (PhaseField K) h2 (puncturedPresentation K) (relativePresentation K)
    (relativeOpenMorphism K) rfl

/-- Full external-source kernel with an arbitrary globally lisse tensor factor. -/
def fullKernel (V : C (relativeAffineScheme K)) :
    C (StartingSourceMaps.affineLine (PhaseField K)) ⥤ C (relativeAffineScheme K) :=
  U.pull (sourceMorphism K) ⋙ tensorRight V

/-- Its literal punctured external-source kernel. -/
def puncturedKernel (V : C (relativeAffineScheme K)) :
    C (localScheme K) ⥤ C (genericScheme K) :=
  U.pull (projectionMorphism K) ⋙ tensorRight ((U.pull (relativeOpenMorphism K)).obj V)

section SourceExtension
include smoothOpen lisseProjection

/-- Smooth-source extension holds for ANY globally lisse full tensor factor. -/
def sourceExtension (V : C (relativeAffineScheme K)) (hV : L (relativeAffineScheme K) V) :
    F.push (PhaseField K) h2 (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.gmPresentation (PhaseField K))
        (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.linePresentation (PhaseField K))
        (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K)) rfl ⋙
      fullKernel C U K V ≅
    puncturedKernel C U K V ⋙
      relativeOpenExtend C U F K h2 :=
  OrdinaryFourierKernelExtensionFromGeneralSmoothBaseChange.kernelExtensionIso C U F L smoothOpen lisseProjection
      (PhaseField K) h2
      (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.gmPresentation (PhaseField K))
      (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.linePresentation (PhaseField K))
      (puncturedPresentation K) (relativePresentation K)
      (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K))
      (relativeOpenMorphism K) (sourceMorphism K) (projectionMorphism K)
      rfl rfl rfl (punctured_source_over K)
      (FourierSourceOpenCartesianFromLaurentLocalization.sourceOpen_isPullback K) V hV

end SourceExtension

/-- The actual bounded degree-zero inverse-image comparison. -/
def boundedDegreeZeroPull {X Y : Scheme} (f : X ⟶ Y) :
    boundedDegreeZero C Y ⋙ UniversalBoundedInverseImagesFromExactSystem.pull C U f ≅
      U.pull f ⋙ boundedDegreeZero C X :=
  Functor.fullyFaithfulCancelRight (boundedProperty (C X)).ι (U.degreeZeroPullback f)

/-- Exact ordinary pullback commutes with every ordinary H^n of the
SAME standard bounded derived category. This is the computed degree
comparison, rather than a separately selected compact object law. -/
def boundedPullCohomology {X Y : Scheme} (f : X ⟶ Y) (n : ℤ) :
    UniversalBoundedInverseImagesFromExactSystem.pull C U f ⋙ cohomology C X n ≅
      cohomology C Y n ⋙ U.pull f :=
  NatIso.ofComponents
    (fun A => (OriginRealizationFromExactInverseImages.exactDerivedCohomology
      (U.pull f) n).app A.obj)
    (fun a => (OriginRealizationFromExactInverseImages.exactDerivedCohomology
      (U.pull f) n).hom.naturality a.hom)

section CompactParameter
include compactBaseChange

/-- The SAME-c compact cohomology comparison along every lifted parameter map. -/
def compactParameterIso (f : parameterScheme K ⟶ parameterScheme K) (n : ℤ) :
    (cohomologyData C O c n).compact ⋙ U.pull f ≅
      U.pull (relativeMap K f) ⋙ (cohomologyData C O c n).compact :=
  Functor.isoWhiskerLeft (boundedDegreeZero C (relativeAffineScheme K) ⋙ derivedBang C O c)
      (boundedPullCohomology C U f n).symm ≪≫
    Functor.isoWhiskerLeft (boundedDegreeZero C (relativeAffineScheme K))
      (Functor.isoWhiskerRight
        (compactBaseChange c c (relativeMap K f) f (relativeMap_isPullback K f))
        (cohomology C (parameterScheme K) n)) ≪≫
    Functor.isoWhiskerRight (boundedDegreeZeroPull C U (relativeMap K f))
      (derivedBang C O c ⋙ cohomology C (parameterScheme K) n)

end CompactParameter

variable (f : parameterScheme K ⟶ parameterScheme K)
  (g : genericScheme K ⟶ genericScheme K)
  (square : IsPullback g (genericProjection K) (genericProjection K) f)
  (coordinate : g ≫ projectionMorphism K = projectionMorphism K)

/-- Ordinary inverse images identify the exact punctured/full parameter square. -/
def openPullIso :
    U.pull (relativeOpenMorphism K) ⋙ U.pull g ≅
      U.pull (relativeMap K f) ⋙ U.pull (relativeOpenMorphism K) :=
  U.composition g (relativeOpenMorphism K) ≪≫
    eqToIso (congrArg (fun a => U.pull a) (relativeMap_open K f g square coordinate)) ≪≫
    (U.composition (relativeOpenMorphism K) (relativeMap K f)).symm

/-- Full kernel transport uses the source-coordinate identity and actual monoidality. -/
def fullParameterIso (V : C (relativeAffineScheme K)) :
    fullKernel C U K V ⋙ U.pull (relativeMap K f) ≅
      fullKernel C U K ((U.pull (relativeMap K f)).obj V) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (U.pull (sourceMorphism K))
      (Functor.Monoidal.commTensorRight (U.pull (relativeMap K f)) V).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (U.composition (relativeMap K f) (sourceMorphism K) ≪≫
        eqToIso (congrArg (fun a => U.pull a) (relativeMap_source K f g square coordinate))) _

/-- Punctured kernel transport retains every external source object. -/
def puncturedParameterIso (V : C (relativeAffineScheme K)) :
    puncturedKernel C U K V ⋙ U.pull g ≅
      puncturedKernel C U K ((U.pull (relativeMap K f)).obj V) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (U.pull (projectionMorphism K))
      (Functor.Monoidal.commTensorRight (U.pull g) ((U.pull (relativeOpenMorphism K)).obj V)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (U.composition g (projectionMorphism K) ≪≫
        eqToIso (congrArg (fun a => U.pull a) coordinate)) _ ≪≫
    Functor.isoWhiskerLeft (U.pull (projectionMorphism K))
      ((tensoringRight (C (genericScheme K))).mapIso ((openPullIso C U K f g square coordinate).app V))

section KernelBaseChange
include smoothOpen lisseProjection lissePull compactBaseChange

/-- ALL-source Fourier compact cohomology base change, with no smoothness guard on f. -/
def baseChangeIso (V : C (relativeAffineScheme K)) (hV : L (relativeAffineScheme K) V) (n : ℤ) :
    puncturedKernel C U K V ⋙
      relativeOpenExtend C U F K h2 ⋙
      (cohomologyData C O c n).compact ⋙ U.pull f ≅
    puncturedKernel C U K V ⋙ U.pull g ⋙
      relativeOpenExtend C U F K h2 ⋙
      (cohomologyData C O c n).compact :=
  Functor.isoWhiskerRight (sourceExtension C U F L smoothOpen lisseProjection K h2 V hV).symm
      ((cohomologyData C O c n).compact ⋙ U.pull f) ≪≫
    Functor.isoWhiskerLeft
      (F.push (PhaseField K) h2 (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.gmPresentation (PhaseField K))
        (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.linePresentation (PhaseField K))
        (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K)) rfl ⋙ fullKernel C U K V)
      (compactParameterIso C U O compactBaseChange K c f n) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        (F.push (PhaseField K) h2 (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.gmPresentation (PhaseField K))
          (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.linePresentation (PhaseField K))
          (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K)) rfl)
        (fullParameterIso C U K f g square coordinate V)) ((cohomologyData C O c n).compact) ≪≫
    Functor.isoWhiskerRight
      (sourceExtension C U F L smoothOpen lisseProjection K h2
        ((U.pull (relativeMap K f)).obj V) (lissePull _ V hV)) ((cohomologyData C O c n).compact) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (puncturedParameterIso C U K f g square coordinate V).symm
        (relativeOpenExtend C U F K h2))
      ((cohomologyData C O c n).compact)

end KernelBaseChange

/-- Literal positive AS punctured kernel, computed by the exact open coordinate equation. -/
def positiveKernelIso (as : C (StartingSourceMaps.affineLine K)) :
    puncturedKernel C U K ((U.pull (kernelMorphism K)).obj as) ≅
      RelativeAffineFourierKernelRestrictionFromInverseImages.puncturedKernelFunctor K C U as :=
  Functor.isoWhiskerLeft (U.pull (projectionMorphism K))
    ((tensoringRight (C (genericScheme K))).mapIso
      ((RelativeAffineFourierKernelRestrictionFromInverseImages.kernelOpenPullIso K C U).app as))

section PositiveBaseChange
include smoothOpen lisseProjection lissePull compactBaseChange

/-- Exact original ALL-f/g/source-A degree-one operational law. -/
def positiveBaseChange (as : C (StartingSourceMaps.affineLine K))
    (hAS : L (StartingSourceMaps.affineLine K) as) (A : C (localScheme K)) :
    (U.pull f).obj ((cohomologyData C O c 1).compact.obj
      ((relativeOpenExtend C U F K h2).obj
        ((RelativeAffineFourierKernelRestrictionFromInverseImages.puncturedKernelFunctor K C U as).obj A))) ≅
    (cohomologyData C O c 1).compact.obj
      ((relativeOpenExtend C U F K h2).obj
        ((U.pull g).obj
          ((RelativeAffineFourierKernelRestrictionFromInverseImages.puncturedKernelFunctor K C U as).obj A))) :=
  (Functor.isoWhiskerRight (positiveKernelIso C U K as).symm
        (relativeOpenExtend C U F K h2 ⋙
          (cohomologyData C O c 1).compact ⋙ U.pull f) ≪≫
    baseChangeIso C U O F L smoothOpen lisseProjection lissePull compactBaseChange K h2 c f g square coordinate
      ((U.pull (kernelMorphism K)).obj as) (lissePull _ as hAS) 1 ≪≫
    Functor.isoWhiskerRight (positiveKernelIso C U K as)
      (U.pull g ⋙ relativeOpenExtend C U F K h2 ⋙
        (cohomologyData C O c 1).compact)).app A


end PositiveBaseChange

end PrimeGap182.TypeIII.CoherentGeneralOpenCompactKernelApplication01

#print axioms PrimeGap182.TypeIII.CoherentGeneralOpenCompactKernelApplication01.relativeOpenExtend
#print axioms PrimeGap182.TypeIII.CoherentGeneralOpenCompactKernelApplication01.sourceExtension
#print axioms PrimeGap182.TypeIII.CoherentGeneralOpenCompactKernelApplication01.boundedDegreeZeroPull
#print axioms PrimeGap182.TypeIII.CoherentGeneralOpenCompactKernelApplication01.boundedPullCohomology
#print axioms PrimeGap182.TypeIII.CoherentGeneralOpenCompactKernelApplication01.compactParameterIso
#print axioms PrimeGap182.TypeIII.CoherentGeneralOpenCompactKernelApplication01.baseChangeIso
#print axioms PrimeGap182.TypeIII.CoherentGeneralOpenCompactKernelApplication01.positiveBaseChange
