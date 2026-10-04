import TypeIIIOrdinaryFourierKernelExtensionFromGeneralSmoothBaseChange
import TypeIIIFourierSourceOpenCartesianFromLaurentLocalization
import TypeIIIFullFourierTargetCartesianFromLaurentLocalization
import TypeIIIFullFourierSourceProjectionSmoothFromPolynomialCoordinates
import TypeIIIMiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology

/-!
Apply the two general ordinary open theorem families to the actual Fourier
source Laurent square. Its Cartesian property, smoothness, presentations,
and punctured positive kernel are proved from the original coordinates.
The general lisse-pull family supplies global lissity of the pulled AS
factor. No selected extension law or exact ordinary j_* is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory MonoidalCategory
namespace PrimeGap182.TypeIII.ActualRelativeFourierKernelExtensionFromPublishedOpenTheorems
open PublishedPhaseApplication GenericCurvePullback GenericSourceSpecialization
open GenericRelativeAffineLineCoordinates FourierSourceMaps FourierNormalizationMaps
open RelativeAffineFourierKernelFromActualCoordinates
open RelativeAffineFourierKernelRestrictionFromInverseImages
open OrdinaryOpenExtensionsFromAdjunctions QSTCompactBridgeFromCompactifiedDerivedPushforward
open OrdinaryFourierKernelExtensionFromGeneralSmoothBaseChange
open MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology

section Geometry
variable (K : Type) [Field K]

/-- The actual full relative source projection is smooth. -/
instance relativeSource_smooth : Smooth (sourceMorphism K) := by
  rw [← FullFourierTargetChartFromRelativeAffineCoordinates.targetChart_source K]
  infer_instance

/-- The original relative affine ambient, presented over its actual PhaseField. -/
def relativePresentation : FieldPresentation (PhaseField K) (relativeAffineScheme K) where
  structureMorphism := sourceMorphism K ≫ lineStructure (PhaseField K)
  locallyFiniteType := inferInstance
  quasiCompact := by
    dsimp only [sourceMorphism, lineStructure]
    infer_instance
  separated := by
    dsimp only [sourceMorphism, lineStructure]
    infer_instance

/-- Inherit the PhaseField presentation through the actual source Laurent open. -/
def puncturedPresentation : FieldPresentation (PhaseField K) (genericScheme K) where
  structureMorphism := relativeOpenMorphism K ≫ (relativePresentation K).structureMorphism
  locallyFiniteType := inferInstance
  quasiCompact := by
    dsimp only [relativeOpenMorphism, relativePresentation, sourceMorphism, lineStructure]
    infer_instance
  separated := inferInstance

theorem punctured_source_over :
    projectionMorphism K ≫ (gmPresentation (PhaseField K)).structureMorphism =
      (puncturedPresentation K).structureMorphism := by
  dsimp only [gmPresentation, puncturedPresentation, relativePresentation]
  rw [← Category.assoc, ← open_comp_sourceMorphism, Category.assoc]

end Geometry

universe mu
variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  [∀ X, MonoidalCategory (C X)]
  (U : ExactInverseImagesToDerived.OrdinarySystem (fun X : Scheme => X) C)
  (F : OrdinaryOpenFamily C U)
  (L : ∀ X : Scheme, ObjectProperty (C X))
  (baseChange : UniversalSmoothOpenBaseChange C U F)
  (projection : UniversalLisseOpenProjection C U F L)
  (lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y),
    L Y A → L X ((U.pull f).obj A))
  (K : Type) [Field K]
  (h2 : (2 : PhaseField K) ≠ 0)

/-- The entire ordinary extension comparison on the literal Fourier kernel. -/
def actualKernelExtensionIso (as : C (StartingSourceMaps.affineLine K))
    (hAS : L (StartingSourceMaps.affineLine K) as) :
    F.push (PhaseField K) h2 (gmPresentation (PhaseField K))
        (linePresentation (PhaseField K))
        (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K)) rfl ⋙
      kernelFunctor K C U as ≅
    puncturedKernelFunctor K C U as ⋙
      F.push (PhaseField K) h2 (puncturedPresentation K) (relativePresentation K)
        (relativeOpenMorphism K) rfl :=
  kernelExtensionIso C U F L baseChange projection (PhaseField K) h2
      (gmPresentation (PhaseField K)) (linePresentation (PhaseField K))
      (puncturedPresentation K) (relativePresentation K)
      (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K))
      (relativeOpenMorphism K) (sourceMorphism K) (projectionMorphism K)
      rfl rfl rfl (punctured_source_over K)
      (FourierSourceOpenCartesianFromLaurentLocalization.sourceOpen_isPullback K)
      ((U.pull (kernelMorphism K)).obj as) (lissePull _ as hAS) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (U.pull (projectionMorphism K))
        ((tensoringRight (C (genericScheme K))).mapIso ((kernelOpenPullIso K C U).app as))) _

end PrimeGap182.TypeIII.ActualRelativeFourierKernelExtensionFromPublishedOpenTheorems

-- Declaration reports consumed by the repository-wide axiom audit.
#print axioms PrimeGap182.TypeIII.ActualRelativeFourierKernelExtensionFromPublishedOpenTheorems.relativeSource_smooth
#print axioms PrimeGap182.TypeIII.ActualRelativeFourierKernelExtensionFromPublishedOpenTheorems.relativePresentation
#print axioms PrimeGap182.TypeIII.ActualRelativeFourierKernelExtensionFromPublishedOpenTheorems.puncturedPresentation
#print axioms PrimeGap182.TypeIII.ActualRelativeFourierKernelExtensionFromPublishedOpenTheorems.punctured_source_over
#print axioms PrimeGap182.TypeIII.ActualRelativeFourierKernelExtensionFromPublishedOpenTheorems.actualKernelExtensionIso
