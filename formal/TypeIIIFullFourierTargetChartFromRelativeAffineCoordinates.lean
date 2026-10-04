import TypeIIIFullFourierCoreFromNativeBoundedOperations
import TypeIIIRelativeAffineFourierKernelFromActualCoordinates

/-!
The native full Fourier plane restricts over the actual punctured target
to the existing full relative source affine line. Its x coordinate remains
polynomial, while the target parameter is Laurent. These coordinate and
scheme-map identities do not supply a compact base-change theorem, identify
cycle functors, or replace the full transform by this target chart.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory

namespace PrimeGap182.TypeIII.FullFourierTargetChartFromRelativeAffineCoordinates
open PublishedPhaseApplication GenericCurvePullback GenericRelativeAffineLineCoordinates

variable (K : Type) [Field K]

/-- In this chart x remains polynomial and y is the original Laurent parameter. -/
def targetChartHom : FullFourierKernelCoordinates.PlaneRing (PhaseField K) →+*
    RelativeAffineRing K :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.C : ParameterRing K →+* RelativeAffineRing K).comp LaurentPolynomial.C)
    (fun i => if i = 0 then MvPolynomial.X 0 else
      MvPolynomial.C (LaurentPolynomial.T 1))

theorem targetChartHom_X_source :
    targetChartHom K (MvPolynomial.X (0 : Fin 2)) = MvPolynomial.X (0 : Fin 1) := by
  simp [targetChartHom]

theorem targetChartHom_X_target :
    targetChartHom K (MvPolynomial.X (1 : Fin 2)) =
      MvPolynomial.C (LaurentPolynomial.T 1) := by
  simp [targetChartHom]

theorem targetChartHom_C (c : PhaseField K) :
    targetChartHom K (MvPolynomial.C c) = MvPolynomial.C (LaurentPolynomial.C c) := by
  simp [targetChartHom]

/-- The full native source projection restricts to the same relative source map. -/
theorem targetChartHom_source :
    (targetChartHom K).comp
      (MvPolynomial.aeval (fun _ : Fin 1 => MvPolynomial.X (0 : Fin 2)) :
        MvPolynomial (Fin 1) (PhaseField K) →ₐ[PhaseField K]
          FullFourierKernelCoordinates.PlaneRing (PhaseField K)).toRingHom =
      RelativeAffineFourierKernelFromActualCoordinates.sourceHom K := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [RelativeAffineFourierKernelFromActualCoordinates.sourceHom, targetChartHom]
  · intro i
    simp [RelativeAffineFourierKernelFromActualCoordinates.sourceHom, targetChartHom]

/-- The target is exactly the original parameter projection followed by Gm→A1. -/
theorem targetChartHom_target :
    (targetChartHom K).comp (FullFourierKernelCoordinates.targetHom (PhaseField K)).toRingHom =
      (MvPolynomial.C : ParameterRing K →+* RelativeAffineRing K).comp
        (ArithmeticSourceMaps.localInputHom (PhaseField K) (PhaseField K)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [FullFourierKernelCoordinates.targetHom, targetChartHom,
      ArithmeticSourceMaps.localInputHom]
  · intro i
    simp [FullFourierKernelCoordinates.targetHom, targetChartHom,
      ArithmeticSourceMaps.localInputHom]
    rfl

/-- Positive xy with the original prime-field coefficient map is the relative kernel. -/
theorem targetChartHom_kernel :
    ((targetChartHom K).comp
        (FullFourierKernelCoordinates.kernelHom (PhaseField K)).toRingHom).comp
      (CanonicalAffineCoefficientChange.coefficientHom K (PhaseField K) 1) =
      RelativeAffineFourierKernelFromActualCoordinates.kernelHom K := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, CanonicalAffineCoefficientChange.coefficientHom,
      MvPolynomial.map_C, FullFourierKernelCoordinates.kernelHom,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.aeval_C,
      RelativeAffineFourierKernelFromActualCoordinates.kernelHom,
      MvPolynomial.eval₂Hom_C]
    rw [MvPolynomial.algebraMap_eq, targetChartHom_C]
    exact congrArg MvPolynomial.C
      (IsScalarTower.algebraMap_apply K (PhaseField K) (ParameterRing K) c).symm
  · intro i
    simp [CanonicalAffineCoefficientChange.coefficientHom,
      FullFourierKernelCoordinates.kernelHom, targetChartHom,
      RelativeAffineFourierKernelFromActualCoordinates.kernelHom, mul_comm]

def targetChartMorphism : relativeAffineScheme K ⟶
    FullFourierKernelCoordinates.planeScheme (PhaseField K) :=
  Spec.map (CommRingCat.ofHom (targetChartHom K))

theorem targetChart_source :
    targetChartMorphism K ≫ FourierOriginFromASKernel.sourceMorphism (PhaseField K) =
      RelativeAffineFourierKernelFromActualCoordinates.sourceMorphism K := by
  dsimp only [targetChartMorphism, FourierOriginFromASKernel.sourceMorphism,
    RelativeAffineFourierKernelFromActualCoordinates.sourceMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, targetChartHom_source]

theorem targetChart_target :
    targetChartMorphism K ≫ FullFourierKernelCoordinates.targetMorphism (PhaseField K) =
      relativeProjection K ≫ ArithmeticSourceMaps.localInputMorphism
        (PhaseField K) (PhaseField K) := by
  dsimp only [targetChartMorphism, FullFourierKernelCoordinates.targetMorphism,
    relativeProjection, ArithmeticSourceMaps.localInputMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, targetChartHom_target]

theorem targetChart_kernel :
    targetChartMorphism K ≫ FullFourierKernelCoordinates.kernelMorphism (PhaseField K) ≫
      CanonicalAffineCoefficientChange.coefficientMorphism K (PhaseField K) 1 =
        RelativeAffineFourierKernelFromActualCoordinates.kernelMorphism K := by
  dsimp only [targetChartMorphism, FullFourierKernelCoordinates.kernelMorphism,
    CanonicalAffineCoefficientChange.coefficientMorphism,
    RelativeAffineFourierKernelFromActualCoordinates.kernelMorphism]
  rw [← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (targetChartHom_kernel K)

end PrimeGap182.TypeIII.FullFourierTargetChartFromRelativeAffineCoordinates

-- Declaration reports consumed by the repository-wide axiom audit.
#print axioms PrimeGap182.TypeIII.FullFourierTargetChartFromRelativeAffineCoordinates.targetChartHom
#print axioms PrimeGap182.TypeIII.FullFourierTargetChartFromRelativeAffineCoordinates.targetChartHom_X_source
#print axioms PrimeGap182.TypeIII.FullFourierTargetChartFromRelativeAffineCoordinates.targetChartHom_X_target
#print axioms PrimeGap182.TypeIII.FullFourierTargetChartFromRelativeAffineCoordinates.targetChartHom_C
#print axioms PrimeGap182.TypeIII.FullFourierTargetChartFromRelativeAffineCoordinates.targetChartHom_source
#print axioms PrimeGap182.TypeIII.FullFourierTargetChartFromRelativeAffineCoordinates.targetChartHom_target
#print axioms PrimeGap182.TypeIII.FullFourierTargetChartFromRelativeAffineCoordinates.targetChartHom_kernel
#print axioms PrimeGap182.TypeIII.FullFourierTargetChartFromRelativeAffineCoordinates.targetChartMorphism
#print axioms PrimeGap182.TypeIII.FullFourierTargetChartFromRelativeAffineCoordinates.targetChart_source
#print axioms PrimeGap182.TypeIII.FullFourierTargetChartFromRelativeAffineCoordinates.targetChart_target
#print axioms PrimeGap182.TypeIII.FullFourierTargetChartFromRelativeAffineCoordinates.targetChart_kernel
