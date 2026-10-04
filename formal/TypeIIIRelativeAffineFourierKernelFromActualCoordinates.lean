import TypeIIIGenericRelativeAffineLineCoordinates
import TypeIIIFourierNormalizationMaps
import TypeIIIArithmeticSourceMaps

/-!
The same original parameter ring supports a full source affine line: x is
polynomial, while the Fourier parameter remains Laurent. The kernel is the
regular product parameter*x, including x=0. Restricting along the actual
Laurent source open gives the literal old universal kernel and source map.
These are coordinate/morphism identities, with no cohomology, ordinary
extension exactness, or realization law supplied.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
namespace PrimeGap182.TypeIII.RelativeAffineFourierKernelFromActualCoordinates
open GenericCurvePullback GenericSourceSpecialization GenericRelativeAffineLineCoordinates
open FourierSourceMaps FourierNormalizationMaps PublishedPhaseApplication

variable (K : Type) [Field K]

/-- The full source coordinate over the actual PhaseField constants. -/
def sourceHom : MvPolynomial (Fin 1) (PhaseField K) →+* RelativeAffineRing K :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.C : ParameterRing K →+* RelativeAffineRing K).comp LaurentPolynomial.C)
    (fun _ => MvPolynomial.X 0)

/-- The exact positive kernel on the full relative source line. -/
def kernelHom : MvPolynomial (Fin 1) K →+* RelativeAffineRing K :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.C : ParameterRing K →+* RelativeAffineRing K).comp
      (algebraMap K (ParameterRing K)))
    (fun _ => MvPolynomial.C (LaurentPolynomial.T 1) * MvPolynomial.X 0)

theorem open_comp_kernelHom :
    (relativeOpenHom K).comp (kernelHom K) = (universalKernelHom K).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, kernelHom, MvPolynomial.eval₂Hom_C, relativeOpenHom_C, universalKernelHom, MvPolynomial.aeval_C]
    change LaurentPolynomial.C (algebraMap K (ParameterRing K) c) =
      algebraMap K (GenericRing K) c
    exact IsScalarTower.algebraMap_apply K (ParameterRing K) (GenericRing K) c
  · intro i
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, kernelHom, MvPolynomial.eval₂Hom_X', map_mul, relativeOpenHom_C, relativeOpenHom_X]
    change LaurentPolynomial.C (LaurentPolynomial.T 1) * (curveUnit K : GenericRing K) =
      (universalKernelHom K) (MvPolynomial.X i)
    simp only [universalKernelHom, MvPolynomial.aeval_X]
    rfl

theorem open_comp_sourceHom :
    (relativeOpenHom K).comp (sourceHom K) =
      (projectionHom K).toRingHom.comp
        (ArithmeticSourceMaps.localInputHom (PhaseField K) (PhaseField K)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, sourceHom, MvPolynomial.eval₂Hom_C, relativeOpenHom_C,
      ArithmeticSourceMaps.localInputHom, MvPolynomial.aeval_C]
    change LaurentPolynomial.C (LaurentPolynomial.C c) =
      LaurentPolynomial.eval₂ _ (curveUnit K) (LaurentPolynomial.C c)
    rw [LaurentPolynomial.eval₂_C]
    rfl
  · intro i
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, sourceHom, MvPolynomial.eval₂Hom_X', relativeOpenHom_X,
      ArithmeticSourceMaps.localInputHom, MvPolynomial.aeval_X]
    change (curveUnit K : GenericRing K) =
      LaurentPolynomial.eval₂ _ (curveUnit K) (LaurentPolynomial.T 1)
    rw [LaurentPolynomial.eval₂_T, zpow_one]

def sourceMorphism : relativeAffineScheme K ⟶ StartingSourceMaps.affineLine (PhaseField K) :=
  Spec.map (CommRingCat.ofHom (sourceHom K))

def kernelMorphism : relativeAffineScheme K ⟶ StartingSourceMaps.affineLine K :=
  Spec.map (CommRingCat.ofHom (kernelHom K))

theorem open_comp_kernelMorphism :
    relativeOpenMorphism K ≫ kernelMorphism K = universalKernelMorphism K := by
  dsimp only [relativeOpenMorphism, kernelMorphism, universalKernelMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, open_comp_kernelHom]

theorem open_comp_sourceMorphism :
    relativeOpenMorphism K ≫ sourceMorphism K = projectionMorphism K ≫
      ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K) := by
  dsimp only [relativeOpenMorphism, sourceMorphism, projectionMorphism,
    ArithmeticSourceMaps.localInputMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, open_comp_sourceHom,
    CommRingCat.ofHom_comp, Spec.map_comp]

/-- The regular kernel vanishes at the actual source-zero section. -/
theorem kernel_at_source_zero (i : Fin 1) :
    relativeZeroHom K (kernelHom K (MvPolynomial.X i)) = 0 := by
  simp only [kernelHom, MvPolynomial.eval₂Hom_X',
    relativeZeroHom, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', mul_zero]

end PrimeGap182.TypeIII.RelativeAffineFourierKernelFromActualCoordinates
