import TypeIIILocalFourierKernelCoordinates

/-!
# The positive Fourier kernel on the full affine plane

The full plane has polynomial source x and target y coordinates, so both
origins are included. Its source-punctured chart is the existing Laurent
source/polynomial target model. Restriction gives the same positive xy
kernel; the existing source inversion then gives pi'/pi and fixes y.
Only coordinate and affine scheme map identities are constructed here.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace PrimeGap182.TypeIII.FullFourierKernelCoordinates

universe u
variable (K : Type u) [Field K]

abbrev PlaneRing := MvPolynomial (Fin 2) K
abbrev planeScheme : Scheme := Spec (.of (PlaneRing K))

def kernelHom : MvPolynomial (Fin 1) K →ₐ[K] PlaneRing K :=
  MvPolynomial.aeval (fun _ => MvPolynomial.X 0 * MvPolynomial.X 1)

def targetHom : MvPolynomial (Fin 1) K →ₐ[K] PlaneRing K :=
  MvPolynomial.aeval (fun _ => MvPolynomial.X 1)

/-- The source-punctured chart sends x to the Laurent variable and y to
the polynomial variable; the target coordinate is not inverted. -/
def chartHom : PlaneRing K →ₐ[K] LocalFourierKernelCoordinates.ModelRing K :=
  MvPolynomial.aeval (fun i =>
    if i = 0 then Polynomial.C (LaurentPolynomial.T 1) else Polynomial.X)

theorem chart_kernelHom :
    (chartHom K).comp (kernelHom K) = LocalFourierKernelCoordinates.globalKernelHom K := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [kernelHom, chartHom, LocalFourierKernelCoordinates.globalKernelHom]

theorem chart_targetHom :
    (chartHom K).comp (targetHom K) = LocalFourierKernelCoordinates.targetHom K := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [targetHom, chartHom, LocalFourierKernelCoordinates.targetHom]

/-- The full positive kernel is regular and zero on the source origin. -/
theorem kernel_at_source_zero (y : K) :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then 0 else y)
      (kernelHom K (MvPolynomial.X 0)) = 0 := by
  simp [kernelHom]

/-- The full positive kernel is regular and zero on the target origin. -/
theorem kernel_at_target_zero (x : K) :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then x else 0)
      (kernelHom K (MvPolynomial.X 0)) = 0 := by
  simp [kernelHom]

def chartMorphism : LocalFourierKernelCoordinates.modelScheme K ⟶ planeScheme K :=
  Spec.map (CommRingCat.ofHom (chartHom K).toRingHom)

def kernelMorphism : planeScheme K ⟶ LocalFourierKernelCoordinates.affineLine K :=
  Spec.map (CommRingCat.ofHom (kernelHom K).toRingHom)

def targetMorphism : planeScheme K ⟶ LocalFourierKernelCoordinates.affineLine K :=
  Spec.map (CommRingCat.ofHom (targetHom K).toRingHom)

theorem chart_kernelMorphism :
    chartMorphism K ≫ kernelMorphism K =
      LocalFourierKernelCoordinates.globalKernelMorphism K := by
  dsimp only [chartMorphism, kernelMorphism, LocalFourierKernelCoordinates.globalKernelMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (chart_kernelHom K))

theorem chart_targetMorphism :
    chartMorphism K ≫ targetMorphism K = LocalFourierKernelCoordinates.targetMorphism K := by
  dsimp only [chartMorphism, targetMorphism, LocalFourierKernelCoordinates.targetMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (chart_targetHom K))

theorem inverted_kernelMorphism :
    LocalFourierKernelCoordinates.coordinateMorphism K ≫ chartMorphism K ≫ kernelMorphism K =
      LocalFourierKernelCoordinates.localKernelMorphism K := by
  rw [chart_kernelMorphism, LocalFourierKernelCoordinates.kernelMorphism_composition]

theorem inverted_targetMorphism :
    LocalFourierKernelCoordinates.coordinateMorphism K ≫ chartMorphism K ≫ targetMorphism K =
      LocalFourierKernelCoordinates.targetMorphism K := by
  rw [chart_targetMorphism, LocalFourierKernelCoordinates.targetMorphism_composition]

end PrimeGap182.TypeIII.FullFourierKernelCoordinates

#print axioms PrimeGap182.TypeIII.FullFourierKernelCoordinates.chart_kernelHom
#print axioms PrimeGap182.TypeIII.FullFourierKernelCoordinates.chart_targetHom
#print axioms PrimeGap182.TypeIII.FullFourierKernelCoordinates.kernel_at_source_zero
#print axioms PrimeGap182.TypeIII.FullFourierKernelCoordinates.kernel_at_target_zero
#print axioms PrimeGap182.TypeIII.FullFourierKernelCoordinates.chart_kernelMorphism
#print axioms PrimeGap182.TypeIII.FullFourierKernelCoordinates.chart_targetMorphism
#print axioms PrimeGap182.TypeIII.FullFourierKernelCoordinates.inverted_kernelMorphism
#print axioms PrimeGap182.TypeIII.FullFourierKernelCoordinates.inverted_targetMorphism
