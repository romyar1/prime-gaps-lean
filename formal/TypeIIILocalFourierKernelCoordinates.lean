import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The actual global-to-local infinity-to-origin kernel coordinate

Use K[pi,pi^-1,y], with y allowed to vanish. The inversion map replaces
the global source x by pi^-1 and fixes the target y=pi'. Thus the
positive global AS kernel xy restricts to pi'/pi, with the same AS
object and no target inversion, reflection or character change.

This is the coordinate application needed for Laumon 2.4.2.1(ii).
The general inverse-image compositor remains an explicit parameter;
the specific AS-kernel comparison is derived from the checked map.
No henselian realization or stationary-phase theorem is asserted here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

namespace PrimeGap182.TypeIII.LocalFourierKernelCoordinates

universe u c d v w
variable (K : Type u) [Field K]

/-- The source coordinate is invertible; the target coordinate is polynomial. -/
abbrev ModelRing := Polynomial (LaurentPolynomial K)

def uniformizer : (LaurentPolynomial K)ˣ :=
  ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1),
    by rw [← LaurentPolynomial.T_add]; simp,
    by rw [← LaurentPolynomial.T_add]; simp⟩

def inversion : LaurentPolynomial K →ₐ[K] LaurentPolynomial K where
  toRingHom := LaurentPolynomial.eval₂ LaurentPolynomial.C (uniformizer K)⁻¹
  commutes' c := LaurentPolynomial.eval₂_C _ _ c

theorem inversion_variable : inversion K (LaurentPolynomial.T 1) = LaurentPolynomial.T (-1) := by
  change LaurentPolynomial.eval₂ LaurentPolynomial.C (uniformizer K)⁻¹
    (LaurentPolynomial.T 1) = _
  rw [LaurentPolynomial.eval₂_T, zpow_one]
  rfl

def coordinateHom : ModelRing K →ₐ[K] ModelRing K := Polynomial.mapAlgHom (inversion K)

theorem coordinateHom_C (a : LaurentPolynomial K) :
    coordinateHom K (Polynomial.C a) = Polynomial.C (inversion K a) :=
  Polynomial.map_C _

theorem coordinateHom_X : coordinateHom K Polynomial.X = Polynomial.X := Polynomial.map_X _

def globalKernelHom : MvPolynomial (Fin 1) K →ₐ[K] ModelRing K :=
  MvPolynomial.aeval (fun _ => Polynomial.C (LaurentPolynomial.T 1) * Polynomial.X)

def localKernelHom : MvPolynomial (Fin 1) K →ₐ[K] ModelRing K :=
  MvPolynomial.aeval (fun _ => Polynomial.C (LaurentPolynomial.T (-1)) * Polynomial.X)

def targetHom : MvPolynomial (Fin 1) K →ₐ[K] ModelRing K :=
  MvPolynomial.aeval (fun _ => Polynomial.X)

/-- The actual global positive kernel xy becomes pi'/pi. -/
theorem kernelHom_composition :
    (coordinateHom K).comp (globalKernelHom K) = localKernelHom K := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, globalKernelHom, localKernelHom, MvPolynomial.aeval_X, map_mul]
  rw [coordinateHom_C, inversion_variable, coordinateHom_X]

/-- The finite target coordinate is fixed, including its origin. -/
theorem targetHom_composition : (coordinateHom K).comp (targetHom K) = targetHom K := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, targetHom, MvPolynomial.aeval_X, coordinateHom_X]

/-- The local kernel extends regularly across target y=0 on the source
punctured chart; its value there is zero. No source-origin extension is claimed. -/
theorem localKernel_at_target_zero :
    Polynomial.eval 0 (localKernelHom K (MvPolynomial.X 0)) = 0 := by
  simp [localKernelHom]

abbrev modelScheme : Scheme := Spec (.of (ModelRing K))
abbrev affineLine : Scheme := Spec (.of (MvPolynomial (Fin 1) K))

def coordinateMorphism : modelScheme K ⟶ modelScheme K :=
  Spec.map (CommRingCat.ofHom (coordinateHom K).toRingHom)

def globalKernelMorphism : modelScheme K ⟶ affineLine K :=
  Spec.map (CommRingCat.ofHom (globalKernelHom K).toRingHom)

def localKernelMorphism : modelScheme K ⟶ affineLine K :=
  Spec.map (CommRingCat.ofHom (localKernelHom K).toRingHom)

def targetMorphism : modelScheme K ⟶ affineLine K :=
  Spec.map (CommRingCat.ofHom (targetHom K).toRingHom)

/-- Scheme-level kernel identity on the full finite-target chart. -/
theorem kernelMorphism_composition :
    coordinateMorphism K ≫ globalKernelMorphism K = localKernelMorphism K := by
  dsimp only [coordinateMorphism, globalKernelMorphism, localKernelMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (kernelHom_composition K))

/-- The scheme map is over the unchanged target affine line. -/
theorem targetMorphism_composition : coordinateMorphism K ≫ targetMorphism K = targetMorphism K := by
  dsimp only [coordinateMorphism, targetMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (targetHom_composition K))

section Pullback
variable {Line : Type c} [Category.{v} Line] {Model : Type d} [Category.{w} Model]
  (pull : (modelScheme K ⟶ affineLine K) → Line ⥤ Model)
  (restriction : Model ⥤ Model)
  (composition : ∀ f, pull f ⋙ restriction ≅ pull (coordinateMorphism K ≫ f))

/-- Apply general inverse-image composition to the checked coordinate
identity. This compares the same AS object and is natural in every line object. -/
def kernelPullbackComparison : pull (globalKernelMorphism K) ⋙ restriction ≅
    pull (localKernelMorphism K) := by
  have h := composition (globalKernelMorphism K)
  rw [kernelMorphism_composition] at h
  exact h

/-- The common AS source is retained, rather than replaced by an unrelated local kernel. -/
abbrev asKernelComparison (as : Line) :
    restriction.obj ((pull (globalKernelMorphism K)).obj as) ≅
      (pull (localKernelMorphism K)).obj as :=
  (kernelPullbackComparison K pull restriction composition).app as

/-- Kernel transport retains the original source morphisms. -/
theorem kernelPullback_natural {A B : Line} (f : A ⟶ B) :
    restriction.map ((pull (globalKernelMorphism K)).map f) ≫
      (kernelPullbackComparison K pull restriction composition).hom.app B =
    (kernelPullbackComparison K pull restriction composition).hom.app A ≫
      (pull (localKernelMorphism K)).map f :=
  by
    change (pull (globalKernelMorphism K) ⋙ restriction).map f ≫
        (kernelPullbackComparison K pull restriction composition).hom.app B =
      (kernelPullbackComparison K pull restriction composition).hom.app A ≫
        (pull (localKernelMorphism K)).map f
    exact (kernelPullbackComparison K pull restriction composition).hom.naturality f

end Pullback
end PrimeGap182.TypeIII.LocalFourierKernelCoordinates

#print axioms PrimeGap182.TypeIII.LocalFourierKernelCoordinates.inversion_variable
#print axioms PrimeGap182.TypeIII.LocalFourierKernelCoordinates.kernelHom_composition
#print axioms PrimeGap182.TypeIII.LocalFourierKernelCoordinates.targetHom_composition
#print axioms PrimeGap182.TypeIII.LocalFourierKernelCoordinates.localKernel_at_target_zero
#print axioms PrimeGap182.TypeIII.LocalFourierKernelCoordinates.kernelMorphism_composition
#print axioms PrimeGap182.TypeIII.LocalFourierKernelCoordinates.targetMorphism_composition
#print axioms PrimeGap182.TypeIII.LocalFourierKernelCoordinates.kernelPullbackComparison
#print axioms PrimeGap182.TypeIII.LocalFourierKernelCoordinates.asKernelComparison
#print axioms PrimeGap182.TypeIII.LocalFourierKernelCoordinates.kernelPullback_natural
