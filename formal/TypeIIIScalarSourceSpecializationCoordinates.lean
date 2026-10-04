import TypeIIIScalarSourcePointCoordinates
import TypeIIIArithmeticSourceMaps

/-!
# Exact scalar source specialization on the actual Laurent curve

Specializing the two parameter units in the original source scalar map
gives the SAME Laurent scalar map with the actual evaluated coefficient
unit. These are ring and Spec identities on whole schemes, for arbitrary
field extensions and arbitrary original parameter-ring units. No sheaf,
stalk, ramification, continuity or source-specific comparison is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped Classical

namespace PrimeGap182.TypeIII.ScalarSourceSpecializationCoordinates

variable (K E : Type) [Field K] [Field E] [Algebra K E]

/-- Original coefficient unit evaluated at the two actual parameter units. -/
def coefficientValue (c : (PhysicalTorusMorphism.TorusRing K)ˣ)
    (lambda xi : Eˣ) : Eˣ :=
  Units.map (PhysicalTorusMorphism.evaluation (K := K) lambda xi).toRingHom c

theorem coefficientValue_ne_zero (c : (PhysicalTorusMorphism.TorusRing K)ˣ)
    (lambda xi : Eˣ) : (coefficientValue K E c lambda xi : E) ≠ 0 :=
  Units.ne_zero _

/-- The literal Laurent constant coefficient algebra map. -/
def constantHom : E →ₐ[K] ArithmeticSourceMaps.FiberRing E where
  toRingHom := LaurentPolynomial.C
  commutes' _ := rfl

theorem evaluation_constantUnits (lambda xi : Eˣ) :
    PhysicalTorusMorphism.evaluation (K := K)
      (ArithmeticSourceMaps.constantUnit E lambda) (ArithmeticSourceMaps.constantUnit E xi) =
      (constantHom K E).comp (PhysicalTorusMorphism.evaluation (K := K) lambda xi) := by
  apply Ideal.Quotient.algHom_ext K
  apply MvPolynomial.algHom_ext
  intro i
  change PhysicalTorusMorphism.evaluation _ _ (PhysicalTorusMorphism.coordinate K i) =
    constantHom K E (PhysicalTorusMorphism.evaluation lambda xi
      (PhysicalTorusMorphism.coordinate K i))
  rw [PhysicalTorusMorphism.evaluation_coordinate,
    PhysicalTorusMorphism.evaluation_coordinate]
  fin_cases i <;> rfl

theorem specialization_comp_parameterHom (lambda xi : Eˣ) :
    (ArithmeticSourceMaps.specializationHom K E lambda xi).comp
      (CanonicalCurveInput.parameterHom K) =
      (constantHom K E).comp (PhysicalTorusMorphism.evaluation (K := K) lambda xi) :=
  (ScalarSourcePointCoordinates.evaluation_parameterHom K
    (PhysicalTorusLaurent.variableUnit E)
    (ArithmeticSourceMaps.constantUnit E lambda) (ArithmeticSourceMaps.constantUnit E xi)).trans
      (evaluation_constantUnits K E lambda xi)

theorem specialization_scalarHom_X (c : (PhysicalTorusMorphism.TorusRing K)ˣ)
    (lambda xi : Eˣ) :
    ArithmeticSourceMaps.specializationHom K E lambda xi
      (CanonicalCurveInput.scalarHom K c (X 0)) =
      LaurentPolynomial.C (coefficientValue K E c lambda xi : E) * LaurentPolynomial.T 1 := by
  have hp := DFunLike.congr_fun (specialization_comp_parameterHom K E lambda xi)
    (c : PhysicalTorusMorphism.TorusRing K)
  simp only [AlgHom.comp_apply] at hp
  have hx : ArithmeticSourceMaps.specializationHom K E lambda xi
      (StartingSourceMaps.coordinateUnit K 0 : StartingSourceMaps.SourceRing K) =
      (PhysicalTorusLaurent.variableUnit E : ArithmeticSourceMaps.FiberRing E) :=
    StartingSourceMaps.evaluation_coordinate (PhysicalTorusLaurent.variableUnit E)
      (ArithmeticSourceMaps.constantUnit E lambda) (ArithmeticSourceMaps.constantUnit E xi) 0
  rw [CanonicalCurveInput.scalarHom, aeval_X]
  change ArithmeticSourceMaps.specializationHom K E lambda xi
      ((CanonicalCurveInput.parameterHom K (c : _)) *
        (StartingSourceMaps.coordinateUnit K 0 : StartingSourceMaps.SourceRing K)) = _
  rw [map_mul, hp, hx]
  rfl

theorem specialization_comp_scalarHom (c : (PhysicalTorusMorphism.TorusRing K)ˣ)
    (lambda xi : Eˣ) :
    (ArithmeticSourceMaps.specializationHom K E lambda xi).comp
      (CanonicalCurveInput.scalarHom K c) =
      (ArithmeticSourceMaps.scalarHom K E (coefficientValue K E c lambda xi)).comp
        (ArithmeticSourceMaps.localInputHom K E) := by
  apply MvPolynomial.algHom_ext
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  rw [hi]
  simp only [AlgHom.comp_apply]
  rw [specialization_scalarHom_X, ArithmeticSourceMaps.localInputHom, aeval_X]
  change _ = LaurentPolynomial.eval₂ LaurentPolynomial.C _ (LaurentPolynomial.T 1)
  rw [LaurentPolynomial.eval₂_T, zpow_one]
  rfl

/-- Equality of the actual morphisms on the complete specialized curve. -/
theorem specialization_scalarMorphism (c : (PhysicalTorusMorphism.TorusRing K)ˣ)
    (lambda xi : Eˣ) :
    ArithmeticSourceMaps.specializationMorphism K E lambda xi ≫
      CanonicalCurveInput.scalarMorphism K c =
      ArithmeticSourceMaps.scalarMorphism K E (coefficientValue K E c lambda xi) ≫
        ArithmeticSourceMaps.localInputMorphism K E := by
  dsimp only [ArithmeticSourceMaps.specializationMorphism, CanonicalCurveInput.scalarMorphism,
    ArithmeticSourceMaps.scalarMorphism, ArithmeticSourceMaps.localInputMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (specialization_comp_scalarHom K E c lambda xi))

theorem coefficientValue_one (lambda xi : Eˣ) :
    coefficientValue K E 1 lambda xi = 1 := map_one _

theorem coefficientValue_xUnit (lambda xi : Eˣ) :
    coefficientValue K E (PhysicalTorusMorphism.xUnit K) lambda xi = lambda :=
  PhysicalTorusMorphism.map_evaluation_xUnit _ _

theorem coefficientValue_yUnit (lambda xi : Eˣ) :
    coefficientValue K E (PhysicalTorusMorphism.yUnit K) lambda xi = xi :=
  PhysicalTorusMorphism.map_evaluation_yUnit _ _

theorem coefficientValue_coefficients (lambda xi : Eˣ) (i : Fin 3) :
    coefficientValue K E (CanonicalCurveInput.coefficients K i) lambda xi =
      ![1, lambda, xi] i := by
  fin_cases i
  · change coefficientValue K E 1 lambda xi = 1
    exact coefficientValue_one K E lambda xi
  · change coefficientValue K E (PhysicalTorusMorphism.xUnit K) lambda xi = lambda
    exact coefficientValue_xUnit K E lambda xi
  · change coefficientValue K E (PhysicalTorusMorphism.yUnit K) lambda xi = xi
    exact coefficientValue_yUnit K E lambda xi

end PrimeGap182.TypeIII.ScalarSourceSpecializationCoordinates
