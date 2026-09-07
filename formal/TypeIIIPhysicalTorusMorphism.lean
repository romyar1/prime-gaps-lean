import TypeIIIPhysicalPolynomialMap
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The actual affine torus morphism underlying the physical parameters

The coordinate ring is the quotient by the two literal inverse-coordinate
relations. Its universal evaluation homomorphism constructs an actual
endomorphism and hence an affine scheme morphism. The polynomial formulas
and every extension-field point are identified with the original parameter
map, not just with an unrelated function on rational points.
-/

noncomputable section
open scoped Classical
open MvPolynomial CategoryTheory AlgebraicGeometry

namespace PrimeGap182.TypeIII.PhysicalTorusMorphism

open PhysicalPolynomialMap FiniteFieldSums

universe u
variable (K : Type u) [Field K]

def torusIdeal : Ideal (MvPolynomial (Fin 4) K) :=
  Ideal.span (Set.range (torusEquations (K := K)))

abbrev TorusRing := MvPolynomial (Fin 4) K ⧸ torusIdeal K

def quotient : MvPolynomial (Fin 4) K →ₐ[K] TorusRing K :=
  Ideal.Quotient.mkₐ K (torusIdeal K)

def coordinate (i : Fin 4) : TorusRing K := quotient K (X i)

theorem quotient_torusEquation (i : Fin 2) :
    quotient K (torusEquations (K := K) i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))

theorem coordinate_zero_one : coordinate K 0 * coordinate K 1 = 1 := by
  have h := quotient_torusEquation K 0
  simpa [torusEquations, coordinate, sub_eq_zero] using h

theorem coordinate_two_three : coordinate K 2 * coordinate K 3 = 1 := by
  have h := quotient_torusEquation K 1
  simpa [torusEquations, coordinate, sub_eq_zero] using h

def xUnit : (TorusRing K)ˣ where
  val := coordinate K 0
  inv := coordinate K 1
  val_inv := coordinate_zero_one K
  inv_val := by rw [mul_comm]; exact coordinate_zero_one K

def yUnit : (TorusRing K)ˣ where
  val := coordinate K 2
  inv := coordinate K 3
  val_inv := coordinate_two_three K
  inv_val := by rw [mul_comm]; exact coordinate_two_three K

variable {K} {A : Type u} [CommRing A] [Algebra K A]

/-- Universal evaluation at a pair of units, with the original quotient map. -/
def evaluation (x y : Aˣ) : TorusRing K →ₐ[K] A := by
  let f : MvPolynomial (Fin 4) K →ₐ[K] A :=
    aeval ![(x : A), (↑x⁻¹ : A), (y : A), (↑y⁻¹ : A)]
  apply Ideal.Quotient.liftₐ (torusIdeal K) f
  have hker : torusIdeal K ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change f (torusEquations (K := K) i) = 0
    fin_cases i <;> simp [f, torusEquations]
  exact fun a ha => hker ha

theorem evaluation_quotient (x y : Aˣ) (f : MvPolynomial (Fin 4) K) :
    evaluation (K := K) x y (quotient K f) =
      aeval ![(x : A), (↑x⁻¹ : A), (y : A), (↑y⁻¹ : A)] f := by
  rfl

theorem evaluation_coordinate (x y : Aˣ) (i : Fin 4) :
    evaluation (K := K) x y (coordinate K i) =
      ![(x : A), (↑x⁻¹ : A), (y : A), (↑y⁻¹ : A)] i := by
  rw [coordinate, evaluation_quotient, aeval_X]

theorem map_evaluation_xUnit (x y : Aˣ) :
    Units.map (evaluation (K := K) x y).toRingHom (xUnit K) = x := by
  apply Units.ext
  exact evaluation_coordinate x y 0

theorem map_evaluation_yUnit (x y : Aˣ) :
    Units.map (evaluation (K := K) x y).toRingHom (yUnit K) = y := by
  apply Units.ext
  exact evaluation_coordinate x y 2

variable (K)

/-- The exact physical parameters as units in any coefficient algebra. -/
def mappedParameters (α m n : Kˣ) (x y : Aˣ) : Aˣ × Aˣ :=
  (Units.map (algebraMap K A) (m / n) * x ^ 3 / y ^ 3,
    Units.map (algebraMap K A) (m / α) * x ^ 2 / y)

/-- The contravariant coordinate homomorphism of the physical torus map. -/
def physicalEnd (α m n : Kˣ) : TorusRing K →ₐ[K] TorusRing K :=
  evaluation (mappedParameters K α m n (xUnit K) (yUnit K)).1
    (mappedParameters K α m n (xUnit K) (yUnit K)).2

theorem aeval_physicalPolynomials (α m n : Kˣ) (x y : Aˣ) (i : Fin 4) :
    aeval ![(x : A), (↑x⁻¹ : A), (y : A), (↑y⁻¹ : A)]
        (physicalPolynomials (α : K) (m : K) (n : K) i) =
      ![((mappedParameters K α m n x y).1 : A),
        (↑(mappedParameters K α m n x y).1⁻¹ : A),
        ((mappedParameters K α m n x y).2 : A),
        (↑(mappedParameters K α m n x y).2⁻¹ : A)] i := by
  fin_cases i <;>
    simp [mappedParameters, physicalPolynomials, div_eq_mul_inv,
      mul_comm, mul_left_comm]

theorem aeval_coordinateUnits :
    aeval ![(xUnit K : TorusRing K), (↑(xUnit K)⁻¹ : TorusRing K),
      (yUnit K : TorusRing K), (↑(yUnit K)⁻¹ : TorusRing K)] = quotient K := by
  ext i
  rw [aeval_X]
  fin_cases i <;> rfl

theorem physicalEnd_coordinate (α m n : Kˣ) (i : Fin 4) :
    physicalEnd K α m n (coordinate K i) =
      quotient K (physicalPolynomials (α : K) (m : K) (n : K) i) := by
  rw [physicalEnd, evaluation_coordinate]
  rw [← aeval_physicalPolynomials, aeval_coordinateUnits]

/-- The bounded-degree polynomial presentation is the actual coordinate map. -/
theorem physicalEnd_polynomial_presentation (α m n : Kˣ) :
    (physicalEnd K α m n).comp (quotient K) =
      aeval (fun i => quotient K (physicalPolynomials (α : K) (m : K) (n : K) i)) := by
  ext i
  simpa only [AlgHom.comp_apply, aeval_X, coordinate] using physicalEnd_coordinate K α m n i

variable {K}

theorem evaluation_comp_physicalEnd (α m n : Kˣ) (x y : Aˣ) :
    (evaluation (K := K) x y).comp (physicalEnd K α m n) =
      evaluation (mappedParameters K α m n x y).1 (mappedParameters K α m n x y).2 := by
  apply Ideal.Quotient.algHom_ext K
  ext i
  change evaluation (K := K) x y (physicalEnd K α m n (coordinate K i)) =
    evaluation (mappedParameters K α m n x y).1 (mappedParameters K α m n x y).2
      (coordinate K i)
  rw [physicalEnd_coordinate, evaluation_quotient, evaluation_coordinate]
  exact aeval_physicalPolynomials K α m n x y i

section FieldPoints

variable {L : Type u} [Field L] [Algebra K L]

theorem mappedParameters_value (α m n : Kˣ) (x y : Lˣ) :
    ((mappedParameters K α m n x y).1 : L) =
        coreLambda (algebraMap K L (m : K)) (algebraMap K L (n : K)) (x : L) (y : L) ∧
      ((mappedParameters K α m n x y).2 : L) =
        coreXi (algebraMap K L (α : K)) (algebraMap K L (m : K)) (x : L) (y : L) := by
  simp [mappedParameters, coreLambda, coreXi, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc]

end FieldPoints

variable (K)

/-- The genuine affine scheme underlying the closed torus presentation. -/
abbrev torusScheme : Scheme := Spec (.of (TorusRing K))

/-- The genuine affine scheme morphism inducing the original physical map. -/
def physicalMorphism (α m n : Kˣ) : torusScheme K ⟶ torusScheme K :=
  Spec.map (CommRingCat.ofHom (physicalEnd K α m n).toRingHom)

variable {K}

def schemePoint (x y : Aˣ) : Spec (.of A) ⟶ torusScheme K :=
  Spec.map (CommRingCat.ofHom (evaluation (K := K) x y).toRingHom)

/-- All algebra-valued points transform through the original morphism.
Finite extension fields are a specialization of this identity. -/
theorem schemePoint_physicalMorphism (α m n : Kˣ) (x y : Aˣ) :
    schemePoint (K := K) x y ≫ physicalMorphism K α m n =
      schemePoint (mappedParameters K α m n x y).1 (mappedParameters K α m n x y).2 := by
  have h := congrArg AlgHom.toRingHom (evaluation_comp_physicalEnd α m n x y)
  dsimp only [schemePoint, physicalMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) h

end PrimeGap182.TypeIII.PhysicalTorusMorphism

#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.torusIdeal
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.TorusRing
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.quotient
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.coordinate
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.quotient_torusEquation
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.coordinate_zero_one
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.coordinate_two_three
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.xUnit
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.yUnit
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.evaluation
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.evaluation_quotient
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.evaluation_coordinate
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.map_evaluation_xUnit
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.map_evaluation_yUnit
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.mappedParameters
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.physicalEnd
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.aeval_physicalPolynomials
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.aeval_coordinateUnits
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.physicalEnd_coordinate
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.physicalEnd_polynomial_presentation
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.evaluation_comp_physicalEnd
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.mappedParameters_value
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.torusScheme
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.physicalMorphism
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.schemePoint
#print axioms PrimeGap182.TypeIII.PhysicalTorusMorphism.schemePoint_physicalMorphism
