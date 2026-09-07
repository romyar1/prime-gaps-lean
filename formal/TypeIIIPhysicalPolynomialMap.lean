import TypeIIICoreTraceCoordinates
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Polynomial presentations for the physical Type III parameter map

The two-dimensional torus is presented as the closed subvariety of affine
four-space with coordinates `(x,xInv,y,yInv)` and equations
`x*xInv=1`, `y*yInv=1`. The original physical map has four polynomial
coordinates of degree at most six in this presentation. Their evaluation
is the literal pair `coreLambda`, `coreXi`, with their inverses.

Thus the degree premise in quantitative sheaf theory, Proposition 6.21,
is verified independently of the characteristic and residue parameters.
This file proves the polynomial facts; the geometric complexity theorem
and its interpretation for the relevant morphism remain separate inputs.
-/

noncomputable section
open scoped Classical
open MvPolynomial

namespace PrimeGap182.TypeIII.PhysicalPolynomialMap

open FiniteFieldSums

variable {K : Type*} [Field K]

/-- A fixed closed affine presentation of the two-dimensional torus. -/
def torusEquations : Fin 2 → MvPolynomial (Fin 4) K :=
  ![X 0 * X 1 - 1, X 2 * X 3 - 1]

/-- Coordinates in the closed affine presentation. -/
def torusCoordinates (x y : K) : Fin 4 → K := ![x, x⁻¹, y, y⁻¹]

theorem eval_torusEquations (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) (i : Fin 2) :
    eval (torusCoordinates x y) (torusEquations (K := K) i) = 0 := by
  fin_cases i <;> simp [torusEquations, torusCoordinates, hx, hy]

/-- The equations describe exactly the torus, with no extra components. -/
theorem torusEquations_zero_iff (z : Fin 4 → K) :
    (∀ i, eval z (torusEquations (K := K) i) = 0) ↔
      ∃ x y : K, x ≠ 0 ∧ y ≠ 0 ∧ z = torusCoordinates x y := by
  constructor
  · intro hz
    have h01 : z 0 * z 1 = 1 := by
      simpa [torusEquations, sub_eq_zero] using hz 0
    have h23 : z 2 * z 3 = 1 := by
      simpa [torusEquations, sub_eq_zero] using hz 1
    have h0 : z 0 ≠ 0 := by
      intro h
      simp [h] at h01
    have h2 : z 2 ≠ 0 := by
      intro h
      simp [h] at h23
    have h1 : z 1 = (z 0)⁻¹ := by
      apply mul_left_cancel₀ h0
      simp [h01, h0]
    have h3 : z 3 = (z 2)⁻¹ := by
      apply mul_left_cancel₀ h2
      simp [h23, h2]
    refine ⟨z 0, z 2, h0, h2, ?_⟩
    funext i
    fin_cases i <;> simp [torusCoordinates, h1, h3]
  · rintro ⟨x, y, hx, hy, rfl⟩
    exact eval_torusEquations x y hx hy

theorem torusEquations_degree_le (i : Fin 2) :
    (torusEquations (K := K) i).totalDegree ≤ 2 := by
  have h : ∀ a b : Fin 4, (X a * X b - 1 : MvPolynomial (Fin 4) K).totalDegree ≤ 2 := by
    intro a b
    refine (totalDegree_sub_C_le _ 1).trans ?_
    exact (totalDegree_mul _ _).trans (by simp)
  fin_cases i
  · exact h 0 1
  · exact h 2 3

/-- The original physical map, polynomial in the fixed torus coordinates.
The output order is `(lambda,lambdaInv,xi,xiInv)`. -/
def physicalPolynomials (α m n : K) : Fin 4 → MvPolynomial (Fin 4) K :=
  ![C (m / n) * X 0 ^ 3 * X 3 ^ 3,
    C (n / m) * X 1 ^ 3 * X 2 ^ 3,
    C (m / α) * X 0 ^ 2 * X 3,
    C (α / m) * X 1 ^ 2 * X 2]

theorem eval_physicalPolynomials (α m n x y : K) (i : Fin 4) :
    eval (torusCoordinates x y) (physicalPolynomials α m n i) =
      torusCoordinates (coreLambda m n x y) (coreXi α m x y) i := by
  fin_cases i <;>
    simp [physicalPolynomials, torusCoordinates, coreLambda, coreXi,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

theorem degree_const_two_powers (c : K) (i j : Fin 4) (a b : ℕ) :
    (C c * X i ^ a * X j ^ b : MvPolynomial (Fin 4) K).totalDegree ≤ a + b := by
  calc
    _ ≤ (C c * X i ^ a : MvPolynomial (Fin 4) K).totalDegree +
        (X j ^ b : MvPolynomial (Fin 4) K).totalDegree := totalDegree_mul _ _
    _ ≤ (C c : MvPolynomial (Fin 4) K).totalDegree +
        (X i ^ a : MvPolynomial (Fin 4) K).totalDegree +
        (X j ^ b : MvPolynomial (Fin 4) K).totalDegree :=
      Nat.add_le_add_right (totalDegree_mul _ _) _
    _ = a + b := by simp

theorem physicalPolynomials_degree_le (α m n : K) (i : Fin 4) :
    (physicalPolynomials α m n i).totalDegree ≤ 6 := by
  fin_cases i
  · exact degree_const_two_powers (m / n) 0 3 3 3
  · exact degree_const_two_powers (n / m) 1 2 3 3
  · change (C (m / α) * X 0 ^ 2 * X 3 : MvPolynomial (Fin 4) K).totalDegree ≤ 6
    have h := degree_const_two_powers (m / α) 0 3 2 1
    rw [pow_one] at h
    exact h.trans (by decide : 2 + 1 ≤ 6)
  · change (C (α / m) * X 1 ^ 2 * X 2 : MvPolynomial (Fin 4) K).totalDegree ≤ 6
    have h := degree_const_two_powers (α / m) 1 2 2 1
    rw [pow_one] at h
    exact h.trans (by decide : 2 + 1 ≤ 6)

/-- The polynomial map lands in the same closed torus for all unit parameters. -/
theorem physicalPolynomials_preserve_torus (α m n : K)
    (hα : α ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0) (z : Fin 4 → K)
    (hz : ∀ i, eval z (torusEquations (K := K) i) = 0) (j : Fin 2) :
    eval (fun i => eval z (physicalPolynomials α m n i))
      (torusEquations (K := K) j) = 0 := by
  obtain ⟨x, y, hx, hy, rfl⟩ := (torusEquations_zero_iff z).mp hz
  have he : (fun i => eval (torusCoordinates x y) (physicalPolynomials α m n i)) =
      torusCoordinates (coreLambda m n x y) (coreXi α m x y) := by
    funext i
    exact eval_physicalPolynomials α m n x y i
  rw [he]
  exact eval_torusEquations _ _ (coreLambda_ne_zero m n x y hm hn hx hy)
    (coreXi_ne_zero α m x y hα hm hx hy) j

/-- The physical inclusion into the original affine plane is also polynomial. -/
def planePolynomials : Fin 2 → MvPolynomial (Fin 4) K := ![X 0, X 2]

theorem eval_planePolynomials (x y : K) (i : Fin 2) :
    eval (torusCoordinates x y) (planePolynomials (K := K) i) = ![x, y] i := by
  fin_cases i <;> simp [planePolynomials, torusCoordinates]

theorem planePolynomials_degree_le (i : Fin 2) :
    (planePolynomials (K := K) i).totalDegree ≤ 1 := by
  fin_cases i <;> simp [planePolynomials]

/-- The explicit bound in QST Proposition 6.21. This definition alone is
arithmetic; application to geometric complexity is a separate published input. -/
def polynomialMapBound (nSource nTarget equations degree : ℕ) : ℕ :=
  6 * 2 ^ (nTarget + equations) * (3 + (nTarget + equations) * degree) ^ (nSource + 1)

theorem physical_polynomialMapBound : polynomialMapBound 4 4 2 6 = 34646092416 := by
  norm_num [polynomialMapBound]

end PrimeGap182.TypeIII.PhysicalPolynomialMap

#print axioms PrimeGap182.TypeIII.PhysicalPolynomialMap.torusEquations
#print axioms PrimeGap182.TypeIII.PhysicalPolynomialMap.torusCoordinates
#print axioms PrimeGap182.TypeIII.PhysicalPolynomialMap.eval_torusEquations
#print axioms PrimeGap182.TypeIII.PhysicalPolynomialMap.torusEquations_zero_iff
#print axioms PrimeGap182.TypeIII.PhysicalPolynomialMap.torusEquations_degree_le
#print axioms PrimeGap182.TypeIII.PhysicalPolynomialMap.physicalPolynomials
#print axioms PrimeGap182.TypeIII.PhysicalPolynomialMap.eval_physicalPolynomials
#print axioms PrimeGap182.TypeIII.PhysicalPolynomialMap.degree_const_two_powers
#print axioms PrimeGap182.TypeIII.PhysicalPolynomialMap.physicalPolynomials_degree_le
#print axioms PrimeGap182.TypeIII.PhysicalPolynomialMap.physicalPolynomials_preserve_torus
#print axioms PrimeGap182.TypeIII.PhysicalPolynomialMap.planePolynomials
#print axioms PrimeGap182.TypeIII.PhysicalPolynomialMap.eval_planePolynomials
#print axioms PrimeGap182.TypeIII.PhysicalPolynomialMap.planePolynomials_degree_le
#print axioms PrimeGap182.TypeIII.PhysicalPolynomialMap.polynomialMapBound
#print axioms PrimeGap182.TypeIII.PhysicalPolynomialMap.physical_polynomialMapBound
