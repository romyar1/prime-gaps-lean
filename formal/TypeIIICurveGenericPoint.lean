import TypeIIICurveFunctionField

/-! The actual generic tangent point lies outside all constant points.

This supplies explicit polynomial evaluations in the curve's function field.
It does not identify a sheaf's lisse locus or construct a local inertia group.
-/

noncomputable section
open scoped Classical
open MvPolynomial

namespace PrimeGap182.TypeIII.CurveFunctionField

variable {k : Type*} [Field k] {f : MvPolynomial (Fin 2) k}

def genericPoint (f : MvPolynomial (Fin 2) k) : Fin 2 → functionField f :=
  fun i => polynomialMap f (X i)

theorem aeval_genericPoint (g : MvPolynomial (Fin 2) k) :
    aeval (genericPoint f) g = polynomialMap f g :=
  congrArg (fun φ : MvPolynomial (Fin 2) k →ₐ[k] functionField f => φ g)
    (MvPolynomial.aeval_unique (polynomialMap f)).symm

theorem polynomialMap_eq_eval_of_genericPoint_eq_constant (x : Fin 2 → k)
    (hx : genericPoint f = fun i => algebraMap k (functionField f) (x i))
    (g : MvPolynomial (Fin 2) k) :
    polynomialMap f g = algebraMap k (functionField f) (eval x g) := by
  induction g using MvPolynomial.induction_on with
  | C c =>
      change algebraMap k (functionField f) c = algebraMap k (functionField f) (eval x (C c))
      rw [eval_C]
  | add a b ha hb =>
      rw [map_add, ha, hb, eval_add, map_add]
  | mul_X a i ha =>
      have hi := congrFun hx i
      change polynomialMap f (X i) = algebraMap k (functionField f) (x i) at hi
      rw [map_mul, ha, hi, eval_mul, eval_X, map_mul]

variable [Fact (Irreducible f)]

theorem gaussSlope_eq_constant_of_genericPoint_eq_constant (x : Fin 2 → k)
    (hx : genericPoint f = fun i => algebraMap k (functionField f) (x i)) :
    gaussSlope f = algebraMap k (functionField f)
      (eval x (pderiv 1 f) / eval x (pderiv 0 f)) := by
  rw [gaussSlope, polynomialMap_eq_eval_of_genericPoint_eq_constant x hx,
    polynomialMap_eq_eval_of_genericPoint_eq_constant x hx, map_div₀]

theorem genericPoint_ne_constant_charP [IsAlgClosed k] (p : ℕ) [CharP k p]
    (hp : f.totalDegree < p) (hd : 1 < f.totalDegree) (x : Fin 2 → k) :
    genericPoint f ≠ fun i => algebraMap k (functionField f) (x i) := by
  intro hx
  exact gaussSlope_ne_constant_charP p hp hd _
    (gaussSlope_eq_constant_of_genericPoint_eq_constant x hx)

theorem genericPoint_ne_constant_charZero [IsAlgClosed k] [CharZero k]
    (hd : 1 < f.totalDegree) (x : Fin 2 → k) :
    genericPoint f ≠ fun i => algebraMap k (functionField f) (x i) := by
  intro hx
  exact gaussSlope_ne_constant_charZero hd _
    (gaussSlope_eq_constant_of_genericPoint_eq_constant x hx)

theorem generic_tangent_data_charP [IsAlgClosed k] (p : ℕ) [CharP k p]
    (hp : f.totalDegree < p) (hd : 1 < f.totalDegree) :
    aeval (genericPoint f) f = 0 ∧
      aeval (genericPoint f) (pderiv 0 f) ≠ 0 ∧
      Transcendental k (gaussSlope f) ∧
      genericPoint f 0 + gaussSlope f * genericPoint f 1 ≠ 0 ∧
      ∀ x : Fin 2 → k,
        genericPoint f ≠ fun i => algebraMap k (functionField f) (x i) := by
  refine ⟨?_, ?_, gaussSlope_transcendental_charP p hp hd,
    criticalValue_ne_zero_charP p hp hd, genericPoint_ne_constant_charP p hp hd⟩
  · rw [aeval_genericPoint]
    exact defining_equation
  · rw [aeval_genericPoint]
    exact partial_zero_ne_zero_charP p hp hd

#print axioms aeval_genericPoint
#print axioms polynomialMap_eq_eval_of_genericPoint_eq_constant
#print axioms genericPoint_ne_constant_charP
#print axioms genericPoint_ne_constant_charZero
#print axioms generic_tangent_data_charP

end PrimeGap182.TypeIII.CurveFunctionField
