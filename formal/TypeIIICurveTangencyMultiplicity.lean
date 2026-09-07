import TypeIIICurveProjection
import TypeIIICurveGenericPoint

/-! Actual generic tangent fiber polynomial and its root multiplicity.

The multiplicity here is Mathlib's polynomial `rootMultiplicity`. No
identification with a geometric ramification index or inertia action is
assumed or asserted.
-/

noncomputable section
open MvPolynomial

namespace PrimeGap182.TypeIII.CurveTangencyMultiplicity

open PrimeGap182.TypeIII.CurveProjection
open PrimeGap182.TypeIII.CurveFunctionField

set_option maxHeartbeats 600000

section PolynomialChainRule

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The actual formal derivative of the literal projection substitution. -/
theorem derivative_projectionPolynomial (f : MvPolynomial (Fin 2) k) (z s : K) :
    (projectionPolynomial f z s).derivative =
      -Polynomial.C z * projectionPolynomial (pderiv 0 f) z s +
        projectionPolynomial (pderiv 1 f) z s := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [projectionPolynomial]
  | add f g hf hg =>
      simp only [projectionPolynomial, map_add] at hf hg ⊢
      rw [hf, hg]
      ring
  | mul_X f i hf =>
      fin_cases i <;>
        norm_num [projectionPolynomial, MvPolynomial.pderiv_mul,
          Pi.single_apply, Polynomial.derivative_mul] at hf ⊢ <;>
        rw [hf] <;> ring

/-- A root's actual multiplicity is bounded by the degree of a nonzero
polynomial, using divisibility by the corresponding power of `T-t`. -/
theorem rootMultiplicity_le_natDegree_of_ne_zero {g : Polynomial K}
    (hg : g ≠ 0) (t : K) : g.rootMultiplicity t ≤ g.natDegree := by
  have h := Polynomial.natDegree_le_of_dvd (g.pow_rootMultiplicity_dvd t) hg
  simpa only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] using h

end PolynomialChainRule

variable {k : Type*} [Field k] {f : MvPolynomial (Fin 2) k}
variable [Fact (Irreducible f)]

/-- The explicit fiber polynomial at the actual generic tangent value. -/
def tangentPolynomial (f : MvPolynomial (Fin 2) k) [Fact (Irreducible f)] :
    Polynomial (functionField f) :=
  projectionPolynomial f (gaussSlope f) (criticalValue f)

/-- Multiplicity of the actual second generic coordinate in that polynomial. -/
def tangentMultiplicity (f : MvPolynomial (Fin 2) k) [Fact (Irreducible f)] : ℕ :=
  (tangentPolynomial f).rootMultiplicity (genericPoint f 1)

theorem eval_projection_at_genericPoint (g : MvPolynomial (Fin 2) k) :
    Polynomial.eval (genericPoint f 1)
      (projectionPolynomial g (gaussSlope f) (criticalValue f)) = polynomialMap f g := by
  rw [eval_projectionPolynomial]
  have hcoords : ![criticalValue f - gaussSlope f * genericPoint f 1, genericPoint f 1] =
      genericPoint f := by
    funext i
    fin_cases i <;> simp [criticalValue, CurveFunctionField.genericPoint]
  rw [hcoords, aeval_genericPoint]

theorem tangentPolynomial_eval :
    Polynomial.eval (genericPoint f 1) (tangentPolynomial f) = 0 := by
  rw [tangentPolynomial, eval_projection_at_genericPoint]
  exact defining_equation

theorem tangentPolynomial_derivative_eval
    (hden : polynomialMap f (pderiv 0 f) ≠ 0) :
    Polynomial.eval (genericPoint f 1) (tangentPolynomial f).derivative = 0 := by
  rw [tangentPolynomial, derivative_projectionPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_C,
    eval_projection_at_genericPoint, eval_projection_at_genericPoint]
  calc
    -gaussSlope f * polynomialMap f (pderiv 0 f) + polynomialMap f (pderiv 1 f) =
        polynomialMap f (pderiv 1 f) - gaussSlope f * polynomialMap f (pderiv 0 f) := by ring
    _ = 0 := critical_direction_equation hden

private theorem tangent_multiplicity_of_transcendental
    (hz : Transcendental k (gaussSlope f))
    (hden : polynomialMap f (pderiv 0 f) ≠ 0) :
    tangentPolynomial f ≠ 0 ∧ (tangentPolynomial f).natDegree = f.totalDegree ∧
      2 ≤ tangentMultiplicity f ∧ tangentMultiplicity f ≤ f.totalDegree ∧
      (Polynomial.X - Polynomial.C (genericPoint f 1)) ^ 2 ∣ tangentPolynomial f := by
  have hf : f ≠ 0 := (Fact.out : Irreducible f).ne_zero
  have hnonzero : tangentPolynomial f ≠ 0 :=
    projectionPolynomial_ne_zero hf hz (criticalValue f)
  have hdegree : (tangentPolynomial f).natDegree = f.totalDegree :=
    natDegree_projectionPolynomial_eq hf hz (criticalValue f)
  have htwo : 2 ≤ tangentMultiplicity f :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hnonzero).mpr
      ⟨tangentPolynomial_eval, tangentPolynomial_derivative_eval hden⟩
  have hle : tangentMultiplicity f ≤ f.totalDegree := by
    rw [← hdegree]
    exact rootMultiplicity_le_natDegree_of_ne_zero hnonzero (genericPoint f 1)
  exact ⟨hnonzero, hdegree, htwo, hle, (Polynomial.le_rootMultiplicity_iff hnonzero).mp htwo⟩

/-- All polynomial multiplicity assertions at the actual generic tangent
are closed under the bounded-characteristic curve hypotheses. -/
theorem tangent_multiplicity_charP [IsAlgClosed k] (p : ℕ) [CharP k p]
    (hp : f.totalDegree < p) (hd : 1 < f.totalDegree) :
    tangentPolynomial f ≠ 0 ∧ (tangentPolynomial f).natDegree = f.totalDegree ∧
      2 ≤ tangentMultiplicity f ∧ tangentMultiplicity f ≤ f.totalDegree ∧
      (Polynomial.X - Polynomial.C (genericPoint f 1)) ^ 2 ∣ tangentPolynomial f :=
  tangent_multiplicity_of_transcendental (gaussSlope_transcendental_charP p hp hd)
    (partial_zero_ne_zero_charP p hp hd)

theorem tangent_multiplicity_charZero [IsAlgClosed k] [CharZero k]
    (hd : 1 < f.totalDegree) :
    tangentPolynomial f ≠ 0 ∧ (tangentPolynomial f).natDegree = f.totalDegree ∧
      2 ≤ tangentMultiplicity f ∧ tangentMultiplicity f ≤ f.totalDegree ∧
      (Polynomial.X - Polynomial.C (genericPoint f 1)) ^ 2 ∣ tangentPolynomial f :=
  tangent_multiplicity_of_transcendental (gaussSlope_transcendental_charZero hd)
    (partial_zero_ne_zero_charZero hd)

/-- Literal degree, root and derivative conditions, multiplicity bounds,
and coprimality with the characteristic prime for the constructed fiber. -/
theorem generic_tangency_multiplicity_charP [IsAlgClosed k]
    (p : ℕ) [CharP k p] (hpPrime : p.Prime)
    (hp : f.totalDegree < p) (hd : 1 < f.totalDegree) :
    (tangentPolynomial f).degree = (f.totalDegree : WithBot ℕ) ∧
      Polynomial.eval (genericPoint f 1) (tangentPolynomial f) = 0 ∧
      Polynomial.eval (genericPoint f 1) (tangentPolynomial f).derivative = 0 ∧
      2 ≤ tangentMultiplicity f ∧ tangentMultiplicity f ≤ f.totalDegree ∧
      tangentMultiplicity f < p ∧ Nat.Coprime (tangentMultiplicity f) p := by
  obtain ⟨hnonzero, hdegree, htwo, hle, _⟩ := tangent_multiplicity_charP p hp hd
  have hlt := hle.trans_lt hp
  refine ⟨?_, tangentPolynomial_eval,
    tangentPolynomial_derivative_eval (partial_zero_ne_zero_charP p hp hd),
    htwo, hle, hlt, ?_⟩
  · rw [Polynomial.degree_eq_natDegree hnonzero, hdegree]
  · exact (Nat.coprime_of_lt_prime (by omega) hlt hpPrime).symm

theorem generic_tangency_multiplicity_charZero [IsAlgClosed k] [CharZero k]
    (hd : 1 < f.totalDegree) :
    (tangentPolynomial f).degree = (f.totalDegree : WithBot ℕ) ∧
      Polynomial.eval (genericPoint f 1) (tangentPolynomial f) = 0 ∧
      Polynomial.eval (genericPoint f 1) (tangentPolynomial f).derivative = 0 ∧
      2 ≤ tangentMultiplicity f ∧ tangentMultiplicity f ≤ f.totalDegree := by
  obtain ⟨hnonzero, hdegree, htwo, hle, _⟩ := tangent_multiplicity_charZero hd
  refine ⟨?_, tangentPolynomial_eval,
    tangentPolynomial_derivative_eval (partial_zero_ne_zero_charZero hd), htwo, hle⟩
  rw [Polynomial.degree_eq_natDegree hnonzero, hdegree]

#print axioms derivative_projectionPolynomial
#print axioms rootMultiplicity_le_natDegree_of_ne_zero
#print axioms eval_projection_at_genericPoint
#print axioms tangentPolynomial_eval
#print axioms tangentPolynomial_derivative_eval
#print axioms tangent_multiplicity_charP
#print axioms tangent_multiplicity_charZero
#print axioms generic_tangency_multiplicity_charP
#print axioms generic_tangency_multiplicity_charZero

end PrimeGap182.TypeIII.CurveTangencyMultiplicity
