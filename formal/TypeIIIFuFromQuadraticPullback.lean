import TypeIIIPublishedLocalConstruction
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Fu's phase rule from the geometric formula and quadratic base change

The external comparison is an isomorphism with the pushforward appearing
in Fu, Theorem 0.1(iii), with its tame factor retained. It supplies no rank
or phase conclusion. General quadratic-cover base change after wild
restriction gives two rank-one characters. Their rank and squared phase
are deduced here, constructing the existing `FuRules` interface.

All sheaf/functor realizations and the published geometric isomorphism
remain explicit inputs. This module does not assert their existence.
-/

noncomputable section
open scoped BigOperators Classical

namespace PrimeGap182.TypeIII.FuFromQuadraticPullback

open PublishedPhaseApplication

universe u v w t

section Coordinates

variable {L : Type*} [Field L]

/-- The derivative ratio and critical value in the printed Legendre formula
for gamma(x)=x^3 and alpha(x)=3*d*x, including its denominator hypotheses. -/
theorem cubic_legendre_identification (d x : L) (hx : x ≠ 0) (h3 : (3 : L) ≠ 0) :
    -((Polynomial.C (3 * d) * Polynomial.X).derivative.eval x) /
        ((Polynomial.X ^ 3 : Polynomial L).derivative.eval x) = -d / x ^ 2 ∧
      (Polynomial.C (3 * d) * Polynomial.X).eval x +
        (Polynomial.X ^ 3 : Polynomial L).eval x * (-d / x ^ 2) = 2 * d * x := by
  constructor
  · rw [Polynomial.derivative_C_mul_X, Polynomial.derivative_X_pow]
    simp only [Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    change -(3 * d) / (3 * x ^ 2) = -d / x ^ 2
    apply (div_eq_div_iff (mul_ne_zero h3 (pow_ne_zero 2 hx)) (pow_ne_zero 2 hx)).mpr
    ring
  · simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
    have hcancel : x ^ 3 * (-d / x ^ 2) = -d * x := by
      rw [← mul_div_assoc, div_eq_iff (pow_ne_zero 2 hx)]
      ring
    rw [hcancel]
    ring

/-- The literal pullback of xi=c/x^2 along xi=T^2/A. -/
theorem quadratic_pullback_equation (A c T x : L) (hA : A ≠ 0) (hx : x ≠ 0) :
    c / x ^ 2 = T ^ 2 / A ↔ (x * T) ^ 2 = A * c := by
  rw [div_eq_div_iff (pow_ne_zero 2 hx) hA, mul_pow]
  rw [mul_comm c A, mul_comm (x ^ 2) (T ^ 2), eq_comm]

/-- Every branch is included; no choice of a single square root is used
to discard the other branch of the pulled-back quadratic covering. -/
theorem quadratic_pullback_branches (A c T x theta : L)
    (hA : A ≠ 0) (hx : x ≠ 0) (hT : T ≠ 0) (htheta : theta ^ 2 = A * c) :
    c / x ^ 2 = T ^ 2 / A ↔ x = theta / T ∨ x = -theta / T := by
  rw [quadratic_pullback_equation A c T x hA hx, ← htheta,
    sq_eq_sq_iff_eq_or_eq_neg]
  simp only [eq_div_iff hT]

/-- The two geometric branches have the two opposite pole coefficients. -/
def signedCoefficient (b theta : L) (i : Fin 2) : L :=
  if i = 0 then b * theta else -(b * theta)

theorem signed_coefficient_sq (b theta : L) (i : Fin 2) :
    signedCoefficient b theta i ^ 2 = b ^ 2 * theta ^ 2 := by
  by_cases hi : i = 0 <;> simp [signedCoefficient, hi, mul_pow]

/-- Substitution of the actual critical value into both branches gives
the squared phase required by the original local interface. -/
theorem cubic_phase_sq (A q theta : L) (htheta : theta ^ 2 = A * (q - 1))
    (i : Fin 2) :
    signedCoefficient (2 * (1 - q)) theta i ^ 2 = 4 * A * (q - 1) ^ 3 := by
  rw [signed_coefficient_sq, htheta]
  ring

end Coordinates

variable {K : Type u} [Field K] {E : Type v} [Field E]
  {G : Type w} [Group G]

/-- Actual rank-one AS(beta/T) wild characters and their phase observables.
The same model is used for both signs, including beta=0. -/
structure LinearPhaseModels (D : PhaseData K E G) where
  phase : PhaseField K → FDRep E G
  profile : ∀ beta, D.HasProfile (phase beta)
  rank : ∀ beta, Module.finrank E (phase beta) = 1
  phases : ∀ beta, D.phases (phase beta) = {beta}

/-- Pushforward under xi=c/x^2 of AS(b*x), tensored with a tame rank-one
factor on the cover, then pulled back by xi=T^2/A and restricted to wild
inertia. `Twist` parametrizes those actual tame factors; they are retained
until this restriction, not discarded before applying local Fourier. -/
structure QuadraticData (Twist : Type t) where
  output : PhaseField K → PhaseField K → PhaseField K → Twist → FDRep E G

/-- General finite-cover base change and AS coordinate substitution.
The two summands are the two branches proved in `quadratic_pullback_branches`.
No Fourier or Kloosterman representation occurs in this rule. -/
structure QuadraticRules [CharZero E] (p : ℕ) [Fact p.Prime] [CharP K p]
    {D : PhaseData K E G} (M : LinearPhaseModels D)
    {Twist : Type t} (Q : QuadraticData (K := K) (E := E) (G := G) Twist) where
  split : 3 < p → ∀ A c b theta : PhaseField K, ∀ twist : Twist,
    A ≠ 0 → c ≠ 0 → theta ^ 2 = A * c →
      Representation.Equiv (Q.output A c b twist).ρ
        (finiteSum (fun i : Fin 2 => M.phase (signedCoefficient b theta i))).ρ

/-- The geometric isomorphism in Fu 0.1(iii), specialized to r=3,s=1.
Here delta(x)=(q-1)/x^2 and beta(x)=2*(1-q)*x, as checked above.
The Kummer/Gauss factor stays inside the quadratic pushforward. This
record asserts neither a phase profile nor rank two nor a scalar equation. -/
structure FuComparison [CharZero E] (p : ℕ) [Fact p.Prime] [CharP K p]
    (C : CubicFourierData K E G) {Twist : Type t}
    (Q : QuadraticData (K := K) (E := E) (G := G) Twist) where
  twist : PhaseField K → Twist
  comparison : 3 < p → ∀ A q : PhaseField K, A ≠ 0 → q ≠ 1 →
    Representation.Equiv (C.output A q).ρ
      (Q.output A (q - 1) (2 * (1 - q)) (twist q)).ρ

/-- Construct the original Fu rule from the geometric formula, quadratic
base change and general rank-one phase laws. Square-root existence is
proved in the actual algebraically closed phase field. -/
theorem fuRules [CharZero E] (p : ℕ) [Fact p.Prime] [CharP K p]
    {D : PhaseData K E G} {C : CubicFourierData K E G}
    (R : PhaseRules D) (M : LinearPhaseModels D) {Twist : Type t}
    (Q : QuadraticData (K := K) (E := E) (G := G) Twist)
    (QR : QuadraticRules p M Q) (F : FuComparison p C Q) : FuRules p D C := by
  constructor
  intro hp A q hA hq
  obtain ⟨theta, htheta⟩ := IsAlgClosed.exists_pow_nat_eq
    (A * (q - 1)) (by decide : 0 < (2 : ℕ))
  let B : Fin 2 → FDRep E G := fun i => M.phase (signedCoefficient (2 * (1 - q)) theta i)
  let e : Representation.Equiv (C.output A q).ρ (finiteSum B).ρ :=
    (F.comparison hp A q hA hq).trans
      (QR.split hp A (q - 1) (2 * (1 - q)) theta (F.twist q)
        hA (sub_ne_zero.mpr hq) htheta)
  have hB : ∀ i, D.HasProfile (B i) := fun i => M.profile _
  have ht := R.transport (C.output A q) (finiteSum B)
    e.toIntertwiningMap e.toLinearEquiv.bijective
  refine ⟨ht.1.mpr (R.sum_profile B hB), ?_, ?_⟩
  · calc
      Module.finrank E (C.output A q) = Module.finrank E (finiteSum B) :=
        e.toLinearEquiv.finrank_eq
      _ = ∑ i : Fin 2, Module.finrank E (B i) := finiteSum_finrank B
      _ = ∑ _i : Fin 2, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact M.rank _
      _ = 2 := by norm_num
  · intro beta hbeta
    rw [ht.2] at hbeta
    obtain ⟨i, hi⟩ := R.sum_phases B hB beta hbeta
    change beta ∈ D.phases (M.phase (signedCoefficient (2 * (1 - q)) theta i)) at hi
    rw [M.phases, Set.mem_singleton_iff] at hi
    rw [hi]
    exact cubic_phase_sq A q theta htheta i

/-- Geometric inputs for the already proved Fu application. The comparison
and quadratic cover refer to the same output, with its tame factor retained.
No finished rank-two or squared-phase conclusion is stored in this record. -/
structure Inputs [CharZero E] (p : ℕ) [Fact p.Prime] [CharP K p]
    (D : PhaseData K E G) (C : CubicFourierData K E G) where
  Twist : Type t
  linear : LinearPhaseModels D
  quadratic : QuadraticData (K := K) (E := E) (G := G) Twist
  coverRules : QuadraticRules p linear quadratic
  comparison : FuComparison p C quadratic

/-- Assemble the original phase rule from its geometric published inputs. -/
theorem Inputs.fuRules [CharZero E] (p : ℕ) [Fact p.Prime] [CharP K p]
    {D : PhaseData K E G} {C : CubicFourierData K E G}
    (S : Inputs p D C) (R : PhaseRules D) : FuRules p D C :=
  FuFromQuadraticPullback.fuRules p R S.linear S.quadratic S.coverRules S.comparison

end PrimeGap182.TypeIII.FuFromQuadraticPullback

#print axioms PrimeGap182.TypeIII.FuFromQuadraticPullback.cubic_legendre_identification
#print axioms PrimeGap182.TypeIII.FuFromQuadraticPullback.quadratic_pullback_equation
#print axioms PrimeGap182.TypeIII.FuFromQuadraticPullback.quadratic_pullback_branches
#print axioms PrimeGap182.TypeIII.FuFromQuadraticPullback.signed_coefficient_sq
#print axioms PrimeGap182.TypeIII.FuFromQuadraticPullback.cubic_phase_sq
#print axioms PrimeGap182.TypeIII.FuFromQuadraticPullback.fuRules
#print axioms PrimeGap182.TypeIII.FuFromQuadraticPullback.Inputs.fuRules
