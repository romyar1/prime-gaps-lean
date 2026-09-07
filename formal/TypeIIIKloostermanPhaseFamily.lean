import TypeIIIArtinSchreierPointTrace
import Mathlib.Algebra.Polynomial.Laurent

/-!
# The actual affine phase family for rank-three Kloosterman sums

The coordinate ring F_p[t,u,u⁻¹,v,v⁻¹] carries the single function
u+v+t/(uv). Its actual Artin--Schreier character sheaf has the required
additive-character trace at every finite-field point (t,u,v).

Summing these actual stalk traces gives the finite Kloosterman sum with
its existing normalization. This is a construction of the phase family
and its integrand sheaf. It does not construct compactly supported
cohomology, the rank-three direct-image sheaf, or any cancellation bound.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open CategoryTheory AlgebraicGeometry
open scoped Classical

/-- The literal coordinate ring of the affine parameter line times
the two-dimensional multiplicative torus over the prime field. -/
abbrev KloostermanPhaseRing (p : ℕ) : Type :=
  LaurentPolynomial (LaurentPolynomial (Polynomial (ZMod p)))

/-- The parameter-coordinate inclusion defining the map to the affine line. -/
def kloostermanPhaseParameterHom (p : ℕ) :
    Polynomial (ZMod p) →+* KloostermanPhaseRing p :=
  LaurentPolynomial.C.comp LaurentPolynomial.C

/-- The actual phase coordinate ring has the original prime characteristic. -/
theorem kloostermanPhaseRing_charP (p : ℕ) [Fact p.Prime] :
    CharP (KloostermanPhaseRing p) p :=
  charP_of_injective_ringHom
    (((kloostermanPhaseParameterHom p).comp Polynomial.C).injective) p

attribute [local instance] kloostermanPhaseRing_charP

/-- The actual function u+v+t u⁻¹v⁻¹ in this one coordinate ring. -/
def kloostermanPhaseFunction (p : ℕ) : KloostermanPhaseRing p :=
  LaurentPolynomial.C (LaurentPolynomial.T 1) + LaurentPolynomial.T 1 +
    kloostermanPhaseParameterHom p Polynomial.X *
      LaurentPolynomial.C (LaurentPolynomial.T (-1)) * LaurentPolynomial.T (-1)

/-- The actual affine phase scheme. -/
abbrev kloostermanPhaseScheme (p : ℕ) : Scheme := Spec (.of (KloostermanPhaseRing p))

/-- Projection of the actual phase family to its affine parameter line. -/
def kloostermanPhaseProjection (p : ℕ) :
    kloostermanPhaseScheme p ⟶ Spec (.of (Polynomial (ZMod p))) :=
  Spec.map (CommRingCat.ofHom (kloostermanPhaseParameterHom p))

section Evaluation

variable (p : ℕ) (K : Type) [Field K] [Algebra (ZMod p) K]
  (t : K) (u v : Kˣ)

/-- An actual finite-torus assignment defines a homomorphism from the
whole phase coordinate ring. The inverse coordinates are handled by the
Laurent universal property, rather than by zero-extended division. -/
def kloostermanPhaseEvaluation : KloostermanPhaseRing p →+* K :=
  LaurentPolynomial.eval₂
    (LaurentPolynomial.eval₂
      (Polynomial.eval₂RingHom (algebraMap (ZMod p) K) t) u) v

/-- The parameter-coordinate map at this point evaluates at t. -/
theorem kloostermanPhaseEvaluation_parameter (g : Polynomial (ZMod p)) :
    kloostermanPhaseEvaluation p K t u v (kloostermanPhaseParameterHom p g) =
      Polynomial.eval₂ (algebraMap (ZMod p) K) t g := by
  simp only [kloostermanPhaseEvaluation, kloostermanPhaseParameterHom,
    RingHom.comp_apply, LaurentPolynomial.eval₂_C, Polynomial.coe_eval₂RingHom]

/-- Evaluating the actual geometric phase gives exactly the expression
in the existing Kloosterman sum. -/
theorem kloostermanPhaseEvaluation_function :
    kloostermanPhaseEvaluation p K t u v (kloostermanPhaseFunction p) =
      (u : K) + (v : K) + t / ((u : K) * (v : K)) := by
  simp only [kloostermanPhaseFunction, map_add, map_mul,
    kloostermanPhaseEvaluation_parameter, Polynomial.eval₂_X]
  simp only [kloostermanPhaseEvaluation, LaurentPolynomial.eval₂_C,
    LaurentPolynomial.eval₂_T, zpow_one, zpow_neg_one, Units.val_inv_eq_inv_val]
  simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc]
  ring

/-- The associated actual K-valued point of the fixed affine phase scheme. -/
def kloostermanPhaseSchemePoint : Spec (.of K) ⟶ kloostermanPhaseScheme p :=
  Spec.map (CommRingCat.ofHom (kloostermanPhaseEvaluation p K t u v))

/-- The actual scheme point lies over the stated parameter value. -/
theorem kloostermanPhaseSchemePoint_over :
    kloostermanPhaseSchemePoint p K t u v ≫ kloostermanPhaseProjection p =
      Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (algebraMap (ZMod p) K) t)) := by
  have h : (kloostermanPhaseEvaluation p K t u v).comp
      (kloostermanPhaseParameterHom p) =
      Polynomial.eval₂RingHom (algebraMap (ZMod p) K) t :=
    RingHom.ext (fun g => kloostermanPhaseEvaluation_parameter p K t u v g)
  dsimp only [kloostermanPhaseSchemePoint, kloostermanPhaseProjection]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

end Evaluation

section ActualSheafTrace

variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Fintype K]
  [Algebra (ZMod p) K] (E : Type) [Field E] (ψ : AddChar (ZMod p) E)

/-- The actual character sheaf of the single function on the fixed
phase family, independent of t,u,v and of the finite extension K. -/
def kloostermanPhaseCharacterSheaf :
    Sheaf (kloostermanPhaseScheme p).smallEtaleTopology (ModuleCat E) :=
  artinSchreierCharacterImageSheaf p (kloostermanPhaseFunction p) E ψ

/-- The geometric Frobenius trace at an actual point of that phase
family. The stalk and operator are the original-base constructions. -/
def kloostermanPhaseTrace (t : K) (u v : Kˣ) : E :=
  let : Algebra (KloostermanPhaseRing p) K :=
    (kloostermanPhaseEvaluation p K t u v).toAlgebra
  LinearMap.trace E
    (ArtinSchreierPointCharacterStalk p (KloostermanPhaseRing p)
      (AlgebraicClosure K) (kloostermanPhaseFunction p) E ψ)
    (artinSchreierPointSheafGeometricFrobenius p (KloostermanPhaseRing p) K
      (AlgebraicClosure K) (kloostermanPhaseFunction p) E ψ)

/-- The integrand is the trace on the actual geometric phase sheaf,
with the positive Artin--Schreier sign and the parameter evaluated at the point. -/
theorem kloostermanPhaseTrace_eq (hpE : (p : E) ≠ 0) (t : K) (u v : Kˣ) :
    kloostermanPhaseTrace p K E ψ t u v =
      ψ (Algebra.trace (ZMod p) K ((u : K) + (v : K) + t / ((u : K) * (v : K)))) := by
  let : CharP K p := artinSchreierPointField_charP p (ZMod p) K
  let : Algebra (KloostermanPhaseRing p) K :=
    (kloostermanPhaseEvaluation p K t u v).toAlgebra
  change LinearMap.trace E
    (ArtinSchreierPointCharacterStalk p (KloostermanPhaseRing p)
      (AlgebraicClosure K) (kloostermanPhaseFunction p) E ψ)
    (artinSchreierPointSheafGeometricFrobenius p (KloostermanPhaseRing p) K
      (AlgebraicClosure K) (kloostermanPhaseFunction p) E ψ) = _
  rw [artinSchreierPointSheafGeometricFrobenius_trace p (KloostermanPhaseRing p) K
    (AlgebraicClosure K) (kloostermanPhaseFunction p) E ψ hpE]
  congr 2
  exact kloostermanPhaseEvaluation_function p K t u v

end ActualSheafTrace

/-- Summing the actual phase-sheaf stalk traces is precisely the finite
rank-three Kloosterman sum with its existing normalization. This is not
a cohomological trace formula or a bound on the sum. -/
theorem kloostermanPhaseTrace_sum (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    [Fintype K] [Algebra (ZMod p) K] (t : K) :
    (Fintype.card K : ℂ)⁻¹ *
        ∑ u : Kˣ, ∑ v : Kˣ, kloostermanPhaseTrace p K ℂ ZMod.stdAddChar t u v =
      FiniteFieldSums.kl3 (FiniteFieldSums.traceAddChar p K) t := by
  have hpℂ : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  simp only [kloostermanPhaseTrace_eq p K ℂ ZMod.stdAddChar hpℂ,
    FiniteFieldSums.kl3, FiniteFieldSums.traceAddChar, AddChar.compAddMonoidHom_apply,
    LinearMap.toAddMonoidHom_coe]

/-- Over the prime field, the sum of the actual phase-sheaf traces
specializes to the original Type III rank-three Kloosterman function. -/
theorem kloostermanPhaseTrace_sum_prime (p : ℕ) [Fact p.Prime] (t : ZMod p) :
    (Fintype.card (ZMod p) : ℂ)⁻¹ *
        ∑ u : (ZMod p)ˣ, ∑ v : (ZMod p)ˣ,
          kloostermanPhaseTrace p (ZMod p) ℂ ZMod.stdAddChar t u v = kl3 p t := by
  convert! (kloostermanPhaseTrace_sum p (ZMod p) t).trans
    (FiniteFieldSums.kl3_prime p t) using 1
  congr 1
  apply Finset.sum_congr (by ext; simp)
  intro u _
  apply Finset.sum_congr (by ext; simp)
  intro v _
  rfl

#print axioms KloostermanPhaseRing
#print axioms kloostermanPhaseParameterHom
#print axioms kloostermanPhaseRing_charP
#print axioms kloostermanPhaseFunction
#print axioms kloostermanPhaseScheme
#print axioms kloostermanPhaseProjection
#print axioms kloostermanPhaseEvaluation
#print axioms kloostermanPhaseEvaluation_parameter
#print axioms kloostermanPhaseEvaluation_function
#print axioms kloostermanPhaseSchemePoint
#print axioms kloostermanPhaseSchemePoint_over
#print axioms kloostermanPhaseCharacterSheaf
#print axioms kloostermanPhaseTrace
#print axioms kloostermanPhaseTrace_eq
#print axioms kloostermanPhaseTrace_sum
#print axioms kloostermanPhaseTrace_sum_prime

end PrimeGap182.TypeIII
