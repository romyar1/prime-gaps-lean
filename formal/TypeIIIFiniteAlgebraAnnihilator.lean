import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished

/-!
# Positive-degree annihilators in finite algebras

Let A be a finite commutative R-algebra and let x belong to the extension
of an ideal I of R.  The actual multiplication endomorphism of A by x
has image in I A.  Cayley–Hamilton for finite modules therefore supplies
a monic annihilator whose nonleading coefficients lie in I.

Multiplication of that polynomial by X gives an annihilator whose image
in (R / I)[X] is X^N for an explicitly positive N.  This construction
requires neither freeness nor nontriviality of A.  When R is nontrivial,
the polynomial has degree exactly N and can be packaged as MonicDegreeEq.
No henselianity, idempotent lifting, or proper-geometric input is assumed.
-/

noncomputable section

universe u v

namespace PrimeGap182.TypeIII.FiniteAlgebraAnnihilator

open Polynomial

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [Algebra R A]
variable (I : Ideal R) (x : A)

/-- Multiplication by an element of the extended ideal has its actual
linear-map range in the corresponding scalar multiple of the whole module. -/
theorem lmul_range_le_smul_top (hx : x ∈ I.map (algebraMap R A)) :
    LinearMap.range (Algebra.lmul R A x) ≤ I • (⊤ : Submodule R A) := by
  rw [Ideal.smul_top_eq_map]
  rintro _ ⟨a, rfl⟩
  change x * a ∈ I.map (algebraMap R A)
  exact Ideal.mul_mem_right _ _ hx

variable [Module.Finite R A]

/-- Finite-module Cayley–Hamilton gives an actual distinguished polynomial
annihilating x, with no basis or nonzero-algebra premise. -/
theorem exists_distinguished_annihilator (hx : x ∈ I.map (algebraMap R A)) :
    ∃ P : R[X], P.IsDistinguishedAt I ∧ aeval x P = 0 := by
  obtain ⟨P, hP, _, hcoeff, hzero⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
      R (Algebra.lmul R A x) I (lmul_range_le_smul_top I x hx)
  refine ⟨P, { monic := hP, mem := ?_ }, ?_⟩
  · intro i hi
    exact (Ideal.pow_le_self (Nat.ne_of_gt (Nat.sub_pos_of_lt hi))) (hcoeff i)
  · apply Algebra.lmul_injective (R := R)
    simpa [← aeval_algHom_apply] using hzero

/-- There is a monic annihilator reducing to X^N with N strictly positive.
The exponent is positive even if A, or the base ring, is the zero ring. -/
theorem exists_positive_annihilator (hx : x ∈ I.map (algebraMap R A)) :
    ∃ N : ℕ, 0 < N ∧ ∃ F : R[X],
      F.Monic ∧ aeval x F = 0 ∧ F.map (Ideal.Quotient.mk I) = X ^ N := by
  obtain ⟨P, hP, hzero⟩ := exists_distinguished_annihilator I x hx
  refine ⟨P.natDegree + 1, Nat.succ_pos _, X * P, monic_X.mul hP.monic, ?_, ?_⟩
  · simp [hzero]
  · simp [Polynomial.map_mul, hP.map_eq_X_pow, pow_succ']

/-- Over a nontrivial base ring the same construction has degree exactly N.
No nontriviality assumption is imposed on A. -/
theorem exists_positive_annihilator_with_degree [Nontrivial R]
    (hx : x ∈ I.map (algebraMap R A)) :
    ∃ N : ℕ, 0 < N ∧ ∃ F : R[X],
      F.Monic ∧ F.natDegree = N ∧ aeval x F = 0 ∧
        F.map (Ideal.Quotient.mk I) = X ^ N := by
  obtain ⟨P, hP, hzero⟩ := exists_distinguished_annihilator I x hx
  refine ⟨P.natDegree + 1, Nat.succ_pos _, X * P, monic_X.mul hP.monic, ?_, ?_, ?_⟩
  · exact natDegree_X_mul hP.monic.ne_zero
  · simp [hzero]
  · simp [Polynomial.map_mul, hP.map_eq_X_pow, pow_succ']

/-- The positive-degree annihilator is available in the actual MonicDegreeEq
type used by the universal coprime factorization algebra. -/
theorem exists_positive_monicDegreeEq_annihilator [Nontrivial R]
    (hx : x ∈ I.map (algebraMap R A)) :
    ∃ N : ℕ, 0 < N ∧ ∃ F : MonicDegreeEq R N,
      aeval x F.1 = 0 ∧ F.1.map (Ideal.Quotient.mk I) = X ^ N := by
  obtain ⟨N, hN, F, hF, hdeg, hzero, hmap⟩ :=
    exists_positive_annihilator_with_degree I x hx
  exact ⟨N, hN, MonicDegreeEq.mk F hF hdeg, hzero, hmap⟩

end PrimeGap182.TypeIII.FiniteAlgebraAnnihilator

#print axioms PrimeGap182.TypeIII.FiniteAlgebraAnnihilator.lmul_range_le_smul_top
#print axioms PrimeGap182.TypeIII.FiniteAlgebraAnnihilator.exists_distinguished_annihilator
#print axioms PrimeGap182.TypeIII.FiniteAlgebraAnnihilator.exists_positive_annihilator
#print axioms PrimeGap182.TypeIII.FiniteAlgebraAnnihilator.exists_positive_annihilator_with_degree
#print axioms PrimeGap182.TypeIII.FiniteAlgebraAnnihilator.exists_positive_monicDegreeEq_annihilator
