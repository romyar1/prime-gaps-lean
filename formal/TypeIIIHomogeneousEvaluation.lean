import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Scalar homogeneity of multivariable polynomial evaluation

Scaling every variable by c multiplies a homogeneous polynomial of
degree d by c^d. The identity holds over arbitrary commutative
semirings, with an arbitrary coefficient homomorphism and variable
type, including zero scalars and the zero polynomial.
-/

namespace PrimeGap182.TypeIII

universe u v w

/-- Evaluation of a homogeneous polynomial commutes with simultaneous
scalar multiplication of all variables, with the expected degree power. -/
theorem homogeneous_eval₂_scale {σ : Type u} {B : Type v} {L : Type w}
    [CommSemiring B] [CommSemiring L]
    {φ : MvPolynomial σ B} {d : ℕ} (hφ : φ.IsHomogeneous d)
    (ρ : B →+* L) (c : L) (w : σ → L) :
    MvPolynomial.eval₂Hom ρ (fun i => c * w i) φ =
      c ^ d * MvPolynomial.eval₂Hom ρ w φ := by
  classical
  have heval (v : σ → L) :
      MvPolynomial.eval₂Hom ρ v φ =
        ∑ s ∈ φ.support, ρ (MvPolynomial.coeff s φ) *
          ∏ i ∈ s.support, v i ^ s i := by
    calc
      _ = MvPolynomial.eval₂Hom ρ v
          (∑ s ∈ φ.support, MvPolynomial.monomial s (MvPolynomial.coeff s φ)) :=
        congrArg (MvPolynomial.eval₂Hom ρ v)
          (MvPolynomial.support_sum_monomial_coeff φ).symm
      _ = _ := by
        simp only [map_sum, MvPolynomial.eval₂Hom_monomial, Finsupp.prod]
  rw [heval, heval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, ← hφ.degree_eq_sum_deg_support hs]
  exact mul_left_comm _ _ _

#print axioms homogeneous_eval₂_scale

end PrimeGap182.TypeIII
