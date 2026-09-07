import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Intersection of two homogeneous coordinate fractions

If homogeneous fractions with denominators powers of distinct coordinate
variables have equal cross products, they have a unique common scalar value.
The proof compares polynomial coefficients and cancels only coordinate
monomials, which are regular over every commutative coefficient ring.

The zero ring and zero denominator exponents are allowed.  This is an
algebraic statement in the original multivariable polynomial ring; it does
not assert a global-sections theorem for a projective scheme.
-/

namespace PrimeGap182.TypeIII

universe u v

/-- Compatible homogeneous coordinate fractions are the same scalar.
No domain, nontriviality, or positive-exponent hypothesis is required. -/
theorem homogeneous_coordinate_intersection {σ : Type u} {R : Type v} [CommRing R]
    {i j : σ} (hij : i ≠ j) {P Q : MvPolynomial σ R} {n m : ℕ}
    (hP : P.IsHomogeneous n) (hQ : Q.IsHomogeneous m)
    (hcross : P * MvPolynomial.X j ^ m = Q * MvPolynomial.X i ^ n) :
    ∃! r : R, P = MvPolynomial.C r * MvPolynomial.X i ^ n ∧
      Q = MvPolynomial.C r * MvPolynomial.X j ^ m := by
  classical
  have monomial_of_cross {F G : MvPolynomial σ R} {a b : σ} {r s : ℕ}
      (hab : a ≠ b) (hF : F.IsHomogeneous r)
      (hFG : F * MvPolynomial.X b ^ s = G * MvPolynomial.X a ^ r) :
      F = MvPolynomial.C (MvPolynomial.coeff (Finsupp.single a r) F) *
        MvPolynomial.X a ^ r := by
    rw [MvPolynomial.C_mul_X_pow_eq_monomial]
    apply MvPolynomial.eq_monomial_of_support_subset_singleton
    intro d hd
    have hd0 : MvPolynomial.coeff d F ≠ 0 := MvPolynomial.mem_support_iff.mp hd
    have hc := congrArg (MvPolynomial.coeff (d + Finsupp.single b s)) hFG
    simp only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_mul_monomial,
      mul_one] at hc
    rw [MvPolynomial.coeff_mul_monomial'] at hc
    have hle' : Finsupp.single a r ≤ d + Finsupp.single b s := by
      by_contra h
      exact hd0 (by simpa only [ite_eq_right h] using hc)
    have hle : Finsupp.single a r ≤ d := by
      apply Finsupp.single_le_iff.mpr
      simpa [hab.symm] using Finsupp.single_le_iff.mp hle'
    have hdeg : Finsupp.degree d = r := by
      simpa only [Finsupp.degree_apply] using (hF.degree_eq_sum_deg_support hd).symm
    obtain ⟨e, he⟩ := exists_add_of_le hle
    have he0 : Finsupp.degree e = 0 := by
      rw [he, map_add, Finsupp.degree_single] at hdeg
      omega
    have hezero : e = 0 := (Finsupp.degree_eq_zero_iff e).mp he0
    simpa only [hezero, add_zero] using he
  have hPmono := monomial_of_cross hij hP hcross
  have hQmono := monomial_of_cross hij.symm hQ hcross.symm
  have hcoeff : MvPolynomial.coeff (Finsupp.single i n) P =
      MvPolynomial.coeff (Finsupp.single j m) Q := by
    apply MvPolynomial.C_injective σ R
    apply (MvPolynomial.isRegular_X_pow (R := R) (n := i) n).right
    apply (MvPolynomial.isRegular_X_pow (R := R) (n := j) m).right
    calc
      _ = P * MvPolynomial.X j ^ m :=
        congrArg (fun F => F * MvPolynomial.X j ^ m) hPmono.symm
      _ = Q * MvPolynomial.X i ^ n := hcross
      _ = (MvPolynomial.C (MvPolynomial.coeff (Finsupp.single j m) Q) *
          MvPolynomial.X j ^ m) * MvPolynomial.X i ^ n :=
        congrArg (fun F => F * MvPolynomial.X i ^ n) hQmono
      _ = _ := by dsimp; ac_rfl
  refine ⟨MvPolynomial.coeff (Finsupp.single i n) P, ⟨hPmono, ?_⟩, ?_⟩
  · rw [hcoeff]
    exact hQmono
  · intro r hr
    have hc := congrArg (MvPolynomial.coeff (Finsupp.single i n)) hr.1
    simpa [MvPolynomial.C_mul_X_pow_eq_monomial] using hc.symm

#print axioms homogeneous_coordinate_intersection

end PrimeGap182.TypeIII
