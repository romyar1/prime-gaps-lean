import TypeIIICurvePolynomial
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.CharZero.Infinite

/-! Constant-direction polynomial core of the Type III curve argument.

This isolated module concerns actual bivariate polynomials and their partial
derivatives. It does not assert any implication from a geometric tangent map,
Fourier support, or a sheaf condition. The frozen analytic closure is unchanged.
-/

noncomputable section

open scoped BigOperators
open MvPolynomial

namespace PrimeGap182.TypeIII.CurveDirection

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

variable {k : Type*} [Field k]

/-- The actual restriction of a bivariate polynomial to an affine line. -/
def linePolynomial (f : MvPolynomial (Fin 2) k) (x y a b : k) : Polynomial k :=
  MvPolynomial.aeval ![Polynomial.C x + Polynomial.C a * Polynomial.X,
    Polynomial.C y + Polynomial.C b * Polynomial.X] f

theorem eval_linePolynomial (f : MvPolynomial (Fin 2) k) (x y a b t : k) :
    Polynomial.eval t (linePolynomial f x y a b) =
      MvPolynomial.eval ![x + a * t, y + b * t] f := by
  change (Polynomial.aeval t) (MvPolynomial.aeval _ f) = _
  rw [MvPolynomial.comp_aeval_apply]
  change MvPolynomial.aeval _ f = MvPolynomial.aeval ![x + a * t, y + b * t] f
  apply congrArg (fun u : Fin 2 → k => MvPolynomial.aeval u f)
  funext i
  fin_cases i <;> simp

/-- The elementary chain rule is proved for the literal affine restriction. -/
theorem derivative_linePolynomial (f : MvPolynomial (Fin 2) k) (x y a b : k) :
    (linePolynomial f x y a b).derivative =
      Polynomial.C a * linePolynomial (pderiv 0 f) x y a b +
      Polynomial.C b * linePolynomial (pderiv 1 f) x y a b := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [linePolynomial]
  | add f g hf hg =>
      simp only [linePolynomial, map_add] at hf hg ⊢
      rw [hf, hg]
      ring
  | mul_X f i hf =>
      fin_cases i <;>
        norm_num [linePolynomial, MvPolynomial.pderiv_mul,
          Pi.single_apply, Polynomial.derivative_mul] at hf ⊢ <;>
        rw [hf] <;> ring

/-- Affine restriction cannot increase the actual total degree. -/
theorem natDegree_linePolynomial_le (f : MvPolynomial (Fin 2) k) (x y a b : k) :
    (linePolynomial f x y a b).natDegree ≤ f.totalDegree := by
  classical
  have hlinear (u v : k) :
      (Polynomial.C u + Polynomial.C v * Polynomial.X).natDegree ≤ 1 :=
    Polynomial.natDegree_add_le_of_degree_le (by simp)
      ((Polynomial.natDegree_C_mul_le v Polynomial.X).trans Polynomial.natDegree_X_le)
  unfold linePolynomial
  conv_lhs => rw [← f.support_sum_monomial_coeff, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  have hddeg : d 0 + d 1 ≤ f.totalDegree := by
    simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using le_totalDegree hd
  rw [MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Polynomial.algebraMap_apply]
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  exact (Polynomial.natDegree_mul_le_of_le
    (by simpa using Polynomial.natDegree_pow_le_of_le (d 0) (hlinear x a))
    (by simpa using Polynomial.natDegree_pow_le_of_le (d 1) (hlinear y b))).trans hddeg

private theorem eq_C_of_derivative_zero_of_cast
    {p : Polynomial k} {N : ℕ} (hpN : p.natDegree ≤ N)
    (hcast : ∀ n : ℕ, n ≤ N → (n : k) = 0 → n = 0)
    (hd : p.derivative = 0) : p = Polynomial.C (p.coeff 0) := by
  apply Polynomial.eq_C_of_natDegree_eq_zero
  by_contra hn
  have hp : p ≠ 0 := by
    intro hp
    simp [hp] at hn
  have hsucc : p.natDegree - 1 + 1 = p.natDegree :=
    Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)
  have hc := congrArg (fun q : Polynomial k => q.coeff (p.natDegree - 1)) hd
  have hmul : p.leadingCoeff * (p.natDegree : k) = 0 := by
    simpa only [Polynomial.coeff_derivative, Polynomial.coeff_zero,
      ← Nat.cast_add_one, hsucc, Polynomial.coeff_natDegree] using hc
  exact hn (hcast _ hpN ((mul_eq_zero.mp hmul).resolve_left
    (Polynomial.leadingCoeff_ne_zero.mpr hp)))

/-- A vanishing constant-direction derivative makes the actual polynomial
constant along every line in that direction, with the small-characteristic
obstruction recorded only as injectivity of the relevant natural scalars. -/
theorem eval_translate_of_direction_zero_of_cast
    (f : MvPolynomial (Fin 2) k) (a b : k)
    (hcast : ∀ n : ℕ, n ≤ f.totalDegree → (n : k) = 0 → n = 0)
    (hD : C a * pderiv 0 f + C b * pderiv 1 f = 0) (x y t : k) :
    MvPolynomial.eval ![x + a * t, y + b * t] f =
      MvPolynomial.eval ![x, y] f := by
  have hd : (linePolynomial f x y a b).derivative = 0 := by
    rw [derivative_linePolynomial]
    have h := congrArg (fun g => linePolynomial g x y a b) hD
    simpa [linePolynomial, MvPolynomial.aeval_C] using h
  have hc := eq_C_of_derivative_zero_of_cast
    (natDegree_linePolynomial_le f x y a b) hcast hd
  calc
    MvPolynomial.eval ![x + a * t, y + b * t] f =
        Polynomial.eval t (linePolynomial f x y a b) :=
      (eval_linePolynomial f x y a b t).symm
    _ = Polynomial.eval 0 (linePolynomial f x y a b) := by rw [hc]; simp
    _ = MvPolynomial.eval ![x, y] f := by
      simpa using eval_linePolynomial f x y a b 0

/-- The perpendicular linear coordinate associated with the direction `(a,b)`. -/
def perpendicularCoordinate (a b : k) : MvPolynomial (Fin 2) k :=
  C b * X 0 - C a * X 1

@[simp] theorem eval_perpendicularCoordinate (a b : k) (z : Fin 2 → k) :
    MvPolynomial.eval z (perpendicularCoordinate a b) = b * z 0 - a * z 1 := by
  simp [perpendicularCoordinate]

theorem eval_polynomial_aeval (p : Polynomial k) (l : MvPolynomial (Fin 2) k)
    (z : Fin 2 → k) :
    MvPolynomial.eval z (Polynomial.aeval l p) =
      Polynomial.eval (MvPolynomial.eval z l) p :=
  (Polynomial.aeval_algHom_apply (MvPolynomial.aeval z) l p).symm

/-- The one-variable representation is constructed from actual restrictions
of `f`; no change of coordinates or decomposition is supplied as a hypothesis. -/
theorem exists_polynomial_perpendicular_of_direction_zero_of_cast [Infinite k]
    (f : MvPolynomial (Fin 2) k) (a b : k) (hab : a ≠ 0 ∨ b ≠ 0)
    (hcast : ∀ n : ℕ, n ≤ f.totalDegree → (n : k) = 0 → n = 0)
    (hD : C a * pderiv 0 f + C b * pderiv 1 f = 0) :
    ∃ p : Polynomial k, f = Polynomial.aeval (perpendicularCoordinate a b) p := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := hab.resolve_left (not_not_intro ha)
    refine ⟨linePolynomial f 0 0 b⁻¹ 0, ?_⟩
    apply MvPolynomial.funext
    intro z
    rw [eval_polynomial_aeval, eval_linePolynomial, eval_perpendicularCoordinate]
    have hz := eval_translate_of_direction_zero_of_cast f a b hcast hD
      (z 0) (z 1) (-(z 1) / b)
    have hfirst : z 0 + a * (-(z 1) / b) = z 0 := by simp [ha]
    have hsecond : z 1 + b * (-(z 1) / b) = 0 := by field_simp; ring
    have hzeta : ![z 0, z 1] = z := by ext i; fin_cases i <;> rfl
    rw [hfirst, hsecond, hzeta] at hz
    simpa [ha, hb] using hz.symm
  · refine ⟨linePolynomial f 0 0 0 (-a⁻¹), ?_⟩
    apply MvPolynomial.funext
    intro z
    rw [eval_polynomial_aeval, eval_linePolynomial, eval_perpendicularCoordinate]
    have hz := eval_translate_of_direction_zero_of_cast f a b hcast hD
      (z 0) (z 1) (-(z 0) / a)
    have hfirst : z 0 + a * (-(z 0) / a) = 0 := by field_simp; ring
    have hsecond : z 1 + b * (-(z 0) / a) =
        -a⁻¹ * (b * z 0 - a * z 1) := by field_simp; ring
    have hzeta : ![z 0, z 1] = z := by ext i; fin_cases i <;> rfl
    rw [hfirst, hsecond, hzeta] at hz
    simpa using hz.symm

theorem exists_polynomial_perpendicular_of_direction_zero_charZero [CharZero k]
    (f : MvPolynomial (Fin 2) k) (a b : k) (hab : a ≠ 0 ∨ b ≠ 0)
    (hD : C a * pderiv 0 f + C b * pderiv 1 f = 0) :
    ∃ p : Polynomial k, f = Polynomial.aeval (perpendicularCoordinate a b) p :=
  exists_polynomial_perpendicular_of_direction_zero_of_cast f a b hab
    (fun _ _ h => Nat.cast_eq_zero.mp h) hD

theorem exists_polynomial_perpendicular_of_direction_zero_charP [Infinite k]
    (p : ℕ) [CharP k p] (f : MvPolynomial (Fin 2) k)
    (hp : f.totalDegree < p) (a b : k) (hab : a ≠ 0 ∨ b ≠ 0)
    (hD : C a * pderiv 0 f + C b * pderiv 1 f = 0) :
    ∃ q : Polynomial k, f = Polynomial.aeval (perpendicularCoordinate a b) q := by
  apply exists_polynomial_perpendicular_of_direction_zero_of_cast f a b hab _ hD
  intro n hn hcast
  exact CharP.natCast_injOn_Iio k p (hn.trans_lt hp) (Nat.zero_lt_of_lt hp)
    (by simpa using hcast)

theorem perpendicularCoordinate_surjective (a b : k) (hab : a ≠ 0 ∨ b ≠ 0) :
    Function.Surjective (fun z : Fin 2 → k =>
      MvPolynomial.eval z (perpendicularCoordinate a b)) := by
  intro r
  by_cases ha : a = 0
  · have hb : b ≠ 0 := hab.resolve_left (not_not_intro ha)
    refine ⟨![r / b, 0], ?_⟩
    simp [ha]
    field_simp
  · refine ⟨![0, -r / a], ?_⟩
    simp
    field_simp

theorem perpendicularCoordinate_sub_C_not_isUnit (a b r : k)
    (hab : a ≠ 0 ∨ b ≠ 0) :
    ¬IsUnit (perpendicularCoordinate a b - C r) := by
  obtain ⟨z, hz⟩ := perpendicularCoordinate_surjective a b hab r
  change MvPolynomial.eval z (perpendicularCoordinate a b) = r at hz
  intro hu
  have h := hu.map (MvPolynomial.eval z)
  rw [map_sub, MvPolynomial.eval_C, hz, sub_self] at h
  exact not_isUnit_zero h

/-- Algebraic closedness and irreducibility turn an actual polynomial in a
nonconstant linear coordinate into a scalar multiple of one affine factor. -/
theorem irreducible_aeval_perpendicular_eq_linear_factor [IsAlgClosed k]
    {f : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (a b : k) (hab : a ≠ 0 ∨ b ≠ 0) (p : Polynomial k)
    (hfp : f = Polynomial.aeval (perpendicularCoordinate a b) p) :
    ∃ d r : k, d ≠ 0 ∧ f = C d * (perpendicularCoordinate a b - C r) := by
  have hpdegree : p.degree ≠ 0 := by
    intro hpdegree
    have hpc := Polynomial.eq_C_of_natDegree_eq_zero
      (Polynomial.natDegree_eq_of_degree_eq_some hpdegree)
    have hfC : f = C (p.coeff 0) := calc
      f = Polynomial.aeval (perpendicularCoordinate a b) p := hfp
      _ = Polynomial.aeval (perpendicularCoordinate a b) (Polynomial.C (p.coeff 0)) :=
        congrArg (Polynomial.aeval (perpendicularCoordinate a b)) hpc
      _ = C (p.coeff 0) := by simp
    have hc : p.coeff 0 ≠ 0 := by
      intro hc
      apply hf.ne_zero
      rw [hfC, hc, map_zero]
    apply hf.not_isUnit
    rw [hfC]
    exact (isUnit_iff_ne_zero.mpr hc).map C
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p hpdegree
  obtain ⟨q, hpq⟩ := Polynomial.dvd_iff_isRoot.mpr hr
  have hfactor : f = (perpendicularCoordinate a b - C r) *
      Polynomial.aeval (perpendicularCoordinate a b) q := by
    rw [hfp, hpq, map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    rfl
  have hu := (hf.isUnit_or_isUnit hfactor).resolve_left
    (perpendicularCoordinate_sub_C_not_isUnit a b r hab)
  obtain ⟨d, hd, hq⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
  refine ⟨d, r, isUnit_iff_ne_zero.mp hd, ?_⟩
  rw [hfactor, hq, mul_comm]

theorem irreducible_direction_eq_linear_factor_charZero [IsAlgClosed k] [CharZero k]
    {f : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (a b : k) (hab : a ≠ 0 ∨ b ≠ 0)
    (hD : C a * pderiv 0 f + C b * pderiv 1 f = 0) :
    ∃ d r : k, d ≠ 0 ∧ f = C d * (perpendicularCoordinate a b - C r) := by
  obtain ⟨p, hp⟩ := exists_polynomial_perpendicular_of_direction_zero_charZero f a b hab hD
  exact irreducible_aeval_perpendicular_eq_linear_factor hf a b hab p hp

theorem irreducible_direction_eq_linear_factor_charP [IsAlgClosed k]
    (p : ℕ) [CharP k p] {f : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (hp : f.totalDegree < p) (a b : k) (hab : a ≠ 0 ∨ b ≠ 0)
    (hD : C a * pderiv 0 f + C b * pderiv 1 f = 0) :
    ∃ d r : k, d ≠ 0 ∧ f = C d * (perpendicularCoordinate a b - C r) := by
  obtain ⟨q, hq⟩ := exists_polynomial_perpendicular_of_direction_zero_charP p f hp a b hab hD
  exact irreducible_aeval_perpendicular_eq_linear_factor hf a b hab q hq

private theorem affine_of_linear_factor {f : MvPolynomial (Fin 2) k} {a b : k}
    (hab : a ≠ 0 ∨ b ≠ 0)
    (h : ∃ d r : k, d ≠ 0 ∧ f = C d * (perpendicularCoordinate a b - C r)) :
    ∃ u v w : k, (u ≠ 0 ∨ v ≠ 0) ∧ f = C u * X 0 + C v * X 1 + C w := by
  obtain ⟨d, r, hd, hf⟩ := h
  refine ⟨d * b, -(d * a), -(d * r), ?_, ?_⟩
  · rcases hab with ha | hb
    · exact Or.inr (neg_ne_zero.mpr (mul_ne_zero hd ha))
    · exact Or.inl (mul_ne_zero hd hb)
  · rw [hf]
    simp only [perpendicularCoordinate, map_mul, map_neg]
    ring

/-- Constant-direction obstruction in characteristic zero: the actual
irreducible polynomial is a nonconstant affine linear polynomial. -/
theorem irreducible_direction_eq_affine_charZero [IsAlgClosed k] [CharZero k]
    {f : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (a b : k) (hab : a ≠ 0 ∨ b ≠ 0)
    (hD : C a * pderiv 0 f + C b * pderiv 1 f = 0) :
    ∃ u v w : k, (u ≠ 0 ∨ v ≠ 0) ∧ f = C u * X 0 + C v * X 1 + C w :=
  affine_of_linear_factor hab (irreducible_direction_eq_linear_factor_charZero hf a b hab hD)

/-- The same exact obstruction below the positive characteristic. -/
theorem irreducible_direction_eq_affine_charP [IsAlgClosed k]
    (p : ℕ) [CharP k p] {f : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (hp : f.totalDegree < p) (a b : k) (hab : a ≠ 0 ∨ b ≠ 0)
    (hD : C a * pderiv 0 f + C b * pderiv 1 f = 0) :
    ∃ u v w : k, (u ≠ 0 ∨ v ≠ 0) ∧ f = C u * X 0 + C v * X 1 + C w :=
  affine_of_linear_factor hab (irreducible_direction_eq_linear_factor_charP p hf hp a b hab hD)

#print axioms eval_linePolynomial
#print axioms derivative_linePolynomial
#print axioms natDegree_linePolynomial_le
#print axioms eval_translate_of_direction_zero_of_cast
#print axioms exists_polynomial_perpendicular_of_direction_zero_of_cast
#print axioms exists_polynomial_perpendicular_of_direction_zero_charZero
#print axioms exists_polynomial_perpendicular_of_direction_zero_charP
#print axioms perpendicularCoordinate_surjective
#print axioms perpendicularCoordinate_sub_C_not_isUnit
#print axioms irreducible_aeval_perpendicular_eq_linear_factor
#print axioms irreducible_direction_eq_linear_factor_charZero
#print axioms irreducible_direction_eq_linear_factor_charP
#print axioms irreducible_direction_eq_affine_charZero
#print axioms irreducible_direction_eq_affine_charP

end PrimeGap182.TypeIII.CurveDirection
