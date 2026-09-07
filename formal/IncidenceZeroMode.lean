import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The actual prime-field zero mode of the incidence matrix

This file concerns the incidence matrix in Lemma 2.1 of the frozen
`incidence_and_many_primes.tex`. The reciprocal kernel is zero at its pole.
The zero mode is defined as its actual Gram matrix. No cancellation estimate,
Deligne bound, prime-distribution assertion, or desired Gram identity is assumed.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators ComplexOrder

variable {p : ℕ} [Fact p.Prime]

/-- The actual exponential `exp(2π i x/p)`. -/
abbrev incidenceCharacter (x : ZMod p) : ℂ := ZMod.stdAddChar x

/-- The reciprocal exponential with its pole removed. -/
def incidenceReciprocal (A x : ZMod p) : ℂ :=
  if x = 0 then 0 else incidenceCharacter (A / x)

/-- Actual incidence rows indexed by all pairs `(e,γ)`, including the zero rows. -/
def primeIncidenceMatrix (A : ZMod p) :
    Matrix (ZMod p × ZMod p) (ZMod p) ℂ :=
  fun z b => incidenceReciprocal A (z.1 * (z.2 + z.1 * b))

/-- The complete zero frequency, with no normalization. -/
def primeIncidenceZeroMode (A : ZMod p) : Matrix (ZMod p) (ZMod p) ℂ :=
  (primeIncidenceMatrix A)ᴴ * primeIncidenceMatrix A

/-- The reciprocal-square matrix appearing in the exact zero-mode identity. -/
def reciprocalSquareMatrix (A : ZMod p) : Matrix (ZMod p) (ZMod p) ℂ :=
  fun b b' => ∑ u : ZMod p,
    if u = 0 then 0 else incidenceCharacter (-A * (b' - b) / u ^ 2)

private theorem sum_omit_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) (a : ι) :
    (∑ x, if x = a then 0 else f x) = (∑ x, f x) - f a := by
  calc
    _ = ∑ x, (f x - if x = a then f a else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : x = a <;> simp [h]
    _ = _ := by simp [Finset.sum_sub_distrib]

private theorem incidenceCharacter_star (x : ZMod p) :
    star (incidenceCharacter x) = incidenceCharacter (-x) := by
  have hp : 0 < ringChar (ZMod p) := by
    simpa only [ringChar.eq (ZMod p) p] using (Fact.out : p.Prime).pos
  exact AddChar.starComp_apply hp x

private theorem incidenceCharacter_sum_mul (c : ZMod p) (hc : c ≠ 0) :
    (∑ x : ZMod p, incidenceCharacter (x * c)) = 0 := by
  simpa [hc] using AddChar.sum_mulShift c (ZMod.isPrimitive_stdAddChar p)

private theorem incidenceCharacter_sum_div (c : ZMod p) (hc : c ≠ 0) :
    (∑ x : ZMod p, incidenceCharacter (c / x)) = 0 := by
  let e : ZMod p ≃ ZMod p :=
    { toFun := Inv.inv
      invFun := Inv.inv
      left_inv := inv_inv
      right_inv := inv_inv }
  calc
    _ = ∑ x : ZMod p, incidenceCharacter (x * c) := by
      simpa [e, div_eq_mul_inv, mul_comm] using
        e.sum_comp (fun x => incidenceCharacter (x * c))
    _ = 0 := incidenceCharacter_sum_mul c hc

private theorem incidenceCharacter_sum_div_nonzero (c : ZMod p) (hc : c ≠ 0) :
    (∑ x : ZMod p, if x = 0 then 0 else incidenceCharacter (c / x)) = -1 := by
  rw [sum_omit_one, incidenceCharacter_sum_div c hc]
  simp

private theorem incidenceCharacter_sum_one_nonzero :
    (∑ x : ZMod p, if x = 0 then (0 : ℂ) else 1) = (p : ℂ) - 1 := by
  rw [sum_omit_one]
  simp

private theorem reciprocalSquareMatrix_diagonal (A b : ZMod p) :
    reciprocalSquareMatrix A b b = (p : ℂ) - 1 := by
  simpa [reciprocalSquareMatrix] using incidenceCharacter_sum_one_nonzero (p := p)

/-- The exact invertible change of variables used for two distinct columns. -/
def incidencePairEquiv (b b' : ZMod p) (hbb : b ≠ b') :
    (ZMod p × ZMod p) ≃ (ZMod p × ZMod p) where
  toFun z := (z.2 + z.1 * b, z.2 + z.1 * b')
  invFun z := ((z.2 - z.1) / (b' - b), (b' * z.1 - b * z.2) / (b' - b))
  left_inv := by
    rintro ⟨e, g⟩
    have hd : b' - b ≠ 0 := sub_ne_zero.mpr hbb.symm
    apply Prod.ext <;> dsimp <;> field_simp <;> ring
  right_inv := by
    rintro ⟨u, v⟩
    have hd : b' - b ≠ 0 := sub_ne_zero.mpr hbb.symm
    apply Prod.ext <;> dsimp <;> field_simp <;> ring

private def offDiagonalKernel (c : ZMod p) (z : ZMod p × ZMod p) : ℂ :=
  if z.1 = 0 ∨ z.2 = 0 ∨ z.1 = z.2 then 0
  else incidenceCharacter (c / (z.1 * z.2))

private theorem incidence_offDiagonal_summand (A b b' : ZMod p) (hbb : b ≠ b')
    (z : ZMod p × ZMod p) :
    star (primeIncidenceMatrix A z b) * primeIncidenceMatrix A z b' =
      offDiagonalKernel (-A * (b' - b)) (incidencePairEquiv b b' hbb z) := by
  rcases z with ⟨e, g⟩
  have hd : b' - b ≠ 0 := sub_ne_zero.mpr hbb.symm
  by_cases he : e = 0
  · simp [primeIncidenceMatrix, incidenceReciprocal, incidencePairEquiv,
      offDiagonalKernel, he]
  by_cases hu : g + e * b = 0
  · simp [primeIncidenceMatrix, incidenceReciprocal, incidencePairEquiv,
      offDiagonalKernel, hu]
  by_cases hv : g + e * b' = 0
  · simp [primeIncidenceMatrix, incidenceReciprocal, incidencePairEquiv,
      offDiagonalKernel, hv]
  have huv : g + e * b ≠ g + e * b' := by
    intro h
    apply hbb
    exact (mul_left_cancel₀ he) (add_left_cancel h)
  simp only [primeIncidenceMatrix, incidenceReciprocal,
    ite_eq_right (mul_ne_zero he hu), ite_eq_right (mul_ne_zero he hv),
    incidencePairEquiv, Equiv.coe_fn_mk, offDiagonalKernel, hu, hv, huv,
    false_or, ↓reduceIte, incidenceCharacter_star]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  field_simp
  ring

private theorem offDiagonalKernel_sum_row (c u : ZMod p) (hc : c ≠ 0) :
    (∑ v : ZMod p, offDiagonalKernel c (u, v)) =
      if u = 0 then 0 else (-1 - incidenceCharacter (c / u ^ 2)) := by
  by_cases hu : u = 0
  · simp [offDiagonalKernel, hu]
  have hrow : (∑ v : ZMod p, offDiagonalKernel c (u, v)) =
      (∑ v : ZMod p, if v = 0 then 0 else incidenceCharacter (c / (u * v))) -
        incidenceCharacter (c / u ^ 2) := by
    calc
      _ = ∑ v : ZMod p, if v = u then 0 else
          (if v = 0 then 0 else incidenceCharacter (c / (u * v))) := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : v = 0 <;> by_cases huv : v = u <;>
          simp_all [offDiagonalKernel, eq_comm]
      _ = _ := by rw [sum_omit_one]; simp only [ite_eq_right hu, pow_two]
  rw [hrow, ite_eq_right hu]
  have hsum : (∑ v : ZMod p, if v = 0 then 0
      else incidenceCharacter (c / (u * v))) = -1 := by
    have hcu : c / u ≠ 0 := div_ne_zero hc hu
    simpa [div_div] using incidenceCharacter_sum_div_nonzero (c / u) hcu
  rw [hsum]

private theorem offDiagonalKernel_sum (c : ZMod p) (hc : c ≠ 0) :
    (∑ z : ZMod p × ZMod p, offDiagonalKernel c z) =
      -((p : ℂ) - 1) -
        ∑ u : ZMod p, if u = 0 then 0 else incidenceCharacter (c / u ^ 2) := by
  rw [Fintype.sum_prod_type]
  simp_rw [offDiagonalKernel_sum_row c _ hc]
  calc
    _ = ∑ u : ZMod p, (-(if u = 0 then (0 : ℂ) else 1) -
        (if u = 0 then 0 else incidenceCharacter (c / u ^ 2))) := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : u = 0 <;> simp [hu]
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        incidenceCharacter_sum_one_nonzero]

theorem primeIncidenceZeroMode_offDiagonal (A b b' : ZMod p)
    (hA : A ≠ 0) (hbb : b ≠ b') :
    primeIncidenceZeroMode A b b' = -((p : ℂ) - 1) - reciprocalSquareMatrix A b b' := by
  have hc : -A * (b' - b) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hA) (sub_ne_zero.mpr hbb.symm)
  change (∑ z, star (primeIncidenceMatrix A z b) * primeIncidenceMatrix A z b') = _
  calc
    _ = ∑ z, offDiagonalKernel (-A * (b' - b)) z :=
      Fintype.sum_equiv (incidencePairEquiv b b' hbb) _ _
        (incidence_offDiagonal_summand A b b' hbb)
    _ = _ := offDiagonalKernel_sum _ hc

private theorem incidenceReciprocal_star_mul_self (A x : ZMod p) :
    star (incidenceReciprocal A x) * incidenceReciprocal A x =
      if x = 0 then 0 else 1 := by
  by_cases hx : x = 0
  · simp [incidenceReciprocal, hx]
  simp only [incidenceReciprocal, ite_eq_right hx, incidenceCharacter_star]
  rw [← AddChar.map_add_eq_mul]
  simp

theorem primeIncidenceZeroMode_diagonal (A b : ZMod p) :
    primeIncidenceZeroMode A b b = ((p : ℂ) - 1) ^ 2 := by
  change (∑ z, star (primeIncidenceMatrix A z b) * primeIncidenceMatrix A z b) = _
  rw [Fintype.sum_prod_type]
  simp only [primeIncidenceMatrix, incidenceReciprocal_star_mul_self]
  have hinner (e : ZMod p) :
      (∑ g : ZMod p, if e * (g + e * b) = 0 then (0 : ℂ) else 1) =
        if e = 0 then 0 else ((p : ℂ) - 1) := by
    by_cases he : e = 0
    · simp [he]
    simp only [mul_eq_zero, he, false_or]
    calc
      _ = ∑ g : ZMod p, if g = 0 then (0 : ℂ) else 1 :=
        Equiv.sum_comp (Equiv.addRight (e * b))
          (fun g => if g = 0 then (0 : ℂ) else 1)
      _ = _ := incidenceCharacter_sum_one_nonzero
  simp_rw [hinner]
  rw [sum_omit_one]
  simp
  ring

/-- The exact matrix identity at manuscript lines 146--151, also valid at `p=2`. -/
theorem primeIncidenceZeroMode_identity (A : ZMod p) (hA : A ≠ 0) :
    primeIncidenceZeroMode A =
      ((p : ℂ) ^ 2 - 1) • (1 : Matrix (ZMod p) (ZMod p) ℂ) -
        ((p : ℂ) - 1) • (Matrix.of fun _ _ => 1) - reciprocalSquareMatrix A := by
  ext b b'
  by_cases hbb : b = b'
  · subst b'
    simp only [primeIncidenceZeroMode_diagonal, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Matrix.of_apply, reciprocalSquareMatrix_diagonal]
    ring
  · simp only [primeIncidenceZeroMode_offDiagonal A b b' hA hbb,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hbb,
      smul_eq_mul, mul_zero, Matrix.of_apply, mul_one, zero_sub]

/-- Actual reciprocal-square feature rows whose Gram matrix is `S₀`. -/
def reciprocalSquareFeatures (A : ZMod p) : Matrix (ZMod p) (ZMod p) ℂ :=
  fun u b => if u = 0 then 0 else incidenceCharacter (-A * b / u ^ 2)

theorem reciprocalSquareMatrix_eq_gram (A : ZMod p) :
    reciprocalSquareMatrix A =
      (reciprocalSquareFeatures A)ᴴ * reciprocalSquareFeatures A := by
  ext b b'
  simp only [reciprocalSquareMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u = 0
  · simp [reciprocalSquareFeatures, hu]
  simp only [reciprocalSquareFeatures, ite_eq_right hu, incidenceCharacter_star]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

theorem reciprocalSquareMatrix_posSemidef (A : ZMod p) :
    (reciprocalSquareMatrix A).PosSemidef := by
  rw [reciprocalSquareMatrix_eq_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem primeIncidenceZeroMode_posSemidef (A : ZMod p) :
    (primeIncidenceZeroMode A).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

/-- The sharp, constant-one prime-field mean bound, expressed in Loewner order. -/
theorem primeIncidenceZeroMode_le (A : ZMod p) (hA : A ≠ 0) :
    (((p : ℂ) ^ 2) • (1 : Matrix (ZMod p) (ZMod p) ℂ) -
      primeIncidenceZeroMode A).PosSemidef := by
  have hJ : (Matrix.of fun _ _ : ZMod p => (1 : ℂ)).PosSemidef := by
    simpa [Matrix.vecMulVec] using
      Matrix.posSemidef_vecMulVec_star_self (fun _ : ZMod p => (1 : ℂ))
  have hp : (0 : ℂ) ≤ (p : ℂ) - 1 := by
    rw [Complex.nonneg_iff]
    constructor
    · simp only [Complex.sub_re, Complex.natCast_re, Complex.one_re]
      exact sub_nonneg.mpr (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
    · simp
  have hsum := (Matrix.PosSemidef.one (n := ZMod p) (R := ℂ)).add
    ((hJ.smul hp).add (reciprocalSquareMatrix_posSemidef A))
  convert hsum using 1
  rw [primeIncidenceZeroMode_identity A hA]
  ext b b'
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

#print axioms primeIncidenceZeroMode_offDiagonal
#print axioms primeIncidenceZeroMode_diagonal
#print axioms primeIncidenceZeroMode_identity
#print axioms reciprocalSquareMatrix_eq_gram
#print axioms reciprocalSquareMatrix_posSemidef
#print axioms primeIncidenceZeroMode_posSemidef
#print axioms primeIncidenceZeroMode_le

end PrimeGap182Audit
