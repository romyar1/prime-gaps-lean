import IncidenceWindow
import IncidenceModalBounds

/-!
# The exact affine progression change in the Type II incidence rows

The first row coordinate is replaced by `u*e+t`, with `u` an actual unit
modulo the oscillatory modulus. Every mode is identified, including zero;
the frequency gcd and the operator norm are preserved.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {q : ℕ} [NeZero q]

def incidenceRowAffineEquiv (u : (ZMod q)ˣ) (t : ZMod q) :
    (ZMod q × ZMod q) ≃ (ZMod q × ZMod q) where
  toFun z := ((u : ZMod q) * z.1 + t, z.2)
  invFun z := (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * (z.1 - t), z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp

def incidenceAffineFrequency (u : (ZMod q)ˣ) (ξ : ZMod q × ZMod q) : ZMod q × ZMod q :=
  (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * ξ.1, ξ.2)

omit [NeZero q] in
theorem incidenceAffineFrequency_gcd (u : (ZMod q)ˣ) (ξ : ZMod q × ZMod q) :
    incidenceFrequencyGCD (incidenceAffineFrequency u ξ) = incidenceFrequencyGCD ξ := by
  have hunit (v : (ZMod q)ˣ) (h : ZMod q) :
      Nat.gcd q ((v : ZMod q) * h).val = Nat.gcd q h.val := by
    rw [ZMod.val_mul, Nat.gcd_comm q _, ← Nat.gcd_rec]
    exact (ZMod.val_coe_unit_coprime v).gcd_mul_left_cancel_right h.val
  simp only [incidenceFrequencyGCD, incidenceAffineFrequency]
  rw [← Nat.gcd_gcd_gcd_left, hunit, Nat.gcd_gcd_gcd_left]

omit [NeZero q] in
theorem incidenceAffineFrequency_zero (u : (ZMod q)ˣ) :
    incidenceAffineFrequency u (0 : ZMod q × ZMod q) = 0 := by
  ext <;> simp [incidenceAffineFrequency]

theorem incidenceAffine_char (u : (ZMod q)ˣ) (t : ZMod q)
    (ξ z : ZMod q × ZMod q) :
    incidenceJointChar ξ ((incidenceRowAffineEquiv u t).symm z) =
      ZMod.stdAddChar (-(incidenceAffineFrequency u ξ).1 * t) *
        incidenceJointChar (incidenceAffineFrequency u ξ) z := by
  simp only [incidenceJointChar, incidenceRowAffineEquiv, Equiv.coe_fn_symm_mk,
    incidenceAffineFrequency]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def incidenceAffineRows (R : Matrix (ZMod q × ZMod q) ι ℂ)
    (u : (ZMod q)ˣ) (t : ZMod q) : Matrix (ZMod q × ZMod q) ι ℂ :=
  R.submatrix (incidenceRowAffineEquiv u t) id

omit [Fintype ι] [DecidableEq ι] in
/-- Complete mode identity for the actual affine progression, with its unit phase. -/
theorem incidenceAffineRows_mode (R : Matrix (ZMod q × ZMod q) ι ℂ)
    (u : (ZMod q)ˣ) (t : ZMod q) (ξ : ZMod q × ZMod q) :
    incidenceMode (incidenceAffineRows R u t) ξ =
      ZMod.stdAddChar (-(incidenceAffineFrequency u ξ).1 * t) •
        incidenceMode R (incidenceAffineFrequency u ξ) := by
  ext b b'
  simp only [incidenceMode, incidenceWeightedGram_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    _ = ∑ z : ZMod q × ZMod q,
        incidenceJointChar ξ ((incidenceRowAffineEquiv u t).symm z) * star (R z b) * R z b' := by
      refine Fintype.sum_equiv (incidenceRowAffineEquiv u t) _ _ ?_
      intro z
      simp only [Equiv.symm_apply_apply, incidenceAffineRows, Matrix.submatrix_apply, id_eq]
    _ = _ := by
      simp only [incidenceAffine_char, Finset.mul_sum, mul_assoc]

theorem incidenceAffineRows_mode_norm (R : Matrix (ZMod q × ZMod q) ι ℂ)
    (u : (ZMod q)ˣ) (t : ZMod q) (ξ : ZMod q × ZMod q) :
    ‖incidenceMode (incidenceAffineRows R u t) ξ‖ =
      ‖incidenceMode R (incidenceAffineFrequency u ξ)‖ := by
  rw [incidenceAffineRows_mode, norm_smul]
  simp only [ZMod.stdAddChar_apply, Circle.norm_coe, one_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem incidenceAffineRows_mode_zero (R : Matrix (ZMod q × ZMod q) ι ℂ)
    (u : (ZMod q)ˣ) (t : ZMod q) :
    incidenceMode (incidenceAffineRows R u t) 0 = incidenceMode R 0 := by
  rw [incidenceAffineRows_mode, incidenceAffineFrequency_zero]
  simp

/-- All squarefree local bounds survive the actual progression change. -/
theorem incidenceAffineRows_squarefree_norm_le (hK4 : AllIncidenceRankFourBounds)
    (hq : Squarefree q) (A : ZMod q) (hA : IsUnit A)
    (u : (ZMod q)ˣ) (t : ZMod q) (ξ : ZMod q × ZMod q) :
    ‖incidenceMode (incidenceAffineRows (incidenceMatrixMod A) u t) ξ‖ ≤
      (8 : ℝ) ^ q.primeFactors.card * (q : ℝ) * Real.sqrt (q : ℝ) *
        Real.sqrt (incidenceFrequencyGCD ξ : ℝ) := by
  rw [incidenceAffineRows_mode_norm]
  have hb := incidenceModeMod_squarefree_norm_le_residue hK4 hq A hA
    (incidenceAffineFrequency u ξ)
  simpa only [incidenceAffineFrequency_gcd, incidenceModeMod] using hb

theorem IncidenceModalBounds.affine {R : Matrix (ZMod q × ZMod q) ι ℂ}
    (hR : IncidenceModalBounds R) (u : (ZMod q)ˣ) (t : ZMod q) :
    IncidenceModalBounds (incidenceAffineRows R u t) := by
  constructor
  · have hz := congrArg norm (incidenceAffineRows_mode_zero R u t)
    rw [incidenceMode_zero, incidenceMode_zero] at hz
    exact hz.trans_le hR.zero_norm_le
  · intro ξ
    rw [incidenceAffineRows_mode_norm]
    simpa only [incidenceAffineFrequency_gcd] using hR.mode_norm_le (incidenceAffineFrequency u ξ)

#print axioms incidenceRowAffineEquiv
#print axioms incidenceAffineFrequency_gcd
#print axioms incidenceAffineRows_mode
#print axioms incidenceAffineRows_mode_norm
#print axioms incidenceAffineRows_mode_zero
#print axioms incidenceAffineRows_squarefree_norm_le
#print axioms IncidenceModalBounds.affine

end PrimeGap182Audit
