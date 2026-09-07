import IncidenceZeroMode
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Exact finite completion of a weighted incidence Gram form

The Fourier transform is joint in the two row coordinates. The zero mode is
kept separate, so its coefficient is the full row-weight mass. The matrix norm
is the Euclidean operator norm, not the entrywise maximum norm.

The final estimate has explicit hypotheses on the actual nonzero finite
matrices. It is not an asymptotic Type II estimate and assumes no such estimate.
The sharp prime zero-mode input is the previously proved and attributed
`IncidenceZeroMode` module.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix WithLp
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {q : ℕ} [NeZero q]

/-- The actual two-coordinate additive character, with positive sign. -/
def incidenceJointChar (ξ z : ZMod q × ZMod q) : ℂ :=
  ZMod.stdAddChar (ξ.1 * z.1 + ξ.2 * z.2)

/-- The unnormalized joint finite Fourier transform, with negative sign. -/
def incidenceJointDFT (f : ZMod q × ZMod q → ℂ) (ξ : ZMod q × ZMod q) : ℂ :=
  ∑ z, f z * incidenceJointChar ξ (-z)

private theorem incidence_char_sum (a : ZMod q) :
    (∑ t : ZMod q, ZMod.stdAddChar (t * a)) = if a = 0 then (q : ℂ) else 0 := by
  simpa using AddChar.sum_mulShift a (ZMod.isPrimitive_stdAddChar q)

theorem incidenceJointChar_sum (z : ZMod q × ZMod q) :
    (∑ ξ, incidenceJointChar ξ z) = if z = 0 then (q : ℂ) ^ 2 else 0 := by
  simp only [incidenceJointChar, Fintype.sum_prod_type,
    AddChar.map_add_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [incidence_char_sum, incidence_char_sum]
  by_cases h₁ : z.1 = 0 <;> by_cases h₂ : z.2 = 0 <;>
    simp [h₁, h₂, Prod.ext_iff, pow_two]

theorem incidenceJointChar_sub (ξ y z : ZMod q × ZMod q) :
    incidenceJointChar ξ (-y) * incidenceJointChar ξ z =
      incidenceJointChar ξ (z - y) := by
  rw [incidenceJointChar, incidenceJointChar, ← AddChar.map_add_eq_mul]
  congr 1
  dsimp [incidenceJointChar]
  ring

theorem incidenceJointDFT_zero (f : ZMod q × ZMod q → ℂ) :
    incidenceJointDFT f 0 = ∑ z, f z := by
  simp [incidenceJointDFT, incidenceJointChar]

theorem incidenceJointDFT_inversion (f : ZMod q × ZMod q → ℂ)
    (z : ZMod q × ZMod q) :
    ((q : ℂ) ^ 2)⁻¹ * ∑ ξ, incidenceJointDFT f ξ * incidenceJointChar ξ z = f z := by
  have hsum : (∑ ξ, incidenceJointDFT f ξ * incidenceJointChar ξ z) =
      (q : ℂ) ^ 2 * f z := by
    simp only [incidenceJointDFT, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, incidenceJointChar_sub, ← Finset.mul_sum,
      incidenceJointChar_sum, sub_eq_zero]
    simp [mul_comm]
  rw [hsum, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (NeZero.ne _)), one_mul]

/-- Joint finite Fourier completion; the weight need not factor in its coordinates. -/
theorem incidenceJointDFT_completion (f g : ZMod q × ZMod q → ℂ) :
    (∑ z, f z * g z) = ((q : ℂ) ^ 2)⁻¹ *
      ∑ ξ, incidenceJointDFT f ξ * ∑ z, incidenceJointChar ξ z * g z := by
  calc
    _ = ∑ z, (((q : ℂ) ^ 2)⁻¹ *
        ∑ ξ, incidenceJointDFT f ξ * incidenceJointChar ξ z) * g z := by
      simp only [incidenceJointDFT_inversion]
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]

variable {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ]

/-- The actual matrix `Rᴴ diag(w) R`, permitting complex Fourier weights. -/
def incidenceWeightedGram (R : Matrix ρ ι ℂ) (w : ρ → ℂ) : Matrix ι ι ℂ :=
  Rᴴ * (diagonal w * R)

/-- The actual unnormalized Gram mode `Rᴴ diag(ψ_ξ) R`. -/
def incidenceMode (R : Matrix (ZMod q × ZMod q) ι ℂ)
    (ξ : ZMod q × ZMod q) : Matrix ι ι ℂ :=
  incidenceWeightedGram R (incidenceJointChar ξ)

/-- The squared Euclidean norm written without a norm-instance ambiguity. -/
def incidenceVectorEnergy (c : ι → ℂ) : ℝ := ∑ b, ‖c b‖ ^ 2

/-- The weighted squared norm of the actual response `R *ᵥ c`. -/
def incidenceRowEnergy (R : Matrix ρ ι ℂ) (W : ρ → ℝ) (c : ι → ℂ) : ℝ :=
  ∑ z, W z * ‖(R *ᵥ c) z‖ ^ 2

omit [DecidableEq ι] in
theorem incidenceWeightedGram_quadratic (R : Matrix ρ ι ℂ)
    (w : ρ → ℂ) (c : ι → ℂ) :
    star c ⬝ᵥ (incidenceWeightedGram R w *ᵥ c) =
      ∑ z, w z * (‖(R *ᵥ c) z‖ ^ 2 : ℝ) := by
  rw [incidenceWeightedGram, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_conjTranspose, star_star, ← mulVec_mulVec]
  simp only [dotProduct, Pi.star_apply, mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro z _
  rw [← mul_assoc, mul_comm (star _), mul_assoc]
  simp only [← starRingEnd_apply, RCLike.conj_mul, Complex.ofReal_pow]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem incidenceWeightedGram_apply (R : Matrix ρ ι ℂ)
    (w : ρ → ℂ) (b b' : ι) :
    incidenceWeightedGram R w b b' = ∑ z, w z * star (R z b) * R z b' := by
  rw [incidenceWeightedGram, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Matrix.diagonal_mul]
  apply Finset.sum_congr rfl
  intro z _
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem incidenceMode_zero (R : Matrix (ZMod q × ZMod q) ι ℂ) :
    incidenceMode R 0 = Rᴴ * R := by
  have hchar : incidenceJointChar (0 : ZMod q × ZMod q) = fun _ => (1 : ℂ) := by
    funext z
    simp [incidenceJointChar]
  simp [incidenceMode, incidenceWeightedGram, hchar, diagonal_one]

omit [Fintype ι] [DecidableEq ι] in
theorem incidenceWeightedGram_completion (R : Matrix (ZMod q × ZMod q) ι ℂ)
    (w : ZMod q × ZMod q → ℂ) :
    incidenceWeightedGram R w =
      ((q : ℂ) ^ 2)⁻¹ • ∑ ξ, incidenceJointDFT w ξ • incidenceMode R ξ := by
  ext b b'
  simp only [incidenceMode, incidenceWeightedGram_apply, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul]
  simpa only [mul_assoc] using
    incidenceJointDFT_completion w (fun z => star (R z b) * R z b')

theorem incidence_quadratic_norm_le (D : Matrix ι ι ℂ) (c : ι → ℂ) :
    ‖star c ⬝ᵥ (D *ᵥ c)‖ ≤ ‖D‖ * incidenceVectorEnergy c := by
  let x : EuclideanSpace ℂ ι := toLp 2 c
  have hi : inner ℂ x (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) D x) =
      star c ⬝ᵥ (D *ᵥ c) := by
    simp [x, PiLp.inner_apply, RCLike.inner_apply, dotProduct, mul_comm]
  rw [← hi]
  calc
    _ ≤ ‖x‖ * ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) D x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖D‖ * ‖x‖) := by
      exact mul_le_mul_of_nonneg_left
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) D |>.le_opNorm x) (norm_nonneg _)
    _ = ‖D‖ * incidenceVectorEnergy c := by
      rw [mul_left_comm, ← pow_two, PiLp.norm_sq_eq_of_L2]
      rfl

omit [DecidableEq ι] in
theorem incidenceVectorEnergy_nonneg (c : ι → ℂ) : 0 ≤ incidenceVectorEnergy c :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq ι] in
theorem incidenceVectorEnergy_cast (c : ι → ℂ) :
    star c ⬝ᵥ c = (incidenceVectorEnergy c : ℂ) := by
  simp [dotProduct, incidenceVectorEnergy, ← starRingEnd_apply, RCLike.conj_mul]

omit [DecidableEq ι] in
theorem incidenceRowEnergy_completion (R : Matrix (ZMod q × ZMod q) ι ℂ)
    (W : ZMod q × ZMod q → ℝ) (c : ι → ℂ) :
    (incidenceRowEnergy R W c : ℂ) = ((q : ℂ) ^ 2)⁻¹ *
      ∑ ξ, incidenceJointDFT (fun z => (W z : ℂ)) ξ *
        (star c ⬝ᵥ (incidenceMode R ξ *ᵥ c)) := by
  simpa only [incidenceRowEnergy, Complex.ofReal_sum, Complex.ofReal_mul,
    incidenceMode, incidenceWeightedGram_quadratic] using
    incidenceJointDFT_completion (fun z => (W z : ℂ))
      (fun z => (‖(R *ᵥ c) z‖ ^ 2 : ℝ))

omit [DecidableEq ι] in
theorem incidenceMode_zero_quadratic (R : Matrix (ZMod q × ZMod q) ι ℂ)
    (c : ι → ℂ) :
    star c ⬝ᵥ (incidenceMode R 0 *ᵥ c) = (incidenceVectorEnergy (R *ᵥ c) : ℂ) := by
  rw [incidenceMode_zero, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_conjTranspose, star_star, incidenceVectorEnergy_cast]

omit [DecidableEq ι] in
/-- Exact separation of the full zero-frequency mass from the other modes. -/
theorem incidenceRowEnergy_completion_re (R : Matrix (ZMod q × ZMod q) ι ℂ)
    (W : ZMod q × ZMod q → ℝ) (c : ι → ℂ) :
    incidenceRowEnergy R W c = ((q : ℝ) ^ 2)⁻¹ *
      ((∑ z, W z) * incidenceVectorEnergy (R *ᵥ c) +
        ∑ ξ ∈ Finset.univ.erase 0,
          (incidenceJointDFT (fun z => (W z : ℂ)) ξ *
            (star c ⬝ᵥ (incidenceMode R ξ *ᵥ c))).re) := by
  have h := incidenceRowEnergy_completion R W c
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ 0),
    incidenceJointDFT_zero, incidenceMode_zero_quadratic] at h
  have hq : ((q : ℂ) ^ 2)⁻¹ = (((q : ℝ) ^ 2)⁻¹ : ℝ) := by
    simp only [Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_natCast]
  rw [hq, ← Complex.ofReal_sum] at h
  have hre := congrArg Complex.re h
  simpa only [Complex.ofReal_re, Complex.re_ofReal_mul, Complex.add_re,
    Complex.re_sum, add_comm] using hre

/-- Completion with the exact zero-mode energy and only explicit local operator bounds. -/
theorem incidenceRowEnergy_le_modes (R : Matrix (ZMod q × ZMod q) ι ℂ)
    (W : ZMod q × ZMod q → ℝ) (c : ι → ℂ)
    (B : ZMod q × ZMod q → ℝ)
    (hB : ∀ ξ, ξ ≠ 0 → ‖incidenceMode R ξ‖ ≤ B ξ) :
    incidenceRowEnergy R W c ≤ ((q : ℝ) ^ 2)⁻¹ *
      ((∑ z, W z) * incidenceVectorEnergy (R *ᵥ c) +
        (∑ ξ ∈ Finset.univ.erase 0,
          ‖incidenceJointDFT (fun z => (W z : ℂ)) ξ‖ * B ξ) * incidenceVectorEnergy c) := by
  rw [incidenceRowEnergy_completion_re]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sq_nonneg _))
  apply add_le_add le_rfl
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ξ hξ
  have hQ : ‖star c ⬝ᵥ (incidenceMode R ξ *ᵥ c)‖ ≤ B ξ * incidenceVectorEnergy c :=
    (incidence_quadratic_norm_le _ c).trans
      (mul_le_mul_of_nonneg_right (hB ξ (Finset.mem_erase.mp hξ).1)
        (incidenceVectorEnergy_nonneg c))
  exact (Complex.re_le_norm _).trans (by
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hQ (norm_nonneg _))

omit [DecidableEq ρ] in
/-- A Loewner Gram bound controls the actual unweighted response energy. -/
theorem incidenceVectorEnergy_image_le (R : Matrix ρ ι ℂ) (C : ℝ)
    (hR : ((C : ℂ) • (1 : Matrix ι ι ℂ) - Rᴴ * R).PosSemidef)
    (c : ι → ℂ) :
    incidenceVectorEnergy (R *ᵥ c) ≤ C * incidenceVectorEnergy c := by
  have h := hR.dotProduct_mulVec_nonneg c
  have hgram : star c ⬝ᵥ ((Rᴴ * R) *ᵥ c) =
      (incidenceVectorEnergy (R *ᵥ c) : ℂ) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose,
      star_star, incidenceVectorEnergy_cast]
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, hgram,
    incidenceVectorEnergy_cast] at h
  have hre := (Complex.nonneg_iff.mp h).1
  simpa only [Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re,
    sub_nonneg] using hre

variable {p : ℕ} [Fact p.Prime]

/-- The actual prime-field mode, with the same reciprocal/pole convention as the manuscript. -/
def primeIncidenceMode (A : ZMod p) (ξ : ZMod p × ZMod p) :
    Matrix (ZMod p) (ZMod p) ℂ :=
  incidenceMode (primeIncidenceMatrix A) ξ

theorem primeIncidenceMode_zero (A : ZMod p) :
    primeIncidenceMode A 0 = primeIncidenceZeroMode A :=
  incidenceMode_zero _

theorem primeIncidenceVectorEnergy_le (A : ZMod p) (hA : A ≠ 0)
    (c : ZMod p → ℂ) :
    incidenceVectorEnergy (primeIncidenceMatrix A *ᵥ c) ≤
      (p : ℝ) ^ 2 * incidenceVectorEnergy c := by
  apply incidenceVectorEnergy_image_le
  simpa only [Complex.ofReal_pow, Complex.ofReal_natCast, primeIncidenceZeroMode] using
    primeIncidenceZeroMode_le A hA

/-- Sharp mean plus completed nonzero modes. The only cancellation hypotheses
are bounds on the actual nonzero finite matrices, in the Euclidean operator norm. -/
theorem primeIncidenceRowEnergy_le (A : ZMod p) (hA : A ≠ 0)
    (W : ZMod p × ZMod p → ℝ) (hW : ∀ z, 0 ≤ W z)
    (c : ZMod p → ℂ) (B : ZMod p × ZMod p → ℝ)
    (hB : ∀ ξ, ξ ≠ 0 → ‖primeIncidenceMode A ξ‖ ≤ B ξ) :
    incidenceRowEnergy (primeIncidenceMatrix A) W c ≤
      ((∑ z, W z) + ((p : ℝ) ^ 2)⁻¹ *
        ∑ ξ ∈ Finset.univ.erase 0,
          ‖incidenceJointDFT (fun z => (W z : ℂ)) ξ‖ * B ξ) *
        incidenceVectorEnergy c := by
  have hmean := primeIncidenceVectorEnergy_le A hA c
  have hmass : 0 ≤ ∑ z, W z := Finset.sum_nonneg fun z _ => hW z
  calc
    _ ≤ ((p : ℝ) ^ 2)⁻¹ *
        ((∑ z, W z) * incidenceVectorEnergy (primeIncidenceMatrix A *ᵥ c) +
          (∑ ξ ∈ Finset.univ.erase 0,
            ‖incidenceJointDFT (fun z => (W z : ℂ)) ξ‖ * B ξ) * incidenceVectorEnergy c) :=
      incidenceRowEnergy_le_modes _ W c B hB
    _ ≤ ((p : ℝ) ^ 2)⁻¹ *
        ((∑ z, W z) * ((p : ℝ) ^ 2 * incidenceVectorEnergy c) +
          (∑ ξ ∈ Finset.univ.erase 0,
            ‖incidenceJointDFT (fun z => (W z : ℂ)) ξ‖ * B ξ) * incidenceVectorEnergy c) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hmean hmass) le_rfl)
        (inv_nonneg.mpr (sq_nonneg _))
    _ = _ := by
      have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      field_simp

#print axioms incidenceJointDFT_inversion
#print axioms incidenceJointDFT_completion
#print axioms incidenceWeightedGram_completion
#print axioms incidence_quadratic_norm_le
#print axioms incidenceRowEnergy_completion_re
#print axioms incidenceRowEnergy_le_modes
#print axioms incidenceVectorEnergy_image_le
#print axioms primeIncidenceRowEnergy_le

end PrimeGap182Audit
