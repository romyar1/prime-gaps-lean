import IncidenceSourceCRT

/-!
# Finite Schur bounds for the actual residue-collapsing coefficient map

Every collision count below is a cardinality of actual input pairs. The
weights may depend jointly on the coefficient and numerator indices.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators

variable {ι ρ κ : Type*} [Fintype ι] [Fintype ρ]

theorem incidenceSymmetricSchur (N : Matrix ι ι ℝ) (C : ℝ)
    (hN : ∀ i j, 0 ≤ N i j) (hsym : ∀ i j, N i j = N j i)
    (hrow : ∀ i, ∑ j, N i j ≤ C) (c : ι → ℂ) :
    (∑ i, ∑ j, N i j * ‖c i‖ * ‖c j‖) ≤ C * incidenceVectorEnergy c := by
  classical
  have hcol (j : ι) : ∑ i, N i j ≤ C := by
    simpa only [hsym] using hrow j
  have hleft : (∑ i, ∑ j, N i j * ‖c i‖ ^ 2) ≤ C * incidenceVectorEnergy c := by
    simp only [← Finset.sum_mul]
    calc
      _ ≤ ∑ i, C * ‖c i‖ ^ 2 :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _))
      _ = _ := by rw [← Finset.mul_sum]; rfl
  have hright : (∑ i, ∑ j, N i j * ‖c j‖ ^ 2) ≤ C * incidenceVectorEnergy c := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    calc
      _ ≤ ∑ j, C * ‖c j‖ ^ 2 :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _))
      _ = _ := by rw [← Finset.mul_sum]; rfl
  have htwo : 2 * (∑ i, ∑ j, N i j * ‖c i‖ * ‖c j‖) ≤
      (∑ i, ∑ j, N i j * ‖c i‖ ^ 2) +
        (∑ i, ∑ j, N i j * ‖c j‖ ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    nlinarith [mul_nonneg (hN i j) (sq_nonneg (‖c i‖ - ‖c j‖))]
  linarith

/-- The actual squared response norm is controlled by a nonnegative
symmetric majorant of its actual Gram entries. -/
theorem incidenceEnergy_le_symmetricSchur (R : Matrix ρ ι ℂ)
    (N : Matrix ι ι ℝ) (C : ℝ)
    (hN : ∀ i j, 0 ≤ N i j) (hsym : ∀ i j, N i j = N j i)
    (hrow : ∀ i, ∑ j, N i j ≤ C)
    (hgram : ∀ i j, ‖(Rᴴ * R) i j‖ ≤ N i j) (c : ι → ℂ) :
    incidenceVectorEnergy (R *ᵥ c) ≤ C * incidenceVectorEnergy c := by
  classical
  have hidentity : star c ⬝ᵥ ((Rᴴ * R) *ᵥ c) =
      (incidenceVectorEnergy (R *ᵥ c) : ℂ) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose,
      star_star, incidenceVectorEnergy_cast]
  have hpos : 0 ≤ incidenceVectorEnergy (R *ᵥ c) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc
    incidenceVectorEnergy (R *ᵥ c) = ‖star c ⬝ᵥ ((Rᴴ * R) *ᵥ c)‖ := by
      rw [hidentity, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
    _ = ‖∑ i, ∑ j, star (c i) * ((Rᴴ * R) i j * c j)‖ := by
      simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, ‖star (c i) * ((Rᴴ * R) i j * c j)‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ i, ∑ j, N i j * ‖c i‖ * ‖c j‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul, norm_star]
      calc
        _ ≤ ‖c i‖ * (N i j * ‖c j‖) := by
          gcongr
          exact hgram i j
        _ = _ := by ring
    _ ≤ C * incidenceVectorEnergy c := incidenceSymmetricSchur N C hN hsym hrow c

/-- The actual map which collapses numerator indices into residue classes. -/
def incidenceFiberMatrix [DecidableEq ρ] (I : ι → Finset κ)
    (r : ι → κ → ρ) (β : ι → κ → ℂ) : Matrix ρ ι ℂ :=
  fun b a => ∑ k ∈ I a, if r a k = b then β a k else 0

def incidenceFiberCollisions [DecidableEq κ] [DecidableEq ρ]
    (I : ι → Finset κ) (r : ι → κ → ρ) (a b : ι) : ℕ :=
  (((I a) ×ˢ (I b)).filter (fun z => r a z.1 = r b z.2)).card

omit [Fintype ι] in
theorem incidenceFiberMatrix_gram [DecidableEq ρ]
    (I : ι → Finset κ) (r : ι → κ → ρ) (β : ι → κ → ℂ) (a b : ι) :
    ((incidenceFiberMatrix I r β)ᴴ * incidenceFiberMatrix I r β) a b =
      ∑ k ∈ I a, ∑ l ∈ I b,
        if r a k = r b l then star (β a k) * β b l else 0 := by
  classical
  have hdelta (k l : κ) :
      (∑ z : ρ, star (if r a k = z then β a k else 0) *
        (if r b l = z then β b l else 0)) =
          if r a k = r b l then star (β a k) * β b l else 0 := by
    by_cases h : r a k = r b l
    · simp [h, eq_comm]
    · simp [mul_ite, h, eq_comm]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, incidenceFiberMatrix,
    star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ l ∈ I b, ∑ k ∈ I a,
        if r a k = r b l then star (β a k) * β b l else 0 := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      exact hdelta k l
    _ = _ := Finset.sum_comm

omit [Fintype ι] in
theorem incidenceFiberMatrix_gram_norm [DecidableEq κ] [DecidableEq ρ]
    (I : ι → Finset κ) (r : ι → κ → ρ) (β : ι → κ → ℂ)
    (hβ : ∀ a k, k ∈ I a → ‖β a k‖ ≤ 1) (a b : ι) :
    ‖((incidenceFiberMatrix I r β)ᴴ * incidenceFiberMatrix I r β) a b‖ ≤
      (incidenceFiberCollisions I r a b : ℝ) := by
  classical
  rw [incidenceFiberMatrix_gram]
  calc
    _ ≤ ∑ k ∈ I a, ∑ l ∈ I b,
        ‖if r a k = r b l then star (β a k) * β b l else 0‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => norm_sum_le _ _))
    _ ≤ ∑ k ∈ I a, ∑ l ∈ I b, if r a k = r b l then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      by_cases h : r a k = r b l
      · simp only [ite_eq_left h, norm_mul, norm_star]
        calc
          _ ≤ (1 : ℝ) * 1 := mul_le_mul (hβ a k hk) (hβ b l hl)
            (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      · simp only [ite_eq_right h, norm_zero, le_refl]
    _ = _ := by
      simp only [incidenceFiberCollisions, Finset.card_filter, Finset.sum_product,
        Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

#print axioms incidenceSymmetricSchur
#print axioms incidenceEnergy_le_symmetricSchur
#print axioms incidenceFiberMatrix_gram
#print axioms incidenceFiberMatrix_gram_norm

end PrimeGap182Audit
