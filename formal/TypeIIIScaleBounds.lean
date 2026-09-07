import TypeIIIResidualProfile

/-!
# The five Type III scales after dyadic selection

These inequalities use the actual product bound R S₀ ≤ 2 Q and the entire
extraction window S / y ≤ S₀ ≤ 2 S. In particular, the negative powers of S₀
retain their factors y^(1/2) and y^(5/8).
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem nonzeroSGScale_nonneg {M R S : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    0 ≤ nonzeroSGScale M R S := by
  unfold nonzeroSGScale
  positivity

theorem zeroSGScale_nonneg {M R S : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    0 ≤ zeroSGScale M R S := by
  unfold zeroSGScale
  positivity

theorem nonzeroSGScale_mono_R {M R R' S : ℝ}
    (hM : 0 ≤ M) (hR : 0 ≤ R) (hRR : R ≤ R') (hS : 0 ≤ S) :
    nonzeroSGScale M R S ≤ nonzeroSGScale M R' S := by
  unfold nonzeroSGScale
  gcongr

theorem nonzeroSGScale_le_paper {M R S Q : ℝ}
    (hM : 0 ≤ M) (hR : 0 ≤ R) (hS : 0 < S) (hQ : 0 < Q) (hRS : R * S ≤ Q) :
    nonzeroSGScale M R S ≤ paperNonzeroScale M Q S := by
  rw [← nonzeroSGScale_at_ratio M hQ hS]
  exact nonzeroSGScale_mono_R hM hR ((le_div_iff₀ hS).mpr hRS) hS.le

def widthNonzeroScale (M Q S y : ℝ) : ℝ :=
  M ^ (7 / 4 : ℝ) * Q ^ 3 * S ^ (-(1 / 2 : ℝ)) * y ^ (1 / 2 : ℝ) +
  M ^ 2 * Q ^ (5 / 2 : ℝ) * S ^ (1 / 4 : ℝ) +
  M ^ 2 * Q ^ 3 * S ^ (-(5 / 8 : ℝ)) * y ^ (5 / 8 : ℝ)

theorem widthNonzeroScale_nonneg {M Q S y : ℝ}
    (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hy : 0 ≤ y) :
    0 ≤ widthNonzeroScale M Q S y := by
  unfold widthNonzeroScale
  positivity

theorem rpow_negative_width {S S₀ y a : ℝ}
    (hS : 0 < S) (hy : 0 < y) (hlo : S / y ≤ S₀) (ha : 0 ≤ a) :
    S₀ ^ (-a) ≤ S ^ (-a) * y ^ a := by
  calc
    _ ≤ (S / y) ^ (-a) := Real.rpow_le_rpow_of_nonpos (div_pos hS hy) hlo (neg_nonpos.mpr ha)
    _ = _ := by rw [Real.div_rpow hS.le hy.le, Real.rpow_neg hy.le, div_inv_eq_mul]

theorem paperNonzeroScale_width {M Q S S₀ y : ℝ}
    (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hS : 0 < S) (hy : 0 < y)
    (hlo : S / y ≤ S₀) (hhi : S₀ ≤ 2 * S) :
    paperNonzeroScale M Q S₀ ≤ 2 * widthNonzeroScale M Q S y := by
  have hS₀ : 0 < S₀ := (div_pos hS hy).trans_le hlo
  have h₁ := rpow_negative_width hS hy hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h₃ := rpow_negative_width hS hy hlo (by norm_num : (0 : ℝ) ≤ 5 / 8)
  have h₂ : S₀ ^ (1 / 4 : ℝ) ≤ 2 * S ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ (2 * S) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hS₀.le hhi (by norm_num)
      _ = (2 : ℝ) ^ (1 / 4 : ℝ) * S ^ (1 / 4 : ℝ) := Real.mul_rpow (by norm_num) hS.le
      _ ≤ 2 * S ^ (1 / 4 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hS.le _)
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hA := mul_le_mul_of_nonneg_left h₁
    (by positivity : 0 ≤ M ^ (7 / 4 : ℝ) * Q ^ 3)
  have hB := mul_le_mul_of_nonneg_left h₂
    (by positivity : 0 ≤ M ^ 2 * Q ^ (5 / 2 : ℝ))
  have hC := mul_le_mul_of_nonneg_left h₃ (by positivity : 0 ≤ M ^ 2 * Q ^ 3)
  have hA₀ : 0 ≤ M ^ (7 / 4 : ℝ) * Q ^ 3 * S ^ (-(1 / 2 : ℝ)) * y ^ (1 / 2 : ℝ) := by
    positivity
  have hC₀ : 0 ≤ M ^ 2 * Q ^ 3 * S ^ (-(5 / 8 : ℝ)) * y ^ (5 / 8 : ℝ) := by positivity
  unfold paperNonzeroScale widthNonzeroScale
  nlinarith only [hA, hB, hC, hA₀, hC₀]

theorem widthNonzeroScale_double_Q {M Q S y : ℝ}
    (hQ : 0 ≤ Q) (hS : 0 ≤ S) :
    widthNonzeroScale M (2 * Q) S y ≤ 8 * widthNonzeroScale M Q S y := by
  have h₂ : (2 * Q) ^ (5 / 2 : ℝ) ≤ 8 * Q ^ (5 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hQ]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hQ _)
    have hh := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (5 / 2 : ℝ) ≤ 3)
    norm_num at hh ⊢
    exact hh
  have hh := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right h₂ (Real.rpow_nonneg hS (1 / 4))) (sq_nonneg M)
  unfold widthNonzeroScale
  nlinarith only [hh]

/-- The three off-diagonal scales with every extraction-width loss explicit. -/
theorem nonzeroSGScale_dyadic_le {M R S₀ Q S y : ℝ}
    (hM : 0 ≤ M) (hR : 0 ≤ R) (hQ : 0 < Q) (hS : 0 < S) (hy : 0 < y)
    (hRS : R * S₀ ≤ 2 * Q) (hlo : S / y ≤ S₀) (hhi : S₀ ≤ 2 * S) :
    nonzeroSGScale M R S₀ ≤ 16 * widthNonzeroScale M Q S y := by
  have hS₀ : 0 < S₀ := (div_pos hS hy).trans_le hlo
  calc
    _ ≤ paperNonzeroScale M (2 * Q) S₀ :=
      nonzeroSGScale_le_paper hM hR hS₀ (by positivity) hRS
    _ ≤ 2 * widthNonzeroScale M (2 * Q) S y :=
      paperNonzeroScale_width hM (by positivity) hS hy hlo hhi
    _ ≤ 2 * (8 * widthNonzeroScale M Q S y) :=
      mul_le_mul_of_nonneg_left (widthNonzeroScale_double_Q hQ.le hS.le) (by norm_num)
    _ = _ := by ring

/-- The two central scales cost no negative-power extraction-width factor. -/
theorem zeroSGScale_dyadic_le {M R S₀ Q S : ℝ}
    (hM : 0 ≤ M) (hS₀ : 0 ≤ S₀) (hQ : 0 ≤ Q)
    (hRS : R * S₀ ≤ 2 * Q) (hhi : S₀ ≤ 2 * S) :
    zeroSGScale M R S₀ ≤ 4 * (M * Q * S + M ^ 2 * Q) := by
  have h₁ := mul_le_mul hRS hhi hS₀ (by positivity : 0 ≤ 2 * Q)
  have h₂ := mul_le_mul_of_nonneg_left hRS (sq_nonneg M)
  have h₃ := mul_le_mul_of_nonneg_left h₁ hM
  have h₄ : 0 ≤ M ^ 2 * Q := by positivity
  unfold zeroSGScale
  nlinarith only [h₂, h₃, h₄]

#print axioms nonzeroSGScale_dyadic_le
#print axioms zeroSGScale_dyadic_le

end

end PrimeGap182.TypeIII
