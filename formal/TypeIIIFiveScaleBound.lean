import TypeIIIScaleBounds
import TypeIIISelectedKernelBound

/-! Uniform envelopes for the five selected second-moment terms. -/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

def fiveScale (N Q S y H : ℝ) : ℝ :=
  widthNonzeroScale N Q S y + H * (N * Q * S + N ^ 2 * Q)

def selectionSubpower (N Q ε : ℝ) : ℝ :=
  (1 + 4 * Q) ^ ε * (1 + N * (4 * Q) ^ 3) ^ ε

theorem fiveScale_nonneg {N Q S y H : ℝ}
    (hN : 0 ≤ N) (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hy : 0 ≤ y) (hH : 0 ≤ H) :
    0 ≤ fiveScale N Q S y H := by
  unfold fiveScale widthNonzeroScale
  positivity

theorem selectionSubpower_nonneg {N Q ε : ℝ} (hN : 0 ≤ N) (hQ : 0 ≤ Q) :
    0 ≤ selectionSubpower N Q ε := by
  unfold selectionSubpower
  positivity

theorem selectedMomentScale_dyadic_le {N R S₀ Q S y H ε : ℝ}
    (hN : 0 ≤ N) (hR : 0 ≤ R) (hS₀ : 1 ≤ S₀) (hQ : 0 < Q)
    (hS : 0 < S) (hy : 0 < y) (hH : 0 ≤ H) (hε : 0 ≤ ε)
    (hRS : R * S₀ ≤ 2 * Q) (hlo : S / y ≤ S₀) (hhi : S₀ ≤ 2 * S) :
    selectedMomentScale N R S₀ H ε ≤
      16 * selectionSubpower N Q ε * fiveScale N Q S y H := by
  have hRle : R ≤ 2 * Q := (le_mul_of_one_le_right hR hS₀).trans hRS
  have hS₀zero : 0 ≤ S₀ := zero_le_one.trans hS₀
  have hA : 0 ≤ (1 + 4 * Q) ^ ε := by positivity
  have hB : 1 ≤ (1 + N * (4 * Q) ^ 3) ^ ε :=
    Real.one_le_rpow (le_add_of_nonneg_right (by positivity)) hε
  have hNZpow : (R * S₀) ^ ε ≤ selectionSubpower N Q ε := by
    apply (Real.rpow_le_rpow (mul_nonneg hR hS₀zero)
      (hRS.trans (by linarith : 2 * Q ≤ 1 + 4 * Q)) hε).trans
    exact le_mul_of_one_le_right hA hB
  have hZpow₁ : (1 + 2 * S₀ * R) ^ ε ≤ (1 + 4 * Q) ^ ε :=
    Real.rpow_le_rpow (by positivity) (by nlinarith only [hRS]) hε
  have hZbase : 1 + N * (2 * R) ^ 3 ≤ 1 + N * (4 * Q) ^ 3 := by
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ hN
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hRle]
  have hZpow₂ : (1 + N * (2 * R) ^ 3) ^ ε ≤ (1 + N * (4 * Q) ^ 3) ^ ε :=
    Real.rpow_le_rpow (by positivity) hZbase hε
  have hZpow : (1 + 2 * S₀ * R) ^ ε * (1 + N * (2 * R) ^ 3) ^ ε ≤
      selectionSubpower N Q ε :=
    mul_le_mul hZpow₁ hZpow₂ (by positivity) hA
  have hNZ := nonzeroSGScale_dyadic_le hN hR hQ hS hy hRS hlo hhi
  have hZ := zeroSGScale_dyadic_le hN hS₀zero hQ.le hRS hhi
  have hbNZ := mul_le_mul hNZpow hNZ
    (nonzeroSGScale_nonneg hN hR hS₀zero) (selectionSubpower_nonneg hN hQ.le)
  have hbZ := mul_le_mul hZpow hZ
    (zeroSGScale_nonneg hN hR hS₀zero) (selectionSubpower_nonneg hN hQ.le)
  have hbZH := mul_le_mul_of_nonneg_left hbZ hH
  have hcenter : 0 ≤ selectionSubpower N Q ε * H * (N * Q * S + N ^ 2 * Q) :=
    mul_nonneg (mul_nonneg (selectionSubpower_nonneg hN hQ.le) hH) (by positivity)
  unfold selectedMomentScale fiveScale
  nlinarith only [hbNZ, hbZH, hcenter]

theorem firstMomentLogBound_mono_S {H S S' : ℝ} (hH : 0 ≤ H) (hS : 0 < S)
    (hSS : S ≤ S') : firstMomentLogBound H S ≤ firstMomentLogBound H S' := by
  unfold firstMomentLogBound
  apply mul_le_mul_of_nonneg_left (add_le_add le_rfl (Real.log_le_log hS hSS))
  exact mul_nonneg (mul_nonneg (by norm_num) hH)
    (pow_nonneg (add_nonneg zero_le_one (Real.log_nonneg (le_max_left _ _))) _)

#print axioms selectedMomentScale_dyadic_le

end

end PrimeGap182.TypeIII
