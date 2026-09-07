import TypeIIIFiveScaleBound

/-! Controlled enlargement of the row interval and modulus scales. -/

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem fiveScale_mono_NQ {N N' Q Q' S y H : ℝ}
    (hN : 0 ≤ N) (hNN : N ≤ N') (hQ : 0 ≤ Q) (hQQ : Q ≤ Q')
    (hS : 0 ≤ S) (hy : 0 ≤ y) (hH : 0 ≤ H) :
    fiveScale N Q S y H ≤ fiveScale N' Q' S y H := by
  have hN' : 0 ≤ N' := hN.trans hNN
  have hQ' : 0 ≤ Q' := hQ.trans hQQ
  unfold fiveScale widthNonzeroScale
  gcongr

theorem monomial_dilate_bound {N Q c d u v : ℝ}
    (hN : 0 ≤ N) (hQ : 0 ≤ Q) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hu : u ≤ 2) (hv : v ≤ 3) :
    (c * N) ^ u * (d * Q) ^ v ≤ (c ^ 2 * d ^ 3) * (N ^ u * Q ^ v) := by
  have hc₀ : 0 ≤ c := zero_le_one.trans hc
  have hd₀ : 0 ≤ d := zero_le_one.trans hd
  have hcu : c ^ u ≤ c ^ (2 : ℕ) := by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le hc hu
  have hdv : d ^ v ≤ d ^ (3 : ℕ) := by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le hd hv
  rw [Real.mul_rpow hc₀ hN, Real.mul_rpow hd₀ hQ]
  calc
    _ = (c ^ u * d ^ v) * (N ^ u * Q ^ v) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul hcu hdv (Real.rpow_nonneg hd₀ _) (sq_nonneg _)) (by positivity)

theorem fiveScale_dilate_NQ {N Q S y H c d : ℝ}
    (hN : 0 ≤ N) (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hy : 0 ≤ y) (hH : 0 ≤ H)
    (hc : 1 ≤ c) (hd : 1 ≤ d) :
    fiveScale (c * N) (d * Q) S y H ≤ c ^ 2 * d ^ 3 * fiveScale N Q S y H := by
  have h₁ := monomial_dilate_bound hN hQ hc hd
    (by norm_num : (7 / 4 : ℝ) ≤ 2) (by norm_num : (3 : ℝ) ≤ 3)
  have h₂ := monomial_dilate_bound hN hQ hc hd
    (by norm_num : (2 : ℝ) ≤ 2) (by norm_num : (5 / 2 : ℝ) ≤ 3)
  have h₃ := monomial_dilate_bound hN hQ hc hd
    (by norm_num : (2 : ℝ) ≤ 2) (by norm_num : (3 : ℝ) ≤ 3)
  have h₄ := monomial_dilate_bound hN hQ hc hd
    (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 : ℝ) ≤ 3)
  have h₅ := monomial_dilate_bound hN hQ hc hd
    (by norm_num : (2 : ℝ) ≤ 2) (by norm_num : (1 : ℝ) ≤ 3)
  norm_num only [Real.rpow_one, Real.rpow_ofNat] at h₁ h₂ h₃ h₄ h₅
  have hA := mul_le_mul_of_nonneg_right h₁
    (by positivity : 0 ≤ S ^ (-(1 / 2 : ℝ)) * y ^ (1 / 2 : ℝ))
  have hB := mul_le_mul_of_nonneg_right h₂ (Real.rpow_nonneg hS (1 / 4))
  have hC := mul_le_mul_of_nonneg_right h₃
    (by positivity : 0 ≤ S ^ (-(5 / 8 : ℝ)) * y ^ (5 / 8 : ℝ))
  have hD := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h₄ hS) hH
  have hE := mul_le_mul_of_nonneg_left h₅ hH
  unfold fiveScale widthNonzeroScale
  nlinarith only [hA, hB, hC, hD, hE]

#print axioms fiveScale_dilate_NQ

end

end PrimeGap182.TypeIII
