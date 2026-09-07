import TypeIIIGlobalInterface

/-! Restricting the actual Type III modulus level. This permits using
the proved source at max(omega,.01) on a smaller requested level, without
changing the convolution, residue classes, or smoothness requirements. -/

noncomputable section
open scoped BigOperators
open PrimeGap186

namespace PrimeGap182.TypeIII

theorem PositiveSmoothTypeIIIGlobalEstimate.mono_omega
    {«ω» «ω'» δ σ : ℝ}
    (h : PositiveSmoothTypeIIIGlobalEstimate «ω'» δ σ) (hω : «ω» ≤ «ω'») :
    PositiveSmoothTypeIIIGlobalEstimate «ω» δ σ := by
  obtain ⟨εcap, hεcap, hb⟩ := h
  refine ⟨εcap, hεcap, ?_⟩
  intro C E Eα D hC ε hε hεle
  dsimp only
  intro A hA
  obtain ⟨K, X, hK, hX, hh⟩ := hb C E Eα D hC ε hε hεle A hA
  refine ⟨K, X, hK, hX, ?_⟩
  intro x hx M N₁ N₂ N₃ hM hN₁ hN₂ hN₃
    hMNlo hMNhi hpair₁₂ hpair₁₃ hpair₂₃ hsize₁ hsize₂ hsize₃ Y hY Q hQ
  apply hh x hx M N₁ N₂ N₃ hM hN₁ hN₂ hN₃
    hMNlo hMNhi hpair₁₂ hpair₁₃ hpair₂₃ hsize₁ hsize₂ hsize₃ Y hY Q
  intro q hq
  have hx1 : 1 ≤ x := (Real.one_le_exp zero_le_one).trans (hX.trans hx)
  exact ⟨(hQ q hq).1, (hQ q hq).2.1, (hQ q hq).2.2.trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)) (zero_le_one.trans hC))⟩

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.PositiveSmoothTypeIIIGlobalEstimate.mono_omega
