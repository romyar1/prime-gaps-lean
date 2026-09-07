import TypeIIIPositiveSmoothGlobal
import TypeIIIGlobalInterface

/-!
# The new global Type III interface, derived from the local Fourier input

The conclusion is the complete actual positive smooth convolution discrepancy
estimate used by the Harman/Heath--Brown source assembly. The epsilon cap is
uniform in the support, coefficient, derivative, and logarithmic-saving
parameters. Coherent primitive residue families are reduced to their actual
common integer representative only after the full analytic estimate is proved.

`LocalFourierHypothesis` remains an explicit finite-field input. No global
distribution estimate, existence of that input, or sheaf theorem is asserted as
an axiom here.
-/

open scoped BigOperators Classical ContDiff NNReal
open PrimeGap186 PrimeGap182Audit

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem LocalFourierHypothesis.positiveSmoothTypeIIIGlobalEstimate
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) {D₀ p₀ : ℕ} (hlocal : LocalFourierHypothesis C₀ D₀ p₀)
    (omegaExp δ σ : ℝ) (hω : 0 < omegaExp) (hδ : 0 < δ)
    (hσupper : σ < 1 / 6)
    (hσ : 1 / 30 + 56 * omegaExp / 15 + 4 * δ / 15 < σ)
    (hswitch : 1 < 108 * omegaExp + 2 * δ) :
    PositiveSmoothTypeIIIGlobalEstimate omegaExp δ σ := by
  have hA : 0 < typeIIIMarginA (typeIIIMu σ) (typeIIITheta omegaExp) δ :=
    (typeIII_criteria_equivalence σ omegaExp δ).1.mpr hσ
  dsimp only [PositiveSmoothTypeIIIGlobalEstimate]
  refine ⟨typeIIIEpsilonCap (typeIIIMu σ) (typeIIITheta omegaExp) δ,
    typeIIIEpsilonCap_pos hA, ?_⟩
  intro C E Eα D hC ε hε hεcap A hAsave
  have hg := hlocal.positive_smooth_convolution_global_log_saving hC₀
    omegaExp δ σ C E Eα D hω hδ hC hσupper hσ hswitch
  dsimp only at hg
  obtain ⟨K, X, hK, hX, hbound⟩ := hg.2 ε hε hεcap A hAsave
  refine ⟨K, X, hK, hX, ?_⟩
  intro x hx M N₁ N₂ N₃ hM hN₁ hN₂ hN₃
    hMNlo hMNhi h₁₂ h₁₃ h₂₃ hN₁hi hN₂hi hN₃hi
    Y hY Qset hQset Lα L₁ L₂ L₃ hLα hL₁ hL₂ hL₃ α hαsupport hαbound
    ψ₁ ψ₂ ψ₃ hψ₁ hψ₂ hψ₃ hs₁ hs₂ hs₃ hd₁ hd₂ hd₃ a ha
  obtain ⟨hu, a₀, hcoherent⟩ := ha
  have hu₀ (q : ℕ+) (hq : q ∈ Qset) : IsUnit (a₀ : ZMod (q : ℕ)) := by
    rw [← hcoherent q hq]
    exact hu q hq
  have hh := hbound x hx M N₁ N₂ N₃ hM hN₁ hN₂ hN₃
    hMNlo hMNhi h₁₂ h₁₃ h₂₃ hN₁hi hN₂hi hN₃hi Y hY Qset hQset
    Lα L₁ L₂ L₃ hLα hL₁ hL₂ hL₃ α hαsupport hαbound
    ψ₁ ψ₂ ψ₃ hψ₁ hψ₂ hψ₃ hs₁ hs₂ hs₃ hd₁ hd₂ hd₃ a₀ hu₀
  convert hh using 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [hcoherent q hq]

#print axioms LocalFourierHypothesis.positiveSmoothTypeIIIGlobalEstimate

end

end PrimeGap182.TypeIII
