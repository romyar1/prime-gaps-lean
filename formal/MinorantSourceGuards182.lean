import MinorantSource182
import TrialAnalyticParameters182
import TypeIIIGlobalEstimate
import TypeIIIGlobalMonotonicity

/-! Numerical-guard and finite-field specialization of the actual minorant
source theorem. The new local Fourier bound gives the entire global Type III
input. Orders one and two use the proved public bilinear estimates. Only the
order-three bilinear estimate remains an explicit intermediate premise. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186 PrimeGap182 PrimeGap182.TypeIII

namespace PrimeGap182Analytic

open Harman

theorem closedMinorantSource_of_guards
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    {j : ℕ} {«ω» δ τ : ℝ} (hg : MinorantAnalyticGuards182 j «ω» δ τ)
    (hbilinear3 : j = 3 → SourceBilinearEstimate j («ω» + τ) (δ + τ)
      ((1 / 2 : ℝ) - 41361 / 100000 + 2 * τ))
    (L0 : ℝ → ℝ) (hL0 : ∀ x : ℝ, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0)) :
    ClosedSourceLogSaving182 1 j «ω» δ L0 := by
  dsimp only [MinorantAnalyticGuards182] at hg
  obtain ⟨hω, hδ, hτ, hτsmall, huupper, hσ, hσhalf, hsmooth, hIIIwall, hII, hcases⟩ := hg
  have hu : 0 < «ω» + τ := add_pos hω hτ
  have hv : 0 < δ + τ := add_pos hδ hτ
  have hj : 1 ≤ j := by
    rcases hcases with h1 | h2 | h3 <;> omega
  have hbilinear : SourceBilinearEstimate j («ω» + τ) (δ + τ)
      ((1 / 2 : ℝ) - 41361 / 100000 + 2 * τ) := by
    rcases hcases with h1 | h2 | h3
    · exact sourceBilinearEstimate_lower_order j («ω» + τ) (δ + τ) _ hu hv hσ
        (Or.inl h1) hII
    · exact sourceBilinearEstimate_lower_order j («ω» + τ) (δ + τ) _ hu hv hσ
        (Or.inr h2) hII
    · exact hbilinear3 h3.1
  have hbump : (1 / 100 : ℝ) ≤ max («ω» + τ) (1 / 100) := le_max_right _ _
  have hIIIb := hlocal.positiveSmoothTypeIIIGlobalEstimate hC
    (max («ω» + τ) (1 / 100)) (δ + τ) ((2159 : ℝ) / 25000 - 2 * τ)
    (by linarith only [hbump]) hv (by linarith only [hτ])
    (by nlinarith only [hIIIwall]) (by linarith only [hbump, hv])
  have hIII : PositiveSmoothTypeIIIGlobalEstimate («ω» + τ) (δ + τ)
      ((2159 : ℝ) / 25000 - 2 * τ) :=
    hIIIb.mono_omega (le_max_left _ _)
  exact closedMinorantSource_of_analytic_inputs τ hτ hτsmall j hj «ω» δ
    ((1 / 2 : ℝ) - 41361 / 100000 + 2 * τ) ((2159 : ℝ) / 25000 - 2 * τ)
    hω hδ (by linarith only [hτ]) hσhalf (by linarith only [hτ])
    (by linarith only [huupper, hτ])
    ⟨τ, hτ, by linarith only [huupper], hIII, hsmooth, hbilinear⟩
    L0 hL0 hL0sub

theorem trialSourceRows_closed_minorant
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    (hbilinear3 : ∀ ν : Fin 2, ∀ row ∈ trialSourceRows ν, row.order = 3 →
      SourceBilinearEstimate row.order
        ((row.omega : ℝ) + (trialAnalyticTolerance182 : ℝ))
        ((row.delta : ℝ) + (trialAnalyticTolerance182 : ℝ))
        ((1 / 2 : ℝ) - 41361 / 100000 + 2 * (trialAnalyticTolerance182 : ℝ)))
    (L0 : ℝ → ℝ) (hL0 : ∀ x : ℝ, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0)) :
    ∀ ν : Fin 2, ∀ row ∈ trialSourceRows ν,
      ClosedSourceLogSaving182 1 row.order (row.omega : ℝ) (row.delta : ℝ) L0 := by
  intro ν row hrow
  exact closedMinorantSource_of_guards hC hlocal
    (trialSourceRows_minorant_analytic ν row hrow).cast_real (hbilinear3 ν row hrow)
    L0 hL0 hL0sub

theorem trialCommonSource_closed_minorant
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    (L0 : ℝ → ℝ) (hL0 : ∀ x : ℝ, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0)) :
    ClosedSourceLogSaving182 1 2 (trialCommonSourceOmega : ℝ)
      (trialCommonSourceDelta : ℝ) L0 :=
  closedMinorantSource_of_guards hC hlocal trialCommonSource_analytic.1.cast_real
    (by intro h; omega) L0 hL0 hL0sub

theorem trialSubtractionSource_closed_minorant
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    (L0 : ℝ → ℝ) (hL0 : ∀ x : ℝ, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0)) :
    ClosedSourceLogSaving182 1 2 (trialSubtractionSourceRow.omega : ℝ)
      (trialSubtractionSourceRow.delta : ℝ) L0 := by
  exact closedMinorantSource_of_guards hC hlocal trialSubtractionSource_analytic.1.cast_real
    (by intro h; norm_num [trialSubtractionSourceRow] at h) L0 hL0 hL0sub

#print axioms closedMinorantSource_of_guards
#print axioms trialSourceRows_closed_minorant
#print axioms trialCommonSource_closed_minorant
#print axioms trialSubtractionSource_closed_minorant

end PrimeGap182Analytic
