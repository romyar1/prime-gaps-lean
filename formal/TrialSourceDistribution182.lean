import TrialBaseDistribution182
import PrimeSourcePublic182
import MinorantSourceGuards182
import SourcePrimeGap182

/-! Actual trial source estimates and the terminal sieve consequence.
The all-moduli base estimate is proved. The old prime sources are obtained
from the two explicit public finite-field bounds. The new minorant sources
are obtained from the explicit Type III local Fourier bound and the one
remaining order-three bilinear estimate on the 31 improved source rows.
Common/subtraction minorant sources need only order two. Defect sources
follow from the exact prime-minus-minorant identity. Thus no source-support,
moment, or independent defect-distribution assumption survives here.

This is an intermediate theorem: the order-three bilinear input and the
262 physical numerical inequalities are stated premises, not proved values.
-/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186 PrimeGap182Analytic PrimeGap182.TypeIII

namespace PrimeGap182

open Harman

/-- The only global analytic input retained by the intermediate trial
assembly: the actual bilinear discrepancy estimate on the improved
order-three rows, with the fixed positive retreat from the row certificate. -/
def TrialOrderThreeBilinear182 : Prop :=
  ∀ row ∈ trialNewSourceRows, row.order = 3 →
    SourceBilinearEstimate 3
      ((row.omega : ℝ) + (trialAnalyticTolerance182 : ℝ))
      ((row.delta : ℝ) + (trialAnalyticTolerance182 : ℝ))
      ((1 / 2 : ℝ) - 41361 / 100000 + 2 * (trialAnalyticTolerance182 : ℝ))

theorem fullDiscrepancy_sub182 (f g : ℕ →₀ ℂ) (q a : ℕ) :
    fullDiscrepancy (f - g) q a = fullDiscrepancy f q a - fullDiscrepancy g q a := by
  have h := hbBoundary_fullDiscrepancy_add (f - g) g q a
  rw [sub_add_cancel] at h
  exact eq_sub_iff_add_eq.mpr h.symm

theorem closedSourceLogSaving182_defect {j : ℕ} {«ω» δ : ℝ} {L0 : ℝ → ℝ}
    (hp : ClosedSourceLogSaving182 0 j «ω» δ L0)
    (hm : ClosedSourceLogSaving182 1 j «ω» δ L0) :
    ClosedSourceLogSaving182 2 j «ω» δ L0 := by
  intro A hA
  obtain ⟨Kp, Xp, hKp, hXp, hp⟩ := hp A hA
  obtain ⟨Km, Xm, hKm, _hXm, hm⟩ := hm A hA
  refine ⟨Kp + Km, max Xp Xm, add_pos hKp hKm, hXp.trans_le (le_max_left _ _), ?_⟩
  intro x hx I hI a ha
  have hp := hp x ((le_max_left _ _).trans hx) I hI a ha
  have hm := hm x ((le_max_right _ _).trans hx) I hI a ha
  calc
    _ ≤ ∑ q ∈ sourceModuli182 j «ω» δ L0 x I,
        (‖fullDiscrepancy (selbergClosedSequence182 0 x) q a‖ +
          ‖fullDiscrepancy (selbergClosedSequence182 1 x) q a‖) := by
      apply Finset.sum_le_sum
      intro q _
      rw [selbergClosedSequence182_defect, fullDiscrepancy_sub182]
      exact norm_sub_le _ _
    _ ≤ Kp * x / (Real.log x) ^ A + Km * x / (Real.log x) ^ A := by
      rw [Finset.sum_add_distrib]
      exact add_le_add hp hm
    _ = (Kp + Km) * x / (Real.log x) ^ A := by ring

private theorem minorant_guard_omega_bounds {j : ℕ} {«ω» δ τ : ℝ}
    (hg : MinorantAnalyticGuards182 j «ω» δ τ) : 0 < «ω» ∧ «ω» < 1 / 4 := by
  dsimp only [MinorantAnalyticGuards182] at hg
  obtain ⟨hω, _hδ, hτ, _hτsmall, hu, _rest⟩ := hg
  exact ⟨hω, by linarith only [hτ, hu]⟩

private theorem prime_guard_omega_bounds {j : ℕ} {«ω» δ τ : ℝ}
    (hg : PrimeAnalyticGuards182 j «ω» δ τ) : 0 < «ω» ∧ «ω» < 1 / 4 := by
  dsimp only [PrimeAnalyticGuards182] at hg
  obtain ⟨hω, _hδ, hτ, hu, _rest⟩ := hg
  exact ⟨hω, by linarith only [hτ, hu]⟩

theorem trialNewSourceRows_closed_minorant_of_orderThree
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    (hbilinear3 : TrialOrderThreeBilinear182)
    (L0 : ℝ → ℝ) (hL0 : ∀ x : ℝ, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0)) :
    ∀ row ∈ trialNewSourceRows,
      ClosedSourceLogSaving182 1 row.order (row.omega : ℝ) (row.delta : ℝ) L0 := by
  intro row hrow
  have hrow' : row ∈ trialSourceRows 1 := by simpa [trialSourceRows] using hrow
  apply closedMinorantSource_of_guards hC hlocal
    (trialSourceRows_minorant_analytic 1 row hrow').cast_real _ L0 hL0 hL0sub
  intro hj
  rw [hj]
  exact hbilinear3 row hrow hj

theorem trialShiftedSourceEstimates182
    (hpublic : PublicPrimeLocalBounds182)
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    (hbilinear3 : TrialOrderThreeBilinear182) (w : Fin 3) (h J : ℕ) :
    TrialShiftedSourceEstimates182 w h J := by
  have hL : ∀ _x : ℝ, 0 < (1 : ℝ) := fun _ => zero_lt_one
  have hLsub : Tendsto (fun x : ℝ => Real.log (1 : ℝ) / Real.log x) atTop (nhds 0) := by
    simpa only [Real.log_one, zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0))
  have hcommon : ∀ w : Fin 3,
      ClosedSourceLogSaving182 w 2 (trialCommonSourceOmega : ℝ)
        (trialCommonSourceDelta : ℝ) (fun _ => 1) := by
    intro w
    fin_cases w
    · exact trialCommonSource_closed_prime hpublic _ hL hLsub
    · exact trialCommonSource_closed_minorant hC hlocal _ hL hLsub
    · exact closedSourceLogSaving182_defect
        (trialCommonSource_closed_prime hpublic _ hL hLsub)
        (trialCommonSource_closed_minorant hC hlocal _ hL hLsub)
  have hsub : ∀ w : Fin 3,
      ClosedSourceLogSaving182 w 2 (trialSubtractionSourceRow.omega : ℝ)
        (trialSubtractionSourceRow.delta : ℝ) (fun _ => 1) := by
    intro w
    fin_cases w
    · exact trialSubtractionSource_closed_prime hpublic _ hL hLsub
    · exact trialSubtractionSource_closed_minorant hC hlocal _ hL hLsub
    · exact closedSourceLogSaving182_defect
        (trialSubtractionSource_closed_prime hpublic _ hL hLsub)
        (trialSubtractionSource_closed_minorant hC hlocal _ hL hLsub)
  refine ⟨trialBaseShiftedLogSaving182 w h J, ?_, ?_, ?_, ?_⟩
  · intro hw row hrow
    subst w
    have hω := prime_guard_omega_bounds (trialOldSourceRows_prime_analytic row hrow).cast_real
    exact (trialOldSourceRows_closed_prime hpublic _ hL hLsub row hrow).shifted_weighted
      hω.1 hω.2 hL hLsub h J
  · intro hw row hrow
    subst w
    have hrow' : row ∈ trialSourceRows 1 := by simpa [trialSourceRows] using hrow
    have hω := minorant_guard_omega_bounds (trialSourceRows_minorant_analytic 1 row hrow').cast_real
    exact (trialNewSourceRows_closed_minorant_of_orderThree hC hlocal hbilinear3
      _ hL hLsub row hrow).shifted_weighted hω.1 hω.2 hL hLsub h J
  · have hω := minorant_guard_omega_bounds trialCommonSource_analytic.1.cast_real
    exact (hcommon w).shifted_weighted hω.1 hω.2 hL hLsub h J
  · have hω := minorant_guard_omega_bounds trialSubtractionSource_analytic.1.cast_real
    exact (hsub w).shifted_weighted hω.1 hω.2 hL hLsub h J

theorem positive_band_moments_of_local_and_orderThree182
    (hn : PhysicalSourceBounds182) (hpublic : PublicPrimeLocalBounds182)
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    (hbilinear3 : TrialOrderThreeBilinear182)
    (H : Finset ℕ) (hH : H.card = 39)
    (hadm : ∀ p : ℕ, p.Prime → ∃ a ∈ Finset.range p, a ∉ H.image (fun h => h % p)) :
    PositiveBandMoments182 H hH :=
  positive_band_moments_of_source_estimates182 hn
    (fun w h => trialShiftedSourceEstimates182 hpublic hC hlocal hbilinear3 w h 13)
    H hH hadm

theorem primeGapLiminf_le_182_of_local_and_orderThree
    (hn : PhysicalSourceBounds182) (hpublic : PublicPrimeLocalBounds182)
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    (hbilinear3 : TrialOrderThreeBilinear182) :
    PrimeGap186.primeGapLiminf ≤ (182 : EReal) :=
  primeGapLiminf_le_182_of_source_estimates hn
    (fun w h => trialShiftedSourceEstimates182 hpublic hC hlocal hbilinear3 w h 13)

theorem infinite_integer_translates_of_local_and_orderThree182
    (hn : PhysicalSourceBounds182) (hpublic : PublicPrimeLocalBounds182)
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    (hbilinear3 : TrialOrderThreeBilinear182)
    (H : Finset ℤ) (hH : H.card = 39)
    (hadm : ∀ p : ℕ, p.Prime → ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a) :
    Set.Infinite {n : ℤ | 2 ≤ (H.filter (fun h => (n + h).toNat.Prime)).card} :=
  infinite_integer_translates_of_source_estimates182 hn
    (fun w h => trialShiftedSourceEstimates182 hpublic hC hlocal hbilinear3 w h 13)
    H hH hadm

theorem infinite_consecutive_prime_pairs_of_local_and_orderThree182
    (hn : PhysicalSourceBounds182) (hpublic : PublicPrimeLocalBounds182)
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    (hbilinear3 : TrialOrderThreeBilinear182) :
    Set.Infinite {p : ℕ | p.Prime ∧ ∃ q : ℕ, p < q ∧ q.Prime ∧ q - p ≤ 182 ∧
      ∀ r : ℕ, p < r → r < q → ¬r.Prime} :=
  infinite_consecutive_prime_pairs_of_source_estimates182 hn
    (fun w h => trialShiftedSourceEstimates182 hpublic hC hlocal hbilinear3 w h 13)

#print axioms closedSourceLogSaving182_defect
#print axioms trialNewSourceRows_closed_minorant_of_orderThree
#print axioms trialShiftedSourceEstimates182
#print axioms positive_band_moments_of_local_and_orderThree182
#print axioms primeGapLiminf_le_182_of_local_and_orderThree
#print axioms infinite_integer_translates_of_local_and_orderThree182
#print axioms infinite_consecutive_prime_pairs_of_local_and_orderThree182

end PrimeGap182
