import TrialAnalyticParameters182
import SieveSourceTransfer182

/-! Exact prime-indicator sources from the proved public MPZ endpoints.
The two original finite-field estimates are explicit hypotheses. The
literal row certificates supply a positive parameter retreat, so no new
global prime-distribution or bilinear estimate is assumed here. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186 PrimeGap182

namespace PrimeGap182Analytic

/-- Precisely the two finite-field hypotheses of the public prime-source
theorems. This is a proposition, not an asserted axiom. -/
def PublicPrimeLocalBounds182 : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (c : ZMod p),
    c ≠ 0 → ‖normalizedKloosterman3 p c‖ ≤ (3 : ℝ)) ∧
  (∀ (p : ℕ) [Fact p.Prime] (A B : ZMod p),
    A ≠ 0 → B ≠ 0 →
      ‖∑ t : ZMod p, if t ≠ 0 ∧ t ≠ -1 then
        unnormalizedKloosterman2 p (A / t) *
          unnormalizedKloosterman2 p (B / (t + 1)) else 0‖ ≤
        8 * (p : ℝ) * Real.sqrt (p : ℝ))

open Classical in
theorem selbergClosedSequence182_prime (x : ℝ) :
    selbergClosedSequence182 0 x =
      ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
        Finsupp.single n (if n.Prime then (1 : ℂ) else 0) := by
  unfold selbergClosedSequence182
  apply Finset.sum_congr rfl
  intro n _hn
  congr 1
  dsimp [selbergWeight182, primeIndicator]
  split_ifs <;> norm_num

theorem closedPrimeSource_of_public_guards
    (hlocal : PublicPrimeLocalBounds182)
    {j : ℕ} {«ω» δ τ : ℝ} (hg : PrimeAnalyticGuards182 j «ω» δ τ)
    (L0 : ℝ → ℝ) (hL0 : ∀ x : ℝ, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0)) :
    ClosedSourceLogSaving182 0 j «ω» δ L0 := by
  classical
  dsimp only [PrimeAnalyticGuards182] at hg
  obtain ⟨hω, hδ, hτ, huupper, hvupper, hσhalf, hσgap, hcases⟩ := hg
  have hu : 0 < «ω» + τ := add_pos hω hτ
  have hv : 0 < δ + τ := add_pos hδ hτ
  have hσ0 : (1 / 10 : ℝ) < 1 / 10 + τ := lt_add_of_pos_right _ hτ
  have hθ0 : (0 : ℝ) < 1 / 2 + 2 * «ω» := by linarith only [hω]
  have hθ : (1 / 2 : ℝ) + 2 * «ω» < 1 / 2 + 2 * («ω» + τ) := by linarith only [hτ]
  have hδgap : δ < δ + τ := lt_add_of_pos_right _ hτ
  intro A hA
  rcases hcases with ⟨hI, hII, hIII⟩ | ⟨rfl, hrange⟩
  · obtain ⟨K, X, hK, hX, hbound⟩ :=
      source_mpz_lowerOrder_primeIndicator_coherent_log_saving_of_deligne hlocal
        j («ω» + τ) (δ + τ) (1 / 10 + τ) hu huupper hv hvupper
        hσ0 hσhalf hσgap hI hII hIII (1 / 2 + 2 * «ω») δ hθ0 hθ hδ hδgap
        L0 hL0 hL0sub 0 0 A hA
    refine ⟨K, X, hK, (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hX, ?_⟩
    intro x hx I hpr a ha
    have hx0 : 0 < x := (Real.exp_pos 1).trans_le (hX.trans hx)
    have hb := hbound x hx x (2 * x) le_rfl (by linarith only [hx0]) le_rfl I hpr a ha
    simpa only [sourceModuli182, selbergClosedSequence182_prime, pow_zero, one_mul,
      Nat.cast_zero, add_zero] using hb
  · obtain ⟨K, X, hK, hX, hbound⟩ :=
      source_mpz3_primeIndicator_coherent_divisor_weight_log_saving_of_deligne hlocal
        («ω» + τ) (δ + τ) hu hv hrange
        (1 / 2 + 2 * «ω») δ hθ0 hθ hδ hδgap L0 hL0 hL0sub 0 A hA
    refine ⟨K, X, hK, (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hX, ?_⟩
    intro x hx I hpr a ha
    have hx0 : 0 < x := (Real.exp_pos 1).trans_le (hX.trans hx)
    have hb := hbound x hx x (2 * x) le_rfl (by linarith only [hx0]) le_rfl I hpr a ha
    simpa only [sourceModuli182, selbergClosedSequence182_prime, pow_zero, one_mul] using hb

theorem trialOldSourceRows_closed_prime
    (hlocal : PublicPrimeLocalBounds182)
    (L0 : ℝ → ℝ) (hL0 : ∀ x : ℝ, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0)) :
    ∀ row ∈ trialOldSourceRows,
      ClosedSourceLogSaving182 0 row.order (row.omega : ℝ) (row.delta : ℝ) L0 := by
  intro row hrow
  exact closedPrimeSource_of_public_guards hlocal
    (trialOldSourceRows_prime_analytic row hrow).cast_real L0 hL0 hL0sub

theorem trialCommonSource_closed_prime
    (hlocal : PublicPrimeLocalBounds182)
    (L0 : ℝ → ℝ) (hL0 : ∀ x : ℝ, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0)) :
    ClosedSourceLogSaving182 0 2 (trialCommonSourceOmega : ℝ)
      (trialCommonSourceDelta : ℝ) L0 :=
  closedPrimeSource_of_public_guards hlocal trialCommonSource_analytic.2.cast_real L0 hL0 hL0sub

theorem trialSubtractionSource_closed_prime
    (hlocal : PublicPrimeLocalBounds182)
    (L0 : ℝ → ℝ) (hL0 : ∀ x : ℝ, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0)) :
    ClosedSourceLogSaving182 0 2 (trialSubtractionSourceRow.omega : ℝ)
      (trialSubtractionSourceRow.delta : ℝ) L0 := by
  exact closedPrimeSource_of_public_guards hlocal
    trialSubtractionSource_analytic.2.cast_real L0 hL0 hL0sub

#print axioms closedPrimeSource_of_public_guards
#print axioms trialOldSourceRows_closed_prime
#print axioms trialCommonSource_closed_prime
#print axioms trialSubtractionSource_closed_prime

end PrimeGap182Analytic
