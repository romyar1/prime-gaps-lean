import IncidenceRawBlockBound
import SourceIncidenceSecondary182
import SourceIncidenceBilinear182

/-! Complete analytic and sieve reduction of the frozen 182 certificate.

The displayed endpoint hypotheses are the 262 physical numerical inequalities,
the two established public prime-local bounds, the established rank-four
Kloosterman bound, and the new Type III local Fourier proposition. In particular
there is no supplied global bilinear, distribution, support, or moment estimate.

The new local Fourier proposition is still an explicit unproved input. Its
manuscript proof has not been completely formalized. Standard-only logical
axiom reports below certify these conditional theorems, not their hypotheses.
-/

noncomputable section
open scoped BigOperators

namespace PrimeGap182Audit

theorem incidenceSecondaryFamily182_of_rank_four (hK4 : AllIncidenceRankFourBounds) :
    IncidenceSecondaryFamily182 := by
  intro «ω» δ γlo γhi hω hδ h1 h2 h3 h4 h5
  obtain ⟨ε₀, hε₀, hraw⟩ := incidenceRawBlockFamily_of_rank_four hK4
    «ω» δ γlo γhi hω hδ h1 h2 h3 h4 h5
  exact ⟨ε₀, hε₀, fun ε hε hsmall =>
    incidenceSecondaryEstimate_of_raw hε (hraw ε hε hsmall)⟩

theorem trialOrderThreeBilinear182_of_rank_four (hK4 : AllIncidenceRankFourBounds) :
    PrimeGap182.TrialOrderThreeBilinear182 :=
  trialOrderThreeBilinear182_of_secondary_family (incidenceSecondaryFamily182_of_rank_four hK4)

#print axioms incidenceSecondaryFamily182_of_rank_four
#print axioms trialOrderThreeBilinear182_of_rank_four

end PrimeGap182Audit

namespace PrimeGap182
open PrimeGap182Audit PrimeGap182Analytic TypeIII

theorem trialShiftedSourceEstimates182_of_local_inputs
    (hpublic : PublicPrimeLocalBounds182) (hK4 : AllIncidenceRankFourBounds)
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    (w : Fin 3) (h J : ℕ) : TrialShiftedSourceEstimates182 w h J :=
  trialShiftedSourceEstimates182 hpublic hC hlocal
    (trialOrderThreeBilinear182_of_rank_four hK4) w h J

theorem primeGapLiminf_le_182_of_local_inputs
    (hn : PhysicalSourceBounds182) (hpublic : PublicPrimeLocalBounds182)
    (hK4 : AllIncidenceRankFourBounds)
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀) :
    PrimeGap186.primeGapLiminf ≤ (182 : EReal) :=
  primeGapLiminf_le_182_of_local_and_orderThree hn hpublic hC hlocal
    (trialOrderThreeBilinear182_of_rank_four hK4)

theorem infinite_integer_translates182_of_local_inputs
    (hn : PhysicalSourceBounds182) (hpublic : PublicPrimeLocalBounds182)
    (hK4 : AllIncidenceRankFourBounds)
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    (H : Finset ℤ) (hH : H.card = 39)
    (hadm : ∀ p : ℕ, p.Prime → ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a) :
    Set.Infinite {n : ℤ | 2 ≤ (H.filter (fun h => (n + h).toNat.Prime)).card} :=
  infinite_integer_translates_of_local_and_orderThree182 hn hpublic hC hlocal
    (trialOrderThreeBilinear182_of_rank_four hK4) H hH hadm

theorem infinite_consecutive_prime_pairs182_of_local_inputs
    (hn : PhysicalSourceBounds182) (hpublic : PublicPrimeLocalBounds182)
    (hK4 : AllIncidenceRankFourBounds)
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀) :
    Set.Infinite {p : ℕ | p.Prime ∧ ∃ q : ℕ, p < q ∧ q.Prime ∧ q - p ≤ 182 ∧
      ∀ r : ℕ, p < r → r < q → ¬r.Prime} :=
  infinite_consecutive_prime_pairs_of_local_and_orderThree182 hn hpublic hC hlocal
    (trialOrderThreeBilinear182_of_rank_four hK4)

#print axioms trialShiftedSourceEstimates182_of_local_inputs
#print axioms primeGapLiminf_le_182_of_local_inputs
#print axioms infinite_integer_translates182_of_local_inputs
#print axioms infinite_consecutive_prime_pairs182_of_local_inputs

end PrimeGap182
