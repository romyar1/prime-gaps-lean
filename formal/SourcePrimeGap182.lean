import SourceCoherentAssembly182
import PositiveSourceMoment182

/-! Terminal consequences of the explicit analytic source estimates and
the 262 physical numerical bounds. All support geometry, restoration,
approximation, arithmetic moments, and prime detection are derived.
The analytic source-estimate bundle remains an explicit input here. -/

noncomputable section
open PrimeGap182Analytic

namespace PrimeGap182

theorem positive_band_moments_of_source_estimates182 (hn : PhysicalSourceBounds182)
    (hs : ∀ w : Fin 3, ∀ h : ℕ, TrialShiftedSourceEstimates182 w h 13)
    (H : Finset ℕ) (hH : H.card = 39)
    (hadm : ∀ p : ℕ, p.Prime → ∃ a ∈ Finset.range p, a ∉ H.image (fun h => h % p)) :
    PositiveBandMoments182 H hH :=
  positive_band_moments_of_physical_sources182 hn H hH hadm
    (fun P => P.coherent_sources_of_estimates H hH (fun i k =>
      hs (TrialSmoothProfiles182.sievePairWeight k) (H.orderEmbOfFin hH i)))

theorem infinite_integer_translates_of_source_estimates182 (hn : PhysicalSourceBounds182)
    (hs : ∀ w : Fin 3, ∀ h : ℕ, TrialShiftedSourceEstimates182 w h 13)
    (H : Finset ℤ) (hH : H.card = 39)
    (hadm : ∀ p : ℕ, p.Prime → ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a) :
    Set.Infinite {n : ℤ | 2 ≤ (H.filter (fun h => (n + h).toNat.Prime)).card} :=
  infinite_int_prime_translates_of_band_moments182
    (positive_band_moments_of_source_estimates182 hn hs) H hH hadm

theorem infinite_consecutive_prime_pairs_of_source_estimates182 (hn : PhysicalSourceBounds182)
    (hs : ∀ w : Fin 3, ∀ h : ℕ, TrialShiftedSourceEstimates182 w h 13) :
    Set.Infinite {p : ℕ | p.Prime ∧ ∃ q : ℕ, p < q ∧ q.Prime ∧ q - p ≤ 182 ∧
      ∀ r : ℕ, p < r → r < q → ¬r.Prime} :=
  infinite_consecutive_prime_pairs_le_182_of_band_moments
    (positive_band_moments_of_source_estimates182 hn hs tuple182 tuple182_card tuple182_admissible)

theorem primeGapLiminf_le_182_of_source_estimates (hn : PhysicalSourceBounds182)
    (hs : ∀ w : Fin 3, ∀ h : ℕ, TrialShiftedSourceEstimates182 w h 13) :
    PrimeGap186.primeGapLiminf ≤ (182 : EReal) :=
  primeGapLiminf_le_182_of_band_moments
    (positive_band_moments_of_source_estimates182 hn hs tuple182 tuple182_card tuple182_admissible)

#print axioms positive_band_moments_of_source_estimates182
#print axioms infinite_integer_translates_of_source_estimates182
#print axioms infinite_consecutive_prime_pairs_of_source_estimates182
#print axioms primeGapLiminf_le_182_of_source_estimates

end PrimeGap182
