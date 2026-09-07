import SourceHighGamma182
import SourceDyadicGlobal182
import SourceIncidenceParameters182
import TrialSourceDistribution182

/-! The entire order-three source distribution follows from the explicit
secondary incidence family. The positive working-parameter retreat and
the arbitrarily small epsilon are chosen here, then the proved low and
high dyadic estimates are joined and transferred to actual source sums. -/

noncomputable section
open PrimeGap182 PrimeGap182Analytic.Harman
namespace PrimeGap182Audit

theorem sourceBilinearEstimate_three_of_secondary_family
    (hfamily : IncidenceSecondaryFamily182)
    {«ω» δ σ γhi : ℝ} (h : IncidenceBilinearWindow «ω» δ σ γhi) :
    SourceBilinearEstimate 3 «ω» δ σ := by
  obtain ⟨r, hr, hw⟩ := h.retreat
  obtain ⟨ε₀, hε₀, hsecondary⟩ :=
    hfamily («ω» + r) (δ + r) (1 / 2 - σ) γhi hw.hω hw.hδ
      hw.h1 hw.h2 hw.h3 hw.h4 hw.h5
  obtain ⟨ε, hε, hεsmall₀, hεsmallδ, hεsmall,
    hεδ, hγmin, hγsource, hγmax, hγhigh⟩ :=
    hw.choose_epsilon δ ε₀ (by linarith only [hr]) hε₀
  obtain ⟨hωsmall, hδsmall, hworking, _, _⟩ := hw.coarse
  have hLow := sourceDyadicDeltaZeroEstimate_of_incidence
    («ω» + r) (δ + r) ε (1 / 2 - σ) γhi
    hw.hω hw.hδ hε hωsmall hδsmall hεsmall hγmin hγsource hγmax
    (hsecondary ε hε hεsmall₀)
  have hHigh := sourceDyadicDeltaZeroEstimate_largeGamma
    («ω» + r) (δ + r) ε hw.hω hw.hδ hε hworking hεsmallδ
  have hFull : SourceDyadicDeltaZeroEstimate («ω» + r) (δ + r) ε
      (1 / 2 - σ) (1 / 2) :=
    hLow.join (hHigh.mono_range hγhigh le_rfl)
  intro ι
  exact sourceBilinearEstimate_three_of_dyadic
    «ω» δ σ («ω» + r) (δ + r) ε h.hω h.hδ h.hσ h.hσupper
    (by linarith only [hr]) (by linarith only [hr]) hεδ
    (by linarith only [hωsmall]) hε (by linarith only [hεsmall]) hFull

theorem trialOrderThreeBilinear182_of_secondary_family
    (hfamily : IncidenceSecondaryFamily182) : TrialOrderThreeBilinear182 := by
  intro row hrow hj
  have hrow' : row ∈ trialSourceRows 1 := by simpa [trialSourceRows] using hrow
  have hg := (trialSourceRows_minorant_analytic 1 row hrow').cast_real
  rw [hj] at hg
  intro ι
  exact sourceBilinearEstimate_three_of_secondary_family hfamily
    (incidenceBilinearWindow_of_minorant_guards hg)

#print axioms sourceBilinearEstimate_three_of_secondary_family
#print axioms trialOrderThreeBilinear182_of_secondary_family

end PrimeGap182Audit
