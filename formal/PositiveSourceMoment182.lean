import SourceFirstMoment182
import SourceMomentLimits182
import SourcePresieve182

/-! From the actual source-supported profiles to positive arithmetic
Selberg moments. The premises are the explicit coherent distribution
estimates and the proved profile energy; no moment limit or DHL statement
is supplied as a premise. -/

noncomputable section
open MeasureTheory Filter PrimeGap186 PrimeGap182Analytic
open scoped BigOperators Topology

namespace PrimeGap182.TrialSmoothProfiles182

theorem eventually_positive_bandPrimeMoment (P : TrialSmoothProfiles182)
    {H : Finset ℕ} (hH : H.card = 39)
    (hadm : ∀ p : ℕ, p.Prime → ∃ a ∈ Finset.range p, a ∉ H.image (fun h => h % p))
    (hs : P.CoherentSources H hH) (henergy : 0 < P.bandHybridEnergy SharpMean.sharpMass) :
    ∀ᶠ x : ℝ in atTop, ∃ res : ℕ,
      0 < bandPrimeMoment182 H P.a (H.orderEmbOfFin hH) P.F x res := by
  classical
  have hchoose (x : ℝ) : ∃ res : ℕ, ∀ i : Fin 39,
      Nat.Coprime (res + H.orderEmbOfFin hH i) (presievingModulus H x) := by
    obtain ⟨res, _, hr⟩ := exists_admissible_presieve_residue182 (𝓗 := H)
      (h𝓗_card := hH) (h𝓗_admissible := hadm) (presievingModulus H x) (presieving_pos H x)
    exact ⟨res, hr⟩
  choose res hres using hchoose
  let M := P.sieveMainCoefficient
  have hM : 0 < M := henergy.trans_le P.bandHybridEnergy_le_sieveMainCoefficient
  have hη : 0 < trialHybridLoss := by norm_num [trialHybridLoss, trialKappa, trialLambda]
  have hρ : 0 < selbergRho182 := by norm_num [selbergRho182]
  let ε : ℝ := M / (4 * trialHybridLoss * selbergRho182 * 39)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hnear : ∀ᶠ x : ℝ in atTop, M / 2 <
      P.sieveLinearMoment H (H.orderEmbOfFin hH) x (res x) / ordinaryMomentScale182 H x :=
    (P.sieveLinearMoment_normalized_limit hH hs res hres).eventually
      (eventually_gt_nhds (half_lt_self hM))
  have hEX : ∀ᶠ x : ℝ in atTop, ∀ i : Fin 39,
      bandSharpMoment182 H P.a (H.orderEmbOfFin hH) i (P.exceptionalFace i) P.F x (res x) ≤
        sieveMomentScale182 H x * (P.sieveKernelIntegral i + ε) :=
    eventually_all.mpr fun i => (P.sieve_exceptional_moment_upper hH i ε hε).mono
      fun x hx => hx (res x)
  filter_upwards [hnear, hEX, eventually_gt_atTop (1 : ℝ)] with x hx hEXx hx1
  refine ⟨res x, ?_⟩
  let Z := ordinaryMomentScale182 H x
  have hZ : 0 < Z := ordinaryMomentScale182_pos H x hx1
  have hnear' : (M / 2) * Z < P.sieveLinearMoment H (H.orderEmbOfFin hH) x (res x) :=
    (lt_div_iff₀ hZ).mp hx
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ => hEXx i
  have hsum' : (∑ i : Fin 39,
      bandSharpMoment182 H P.a (H.orderEmbOfFin hH) i (P.exceptionalFace i) P.F x (res x)) ≤
        sieveMomentScale182 H x * ((∑ i : Fin 39, P.sieveKernelIntegral i) + 39 * ε) := by
    simpa only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using hsum
  have hpenalty := mul_le_mul_of_nonneg_left hsum' hη.le
  have hloss : trialHybridLoss * sieveMomentScale182 H x * (39 * ε) = (M / 4) * Z := by
    rw [sieveMomentScale182_eq_rho_mul H x hx1]
    dsimp only [ε, Z]
    field_simp [hη.ne', hρ.ne']
  have hbridge : P.sieveLinearMoment H (H.orderEmbOfFin hH) x (res x) - (M / 4) * Z ≤
      (∑ i : Fin 39, ∑ k : Fin 6, sievePairCoefficient k *
        P.sievePairMoment H (H.orderEmbOfFin hH) i k x (res x)) -
          trialHybridLoss * (∑ i : Fin 39,
            bandSharpMoment182 H P.a (H.orderEmbOfFin hH) i (P.exceptionalFace i) P.F x (res x)) -
          bandOrdinaryMoment182 H P.a (H.orderEmbOfFin hH) P.F x (res x) := by
    unfold sieveLinearMoment
    nlinarith only [hpenalty, hloss]
  have hpos : 0 < P.sieveLinearMoment H (H.orderEmbOfFin hH) x (res x) - (M / 4) * Z := by
    nlinarith only [hnear', mul_pos (show 0 < M / 4 from div_pos hM (by norm_num)) hZ]
  exact hpos.trans_le (hbridge.trans (P.sieve_first_moment_lower hH x hx1 (res x)))

theorem positive_band_moments (P : TrialSmoothProfiles182) {H : Finset ℕ} (hH : H.card = 39)
    (hadm : ∀ p : ℕ, p.Prime → ∃ a ∈ Finset.range p, a ∉ H.image (fun h => h % p))
    (hs : P.CoherentSources H hH) (henergy : 0 < P.bandHybridEnergy SharpMean.sharpMass) :
    PositiveBandMoments182 H hH := by
  refine ⟨P.m, P.a, P.F, ?_⟩
  intro N
  exact ((eventually_gt_atTop (N : ℝ)).and
    (P.eventually_positive_bandPrimeMoment hH hadm hs henergy)).exists

#print axioms eventually_positive_bandPrimeMoment
#print axioms positive_band_moments

end PrimeGap182.TrialSmoothProfiles182

namespace PrimeGap182

theorem positive_band_moments_of_physical_sources182 (hn : PhysicalSourceBounds182)
    (H : Finset ℕ) (hH : H.card = 39)
    (hadm : ∀ p : ℕ, p.Prime → ∃ a ∈ Finset.range p, a ∉ H.image (fun h => h % p))
    (hs : ∀ P : TrialSmoothProfiles182, P.CoherentSources H hH) :
    PositiveBandMoments182 H hH := by
  obtain ⟨P, hP⟩ := positive_band_profiles_at_actual_sharp_deficit182 hn
  exact P.positive_band_moments hH hadm (hs P) hP

#print axioms positive_band_moments_of_physical_sources182

end PrimeGap182
