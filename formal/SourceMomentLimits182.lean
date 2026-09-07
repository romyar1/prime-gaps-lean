import SourcePairingEnergy182

/-! Normalized limits of the actual six source pairings and ordinary
square for an arbitrary choice of admissible presieving residues. -/

noncomputable section
open MeasureTheory Filter PrimeGap186 PrimeGap182Analytic
open scoped BigOperators Topology

namespace PrimeGap182Analytic

theorem tendsto_div_of_uniform_error182 (S Z : ℝ → ℝ) (L : ℝ)
    (hZ : ∀ᶠ x : ℝ in atTop, 0 < Z x)
    (hS : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, |S x - Z x * L| ≤ ε * Z x) :
    Tendsto (fun x => S x / Z x) atTop (nhds L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hZ, hS (ε / 2) (half_pos hε)] with x hx hs
  have heq : S x / Z x - L = (S x - Z x * L) / Z x := by field_simp
  rw [Real.dist_eq, heq, abs_div, abs_of_pos hx]
  exact ((div_le_iff₀ hx).mpr hs).trans_lt (half_lt_self hε)

end PrimeGap182Analytic

namespace PrimeGap182.TrialSmoothProfiles182

theorem sieve_pair_normalized_limit (P : TrialSmoothProfiles182) {H : Finset ℕ} (hH : H.card = 39)
    (hs : P.CoherentSources H hH) (res : ℝ → ℕ)
    (hres : ∀ x (i : Fin 39), Nat.Coprime (res x + H.orderEmbOfFin hH i) (presievingModulus H x))
    (i : Fin 39) (k : Fin 6) :
    Tendsto (fun x => P.sievePairMoment H (H.orderEmbOfFin hH) i k x (res x) /
      ordinaryMomentScale182 H x) atTop
      (nhds (selbergRho182 * (selbergWeightMean182 (sievePairWeight k) * P.sievePairIntegral i k))) := by
  have hp := tendsto_div_of_uniform_error182
    (fun x => P.sievePairMoment H (H.orderEmbOfFin hH) i k x (res x))
    (sieveMomentScale182 H) (selbergWeightMean182 (sievePairWeight k) * P.sievePairIntegral i k)
    ((eventually_gt_atTop (1 : ℝ)).mono fun x hx => sieveMomentScale182_pos H x hx)
    (by
      intro ε hε
      filter_upwards [P.sieve_pair_moment hH hs i k ε hε] with x hx
      simpa only [mul_comm] using hx (res x) (hres x i))
  apply (hp.const_mul selbergRho182).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [sieveMomentScale182_eq_rho_mul H x hx]
  field_simp [show selbergRho182 ≠ 0 by norm_num [selbergRho182]]

theorem ordinary_square_normalized_limit (P : TrialSmoothProfiles182) {H : Finset ℕ}
    (hH : H.card = 39) (res : ℝ → ℕ) :
    Tendsto (fun x => bandOrdinaryMoment182 H P.a (H.orderEmbOfFin hH) P.F x (res x) /
      ordinaryMomentScale182 H x) atTop
      (nhds (∫ X, P.F X ^ 2 ∂Measure.pi (fun _ : Fin 39 => selbergBandMeasure182 P.a))) := by
  apply tendsto_div_of_uniform_error182
  · exact (eventually_gt_atTop (1 : ℝ)).mono fun x hx => ordinaryMomentScale182_pos H x hx
  · intro ε hε
    exact (P.ordinary_square_moment hH ε hε).mono fun x hx => hx (res x)

def sieveLinearMoment (P : TrialSmoothProfiles182) (H : Finset ℕ) (h : Fin 39 → ℕ)
    (x : ℝ) (res : ℕ) : ℝ :=
  (∑ i : Fin 39, ∑ k : Fin 6, sievePairCoefficient k * P.sievePairMoment H h i k x res) -
    trialHybridLoss * sieveMomentScale182 H x * (∑ i : Fin 39, P.sieveKernelIntegral i) -
      bandOrdinaryMoment182 H P.a h P.F x res

theorem sieveLinearMoment_normalized_limit (P : TrialSmoothProfiles182) {H : Finset ℕ}
    (hH : H.card = 39) (hs : P.CoherentSources H hH) (res : ℝ → ℕ)
    (hres : ∀ x (i : Fin 39), Nat.Coprime (res x + H.orderEmbOfFin hH i) (presievingModulus H x)) :
    Tendsto (fun x => P.sieveLinearMoment H (H.orderEmbOfFin hH) x (res x) /
      ordinaryMomentScale182 H x) atTop (nhds P.sieveMainCoefficient) := by
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin 39)) (fun i _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin 6)) (fun k _ =>
      (P.sieve_pair_normalized_limit hH hs res hres i k).const_mul (sievePairCoefficient k)))
  have hh := (hsum.sub_const (trialHybridLoss * selbergRho182 *
    (∑ i : Fin 39, P.sieveKernelIntegral i))).sub (P.ordinary_square_normalized_limit hH res)
  have hlimit : (∑ i : Fin 39, ∑ k : Fin 6, sievePairCoefficient k *
      (selbergRho182 * (selbergWeightMean182 (sievePairWeight k) * P.sievePairIntegral i k))) -
        trialHybridLoss * selbergRho182 * (∑ i : Fin 39, P.sieveKernelIntegral i) -
          (∫ X, P.F X ^ 2 ∂Measure.pi (fun _ : Fin 39 => selbergBandMeasure182 P.a)) =
            P.sieveMainCoefficient := by
    unfold sieveMainCoefficient
    simp only [Finset.sum_sub_distrib, mul_sub, Finset.mul_sum, selbergRho182, trialRhoStar, Rat.cast_div,
      Rat.cast_ofNat]
    congr 1
    apply congrArg₂ (· - ·)
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  rw [hlimit] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  unfold sieveLinearMoment
  rw [sieveMomentScale182_eq_rho_mul H x hx]
  simp only [sub_div, Finset.sum_div]
  have hZ := (ordinaryMomentScale182_pos H x hx).ne'
  field_simp [hZ]

#print axioms sieve_pair_normalized_limit
#print axioms sieveLinearMoment_normalized_limit

end PrimeGap182.TrialSmoothProfiles182
