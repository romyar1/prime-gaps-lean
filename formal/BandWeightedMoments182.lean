import BandDiscrepancy182
import BandMomentNormalization182

/-! Actual weighted bilinear moments of the finite-band arrays. The sole
analytic premise here is the coherent full-discrepancy estimate on the
explicit supported moduli. No arithmetic moment limit is assumed. -/

noncomputable section
open MeasureTheory Filter PrimeGap186
open scoped BigOperators Topology

namespace PrimeGap182Analytic

theorem erasedBandArray182_weighted_log_error {H : Finset ℕ} (hH : H.card = 39)
    {m : ℕ} (a : Fin (m + 2) → ℝ) (i : Fin 39) (w : Fin 3)
    (G G' : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F F' : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hbG : Bornology.IsBounded (Set.range G)) (hbG' : Bornology.IsBounded (Set.range G'))
    (hbF : Bornology.IsBounded (Set.range F)) (hbF' : Bornology.IsBounded (Set.range F'))
    (hSource : BandCoherentDiscrepancy182 H (H.orderEmbOfFin hH) i w
      (erasedBandArray182 H a i G F) (erasedBandArray182 H a i G' F')) :
    ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ res : ℕ, Nat.Coprime (res + H.orderEmbOfFin hH i) (presievingModulus H x) →
        |bandWeightedBilinear182 H (H.orderEmbOfFin hH) i w
            (erasedBandArray182 H a i G F x) (erasedBandArray182 H a i G' F' x) x res -
          ((∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊, selbergWeight182 w x (n + H.orderEmbOfFin hH i)) /
            ((presievingModulus H x).totient : ℝ)) *
              selbergPrimeGram182 (erasedBandArray182 H a i G F x)
                (erasedBandArray182 H a i G' F' x)| ≤ K * x / (Real.log x) ^ A := by
  obtain ⟨C, hC, hb⟩ := erasedBandArray182_coefficient_log_bound hH a i G F hbG hbF
  obtain ⟨C', hC', hb'⟩ := erasedBandArray182_coefficient_log_bound hH a i G' F' hbG' hbF'
  intro A hA
  obtain ⟨K, hK, hsource⟩ := hSource A hA
  refine ⟨C * C' * K, mul_pos (mul_pos hC hC') hK, ?_⟩
  filter_upwards [hb, hb', hsource, selbergCarrier182_prime_cap H] with x hx hx' hs hcap
  intro res hres
  have hlog : 0 < Real.log x := Real.log_pos hcap.1
  have hfinite := erasedBandArray182_finite_weighted_moment hH a i w G G' F F' x hcap.1 hcap.2
    (C * Real.log x) (C' * Real.log x) (K * x / (Real.log x) ^ (A + 2))
    (mul_pos hC hlog).le (mul_pos hC' hlog).le hx.2 hx'.2 hs res hres
  convert hfinite using 1
  rw [Real.rpow_add hlog, Real.rpow_two]
  field_simp [hlog.ne']

theorem erasedBandArray182_weighted_moment {H : Finset ℕ} (hH : H.card = 39)
    {m : ℕ} (a : Fin (m + 2) → ℝ) (ha : StrictMono a) (ha0 : a 0 = 0)
    (haLast : a (Fin.last (m + 1)) = selbergFragmentCap182) (i : Fin 39) (w : Fin 3)
    (G G' : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F F' : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hG : Measurable G) (hG' : Measurable G') (hF : Measurable F) (hF' : Measurable F')
    (hbG : Bornology.IsBounded (Set.range G)) (hbG' : Bornology.IsBounded (Set.range G'))
    (hbF : Bornology.IsBounded (Set.range F)) (hbF' : Bornology.IsBounded (Set.range F'))
    (hcG : ∀ᵐ Y ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a), ContinuousAt G Y)
    (hcG' : ∀ᵐ Y ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a), ContinuousAt G' Y)
    (hcF : ∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => selbergBandMeasure182 a), ContinuousAt F X)
    (hcF' : ∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => selbergBandMeasure182 a), ContinuousAt F' X)
    (hSource : BandCoherentDiscrepancy182 H (H.orderEmbOfFin hH) i w
      (erasedBandArray182 H a i G F) (erasedBandArray182 H a i G' F')) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
      ∀ res : ℕ, Nat.Coprime (res + H.orderEmbOfFin hH i) (presievingModulus H x) →
        |bandWeightedBilinear182 H (H.orderEmbOfFin hH) i w
            (erasedBandArray182 H a i G F x) (erasedBandArray182 H a i G' F' x) x res -
          (selbergWeightMean182 w *
            (∫ Y, bandCombinedFace182 a i G F Y * bandCombinedFace182 a i G' F' Y
              ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a))) *
            sieveMomentScale182 H x| ≤ ε * sieveMomentScale182 H x := by
  have hnorm := selberg39_moment_from_diagonal_error (𝓗 := H)
    (fun x res => bandWeightedBilinear182 H (H.orderEmbOfFin hH) i w
      (erasedBandArray182 H a i G F x) (erasedBandArray182 H a i G' F' x) x res)
    (fun x res => Nat.Coprime (res + H.orderEmbOfFin hH i) (presievingModulus H x))
    (fun x => ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊, selbergWeight182 w x (n + H.orderEmbOfFin hH i))
    (fun x => selbergPrimeGram182 (erasedBandArray182 H a i G F x) (erasedBandArray182 H a i G' F' x))
    (selbergWeightMean182 w)
    (∫ Y, bandCombinedFace182 a i G F Y * bandCombinedFace182 a i G' F' Y
      ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a))
    (selbergWeight182_shifted_mean w (H.orderEmbOfFin hH i))
    (erasedBandArray182_primeGram_tendsto hH a ha ha0 haLast i G G' F F'
      hG hG' hF hF' hbG hbG' hbF hbF' hcG hcG' hcF hcF')
    (erasedBandArray182_weighted_log_error hH a i w G G' F F' hbG hbG' hbF hbF' hSource)
  intro ε hε
  have hρ : 0 < selbergRho182 := by norm_num [selbergRho182]
  filter_upwards [hnorm (ε * selbergRho182) (mul_pos hε hρ),
    eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro res hres
  have hr := hx res hres
  rw [sieveMomentScale182_eq_rho_mul H x hx1]
  convert hr using 1 <;>
    simp only [selbergRho182, ordinaryMomentScale182, selbergNormalizer182] <;> ring

#print axioms erasedBandArray182_weighted_log_error
#print axioms erasedBandArray182_weighted_moment

end PrimeGap182Analytic
