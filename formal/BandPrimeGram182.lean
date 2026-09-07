import SourceOrdinaryMoments182

/-! Prime Gram limits for actual canonical 38-coordinate arrays plus
weighted erasures of 39-coordinate arrays. The limit and coefficient
bounds follow from the proved harmonic and Selberg period estimates. -/

noncomputable section
open MeasureTheory Filter PrimeGap186 PrimeGap182.Selberg
open scoped BigOperators Topology

namespace PrimeGap182Analytic

open Classical in
def selbergDivisorSupport182 (z : (Fin 38 → ℕ) →₀ ℝ) : Finset (Fin 38 → ℕ) :=
  z.support.biUnion (fun r => Fintype.piFinset (fun j => (r j).divisors))

def SelbergCompatible182 (d e : Fin 38 → ℕ) : Prop :=
  ∀ j k : Fin 38, j ≠ k → Nat.Coprime (d j) (e k)

open Classical in
def selbergPrimeGram182 (z z' : (Fin 38 → ℕ) →₀ ℝ) : ℝ :=
  ∑ d ∈ selbergDivisorSupport182 z, ∑ e ∈ selbergDivisorSupport182 z',
    if ∀ j k : Fin 38, j ≠ k → Nat.Coprime (d j) (e k) then
      PrimeGap182.Selberg.selbergCoefficient z d * PrimeGap182.Selberg.selbergCoefficient z' e /
        (∏ j, ((Nat.lcm (d j) (e j)).totient : ℝ)) else 0

theorem erasedBandArray182_support_data {m : ℕ} (H : Finset ℕ) (a : Fin (m + 2) → ℝ)
    (i : Fin 39) (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (x : ℝ) (r : Fin 38 → ℕ)
    (hr : r ∈ (erasedBandArray182 H a i G F x).support) :
    Squarefree (∏ j, r j) ∧ ∀ j, r j ∈ (selbergPrimorial182 H x).divisors := by
  rcases Finset.mem_union.mp (Finsupp.support_add hr) with hr | hr
  · have h := canonicalBandArray182_support_data H a G x r hr
    exact ⟨h.1, h.2.1⟩
  · obtain ⟨s, hs, hsr⟩ := selbergErasedArray39_support_witness i
      (canonicalBandArray182 H a F x) r hr
    have h := canonicalBandArray182_support_data H a F x s hs
    have hdvd : (∏ j, r j) ∣ ∏ j, s j := by
      rw [← hsr, Fin.prod_univ_succAbove _ i]
      exact dvd_mul_left _ _
    exact ⟨h.1.squarefree_of_dvd hdvd, fun j => by simpa only [← hsr] using h.2.1 (i.succAbove j)⟩

theorem erasedBandArray182_divisor_support_data {m : ℕ} (H : Finset ℕ)
    (a : Fin (m + 2) → ℝ) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (x : ℝ) (d : Fin 38 → ℕ)
    (hd : d ∈ selbergDivisorSupport182 (erasedBandArray182 H a i G F x)) :
    Squarefree (∏ j, d j) ∧ Nat.Coprime (∏ j, d j) (presievingModulus H x) ∧
      (∏ j, d j) ∣ selbergPrimorial182 H x := by
  obtain ⟨r, hr, hdr⟩ := Finset.mem_biUnion.mp hd
  have hdiv (j : Fin 38) : d j ∣ r j := Nat.dvd_of_mem_divisors (Fintype.mem_piFinset.mp hdr j)
  obtain ⟨hrsq, hrq⟩ := erasedBandArray182_support_data H a i G F x r hr
  have hsq : Squarefree (∏ j, d j) :=
    hrsq.squarefree_of_dvd (Finset.prod_dvd_prod_of_dvd _ _ fun j _ => hdiv j)
  have hwhole : (∏ j, d j) ∣ selbergPrimorial182 H x := by
    apply hsq.isRadical 38 (selbergPrimorial182 H x)
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Finset.prod_dvd_prod_of_dvd (s := Finset.univ) d (fun _ => selbergPrimorial182 H x)
        (fun j _ => (hdiv j).trans (Nat.dvd_of_mem_divisors (hrq j)))
  have hqW : (selbergPrimorial182 H x).Coprime (presievingModulus H x) := by
    apply Nat.Coprime.prod_left
    intro p hp
    obtain ⟨hp, hpW⟩ := Finset.mem_filter.mp hp
    exact (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primesLE hp)).mpr hpW
  exact ⟨hsq, hqW.coprime_dvd_left hwhole, hwhole⟩

theorem erasedBandArray182_coefficient_log_bound {H : Finset ℕ} (hH : H.card = 39) {m : ℕ}
    (a : Fin (m + 2) → ℝ) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hbG : Bornology.IsBounded (Set.range G)) (hbF : Bornology.IsBounded (Set.range F)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      1 < x ∧ ∀ d : Fin 38 → ℕ,
        |PrimeGap182.Selberg.selbergCoefficient (erasedBandArray182 H a i G F x) d| ≤ C * Real.log x := by
  have h := canonical_and_erased_finite_coefficient_log_root_subpower
    (𝓗 := H) (h𝓗_card := hH) i selbergFragmentCap182
    (by norm_num [selbergFragmentCap182, selbergRho182]) a (fun _ : Fin 1 => (1 : ℝ))
    (fun _ => G) (fun _ => F) (fun _ => hbG) (fun _ => hbF)
  simpa only [Fin.sum_univ_one, one_smul, erasedBandArray182, canonicalBandArray182,
    selbergErasedArray39, selbergNormalizer182, selbergPrimorial182, selbergRho182,
    finPiFinset_eq_classical] using h.1

set_option maxHeartbeats 4000000 in
theorem erasedBandArray182_primeGram_tendsto {H : Finset ℕ} (hH : H.card = 39) {m : ℕ}
    (a : Fin (m + 2) → ℝ) (ha : StrictMono a) (ha0 : a 0 = 0)
    (haLast : a (Fin.last (m + 1)) = selbergFragmentCap182) (i : Fin 39)
    (G G' : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F F' : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hG : Measurable G) (hG' : Measurable G') (hF : Measurable F) (hF' : Measurable F')
    (hbG : Bornology.IsBounded (Set.range G)) (hbG' : Bornology.IsBounded (Set.range G'))
    (hbF : Bornology.IsBounded (Set.range F)) (hbF' : Bornology.IsBounded (Set.range F'))
    (hcG : ∀ᵐ Y ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a), ContinuousAt G Y)
    (hcG' : ∀ᵐ Y ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a), ContinuousAt G' Y)
    (hcF : ∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => selbergBandMeasure182 a), ContinuousAt F X)
    (hcF' : ∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => selbergBandMeasure182 a), ContinuousAt F' X) :
    Tendsto (fun x => selbergNormalizer182 H x ^ 38 *
      selbergPrimeGram182 (erasedBandArray182 H a i G F x) (erasedBandArray182 H a i G' F' x))
      atTop (nhds (∫ Y, bandCombinedFace182 a i G F Y * bandCombinedFace182 a i G' F' Y
        ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a))) := by
  obtain ⟨M, hM, hamp⟩ := erasedBandArray182_amplitude hH a i G F hbG hbF
  obtain ⟨M', hM', hamp'⟩ := erasedBandArray182_amplitude hH a i G' F' hbG' hbF'
  let z := erasedBandArray182 H a i G F
  let z' := erasedBandArray182 H a i G' F'
  let B := selbergNormalizer182 H
  let D (x : ℝ) := mixedHarmonic (fun r : Fin 38 → ℕ => ∏ k, ((r k).totient : ℝ)) (z x) (z' x)
  have hlim := erasedBandArray182_harmonic_tendsto (H := H) a ha ha0 haLast i G G' F F'
    hG hG' hF hF' hbG hbG' hbF hbF' hcG hcG' hcF hcF'
  have herr : Tendsto (fun x => B x ^ 38 * (selbergPrimeGram182 (z x) (z' x) - D x))
      atTop (nhds 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hcompare := selberg38_prime_bilinear_comparison (𝓗 := H) (h𝓗_card := hH)
      i selbergFragmentCap182 M M' (by norm_num [selbergFragmentCap182, selbergRho182])
      hM.le hM'.le (ε / 2) (half_pos hε)
    filter_upwards [hamp, hamp', hcompare] with x hx hx' hc
    have hB : 0 < B x := hc.1
    have hcomp := hc.2 (z x) (z' x)
      (erasedBandArray182_support_data H a i G F x)
      (erasedBandArray182_support_data H a i G' F' x) hx hx'
    have hcomp' : |selbergPrimeGram182 (z x) (z' x) - D x| ≤ (ε / 2) / B x ^ 38 := by
      simpa only [selbergPrimeGram182, selbergDivisorSupport182,
        D, B, mixedHarmonic, selbergNormalizer182, selbergRho182,
        finPiFinset_eq_classical] using hcomp
    have hh : |B x ^ 38 * (selbergPrimeGram182 (z x) (z' x) - D x)| ≤ ε / 2 := by
      rw [abs_mul, abs_of_pos (pow_pos hB 38)]
      exact (mul_le_mul_of_nonneg_left hcomp' (pow_pos hB 38).le).trans_eq
        (mul_div_cancel₀ _ (pow_pos hB 38).ne')
    simpa only [Real.dist_eq, sub_zero] using hh.trans_lt (half_lt_self hε)
  convert herr.add hlim using 1
  · funext x
    dsimp only [B, D, z, z']
    ring
  · simp only [zero_add]

#print axioms erasedBandArray182_divisor_support_data
#print axioms erasedBandArray182_coefficient_log_bound
#print axioms erasedBandArray182_primeGram_tendsto

end PrimeGap182Analytic
