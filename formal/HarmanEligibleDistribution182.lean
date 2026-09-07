import HarmanEligibleTuples182
import HarmanFiveBoxes182

/-! Distribution of the actual eligible five-prime source, followed by the
exact eligible-plus-collision source remainder. The only distribution
input is the explicit SourceBilinearEstimate. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

open Classical in
theorem sourceFiveEligible_coherent_log_saving_of_bilinear
    (j : ℕ) («ω» δ σ : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ)
    (hσgap : (1 / 2 : ℝ) - 41361 / 100000 < σ)
    (hretreat : ∃ r : ℝ, 0 < r ∧ «ω» + r < 1 / 4 ∧
      SourceBilinearEstimate j («ω» + r) (δ + r) σ)
    (L0 : ℝ → ℝ) (hL0 : ∀ x : ℝ, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0)) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ Real.exp 100 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ k : Fin 2,
      ∀ Y : Set.Ici (1 : ℝ), (Y : ℝ) = x ^ δ →
      ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
      ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
        let F := sourceFiveEligibleSequence x k (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊)
        let Q := (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω») * L0 x⌋₊).filter (fun q =>
          q ∣ (∏ p ∈ I, p) ∧ Nonempty (DenseDivisibilityWitness Y j q))
        (∑ q ∈ Q, ‖fullDiscrepancy F q a‖) ≤ K * x / (Real.log x) ^ A := by
  intro A hA
  obtain ⟨K, Xb, hK, hXb, hbound⟩ :=
    central_five_prime_boolean_cut_subpower_coherent_log_saving_of_bilinear
      j «ω» δ σ hω hδ hσgap hretreat L0 hL0 hL0sub A hA
  obtain ⟨Xe, hXe⟩ := eventually_sourceFive_envelope.exists_forall_of_atTop
  refine ⟨K, max Xb Xe, hK, hXb.trans (le_max_left _ _), ?_⟩
  intro x hx k Y hY I hI a ha F Q
  have hxb : Xb ≤ x := (le_max_left _ _).trans hx
  obtain ⟨hx1, he⟩ := hXe x ((le_max_right _ _).trans hx)
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hboolean : ∀ p ∈ sourceFivePrimeCarrier x,
      ∀ q ∈ sourceFivePrimeCarrier x,
      (∀ d ∈ sourceFiveEligibleMonomialCuts x,
        eligibleCutTest d p ↔ eligibleCutTest d q) →
        (sourceFiveEligiblePredicate x k p ↔ sourceFiveEligiblePredicate x k q) := by
    intro p hp q hq ht
    have hps := sourceFivePrimeCarrier_spec hx0 hp
    have hqs := sourceFivePrimeCarrier_spec hx0 hq
    exact sourceFiveEligibleMonomialCuts_boolean x hx1 k p q
      (fun i => (hps i).1) (fun i => (hqs i).1)
      (fun i => (hps i).2.1) (fun i => (hqs i).2.1)
      (fun i => (hps i).2.2) (fun i => (hqs i).2.2) ht
  have hb := hbound x hxb Y hY (sourceFiveEligibleMonomialCuts x)
    (sourceFiveEligiblePredicate x k) (sourceFiveEligibleMonomialCuts_card_le x)
    (sourceFiveEligibleMonomialCuts_data x hx0) hboolean
    (sourceFiveEligiblePredicate_central hx1 he k) I hI a ha
  dsimp only [F]
  rw [sourceFiveEligibleSequence_eq_tuple_sum hx1 he k]
  exact hb

theorem harman_subpower_height_le (β γ : ℝ) (hβγ : β < γ)
    (L0 : ℝ → ℝ) (hL0 : ∀ x : ℝ, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0)) :
    ∀ᶠ x : ℝ in atTop, x ^ β * L0 x ≤ x ^ γ := by
  have hsmall := (tendsto_order.mp hL0sub).2 (γ - β) (sub_pos.mpr hβγ)
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with x hs hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hL : L0 x ≤ x ^ (γ - β) := by
    apply (Real.log_le_log_iff (hL0 x) (Real.rpow_pos_of_pos hx0 _)).mp
    rw [Real.log_rpow hx0]
    exact ((div_lt_iff₀ (Real.log_pos hx)).mp hs).le
  calc
    _ ≤ x ^ β * x ^ (γ - β) :=
      mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg hx0.le _)
    _ = x ^ (β + (γ - β)) := (Real.rpow_add hx0 _ _).symm
    _ = _ := by congr 1; ring

open Classical in
theorem sourceFive_sub_sharpResidual_coherent_log_saving_of_bilinear
    (j : ℕ) («ω» δ σ : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ)
    (hlevel : (1 / 2 : ℝ) + 2 * «ω» < 53 / 100)
    (hσgap : (1 / 2 : ℝ) - 41361 / 100000 < σ)
    (hretreat : ∃ r : ℝ, 0 < r ∧ «ω» + r < 1 / 4 ∧
      SourceBilinearEstimate j («ω» + r) (δ + r) σ)
    (L0 : ℝ → ℝ) (hL0 : ∀ x : ℝ, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0)) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ Real.exp 100 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ k : Fin 2,
      ∀ Y : Set.Ici (1 : ℝ), (Y : ℝ) = x ^ δ →
      ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
      ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
        let F : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊, Finsupp.single n
          (((if k = 0 then sourceT5 x n else sourceU3 x n) - sharpResidualCount x k n : ℝ) : ℂ)
        let Q := (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω») * L0 x⌋₊).filter (fun q =>
          q ∣ (∏ p ∈ I, p) ∧ Nonempty (DenseDivisibilityWitness Y j q))
        (∑ q ∈ Q, ‖fullDiscrepancy F q a‖) ≤ K * x / (Real.log x) ^ A := by
  intro A hA
  obtain ⟨Ke, Xe, hKe, hXe, he⟩ :=
    sourceFiveEligible_coherent_log_saving_of_bilinear j «ω» δ σ hω hδ hσgap
      hretreat L0 hL0 hL0sub A hA
  obtain ⟨Kc, Xc, hKc, _hXc, hc⟩ := sourceFiveCollision_weighted_log_saving 0 A hA
  obtain ⟨Xg, hXg⟩ := eventually_sourceFive_envelope.exists_forall_of_atTop
  obtain ⟨Xl, hXl⟩ := (harman_subpower_height_le (1 / 2 + 2 * «ω»)
    (53 / 100) hlevel L0 hL0 hL0sub).exists_forall_of_atTop
  refine ⟨Ke + Kc, max Xe (max Xc (max Xg Xl)), by positivity,
    hXe.trans (le_max_left _ _), ?_⟩
  intro x hx k Y hY I hI a ha F Q
  have hxe : Xe ≤ x := (le_max_left _ _).trans hx
  have hxc : Xc ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxg : Xg ≤ x := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  have hxl : Xl ≤ x := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  obtain ⟨hx1, henv⟩ := hXg x hxg
  have hg : 2 * x < x ^ (6 * ((8639 : ℝ) / 50000)) :=
    henv.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hx1 (by norm_num))
  have hQ : Q ⊆ Finset.Icc 1 ⌊x ^ ((53 : ℝ) / 100)⌋₊ := by
    intro q hq
    obtain ⟨hqI, _⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hqI).1,
      (Finset.mem_Icc.mp hqI).2.trans (Nat.floor_mono (hXl x hxl))⟩
  have hqa : ∀ q ∈ Q, Nat.Coprime a q := by
    intro q hq
    exact ha.of_dvd_right (Finset.mem_filter.mp hq).2.1
  have hbE := he x hxe k Y hY I hI a ha
  have hbC := hc x hxc k (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊) (fun _ h => h)
    Q hQ (fun _ => a) hqa
  simp only [pow_zero, one_mul] at hbC
  have hF : F = sourceFiveEligibleSequence x k (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊) +
      sourceFiveCollisionSequence x k (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊) :=
    sharp_source_remainder_sequence hx1 hg k _ (fun _ h => h)
  calc
    _ ≤ (∑ q ∈ Q, ‖fullDiscrepancy
        (sourceFiveEligibleSequence x k (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊)) q a‖) +
        ∑ q ∈ Q, ‖fullDiscrepancy
          (sourceFiveCollisionSequence x k (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊)) q a‖ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro q _hq
      rw [hF, hbBoundary_fullDiscrepancy_add]
      exact norm_add_le _ _
    _ ≤ Ke * x / (Real.log x) ^ A + Kc * x / (Real.log x) ^ A := add_le_add hbE hbC
    _ = (Ke + Kc) * x / (Real.log x) ^ A := by ring

#print axioms sourceFiveEligible_coherent_log_saving_of_bilinear
#print axioms sourceFive_sub_sharpResidual_coherent_log_saving_of_bilinear

end PrimeGap182Analytic.Harman
