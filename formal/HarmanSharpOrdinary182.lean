import HarmanEligibleTuples182
import HarmanOrdinaryBoxes182

/-! Ordinary distribution below one-half for the actual squarefree sharp
residual and sharp defect. The tuple identity retains the distinct-prime
restriction. All boundary, finite tuple, and BV consequences are proved. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

open Classical in
theorem sharpResidual_closed_eq_tuple_sum {x : ℝ} (hx : 1 < x)
    (he : 2 * x ≤ x ^ ((10001 : ℝ) / 10000)) (j : Fin 2) :
    (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
      Finsupp.single n (sharpResidualCount x j n : ℂ)) =
      ∑ p ∈ sourceFivePrimeCarrier x, Finsupp.single (∏ i, p i)
        (if sourceFiveSharpPredicate x j p then (1 : ℂ) else 0) := by
  convert sourceFive_filteredSequence_eq_tuple_sum hx he j
      (fun p => Function.Injective p ∧ fivePairCaps x p) using 1
  · apply Finset.sum_congr rfl
    intro n hn
    have hnx : x ≤ (n : ℝ) := Nat.ceil_le.mp (Finset.mem_Icc.mp hn).1
    unfold sharpResidualCount
    rw [sharpResidualTuples_eq_source_filter hx n hnx j]
    simp only [Complex.ofReal_natCast]
    congr
  · apply Finset.sum_congr rfl
    intro p _hp
    unfold sourceFiveSharpPredicate
    congr

open Classical in
theorem sharpResidualCount_ordinary_bv_log_saving
    (θ : ℝ) (hθ0 : 0 < θ) (hθ : θ < 1 / 2) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ Real.exp 100 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ j : Fin 2,
      ∀ a : ℕ → ℕ,
      (∀ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, Nat.Coprime (a q) q) →
        (∑ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, ‖fullDiscrepancy
          (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
            Finsupp.single n (sharpResidualCount x j n : ℂ)) q (a q)‖) ≤
          K * x / (Real.log x) ^ A := by
  intro A hA
  obtain ⟨K, Xb, hK, hXb, hbound⟩ :=
    five_prime_boolean_cut_ordinary_bv_log_saving θ hθ0 hθ A hA
  obtain ⟨Xe, hXe⟩ := eventually_sourceFive_envelope.exists_forall_of_atTop
  refine ⟨K, max Xb Xe, hK, hXb.trans (le_max_left _ _), ?_⟩
  intro x hx j a ha
  have hxb : Xb ≤ x := (le_max_left _ _).trans hx
  obtain ⟨hx1, he⟩ := hXe x ((le_max_right _ _).trans hx)
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hboolean : ∀ p ∈ sourceFivePrimeCarrier x,
      ∀ q ∈ sourceFivePrimeCarrier x,
      (∀ d ∈ sourceFiveEligibleMonomialCuts x,
        eligibleCutTest d p ↔ eligibleCutTest d q) →
        (sourceFiveSharpPredicate x j p ↔ sourceFiveSharpPredicate x j q) := by
    intro p hp q hq ht
    have hps := sourceFivePrimeCarrier_spec hx0 hp
    have hqs := sourceFivePrimeCarrier_spec hx0 hq
    exact sourceFiveSharpMonomialCuts_boolean x hx1 j p q
      (fun i => (hps i).1) (fun i => (hqs i).1)
      (fun i => (hps i).2.1) (fun i => (hqs i).2.1)
      (fun i => (hps i).2.2) (fun i => (hqs i).2.2) ht
  have hb := hbound x hxb (sourceFiveEligibleMonomialCuts x)
    (sourceFiveSharpPredicate x j) (sourceFiveEligibleMonomialCuts_card_le x)
    (sourceFiveEligibleMonomialCuts_data x hx0) hboolean
    (fun _ _ h => h.1) (Finset.Icc 1 ⌊x ^ θ⌋₊) (fun _ h => h) a ha
  rw [sharpResidual_closed_eq_tuple_sum hx1 he j]
  exact hb

open Classical in
theorem sharpDefect_closed_eq_add_residuals (x : ℝ) :
    (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
      Finsupp.single n (sharpDefect x (41361 / 100000) n : ℂ)) =
    (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
      Finsupp.single n (sharpResidualCount x 0 n : ℂ)) +
    ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
      Finsupp.single n (sharpResidualCount x 1 n : ℂ) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  simp only [sharpDefect_eq_residual_counts, sharpResidualCount,
    Complex.ofReal_add, Finsupp.single_add]

open Classical in
theorem sharpDefect_ordinary_bv_log_saving
    (θ : ℝ) (hθ0 : 0 < θ) (hθ : θ < 1 / 2) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ Real.exp 100 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ a : ℕ → ℕ,
      (∀ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, Nat.Coprime (a q) q) →
        (∑ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, ‖fullDiscrepancy
          (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
            Finsupp.single n (sharpDefect x (41361 / 100000) n : ℂ)) q (a q)‖) ≤
          K * x / (Real.log x) ^ A := by
  intro A hA
  obtain ⟨K, X, hK, hX, hb⟩ := sharpResidualCount_ordinary_bv_log_saving θ hθ0 hθ A hA
  refine ⟨2 * K, X, by positivity, hX, ?_⟩
  intro x hx a ha
  have h0 := hb x hx 0 a ha
  have h1 := hb x hx 1 a ha
  rw [sharpDefect_closed_eq_add_residuals]
  calc
    _ ≤ (∑ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, ‖fullDiscrepancy
        (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
          Finsupp.single n (sharpResidualCount x 0 n : ℂ)) q (a q)‖) +
        ∑ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, ‖fullDiscrepancy
          (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
            Finsupp.single n (sharpResidualCount x 1 n : ℂ)) q (a q)‖ := by
      simpa only [pow_zero, one_mul] using hbBoundary_weighted_discrepancy_add_le
        (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
          Finsupp.single n (sharpResidualCount x 0 n : ℂ))
        (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
          Finsupp.single n (sharpResidualCount x 1 n : ℂ))
        (Finset.Icc 1 ⌊x ^ θ⌋₊) a 0
    _ ≤ K * x / (Real.log x) ^ A + K * x / (Real.log x) ^ A := add_le_add h0 h1
    _ = _ := by ring

open Classical in
theorem sharpMinorant_ordinary_bv_log_saving
    (θ : ℝ) (hθ0 : 0 < θ) (hθ : θ < 1 / 2) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ Real.exp 100 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ a : ℕ → ℕ,
      (∀ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, Nat.Coprime (a q) q) →
        (∑ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, ‖fullDiscrepancy
          (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
            Finsupp.single n (sharpMinorant x (41361 / 100000) n : ℂ)) q (a q)‖) ≤
          K * x / (Real.log x) ^ A := by
  intro A hA
  obtain ⟨Kp, Xp, hKp, _hXp, hp⟩ :=
    primeIndicator_dyadic_allModuli_bombieriVinogradov θ hθ0 hθ A hA
  obtain ⟨Kd, Xd, hKd, hXd, hd⟩ := sharpDefect_ordinary_bv_log_saving θ hθ0 hθ A hA
  refine ⟨Kp + Kd, max Xp Xd, by positivity, hXd.trans (le_max_right _ _), ?_⟩
  intro x hx a ha
  let N := Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊
  let Q := Finset.Icc 1 ⌊x ^ θ⌋₊
  let P : ℕ →₀ ℂ := ∑ n ∈ N, Finsupp.single n (if n.Prime then 1 else 0)
  let D : ℕ →₀ ℂ := ∑ n ∈ N,
    Finsupp.single n (sharpDefect x (41361 / 100000) n : ℂ)
  have hΔ (q b : ℕ) : fullDiscrepancy
      (∑ n ∈ N, Finsupp.single n (sharpMinorant x (41361 / 100000) n : ℂ)) q b =
      fullDiscrepancy P q b - fullDiscrepancy D q b := by
    simp only [P, D, fullDiscrepancy_sample, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    simp only [sharpMinorant, Complex.ofReal_sub, apply_ite Complex.ofReal,
      Complex.ofReal_zero, Complex.ofReal_one]
    split_ifs <;> ring
  have hbP := hp x ((le_max_left _ _).trans hx) Q (fun _ h => h) a ha
  have hbD := hd x ((le_max_right _ _).trans hx) a ha
  calc
    _ ≤ (∑ q ∈ Q, ‖fullDiscrepancy P q (a q)‖) +
        ∑ q ∈ Q, ‖fullDiscrepancy D q (a q)‖ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro q _hq
      rw [hΔ]
      exact norm_sub_le _ _
    _ ≤ Kp * x / (Real.log x) ^ A + Kd * x / (Real.log x) ^ A := add_le_add hbP hbD
    _ = _ := by ring

#print axioms sharpResidual_closed_eq_tuple_sum
#print axioms sharpResidualCount_ordinary_bv_log_saving
#print axioms sharpDefect_ordinary_bv_log_saving
#print axioms sharpMinorant_ordinary_bv_log_saving

end PrimeGap182Analytic.Harman
