import SourceCoherentAssembly182
import HarmanSharpOrdinary182

/-! Ordinary BV for the three actual sieve weights, with arbitrary
divisor weights and fixed shifts. This discharges the all-moduli base
field of TrialShiftedSourceEstimates182 without an analytic premise. -/

noncomputable section
open PrimeGap186 PrimeGap182Analytic Filter
open scoped BigOperators Topology

namespace PrimeGap182

theorem selbergClosedSequence182_prime_eq (x : ℝ) :
    selbergClosedSequence182 0 x = ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
      Finsupp.single n (if n.Prime then (1 : ℂ) else 0) := by
  classical
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  dsimp [selbergWeight182, primeIndicator]
  split_ifs <;> rfl

theorem selbergClosedSequence182_ordinary_bv (w : Fin 3) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ : θ < 1 / 2) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ 1 < X ∧
      ∀ x : ℝ, X ≤ x → ∀ a : ℕ → ℕ,
      (∀ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, Nat.Coprime (a q) q) →
        (∑ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊,
          ‖fullDiscrepancy (selbergClosedSequence182 w x) q (a q)‖) ≤
            K * x / (Real.log x) ^ A := by
  classical
  intro A hA
  fin_cases w
  · obtain ⟨K, X, hK, hX, hb⟩ :=
      primeIndicator_dyadic_allModuli_bombieriVinogradov θ hθ0 hθ A hA
    refine ⟨K, X, hK, (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hX, ?_⟩
    intro x hx a ha
    change (∑ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊,
      ‖fullDiscrepancy (selbergClosedSequence182 0 x) q (a q)‖) ≤ _
    rw [selbergClosedSequence182_prime_eq]
    exact hb x hx _ (fun _ h => h) a ha
  · obtain ⟨K, X, hK, hX, hb⟩ :=
      Harman.sharpMinorant_ordinary_bv_log_saving θ hθ0 hθ A hA
    refine ⟨K, X, hK, (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 100)).trans_le hX, ?_⟩
    intro x hx a ha
    exact hb x hx a ha
  · obtain ⟨K, X, hK, hX, hb⟩ :=
      Harman.sharpDefect_ordinary_bv_log_saving θ hθ0 hθ A hA
    refine ⟨K, X, hK, (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 100)).trans_le hX, ?_⟩
    intro x hx a ha
    exact hb x hx a ha

theorem selbergClosedSequence182_weighted_ordinary_bv (w : Fin 3) (J : ℕ) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ : θ < 1 / 2) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ 1 < X ∧
      ∀ x : ℝ, X ≤ x → ∀ a : ℕ → ℕ,
      (∀ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, Nat.Coprime (a q) q) →
        (∑ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊,
          (q.divisors.card : ℝ) ^ J * ‖fullDiscrepancy (selbergClosedSequence182 w x) q (a q)‖) ≤
            K * x / (Real.log x) ^ A := by
  intro A hA
  obtain ⟨P, Kc, Xc, hKc, _hXc, hcrude⟩ :=
    selbergWeight_divisor_weight_log_growth θ hθ0 (by linarith) (2 * J)
  obtain ⟨Ks, Xs, hKs, hXs, hsmall⟩ :=
    selbergClosedSequence182_ordinary_bv w θ hθ0 hθ (2 * A + (P : ℝ)) (by positivity)
  refine ⟨Ks + Kc, max Xs Xc, add_pos hKs hKc, hXs.trans_le (le_max_left _ _), ?_⟩
  intro x hx a ha
  have hxs : Xs ≤ x := (le_max_left _ _).trans hx
  have hxc : Xc ≤ x := (le_max_right _ _).trans hx
  have hx1 : 1 < x := hXs.trans_le hxs
  exact sum_divisor_weighted_log_saving_of_two_bounds
    (Finset.Icc 1 ⌊x ^ θ⌋₊) J (fun q => ‖fullDiscrepancy (selbergClosedSequence182 w x) q (a q)‖)
    (fun q _ => norm_nonneg _) x (Real.log x) A Ks Kc P
    (zero_lt_one.trans hx1).le (Real.log_pos hx1) hKs hKc (hsmall x hxs a ha)
    (hcrude x hxc w _ (fun _ h => h) a ha)

theorem selbergShiftedSequence182_weighted_ordinary_bv (w : Fin 3) (h J : ℕ) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ : θ < 1 / 2) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ 1 < X ∧
      ∀ x : ℝ, X ≤ x → ∀ a : ℕ → ℕ,
      (∀ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, Nat.Coprime (a q) q) →
        (∑ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊,
          (q.divisors.card : ℝ) ^ J * ‖fullDiscrepancy (selbergShiftedSequence182 w h x) q (a q)‖) ≤
            K * x / (Real.log x) ^ A := by
  intro A hA
  obtain ⟨K, Xb, hK, hXb, hb⟩ :=
    selbergClosedSequence182_weighted_ordinary_bv w J θ hθ0 hθ A hA
  obtain ⟨Xe, he⟩ := eventually_atTop.mp
    (selbergWeight_shifted_discrepancy_divisor_weight_eventually h θ (by linarith) J A)
  refine ⟨K + 1, max Xb Xe, by positivity, hXb.trans_le (le_max_left _ _), ?_⟩
  intro x hx a ha
  have hb := hb x ((le_max_left _ _).trans hx) a ha
  have he := he x ((le_max_right _ _).trans hx) w _ (fun _ h => h) a
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, (q.divisors.card : ℝ) ^ J *
        (‖fullDiscrepancy (selbergClosedSequence182 w x) q (a q)‖ +
          ‖fullDiscrepancy (selbergShiftedSequence182 w h x) q (a q) -
            fullDiscrepancy (selbergClosedSequence182 w x) q (a q)‖) := by
      apply Finset.sum_le_sum
      intro q _
      have hn := norm_le_norm_add_norm_sub
        (fullDiscrepancy (selbergClosedSequence182 w x) q (a q))
        (fullDiscrepancy (selbergShiftedSequence182 w h x) q (a q))
      rw [norm_sub_rev] at hn
      exact mul_le_mul_of_nonneg_left hn (pow_nonneg (Nat.cast_nonneg _) _)
    _ = (∑ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, (q.divisors.card : ℝ) ^ J *
        ‖fullDiscrepancy (selbergClosedSequence182 w x) q (a q)‖) +
        ∑ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, (q.divisors.card : ℝ) ^ J *
          ‖fullDiscrepancy (selbergShiftedSequence182 w h x) q (a q) -
            fullDiscrepancy (selbergClosedSequence182 w x) q (a q)‖ := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ K * x / (Real.log x) ^ A + x / (Real.log x) ^ A := add_le_add hb he
    _ = (K + 1) * x / (Real.log x) ^ A := by ring

theorem trialBaseShiftedLogSaving182 (w : Fin 3) (h J : ℕ) :
    TrialBaseShiftedLogSaving182 w h J :=
  selbergShiftedSequence182_weighted_ordinary_bv w h J (trialBaseModulusExponent : ℝ)
    (by norm_num [trialBaseModulusExponent]) (by norm_num [trialBaseModulusExponent])

#print axioms selbergClosedSequence182_ordinary_bv
#print axioms selbergClosedSequence182_weighted_ordinary_bv
#print axioms selbergShiftedSequence182_weighted_ordinary_bv
#print axioms trialBaseShiftedLogSaving182

end PrimeGap182
