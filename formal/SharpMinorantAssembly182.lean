import SharpBuchstab182

/-! Linear assembly of the twelve literal sharp-minorant pieces. The
component estimates are explicit inputs of this intermediate lemma; the
analytic assembly supplies them separately. Adapted from Apache-2.0
PrimeGaps186 at the source hash checked by the generator. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

open Classical in
theorem sharp_minorant_log_saving_of_twelve_components
    (j : ℕ) («ω» δ A : ℝ) (L0 : ℝ → ℝ)
    (hparts : ∀ i : Fin 12, ∃ K X : ℝ, 0 < K ∧
      ∀ x : ℝ, X ≤ x → ∀ Y : Set.Ici (1 : ℝ), (Y : ℝ) = x ^ δ →
      ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
      ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
        let F : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
          Finsupp.single n (sharpBuchstabPiece x i n : ℂ)
        let Q := (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω») * L0 x⌋₊).filter (fun q =>
          q ∣ (∏ p ∈ I, p) ∧
            Nonempty (DenseDivisibilityWitness Y j q))
        (∑ q ∈ Q, ‖fullDiscrepancy F q a‖) ≤ K * x / (Real.log x) ^ A) :
    ∃ K X : ℝ, 0 < K ∧ 1 < X ∧
      ∀ x : ℝ, X ≤ x → ∀ Y : Set.Ici (1 : ℝ), (Y : ℝ) = x ^ δ →
      ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
      ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
        let ρx : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
          Finsupp.single n
            (((if n.Prime then (1 : ℝ) else 0) - sharpResidualCount x 0 n -
              sharpResidualCount x 1 n : ℝ) : ℂ)
        let Q := (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω») * L0 x⌋₊).filter (fun q =>
          q ∣ (∏ p ∈ I, p) ∧
            Nonempty (DenseDivisibilityWitness Y j q))
        (∑ q ∈ Q, ‖fullDiscrepancy ρx q a‖) ≤ K * x / (Real.log x) ^ A := by
  choose K X hK hb using hparts
  obtain ⟨Xc, hXc⟩ := eventually_atTop.mp sharp_buchstab_weighted_discrepancy_cover
  let X0 := max 2 (max Xc (∑ i : Fin 12, |X i|))
  have hsumpos : 0 < ∑ i : Fin 12, K i :=
    Finset.sum_pos (fun i _hi => hK i) Finset.univ_nonempty
  refine ⟨∑ i : Fin 12, K i, X0, hsumpos, ?_, ?_⟩
  · exact (by norm_num : (1 : ℝ) < 2).trans_le (le_max_left _ _)
  · intro x hx Y hY I hI a ha ρx Q
    have hxc : Xc ≤ x :=
      (le_max_left Xc _).trans ((le_max_right _ _).trans hx)
    have hxi (i : Fin 12) : X i ≤ x := by
      calc
        X i ≤ |X i| := le_abs_self _
        _ ≤ ∑ l : Fin 12, |X l| :=
          Finset.single_le_sum (fun l _hl => abs_nonneg (X l)) (Finset.mem_univ i)
        _ ≤ x := (le_max_right Xc _).trans ((le_max_right _ _).trans hx)
    have hcover := hXc x hxc (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊) Finset.Subset.rfl
      Q (fun _ => a) (fun _ => 1) (fun _ _ => by norm_num)
    simp only [one_mul] at hcover
    calc
      (∑ q ∈ Q, ‖fullDiscrepancy ρx q a‖) ≤
          ∑ i : Fin 12, ∑ q ∈ Q, ‖fullDiscrepancy
            (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
              Finsupp.single n (sharpBuchstabPiece x i n : ℂ)) q a‖ := hcover
      _ ≤ ∑ i : Fin 12, K i * x / (Real.log x) ^ A := by
        apply Finset.sum_le_sum
        intro i _hi
        exact hb i x (hxi i) Y hY I hI a ha
      _ = (∑ i : Fin 12, K i) * x / (Real.log x) ^ A := by
        rw [← Finset.sum_div, ← Finset.sum_mul]

#print axioms sharp_minorant_log_saving_of_twelve_components

end PrimeGap182Analytic.Harman
