import HarmanResidualGeometry182
import SquareDivisorSaving182

/-! The repeated-prime contribution of each actual five-prime source has
arbitrary logarithmic saving, uniformly over interval restrictions,
primitive residue choices, and all modulus subsets below x^.53. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186 Classical

namespace PrimeGap182Analytic.Harman

def sourceFiveCollisionSequence (x : ℝ) (j : Fin 2) (I : Finset ℕ) : ℕ →₀ ℂ :=
  ∑ n ∈ I, Finsupp.single n ((sourceFiveCollision x n j).card : ℂ)

def sourceFiveEligibleSequence (x : ℝ) (j : Fin 2) (I : Finset ℕ) : ℕ →₀ ℂ :=
  ∑ n ∈ I, Finsupp.single n ((sourceFiveEligible x n j).card : ℂ)

theorem sourceFiveCollision_weighted_log_saving (J : ℕ) (A : ℝ) (hA : 0 < A) :
    ∃ K X : ℝ, 0 < K ∧ Real.exp 1 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ j : Fin 2, ∀ I : Finset ℕ,
      I ⊆ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ →
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 ⌊x ^ ((53 : ℝ) / 100)⌋₊ →
      ∀ a : ℕ → ℕ, (∀ q ∈ S, Nat.Coprime (a q) q) →
      (∑ q ∈ S, (q.divisors.card : ℝ) ^ J *
        ‖fullDiscrepancy (sourceFiveCollisionSequence x j I) q (a q)‖) ≤
          K * x / (Real.log x) ^ A := by
  obtain ⟨K, Xs, hK, hXs, hsave⟩ := square_supported_log_saving182 5 J A hA
  obtain ⟨Xe, hXe⟩ := eventually_sourceFive_envelope.exists_forall_of_atTop
  refine ⟨K, max Xs Xe, hK, hXs.trans (le_max_left _ _), ?_⟩
  intro x hx j I hI S hS a ha
  obtain ⟨hx1, henv⟩ := hXe x ((le_max_right _ _).trans hx)
  have hx0 : 0 < x := zero_lt_one.trans hx1
  let N : ℕ := ⌊2 * x⌋₊
  let e : ℕ → ℂ := fun n => if n ∈ I then ((sourceFiveCollision x n j).card : ℂ) else 0
  have hIbig : I ⊆ Finset.Icc 1 N := by
    intro n hn
    have hi := Finset.mem_Icc.mp (hI hn)
    have hnx : x ≤ (n : ℝ) := Nat.ceil_le.mp hi.1
    exact Finset.mem_Icc.mpr ⟨Nat.cast_pos.mp (hx0.trans_le hnx), hi.2⟩
  have heq : (∑ n ∈ Finset.Icc 1 N, Finsupp.single n (e n)) = sourceFiveCollisionSequence x j I := by
    calc
      _ = ∑ n ∈ I, Finsupp.single n (e n) := by
        symm
        apply Finset.sum_subset hIbig
        intro n _ hn
        simp only [e, ite_eq_right hn, Finsupp.single_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [e, ite_eq_left hn]
  have hb : ∀ n ∈ Finset.Icc 1 N, ‖e n‖ ≤ (n.divisors.card : ℝ) ^ 5 := by
    intro n _
    by_cases hn : n ∈ I
    · simp only [e, ite_eq_left hn, Complex.norm_natCast]
      exact_mod_cast sourceFiveCollision_card_le_divisor_power x n j
    · simp only [e, ite_eq_right hn, norm_zero]
      positivity
  have hs : ∀ n ∈ Finset.Icc 1 N, e n ≠ 0 →
      ∃ p : ℕ, p.Prime ∧ x ^ ((8639 : ℝ) / 50000) ≤ (p : ℝ) ∧
        (p : ℝ) ≤ x ^ ((31 : ℝ) / 100) ∧ p ^ 2 ∣ n := by
    intro n hn hne
    have hi : n ∈ I := by
      by_contra hi
      exact hne (by simp only [e, ite_eq_right hi])
    have hc : (sourceFiveCollision x n j).card ≠ 0 := by
      intro hc
      exact hne (by simp only [e, ite_eq_left hi, hc, Nat.cast_zero])
    obtain ⟨p, hp⟩ := Finset.card_ne_zero.mp hc
    have hnx : (n : ℝ) ≤ 2 * x :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le (by positivity))
    obtain ⟨r, hr, hlo, hhi, hdiv⟩ := sourceFiveCollision_square hx1 henv hnx hp
    exact ⟨r, hr, hlo, hhi.le, hdiv⟩
  have hraw := hsave x ((le_max_left _ _).trans hx) S hS a ha e hb hs
  rw [heq] at hraw
  exact hraw

theorem sharp_source_remainder_sequence {x : ℝ} (hx : 1 < x)
    (hg : 2 * x < x ^ (6 * ((8639 : ℝ) / 50000))) (j : Fin 2)
    (I : Finset ℕ) (hI : I ⊆ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊) :
    (∑ n ∈ I, Finsupp.single n
      (((if j = 0 then sourceT5 x n else sourceU3 x n) - sharpResidualCount x j n : ℝ) : ℂ)) =
      sourceFiveEligibleSequence x j I + sourceFiveCollisionSequence x j I := by
  rw [sourceFiveEligibleSequence, sourceFiveCollisionSequence, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hi := Finset.mem_Icc.mp (hI hn)
  have hlo : x ≤ (n : ℝ) := Nat.ceil_le.mp hi.1
  have hhi : (n : ℝ) ≤ 2 * x :=
    (Nat.cast_le.mpr hi.2).trans (Nat.floor_le (by linarith only [hx]))
  rw [sharp_residual_source_difference hx hg n hlo hhi j]
  simp only [Complex.ofReal_add, Complex.ofReal_natCast, Finsupp.single_add]

#print axioms sourceFiveCollision_weighted_log_saving
#print axioms sharp_source_remainder_sequence

end PrimeGap182Analytic.Harman
