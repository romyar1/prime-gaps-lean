import HarmanBuchstab182
import SharpResidualTuples182

/-! Exact twelve-piece identity for the literal sharp minorant, including
its squarefree restriction and strict residual orders. The discrepancy
cover allows arbitrary nonnegative modulus weights and arbitrary residue
choices. It does not assert the distribution estimates for the pieces.
The linear assembly is adapted from Apache-2.0 PrimeGaps186, at the hash
checked by scripts/build_sharp_buchstab.py. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

def sharpResidualCount (x : ℝ) (j : Fin 2) (n : ℕ) : ℝ :=
  (sharpResidualTuples x (41361 / 100000) n j).card

open Classical in
theorem sharpMinorant_eq_two_residuals (x : ℝ) (n : ℕ) :
    sharpMinorant x (41361 / 100000) n =
      (if n.Prime then (1 : ℝ) else 0) - sharpResidualCount x 0 n -
        sharpResidualCount x 1 n := by
  simp only [sharpMinorant, sharpDefect_eq_residual_counts, sharpResidualCount, sub_add_eq_sub_sub]

noncomputable def sharpBuchstabPiece (x : ℝ) (i : Fin 12) (n : ℕ) : ℝ :=
  ![siftedTheta x 0 (fun _ => 1) n,
    siftedTheta x 1 (fun _ => 1) n,
    siftedTheta x 2 (fun _ => 1) n,
    siftedTheta x 3 (fun _ => 1) n,
    siftedTheta x 4 (fun _ => 1) n,
    sourceLargeFirst x n,
    sourceCentralPair x n,
    sourceT3 x n,
    sourceT5 x n - sharpResidualCount x 0 n,
    sourceT4 x n - sourceU1 x n,
    siftedTheta x 5 (fun _ => 1) n,
    sourceU3 x n - sharpResidualCount x 1 n] i

/-- The signs of the twelve Buchstab pieces, in the same index order as the piece array. -/
def sharpBuchstabSign : Fin 12 → ℝ :=
  ![1, -1, 1, 1, -1, -1, 1, 1, 1, -1, -1, 1]

theorem sharpBuchstabSign_norm (i : Fin 12) :
    ‖(sharpBuchstabSign i : ℂ)‖ = 1 := by
  fin_cases i <;> norm_num [sharpBuchstabSign]

theorem sharp_buchstab_pointwise :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, x ≤ (n : ℝ) → (n : ℝ) ≤ 2 * x →
      (if n.Prime then (1 : ℝ) else 0) - sharpResidualCount x 0 n -
          sharpResidualCount x 1 n =
        ∑ i : Fin 12, sharpBuchstabSign i * sharpBuchstabPiece x i n := by
  classical
  obtain ⟨X, hX, hreverse⟩ := sourceU1_eventually_eq_siftedTheta_five_sub_sourceU3
  filter_upwards [eventually_ge_atTop X] with x hx
  intro n hnlo hnhi
  have hprime := primeIndicator_source_buchstab (hX.trans hx) hnlo hnhi
  have hU := hreverse x hx n hnlo hnhi
  simp only [sharpBuchstabPiece, sharpBuchstabSign,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, one_mul, neg_one_mul, add_zero]
  linarith

open Classical in
theorem sharp_buchstab_finsupp :
    ∀ᶠ x : ℝ in atTop, ∀ S : Finset ℕ,
      S ⊆ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ →
      (∑ n ∈ S, Finsupp.single n
        (((if n.Prime then (1 : ℝ) else 0) - sharpResidualCount x 0 n -
          sharpResidualCount x 1 n : ℝ) : ℂ)) =
        ∑ i : Fin 12, (sharpBuchstabSign i : ℂ) •
          (∑ n ∈ S, Finsupp.single n (sharpBuchstabPiece x i n : ℂ)) := by
  filter_upwards [sharp_buchstab_pointwise,
    eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro S hS
  have hpoint (n : ℕ) (hn : n ∈ S) :
      (((if n.Prime then (1 : ℝ) else 0) - sharpResidualCount x 0 n -
        sharpResidualCount x 1 n : ℝ) : ℂ) =
      ∑ i : Fin 12, (sharpBuchstabSign i : ℂ) *
        (sharpBuchstabPiece x i n : ℂ) := by
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp (hS hn)
    have hlo : x ≤ (n : ℝ) := (Nat.le_ceil x).trans (Nat.cast_le.mpr hnlo)
    have hhi : (n : ℝ) ≤ 2 * x :=
      (Nat.cast_le.mpr hnhi).trans (Nat.floor_le (by linarith))
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul] using
      congrArg Complex.ofReal (hx n hlo hhi)
  calc
    _ = ∑ n ∈ S, Finsupp.single n
        (∑ i : Fin 12, (sharpBuchstabSign i : ℂ) *
          (sharpBuchstabPiece x i n : ℂ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hpoint n hn]
    _ = ∑ n ∈ S, ∑ i : Fin 12,
        Finsupp.single n ((sharpBuchstabSign i : ℂ) *
          (sharpBuchstabPiece x i n : ℂ)) := by
      simp only [Finsupp.single_finsetSum]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      simp only [Finsupp.smul_single, smul_eq_mul]

open Classical in
theorem sharp_buchstab_discrepancy :
    ∀ᶠ x : ℝ in atTop, ∀ S : Finset ℕ,
      S ⊆ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ → ∀ q a : ℕ,
      fullDiscrepancy
        (∑ n ∈ S, Finsupp.single n
          (((if n.Prime then (1 : ℝ) else 0) - sharpResidualCount x 0 n -
            sharpResidualCount x 1 n : ℝ) : ℂ)) q a =
        ∑ i : Fin 12, (sharpBuchstabSign i : ℂ) *
          fullDiscrepancy
            (∑ n ∈ S, Finsupp.single n (sharpBuchstabPiece x i n : ℂ)) q a := by
  filter_upwards [sharp_buchstab_pointwise,
    eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro S hS q a
  let w (n : ℕ) : ℂ :=
    (if n % q = a % q then 1 else 0) -
      (if Nat.Coprime n q then 1 else 0) / (q.totient : ℂ)
  have hpoint (n : ℕ) (hn : n ∈ S) :
      (((if n.Prime then (1 : ℝ) else 0) - sharpResidualCount x 0 n -
        sharpResidualCount x 1 n : ℝ) : ℂ) =
      ∑ i : Fin 12, (sharpBuchstabSign i : ℂ) *
        (sharpBuchstabPiece x i n : ℂ) := by
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp (hS hn)
    have hlo : x ≤ (n : ℝ) := (Nat.le_ceil x).trans (Nat.cast_le.mpr hnlo)
    have hhi : (n : ℝ) ≤ 2 * x :=
      (Nat.cast_le.mpr hnhi).trans (Nat.floor_le (by linarith))
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul] using
      congrArg Complex.ofReal (hx n hlo hhi)
  simp only [fullDiscrepancy_indexed_sample]
  change (∑ n ∈ S,
      (((if n.Prime then (1 : ℝ) else 0) - sharpResidualCount x 0 n -
        sharpResidualCount x 1 n : ℝ) : ℂ) * w n) =
    ∑ i : Fin 12, (sharpBuchstabSign i : ℂ) *
      ∑ n ∈ S, (sharpBuchstabPiece x i n : ℂ) * w n
  calc
    _ = ∑ n ∈ S, (∑ i : Fin 12, (sharpBuchstabSign i : ℂ) *
        (sharpBuchstabPiece x i n : ℂ)) * w n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hpoint n hn]
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm

open Classical in
theorem sharp_buchstab_weighted_discrepancy_cover :
    ∀ᶠ x : ℝ in atTop, ∀ S : Finset ℕ,
      S ⊆ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ →
      ∀ Q : Finset ℕ, ∀ a : ℕ → ℕ, ∀ w : ℕ → ℝ,
      (∀ q ∈ Q, 0 ≤ w q) →
      (∑ q ∈ Q, w q * ‖fullDiscrepancy
        (∑ n ∈ S, Finsupp.single n
          (((if n.Prime then (1 : ℝ) else 0) - sharpResidualCount x 0 n -
            sharpResidualCount x 1 n : ℝ) : ℂ)) q (a q)‖) ≤
        ∑ i : Fin 12, ∑ q ∈ Q, w q * ‖fullDiscrepancy
          (∑ n ∈ S, Finsupp.single n (sharpBuchstabPiece x i n : ℂ)) q (a q)‖ := by
  filter_upwards [sharp_buchstab_discrepancy] with x hx
  intro S hS Q a w hw
  have hpoint (q : ℕ) (hq : q ∈ Q) :
      w q * ‖fullDiscrepancy
        (∑ n ∈ S, Finsupp.single n
          (((if n.Prime then (1 : ℝ) else 0) - sharpResidualCount x 0 n -
            sharpResidualCount x 1 n : ℝ) : ℂ)) q (a q)‖ ≤
      ∑ i : Fin 12, w q * ‖fullDiscrepancy
        (∑ n ∈ S, Finsupp.single n (sharpBuchstabPiece x i n : ℂ)) q (a q)‖ := by
    rw [hx S hS q (a q), ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (hw q hq)
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _hi
    rw [norm_mul, sharpBuchstabSign_norm, one_mul]
  exact (Finset.sum_le_sum hpoint).trans_eq (Finset.sum_comm ..)

theorem sharpMinorant_buchstab_pointwise :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, x ≤ (n : ℝ) → (n : ℝ) ≤ 2 * x →
      sharpMinorant x (41361 / 100000) n =
        ∑ i : Fin 12, sharpBuchstabSign i * sharpBuchstabPiece x i n := by
  simpa only [sharpMinorant_eq_two_residuals] using sharp_buchstab_pointwise

open Classical in
theorem sharpMinorant_buchstab_weighted_discrepancy_cover :
    ∀ᶠ x : ℝ in atTop, ∀ S : Finset ℕ,
      S ⊆ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ →
      ∀ Q : Finset ℕ, ∀ a : ℕ → ℕ, ∀ w : ℕ → ℝ,
      (∀ q ∈ Q, 0 ≤ w q) →
      (∑ q ∈ Q, w q * ‖fullDiscrepancy
        (∑ n ∈ S, Finsupp.single n
          (sharpMinorant x (41361 / 100000) n : ℂ)) q (a q)‖) ≤
        ∑ i : Fin 12, ∑ q ∈ Q, w q * ‖fullDiscrepancy
          (∑ n ∈ S, Finsupp.single n (sharpBuchstabPiece x i n : ℂ)) q (a q)‖ := by
  simpa only [sharpMinorant_eq_two_residuals] using sharp_buchstab_weighted_discrepancy_cover

#print axioms sharpMinorant_buchstab_pointwise
#print axioms sharp_buchstab_finsupp
#print axioms sharpMinorant_buchstab_weighted_discrepancy_cover

end PrimeGap182Analytic.Harman
