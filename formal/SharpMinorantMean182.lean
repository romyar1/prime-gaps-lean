import SharpMeanBoundary182

/-! The actual sharp five-prime minorant has the claimed integral mean.
All prime-counting, tuple multiplicity, weak convergence and collision
boundary inputs are proved. A numerical upper bound on this integral is
a separate task, not an axiom or a hidden premise of this result. -/

noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Filter MeasureTheory Set PrimeGap186

namespace PrimeGap182Analytic.SharpMean

def sharpFirstCount (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
  ((sharpResidualTuples x (41361 / 100000) n 0).card : ℝ)

private theorem realIte_eq_classical (p : Prop) (dec : Decidable p) (a b : ℝ) :
    @ite ℝ p dec a b = @ite ℝ p (Classical.propDecidable p) a b := by
  by_cases hp : p <;> simp only [hp, ↓reduceIte]

theorem sharpFirstCount_mass_tendsto :
    Tendsto (fun x : ℝ => Real.log x / x * sharpFirstCount x)
      atTop (nhds sharpFirstMass) := by
  classical
  let S (x : ℝ) : ℝ := ∑ p ∈ exceptionalPrimeQuadruples x,
    if primeQuadrupleExponents x p ∈ sharpResidualRegion then
      ((∏ i, (p i : ℝ)) * (1 - ∑ i, primeQuadrupleExponents x p i))⁻¹ else 0
  have hS : Tendsto S atTop (nhds sharpFirstMass) := sharpFirstMass_reciprocal_tendsto
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε / 8 := by positivity
  have hsmall : ∀ᶠ x : ℝ in atTop, |S x - sharpFirstMass| ≤ ε / 8 := by
    have hl : Tendsto (fun x : ℝ => |S x - sharpFirstMass|) atTop (nhds 0) := by
      simpa only [sub_self, abs_zero] using (hS.sub_const sharpFirstMass).abs
    exact hl.eventually_le_const he
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    closed_final_prime_prefix_error_uniform (ε / 8) he,
    sharpBoundaryMass_tendsto.eventually_le_const he, hsmall] with x hx hcount hboundary hregion
  let slice (p : Fin 4 → ℕ) : Finset ℕ :=
    (Finset.Icc ⌈x / (∏ i, (p i : ℝ))⌉₊ ⌊2 * x / (∏ i, (p i : ℝ))⌋₊).filter Nat.Prime
  let w (p : Fin 4 → ℕ) : ℝ :=
    ((∏ i, (p i : ℝ)) * (1 - ∑ i, primeQuadrupleExponents x p i))⁻¹
  let E (p : Fin 4 → ℕ) : ℝ :=
    |Real.log x / x * ((slice p).card : ℝ) - w p|
  let cut (p : Fin 4 → ℕ) (q : ℕ) : Prop :=
    q ∈ exceptionalPrimeBand x ∧ sharpPrimeCut x (Fin.snoc p q)
  let R (p : Fin 4 → ℕ) : Prop := primeQuadrupleExponents x p ∈ sharpResidualRegion
  let B (j : SharpBoundary) (p : Fin 4 → ℕ) : Prop :=
    |sharpBoundaryValue (primeQuadrupleExponents x p) j| ≤ Real.log 2 / Real.log x
  have hE : (∑ p ∈ exceptionalPrimeQuadruples x, E p) ≤ ε / 8 := by
    simpa only [E, slice, w, exceptionalPrimeQuadruples, exceptionalPrimeBand,
      exceptionalExponentLower, exceptionalExponentUpper, primeQuadrupleExponents,
      one_mul, sub_self, sub_zero, show (2 : ℝ) - 1 = 1 from by norm_num] using
      hcount 1 2 (by norm_num) (by norm_num) (by norm_num)
  have hw : ∀ p ∈ exceptionalPrimeQuadruples x, 0 ≤ w p := by
    intro p hp
    obtain ⟨_, hM, _, hβ, _⟩ := prime_prefix_compact_geometry x hx p (Fintype.mem_piFinset.mp hp)
    exact inv_nonneg.mpr (mul_nonneg hM.le ((by norm_num : (0 : ℝ) ≤ 1 / 25).trans hβ))
  have hstable : ∀ p ∈ exceptionalPrimeQuadruples x,
      (∀ j ∈ (Finset.univ : Finset SharpBoundary), ¬ B j p) →
      ∀ q ∈ slice p, cut p q ↔ R p := by
    intro p hp hout q hq
    exact sharp_slice_cut_stable x hx p hp
      (fun j => lt_of_not_ge (hout j (Finset.mem_univ j))) q hq
  have hidentity : sharpFirstCount x =
      ∑ p ∈ exceptionalPrimeQuadruples x, ∑ q ∈ slice p, if cut p q then (1 : ℝ) else 0 :=
    sharp_first_count_as_prefix x hx
  have hL : 0 ≤ Real.log x / x := div_nonneg (Real.log_pos hx).le (zero_lt_one.trans hx).le
  have hbound : |Real.log x / x * sharpFirstCount x - S x| ≤
      2 * (∑ p ∈ exceptionalPrimeQuadruples x, E p) + sharpBoundaryMass x := by
    rw [hidentity]
    simpa only [one_mul, S, R, B, w, sharpBoundaryMass, realIte_eq_classical] using
      finite_slice_count_error_by_boundary_mass (exceptionalPrimeQuadruples x) slice
        (Finset.univ : Finset SharpBoundary) cut R B w E
        (Real.log x / x) 1 hL (by norm_num) hw (fun p _ => by simp only [one_mul]; exact le_rfl) hstable
  have htri := abs_sub_le (Real.log x / x * sharpFirstCount x) (S x) sharpFirstMass
  rw [Real.dist_eq]
  linarith only [hbound, htri, hE, hboundary, hregion, hε]

def sharpMass : ℝ := 6 * sharpFirstMass

theorem sharpMass_nonneg : 0 ≤ sharpMass := mul_nonneg (by norm_num) sharpFirstMass_nonneg

theorem sharpDefect_mass_tendsto : Tendsto
    (fun x : ℝ => Real.log x / x *
      ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊, sharpDefect x (41361 / 100000) n)
    atTop (nhds sharpMass) := by
  unfold sharpMass
  have h := sharpFirstCount_mass_tendsto.const_mul 6
  convert h using 1
  ext x
  simp only [sharpDefect_eq_six_first_count, ← Finset.mul_sum, sharpFirstCount]
  ring

open Classical in
theorem sharpMinorant_signed_mean : Tendsto
    (fun x : ℝ => Real.log x / x *
      ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊, sharpMinorant x (41361 / 100000) n)
    atTop (nhds (1 - sharpMass)) := by
  have hp : Tendsto (fun x : ℝ => Real.log x / x *
      ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊, if n.Prime then (1 : ℝ) else 0)
      atTop (nhds 1) := by
    simpa only [Finset.sum_boole] using closed_dyadic_prime_count_tendsto
  simpa only [sharpMinorant, Finset.sum_sub_distrib, mul_sub] using hp.sub sharpDefect_mass_tendsto

#print axioms sharpFirstCount_mass_tendsto
#print axioms sharpDefect_mass_tendsto
#print axioms sharpMinorant_signed_mean

end PrimeGap182Analytic.SharpMean
