import SharpMeanTuples182
import SharpPrimeSliceGeometry182

/-! Every boundary term is an actual affine strip in prime-exponent space.
The additional ten strips remove repeated primes. No stability or
vanishing-boundary hypothesis is left to the arithmetic mean theorem. -/

noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Filter MeasureTheory Set PrimeGap186

namespace PrimeGap182Analytic.SharpMean

abbrev SharpBoundary := Fin 19 ⊕ Fin 10

def sharpBoundaryCoefficients : SharpBoundary → Fin 5 → ℝ :=
  Sum.elim sharpCoreCoefficients sharpCollisionCoefficients

def sharpBoundaryThreshold : SharpBoundary → ℝ := Sum.elim sharpCoreThreshold (fun _ => 0)

def sharpBoundaryNormal (j : SharpBoundary) (i : Fin 4) : ℝ :=
  sharpBoundaryCoefficients j i.castSucc - sharpBoundaryCoefficients j (Fin.last 4)

def sharpBoundaryOffset (j : SharpBoundary) : ℝ :=
  sharpBoundaryThreshold j - sharpBoundaryCoefficients j (Fin.last 4)

def sharpBoundaryValue (t : Fin 4 → ℝ) (j : SharpBoundary) : ℝ :=
  (∑ i, sharpBoundaryNormal j i * t i) - sharpBoundaryOffset j

theorem sharpBoundaryNormal_ne_zero (j : SharpBoundary) : sharpBoundaryNormal j ≠ 0 := by
  rcases j with j | j
  · exact sharpCoreNormal_ne_zero j
  · fin_cases j <;>
      norm_num [sharpBoundaryNormal, sharpBoundaryCoefficients, sharpCollisionCoefficients,
        Function.ne_iff, Fin.exists_fin_succ, Fin.last, Matrix.cons_val_four]

theorem sharpBoundary_last_bound (j : SharpBoundary) :
    |sharpBoundaryCoefficients j (Fin.last 4)| ≤ 1 := by
  rcases j with j | j
  · exact sharpCore_last_bound j
  · fin_cases j <;>
      norm_num [sharpBoundaryCoefficients, sharpCollisionCoefficients, Fin.last, Matrix.cons_val_four]

theorem sharpBoundary_move (t : Fin 4 → ℝ) (z δ : ℝ)
    (hδ : |z - (1 - ∑ i, t i)| ≤ δ) (j : SharpBoundary) :
    |((∑ i, sharpBoundaryCoefficients j i * Fin.snoc (α := fun _ => ℝ) t z i) - sharpBoundaryThreshold j) -
      sharpBoundaryValue t j| ≤ δ := by
  have h := snoc_affine_sub_abs_le (sharpBoundaryCoefficients j) (sharpBoundaryThreshold j) t hδ
  rw [snoc_affine_limit_eq] at h
  exact h.trans (mul_le_of_le_one_left ((abs_nonneg _).trans hδ) (sharpBoundary_last_bound j))

theorem sharpCore_stable (t : Fin 4 → ℝ) (z δ : ℝ)
    (hδ : |z - (1 - ∑ i, t i)| ≤ δ)
    (hout : ∀ j, δ < |sharpBoundaryValue t j|) :
    sharpCoreStrict (Fin.snoc t z) ↔ t ∈ sharpResidualRegion := by
  change (∀ j, sharpCoreThreshold j < ∑ i, sharpCoreCoefficients j i * Fin.snoc (α := fun _ => ℝ) t z i) ↔
    sharpCoreClosed (Fin.snoc t (1 - ∑ i, t i))
  rw [sharpCoreClosed_snoc]
  apply forall_congr'
  intro j
  have h := mixed_closed_iff_of_outside_strip true
    (sharpBoundary_move t z δ hδ (Sum.inl j)) (hout (Sum.inl j))
  simpa only [Bool.true_eq, ↓reduceIte, sub_pos, sub_nonneg, sharpBoundaryValue,
    sharpBoundaryNormal, sharpBoundaryOffset, sharpBoundaryCoefficients,
    sharpBoundaryThreshold, Sum.elim_inl, sharpCoreNormal, sharpCoreOffset,
    show Fin.last 4 = (4 : Fin 5) from rfl] using h

theorem sharpCollision_nonzero_iff (α : Fin 5 → ℝ) :
    (∀ j : Fin 10, (∑ i, sharpCollisionCoefficients j i * α i) ≠ 0) ↔
      Function.Injective α := by
  have he : (∀ j : Fin 10, (∑ i, sharpCollisionCoefficients j i * α i) ≠ 0) ↔
      ∀ i j : Fin 5, i < j → α i ≠ α j := by
    simp [sharpCollisionCoefficients, Fin.forall_fin_succ, Fin.sum_univ_succ,
      ← sub_eq_add_neg, sub_ne_zero, and_assoc]
  rw [he]
  constructor
  · intro h i j hij
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hlt
    · exact h i j hlt hij
    · exact h j i hlt hij.symm
  · intro h i j hij heq
    exact hij.ne (h heq)

theorem sharp_snoc_injective_of_outside (t : Fin 4 → ℝ) (z δ : ℝ)
    (hδ : |z - (1 - ∑ i, t i)| ≤ δ)
    (hout : ∀ j, δ < |sharpBoundaryValue t j|) :
    Function.Injective (Fin.snoc t z) := by
  apply (sharpCollision_nonzero_iff _).mp
  intro j heq
  have h := sharpBoundary_move t z δ hδ (Sum.inr j)
  have hz : (∑ i, sharpBoundaryCoefficients (Sum.inr j) i * Fin.snoc (α := fun _ => ℝ) t z i) -
      sharpBoundaryThreshold (Sum.inr j) = 0 := by
    simpa only [sharpBoundaryCoefficients, sharpBoundaryThreshold, Sum.elim_inr, sub_zero] using heq
  rw [hz, zero_sub, abs_neg] at h
  exact (not_le_of_gt (hout (Sum.inr j))) h

theorem sharp_slice_cut_stable (x : ℝ) (hx : 1 < x) (p : Fin 4 → ℕ)
    (hp : p ∈ exceptionalPrimeQuadruples x)
    (hout : ∀ j, Real.log 2 / Real.log x <
      |sharpBoundaryValue (primeQuadrupleExponents x p) j|)
    (q : ℕ)
    (hq : q ∈ (Finset.Icc ⌈x / (∏ i, (p i : ℝ))⌉₊
      ⌊2 * x / (∏ i, (p i : ℝ))⌋₊).filter Nat.Prime) :
    (q ∈ exceptionalPrimeBand x ∧ sharpPrimeCut x (Fin.snoc p q)) ↔
      primeQuadrupleExponents x p ∈ sharpResidualRegion := by
  have hpr : ∀ i, (p i).Prime := fun i =>
    (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)).2
  have hpp : 0 < ∏ i, p i := Finset.prod_pos (fun i _ => (hpr i).pos)
  have hqp := (Finset.mem_filter.mp hq).2
  have hn : (∏ i, p i) * q ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ := by
    apply (mul_mem_closed_nat_interval_iff _ _ hpp x (2 * x) (by linarith only [hx])).mpr
    simpa only [Nat.cast_prod] using (Finset.mem_filter.mp hq).1
  obtain ⟨_, _, _, _, _, _, _, _, _, hlog, hlo, hhi⟩ :=
    prime_prefix_interval_log_geometry x 1 2 hx (by norm_num) (by norm_num) p
      (Fintype.mem_piFinset.mp hp) q (by simpa only [one_mul] using hn)
  have hmove : |Real.logb x (q : ℝ) - (1 - ∑ i, Real.logb x (p i : ℝ))| ≤
      Real.log 2 / Real.log x := by
    rw [hlog, add_sub_cancel_left, abs_of_nonneg hlo]
    exact hhi
  have hlogfun : (fun i => Real.logb x ((Fin.snoc (α := fun _ => ℕ) p q i : ℕ) : ℝ)) =
      Fin.snoc (primeQuadrupleExponents x p) (Real.logb x (q : ℝ)) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact rfl
    · simp only [Fin.snoc_castSucc, primeQuadrupleExponents]
  have hinj : Function.Injective (Fin.snoc p q) := by
    intro i j hij
    apply sharp_snoc_injective_of_outside _ _ _ hmove hout
    change Fin.snoc (α := fun _ => ℝ) (primeQuadrupleExponents x p) (Real.logb x (q : ℝ)) i =
      Fin.snoc (α := fun _ => ℝ) (primeQuadrupleExponents x p) (Real.logb x (q : ℝ)) j
    rw [← hlogfun]
    exact congrArg (fun n : ℕ => Real.logb x (n : ℝ)) hij
  have hc : sharpPrimeCut x (Fin.snoc p q) ↔
      primeQuadrupleExponents x p ∈ sharpResidualRegion := by
    simp only [sharpPrimeCut, hinj, true_and, hlogfun]
    exact sharpCore_stable _ _ _ hmove hout
  constructor
  · exact fun h => hc.mp h.2
  · intro hr
    have hcut := hc.mpr hr
    refine ⟨?_, hcut⟩
    have hpr5 : ∀ i, Nat.Prime (Fin.snoc (α := fun _ => ℕ) p q i) := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using hqp
      · simpa only [Fin.snoc_castSucc] using hpr j
    have hprod : x ≤ ∏ i, ((Fin.snoc (α := fun _ => ℕ) p q i : ℕ) : ℝ) := by
      simpa only [← Nat.cast_prod, Fin.prod_snoc, Nat.cast_mul] using
        Nat.ceil_le.mp (Finset.mem_Icc.mp hn).1
    simpa only [Fin.snoc_last] using sharpPrimeCut_band x hx (Fin.snoc p q) hpr5 hprod hcut (Fin.last 4)

open Classical in
def sharpBoundaryMass (x : ℝ) : ℝ := ∑ j : SharpBoundary,
  ∑ p ∈ exceptionalPrimeQuadruples x,
    if |sharpBoundaryValue (primeQuadrupleExponents x p) j| ≤ Real.log 2 / Real.log x then
      ((∏ i, (p i : ℝ)) * (1 - ∑ i, primeQuadrupleExponents x p i))⁻¹ else 0

private theorem primePiFinset_eq_classical {k : ℕ} (t : Fin k → Finset ℕ)
    (dec : DecidableEq (Fin k)) :
    @Fintype.piFinset (Fin k) dec inferInstance (fun _ => ℕ) t =
      @Fintype.piFinset (Fin k) (Classical.typeDecidableEq _) inferInstance (fun _ => ℕ) t := by
  ext r
  simp only [Fintype.mem_piFinset]

private theorem primeFilter_eq_classical (s : Finset ℕ) (dec : DecidablePred Nat.Prime) :
    @Finset.filter ℕ Nat.Prime dec s =
      @Finset.filter ℕ Nat.Prime (Classical.decPred _) s := by
  ext n
  simp only [Finset.mem_filter]

theorem sharpBoundaryMass_tendsto : Tendsto sharpBoundaryMass atTop (nhds 0) := by
  have hl :=
    reciprocal_four_weighted_affine_moving_strip_finset_tendsto
      (Finset.univ : Finset SharpBoundary) sharpBoundaryNormal sharpBoundaryOffset (fun _ => 1)
      (fun j _ => sharpBoundaryNormal_ne_zero j) (by intro j _; norm_num)
  apply hl.congr'
  apply Filter.Eventually.of_forall
  intro x
  simp only [sharpBoundaryMass, sharpBoundaryValue, exceptionalPrimeQuadruples,
    exceptionalPrimeBand, exceptionalExponentLower, exceptionalExponentUpper,
    primeQuadrupleExponents, one_mul, primePiFinset_eq_classical, primeFilter_eq_classical]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro p _
  exact (ite_eq_ite _ _ _).mpr True.intro

#print axioms sharpCore_stable
#print axioms sharp_snoc_injective_of_outside
#print axioms sharp_slice_cut_stable
#print axioms sharpBoundaryMass_tendsto

end PrimeGap182Analytic.SharpMean
