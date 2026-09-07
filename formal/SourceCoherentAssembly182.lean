import SourceSupportedModuli182
import SieveSourceTransfer182

/-! Finite assembly of the actual analytic source estimates. The base
input is an all-moduli BV statement with arbitrary primitive residues;
the other inputs are the literal shifted prime/minorant/defect estimates.
Actual array support is proved in SourceSupportedModuli182. -/

noncomputable section
open PrimeGap186 PrimeGap182Analytic Filter
open scoped BigOperators Topology
set_option maxRecDepth 4096

namespace PrimeGap182

def TrialBaseShiftedLogSaving182 (w : Fin 3) (h J : ℕ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ 1 < X ∧
    ∀ x : ℝ, X ≤ x → ∀ a : ℕ → ℕ,
    (∀ q ∈ Finset.Icc 1 ⌊x ^ (trialBaseModulusExponent : ℝ)⌋₊, Nat.Coprime (a q) q) →
      (∑ q ∈ Finset.Icc 1 ⌊x ^ (trialBaseModulusExponent : ℝ)⌋₊,
        (q.divisors.card : ℝ) ^ J * ‖fullDiscrepancy (selbergShiftedSequence182 w h x) q (a q)‖) ≤
          K * x / (Real.log x) ^ A

structure TrialShiftedSourceEstimates182 (w : Fin 3) (h J : ℕ) : Prop where
  base : TrialBaseShiftedLogSaving182 w h J
  old : w = 0 → ∀ row ∈ trialOldSourceRows,
    ShiftedSourceLogSaving182 w row.order (row.omega : ℝ) (row.delta : ℝ) (fun _ => 1) h J
  improved : w = 1 → ∀ row ∈ trialNewSourceRows,
    ShiftedSourceLogSaving182 w row.order (row.omega : ℝ) (row.delta : ℝ) (fun _ => 1) h J
  common : ShiftedSourceLogSaving182 w 2 (trialCommonSourceOmega : ℝ) (trialCommonSourceDelta : ℝ)
    (fun _ => 1) h J
  subtraction : ShiftedSourceLogSaving182 w 2 (trialSubtractionSourceRow.omega : ℝ)
    (trialSubtractionSourceRow.delta : ℝ) (fun _ => 1) h J

abbrev TrialDistributionIndex182 := Fin 3 ⊕ ((ν : Fin 2) × Fin (trialSourceRows ν).length)

open Classical in
def trialBaseCarrierModuli182 (x : ℝ) (I : Finset ℕ) : Finset ℕ :=
  (∏ p ∈ I, p).divisors.filter (fun q => (q : ℝ) ≤ x ^ (trialBaseModulusExponent : ℝ))

def trialSourceClassModuli182 (w : Fin 3) : TrialDistributionIndex182 → ℝ → Finset ℕ → Finset ℕ
  | .inl b => fun x I => if b = 0 then trialBaseCarrierModuli182 x I
      else if b = 1 then sourceModuli182 2 (trialCommonSourceOmega : ℝ)
        (trialCommonSourceDelta : ℝ) (fun _ => 1) x I
      else sourceModuli182 2 (trialSubtractionSourceRow.omega : ℝ)
        (trialSubtractionSourceRow.delta : ℝ) (fun _ => 1) x I
  | .inr ⟨ν, j⟩ => fun x I =>
      if (w = 0 ∧ ν = 0) ∨ (w = 1 ∧ ν = 1) then
        let row := (trialSourceRows ν).get j
        sourceModuli182 row.order (row.omega : ℝ) (row.delta : ℝ) (fun _ => 1) x I
      else ∅

def TrialCarrierLogSaving182 (w : Fin 3) (h J : ℕ)
    (Q : ℝ → Finset ℕ → Finset ℕ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ Real.exp 1 ≤ X ∧
    ∀ x : ℝ, X ≤ x → ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
    ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
      (∑ q ∈ Q x I, (q.divisors.card : ℝ) ^ J *
        ‖fullDiscrepancy (selbergShiftedSequence182 w h x) q a‖) ≤ K * x / (Real.log x) ^ A

theorem TrialBaseShiftedLogSaving182.carrier {w : Fin 3} {h J : ℕ}
    (hb : TrialBaseShiftedLogSaving182 w h J) :
    TrialCarrierLogSaving182 w h J trialBaseCarrierModuli182 := by
  classical
  intro A hA
  obtain ⟨K, X, hK, _hX, hbound⟩ := hb A hA
  refine ⟨K, max X (Real.exp 1), hK, le_max_right _ _, ?_⟩
  intro x hx I hI a ha
  have hprod : 0 < ∏ p ∈ I, p := Finset.prod_pos fun p hp => (hI p hp).pos
  let ar : ℕ → ℕ := fun q => if q ∣ ∏ p ∈ I, p then a else 1
  have har : ∀ q ∈ Finset.Icc 1 ⌊x ^ (trialBaseModulusExponent : ℝ)⌋₊, Nat.Coprime (ar q) q := by
    intro q _
    dsimp only [ar]
    split_ifs with hq
    · exact ha.of_dvd_right hq
    · exact Nat.coprime_one_left _
  have hsub : trialBaseCarrierModuli182 x I ⊆ Finset.Icc 1 ⌊x ^ (trialBaseModulusExponent : ℝ)⌋₊ := by
    intro q hq
    obtain ⟨hqd, hqr⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hqd) hprod,
      Nat.le_floor hqr⟩
  calc
    _ = ∑ q ∈ trialBaseCarrierModuli182 x I, (q.divisors.card : ℝ) ^ J *
        ‖fullDiscrepancy (selbergShiftedSequence182 w h x) q (ar q)‖ := by
      apply Finset.sum_congr rfl
      intro q hq
      simp only [ar, ite_eq_left (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hq).1)]
    _ ≤ ∑ q ∈ Finset.Icc 1 ⌊x ^ (trialBaseModulusExponent : ℝ)⌋₊,
        (q.divisors.card : ℝ) ^ J * ‖fullDiscrepancy (selbergShiftedSequence182 w h x) q (ar q)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ =>
        mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (norm_nonneg _))
    _ ≤ K * x / (Real.log x) ^ A := hbound x ((le_max_left _ _).trans hx) ar har

theorem shiftedSource_carrier {w : Fin 3} {h J density : ℕ} {«ω» δ : ℝ}
    (hs : ShiftedSourceLogSaving182 w density «ω» δ (fun _ => 1) h J) :
    TrialCarrierLogSaving182 w h J (sourceModuli182 density «ω» δ (fun _ => 1)) := by
  intro A hA
  obtain ⟨K, X, hK, _hX, hs⟩ := hs A hA
  exact ⟨K, max X (Real.exp 1), hK, le_max_right _ _, fun x hx => hs x ((le_max_left _ _).trans hx)⟩

theorem TrialShiftedSourceEstimates182.class_saving {w : Fin 3} {h J : ℕ}
    (hs : TrialShiftedSourceEstimates182 w h J) (c : TrialDistributionIndex182) :
    TrialCarrierLogSaving182 w h J (trialSourceClassModuli182 w c) := by
  classical
  rcases c with b | ⟨ν, j⟩
  · fin_cases b
    · exact hs.base.carrier
    · exact shiftedSource_carrier hs.common
    · exact shiftedSource_carrier hs.subtraction
  · by_cases hc : (w = 0 ∧ ν = 0) ∨ (w = 1 ∧ ν = 1)
    · rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact shiftedSource_carrier (hs.old rfl _ (List.get_mem _ _))
      · exact shiftedSource_carrier (hs.improved rfl _ (List.get_mem _ _))
    · intro A _hA
      refine ⟨1, Real.exp 1, zero_lt_one, le_rfl, ?_⟩
      intro x hx I _hI a _ha
      simp only [trialSourceClassModuli182, hc, ↓reduceIte, Finset.sum_empty, one_mul]
      have hx1 : 1 ≤ x := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hx
      exact div_nonneg (zero_le_one.trans hx1) (Real.rpow_nonneg (Real.log_nonneg hx1) _)

theorem TrialShiftedSourceEstimates182.union_saving {w : Fin 3} {h J : ℕ}
    (hs : TrialShiftedSourceEstimates182 w h J) :
    TrialCarrierLogSaving182 w h J (fun x I =>
      Finset.univ.biUnion (fun c : TrialDistributionIndex182 => trialSourceClassModuli182 w c x I)) :=
  finite_coherent_discrepancy_log_saving (selbergShiftedSequence182 w h) J
    (trialSourceClassModuli182 w) hs.class_saving

theorem trialDenseModulus_mem_sourceModuli (density : ℕ) («ω» δ : ℚ) (x : ℝ) (I : Finset ℕ)
    (hI : 0 < ∏ p ∈ I, p) (q : ℕ) (hq : q ∣ ∏ p ∈ I, p)
    (hd : TrialDenseModulus182 density «ω» δ x q) :
    q ∈ sourceModuli182 density («ω» : ℝ) (δ : ℝ) (fun _ => 1) x I := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hq hI,
    Nat.le_floor (by simpa only [mul_one] using hd.1)⟩, hq, hd.2⟩

theorem trialSupportedModulus_mem_union (w : Fin 3) (x : ℝ) (I : Finset ℕ)
    (hI : 0 < ∏ p ∈ I, p) (q : ℕ) (hq : q ∣ ∏ p ∈ I, p)
    (hs : TrialSupportedModulus182 w x q) :
    q ∈ Finset.univ.biUnion (fun c : TrialDistributionIndex182 => trialSourceClassModuli182 w c x I) := by
  classical
  rcases hs with hb | ⟨rfl, row, hr, hd⟩ | ⟨rfl, row, hr, hd⟩ | hc | hs
  · exact Finset.mem_biUnion.mpr ⟨.inl 0, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hq, hI.ne'⟩, hb⟩⟩
  · change row ∈ trialSourceRows 0 at hr
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hr
    refine Finset.mem_biUnion.mpr ⟨.inr ⟨0, j⟩, Finset.mem_univ _, ?_⟩
    change q ∈ sourceModuli182 ((trialSourceRows 0).get j).order
      (((trialSourceRows 0).get j).omega : ℝ) (((trialSourceRows 0).get j).delta : ℝ) (fun _ => 1) x I
    rw [hj]
    exact trialDenseModulus_mem_sourceModuli _ _ _ x I hI q hq hd
  · change row ∈ trialSourceRows 1 at hr
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hr
    refine Finset.mem_biUnion.mpr ⟨.inr ⟨1, j⟩, Finset.mem_univ _, ?_⟩
    change q ∈ sourceModuli182 ((trialSourceRows 1).get j).order
      (((trialSourceRows 1).get j).omega : ℝ) (((trialSourceRows 1).get j).delta : ℝ) (fun _ => 1) x I
    rw [hj]
    exact trialDenseModulus_mem_sourceModuli _ _ _ x I hI q hq hd
  · exact Finset.mem_biUnion.mpr ⟨.inl 1, Finset.mem_univ _,
      trialDenseModulus_mem_sourceModuli _ _ _ x I hI q hq hc⟩
  · exact Finset.mem_biUnion.mpr ⟨.inl 2, Finset.mem_univ _,
      trialDenseModulus_mem_sourceModuli _ _ _ x I hI q hq hs⟩

namespace TrialSmoothProfiles182

theorem coherent_sources_of_estimates (P : TrialSmoothProfiles182) (H : Finset ℕ) (hH : H.card = 39)
    (hs : ∀ i : Fin 39, ∀ k : Fin 6,
      TrialShiftedSourceEstimates182 (sievePairWeight k) (H.orderEmbOfFin hH i) 13) :
    P.CoherentSources H hH := by
  classical
  intro i k A hA
  obtain ⟨K, X, hK, _hX, hb⟩ := (hs i k).union_saving (A + 2) (by linarith)
  refine ⟨K, hK, ?_⟩
  filter_upwards [P.sieve_moduli_supported_eventually H, eventually_ge_atTop X] with x hsource hx
  intro a ha
  have hcarrier := selbergCarrier182_data H x
  have hsubset : selbergModuliSupport182 H x
      (P.sieveFaceArray H i (sievePairLeft k) x) (P.sieveFaceArray H i (sievePairRight k) x) ⊆
      Finset.univ.biUnion (fun c : TrialDistributionIndex182 =>
        trialSourceClassModuli182 (sievePairWeight k) c x (selbergCarrier182 H x)) := by
    intro q hq
    have hdiv := erasedBandArray182_moduli_subset H P.a i
      (P.sieveFacePart i (sievePairLeft k)) (P.sieveFacePart i (sievePairRight k))
      (P.sieveRootPart (sievePairLeft k)) (P.sieveRootPart (sievePairRight k)) x hq
    apply trialSupportedModulus_mem_union (sievePairWeight k) x (selbergCarrier182 H x)
      hcarrier.2.2 q _ (hsource i k q hq)
    exact Nat.dvd_of_mem_divisors hdiv
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun q _ _ =>
    mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (norm_nonneg _))).trans
      (hb x hx (selbergCarrier182 H x) hcarrier.1 a ha)

end TrialSmoothProfiles182

#print axioms TrialBaseShiftedLogSaving182.carrier
#print axioms TrialShiftedSourceEstimates182.union_saving
#print axioms trialSupportedModulus_mem_union
#print axioms TrialSmoothProfiles182.coherent_sources_of_estimates

end PrimeGap182
