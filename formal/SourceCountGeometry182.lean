import SourceCountCertificate182
import SourceBounds182

/-! Geometric justification of the fine/coarse source-local count bounds.
The owner event is a concrete lower bound on mass in at most two or three
coordinates; identifying that event from the actual offender belongs to the
source-cover argument. No local count inequality is assumed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

theorem source_shifted_quotient_antitone (s t c o : ℝ)
    (hst : s ≤ t) (hs : 0 < s + c) (hco : o + c ≤ 0) :
    (t - o) / (t + c) ≤ (s - o) / (s + c) := by
  have ht : 0 < t + c := by linarith
  apply (div_le_div_iff₀ ht hs).mpr
  have h := mul_nonneg (sub_nonneg.mpr hst) (neg_nonneg.mpr hco)
  nlinarith only [h]

theorem source_finite_count_budget {ι : Type*} [Fintype ι]
    (E : Finset ι) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (D : ℝ) (hD : 0 < D) (hE : ∀ i ∈ E, D ≤ x i) :
    E.card ≤ ⌊(∑ i, x i) / D⌋₊ := by
  apply Nat.le_floor
  apply (le_div_iff₀ hD).mpr
  calc
    _ = ∑ _i ∈ E, D := by simp
    _ ≤ ∑ i ∈ E, x i := Finset.sum_le_sum hE
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hx i)

theorem source_finite_owner_budget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E A : Finset ι) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (D O : ℝ) (hD : 0 < D) (hE : ∀ i ∈ E, D ≤ x i)
    (hA : O ≤ ∑ i ∈ A, x i) :
    E.card ≤ A.card + ⌊((∑ i, x i) - O) / D⌋₊ := by
  have hsum : (∑ i ∈ E \ A, x i) + (∑ i ∈ A, x i) ≤ ∑ i, x i := by
    rw [← Finset.sum_union Finset.sdiff_disjoint]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hx i)
  have hcard : ((E \ A).card : ℝ) * D ≤ (∑ i, x i) - O := by
    have hpart : ((E \ A).card : ℝ) * D ≤ ∑ i ∈ E \ A, x i := by
      calc
        _ = ∑ _i ∈ E \ A, D := by simp
        _ ≤ _ := Finset.sum_le_sum fun i hi => hE i (Finset.mem_sdiff.mp hi).1
    linarith
  have hfloor : (E \ A).card ≤ ⌊((∑ i, x i) - O) / D⌋₊ :=
    Nat.le_floor ((le_div_iff₀ hD).mpr hcard)
  exact (Finset.card_le_card_sdiff_add_card (s := E) (t := A)).trans (by omega)

theorem source_finite_count_endpoint_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E A : Finset ι) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (c L O : ℝ) (hc : c ≤ 0) (hOc : O + c ≤ 0) (hL : L ≤ ∑ i, x i)
    (hD : 0 < L + c) (hA : O ≤ ∑ i ∈ A, x i)
    (hE : ∀ i ∈ E, (∑ j, x j) + c ≤ x i) :
    E.card ≤ min (Fintype.card ι) (min ⌊L / (L + c)⌋₊
      (A.card + ⌊(L - O) / (L + c)⌋₊)) := by
  have hD' : 0 < (∑ i, x i) + c := by linarith
  apply le_min
  · simpa using Finset.card_le_card (Finset.subset_univ E)
  apply le_min
  · apply (source_finite_count_budget E x hx _ hD' hE).trans
    apply Nat.floor_mono
    simpa only [sub_zero, zero_add] using
      source_shifted_quotient_antitone L (∑ i, x i) c 0 hL hD (by simpa using hc)
  · apply (source_finite_owner_budget E A x hx _ O hD' hE hA).trans
    exact Nat.add_le_add_left (Nat.floor_mono
      (source_shifted_quotient_antitone L (∑ i, x i) c O hL hD hOc)) A.card

@[norm_cast]
theorem trialNatFloor_ratCast (q : ℚ) : ⌊(q : ℝ)⌋₊ = ⌊q⌋₊ := by
  rw [← Int.floor_toNat, Rat.floor_cast, Int.floor_toNat]

def trialSourceMidpoints (X : Fin 39 → FiniteMeasure ℝ) (i : Fin 39) : ℝ :=
  (trialCellMidpoint (trialCellIndex (X i)) : ℝ)

def trialSourceEligible (X : Fin 39 → FiniteMeasure ℝ) : Finset (Fin 39) :=
  Finset.univ.filter (fun i => trialSourceCellSum (i.removeNth X) ≤ 359896)

def TrialSourceOwnerEvent (r : TrialOuterCertificateData)
    (X : Fin 39 → FiniteMeasure ℝ) : Prop :=
  ∃ A : Finset (Fin 39), A.card ≤ r.maxOwners ∧
    (r.maxOwners = 0 ∨ 0 < A.card) ∧
    (r.ownerMass : ℝ) ≤ ∑ i ∈ A, ((X i).mass : ℝ)

theorem trialSourceMidpoints_nonneg (X : Fin 39 → FiniteMeasure ℝ) (i : Fin 39) :
    0 ≤ trialSourceMidpoints X i := by
  dsimp only [trialSourceMidpoints, trialCellMidpoint]
  exact Rat.cast_nonneg.mpr (mul_nonneg (by positivity) trialMesh_pos.le)

theorem trialSourceMidpoints_sum (X : Fin 39 → FiniteMeasure ℝ) :
    (∑ i, trialSourceMidpoints X i) =
      ((trialSourceCellSum X : ℝ) + 39 / 2) * (trialMesh : ℝ) := by
  simp only [trialSourceMidpoints, trialCellMidpoint, Rat.cast_mul, Rat.cast_add,
    Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, ← Finset.sum_mul,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, trialSourceCellSum, Nat.cast_sum]
  ring

theorem trialSourceMidpoint_mass (X : Fin 39 → FiniteMeasure ℝ) (i : Fin 39) :
    ((X i).mass : ℝ) ≤ trialSourceMidpoints X i + (trialMesh : ℝ) / 2 := by
  have hh : (0 : ℝ) < (trialMesh : ℝ) := Rat.cast_pos.mpr trialMesh_pos
  have hcell := (div_le_iff₀ hh).mp
    (Nat.lt_floor_add_one (((X i).mass : ℝ) / (trialMesh : ℝ))).le
  change ((X i).mass : ℝ) ≤ ((trialCellIndex (X i) : ℝ) + 1) * (trialMesh : ℝ) at hcell
  simp only [trialSourceMidpoints, trialCellMidpoint, Rat.cast_mul, Rat.cast_add,
    Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one]
  linarith

theorem trialSourceOwner_midpoint_budget (r : TrialOuterCertificateData)
    (X : Fin 39 → FiniteMeasure ℝ) (A : Finset (Fin 39))
    (hA : (r.ownerMass : ℝ) ≤ ∑ i ∈ A, ((X i).mass : ℝ)) :
    (trialSourceReservedMass r A.card : ℝ) ≤ ∑ i ∈ A, trialSourceMidpoints X i := by
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ A) => trialSourceMidpoint_mass X i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  simp only [trialSourceReservedMass, Rat.cast_max, Rat.cast_zero, Rat.cast_sub,
    Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
  apply max_le
  · exact Finset.sum_nonneg fun i _ => trialSourceMidpoints_nonneg X i
  · linarith

theorem trialSourceEligible_threshold (X : Fin 39 → FiniteMeasure ℝ)
    (i : Fin 39) (hi : i ∈ trialSourceEligible X) :
    (∑ k, trialSourceMidpoints X k) + (trialSourceCountOffset : ℝ) ≤
      trialSourceMidpoints X i := by
  have he := (Finset.mem_filter.mp hi).2
  have hsum : trialSourceCellSum X = trialCellIndex (X i) +
      trialSourceCellSum (i.removeNth X) := by
    simpa only [trialSourceCellSum, Fin.removeNth] using
      Fin.sum_univ_succAbove (fun k => trialCellIndex (X k)) i
  have hgrid : (359934 : ℚ) * trialMesh ≤ trialEnlargedRadius := by decide +kernel
  have hR : ((trialSourceCellSum (i.removeNth X) : ℚ) + 38) * trialMesh ≤
      trialEnlargedRadius := by
    apply le_trans _ hgrid
    apply mul_le_mul_of_nonneg_right _ trialMesh_pos.le
    exact_mod_cast (show trialSourceCellSum (i.removeNth X) + 38 ≤ 359934 by omega)
  have hR' : ((trialSourceCellSum (i.removeNth X) : ℝ) + 38) * (trialMesh : ℝ) ≤
      (trialEnlargedRadius : ℝ) := by exact_mod_cast hR
  rw [trialSourceMidpoints_sum, hsum]
  simp only [trialSourceMidpoints, trialCellMidpoint, trialSourceCountOffset,
    Rat.cast_mul, Rat.cast_add, Rat.cast_sub, Rat.cast_natCast, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_one, Nat.cast_add]
  linarith

theorem trialSource_coarse_index_bounds (X : Fin 39 → FiniteMeasure ℝ) :
    48 * (∑ i, trialCellIndex (X i) / 48) ≤ trialSourceCellSum X ∧
      trialSourceCellSum X ≤ 48 * (∑ i, trialCellIndex (X i) / 48) + 39 * 47 := by
  constructor
  · simpa only [trialSourceCellSum, Finset.mul_sum] using
      (Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin 39))) =>
        show 48 * (trialCellIndex (X i) / 48) ≤ trialCellIndex (X i) by omega)
  · simpa only [trialSourceCellSum, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_id] using
      (Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin 39))) =>
        show trialCellIndex (X i) ≤ 48 * (trialCellIndex (X i) / 48) + 47 by omega)

theorem trialSourceBandLower_le_midpoint_sum (r : TrialOuterCertificateData)
    (hShape : TrialSourceCountTableShape r) (b : Fin r.counts.length)
    (X : Fin 39 → FiniteMeasure ℝ)
    (hDomain : TrialSourceDomain r.cover X)
    (hFirst : (r.counts.get b).first ≤ trialSourceCountIndex r X) :
    (trialSourceBandLower r (r.counts.get b) : ℝ) ≤
        ∑ i, trialSourceMidpoints X i := by
  let band := r.counts.get b
  have hFirst' : band.first ≤ trialSourceCountIndex r X := hFirst
  rcases hDomain.2 with ⟨p, hp, _, _⟩
  have hsource : trialSourceFirstIndex r.cover ≤ trialSourceCellSum X :=
    (hShape.2.2.2 p).1.trans hp
  have hn : (if r.countCoarse then max (trialSourceFirstIndex r.cover) (48 * band.first)
      else band.first) ≤ trialSourceCellSum X := by
    by_cases hc : r.countCoarse = true
    · simp only [hc, ite_true, trialSourceCountIndex] at hFirst' ⊢
      exact max_le hsource ((Nat.mul_le_mul_left 48 hFirst').trans
        (trialSource_coarse_index_bounds X).1)
    · simpa [trialSourceCountIndex, hc] using hFirst'
  have hq : trialSourceBandLower r band ≤
      ((trialSourceCellSum X : ℚ) + 39 / 2) * trialMesh := by
    dsimp only [trialSourceBandLower]
    apply mul_le_mul_of_nonneg_right _ trialMesh_pos.le
    exact add_le_add (Nat.cast_le.mpr hn) (le_refl (39 / 2 : ℚ))
  rw [trialSourceMidpoints_sum]
  simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq

theorem trialSourceReservedMass_bounds (r : TrialOuterCertificateData)
    (hM : 0 ≤ r.ownerMass) (k : ℕ) :
    0 ≤ trialSourceReservedMass r k ∧ trialSourceReservedMass r k ≤ r.ownerMass := by
  dsimp only [trialSourceReservedMass]
  exact ⟨le_max_left _ _, max_le hM (sub_le_self _
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) trialMesh_pos.le) (by norm_num)))⟩

/-- Every recorded count dominates the actual eligible-coordinate count on
its source domain and owner event. The owner event gives a mass reservation,
not a count estimate. -/
theorem sourceCountBand_dominates (r : TrialOuterCertificateData)
    (hShape : TrialSourceCountTableShape r)
    (hmass : 0 ≤ r.ownerMass ∧ r.ownerMass + trialSourceCountOffset ≤ 0)
    (b : Fin r.counts.length)
    (hcert : TrialSourceCountBandCertified r (r.counts.get b))
    (X : Fin 39 → FiniteMeasure ℝ)
    (hDomain : TrialSourceDomain r.cover X)
    (hBand : (r.counts.get b).first ≤ trialSourceCountIndex r X ∧
      trialSourceCountIndex r X ≤ (r.counts.get b).last)
    (hOwner : TrialSourceOwnerEvent r X) :
    (trialSourceEligible X).card ≤ (r.counts.get b).count := by
  let band := r.counts.get b
  change TrialSourceCountBandCertified r band at hcert
  have hLower := trialSourceBandLower_le_midpoint_sum r hShape b X hDomain hBand.1
  rcases hOwner with ⟨A, hk, hkp, hA⟩
  let O := trialSourceReservedMass r A.card
  let L := max (trialSourceBandLower r band) O
  have hO : (O : ℝ) ≤ ∑ i ∈ A, trialSourceMidpoints X i :=
    trialSourceOwner_midpoint_budget r X A hA
  have hOall : (O : ℝ) ≤ ∑ i, trialSourceMidpoints X i :=
    hO.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
      (fun i _ _ => trialSourceMidpoints_nonneg X i))
  have hL : (L : ℝ) ≤ ∑ i, trialSourceMidpoints X i := by
    exact_mod_cast (max_le hLower hOall)
  by_cases hden : trialSourceBandLower r band + trialSourceCountOffset ≤ 0
  · have h39 : 39 ≤ band.count := by
      simpa only [TrialSourceCountBandCertified, hden, ite_true] using hcert
    exact (show (trialSourceEligible X).card ≤ 39 by
      simpa using Finset.card_le_card (Finset.subset_univ (trialSourceEligible X))).trans h39
  · have hDq : 0 < L + trialSourceCountOffset := by
      have := le_max_left (trialSourceBandLower r band) O
      dsimp only [L]
      linarith
    have hD : (0 : ℝ) < (L : ℝ) + (trialSourceCountOffset : ℝ) := by exact_mod_cast hDq
    have hOcq : O + trialSourceCountOffset ≤ 0 := by
      have hOM := (trialSourceReservedMass_bounds r hmass.1 A.card).2
      change O ≤ r.ownerMass at hOM
      linarith [hmass.2]
    have hOc : (O : ℝ) + (trialSourceCountOffset : ℝ) ≤ 0 := by exact_mod_cast hOcq
    have hcq : trialSourceCountOffset ≤ 0 := by linarith [hmass.1, hmass.2]
    have hc : (trialSourceCountOffset : ℝ) ≤ 0 := by exact_mod_cast hcq
    have hbound := source_finite_count_endpoint_bound (trialSourceEligible X) A
      (trialSourceMidpoints X) (trialSourceMidpoints_nonneg X)
      (trialSourceCountOffset : ℝ) (L : ℝ) (O : ℝ) hc hOc hL hD hO
      (fun i hi => trialSourceEligible_threshold X i hi)
    have hbound' : (trialSourceEligible X).card ≤ trialSourceCountFloorBound r band A.card := by
      simpa only [trialSourceCountFloorBound, Fintype.card_fin, ← Rat.cast_add,
        ← Rat.cast_sub, ← Rat.cast_div, trialNatFloor_ratCast] using hbound
    have hcert' := (show ∀ k : Fin (r.maxOwners + 1),
        (r.maxOwners = 0 ∨ 0 < k.val) → trialSourceCountFloorBound r band k.val ≤ band.count from
      by simpa only [TrialSourceCountBandCertified, hden, ite_false] using hcert)
        ⟨A.card, by omega⟩ hkp
    exact hbound'.trans hcert'

theorem trialSourceCountBand_dominates (j : Fin 60)
    (b : Fin (trialOuterCertificates j).counts.length)
    (X : Fin 39 → FiniteMeasure ℝ)
    (hDomain : TrialSourceDomain (trialOuterCertificates j).cover X)
    (hBand : ((trialOuterCertificates j).counts.get b).first ≤
        trialSourceCountIndex (trialOuterCertificates j) X ∧
      trialSourceCountIndex (trialOuterCertificates j) X ≤
        ((trialOuterCertificates j).counts.get b).last)
    (hOwner : TrialSourceOwnerEvent (trialOuterCertificates j) X) :
    (trialSourceEligible X).card ≤ ((trialOuterCertificates j).counts.get b).count :=
  sourceCountBand_dominates (trialOuterCertificates j) (trialSourceCountTable_shape j)
    ⟨(trialSourceOwnerMass_bounds j).1, (trialSourceOwnerMass_bounds j).2.1⟩ b
    (trialSourceCountBand_certified j b) X hDomain hBand hOwner

theorem sourceCountBands_cover (l : List TrialSourceCountBand) :
    l.IsChain (fun a b => a.last + 1 = b.first) → l ≠ [] →
    ∀ n : ℕ, (l.headD ⟨0, 0, 0, 0⟩).first ≤ n →
      n ≤ (l.getLastD ⟨0, 0, 0, 0⟩).last →
      ∃ b ∈ l, b.first ≤ n ∧ n ≤ b.last := by
  induction l with
  | nil => intro _ hn; exact (hn rfl).elim
  | cons a l ih =>
    intro hc _ n hlo hhi
    cases l with
    | nil => exact ⟨a, by simp, by simpa using hlo, by simpa using hhi⟩
    | cons b l =>
      by_cases ha : n ≤ a.last
      · exact ⟨a, by simp, by simpa using hlo, ha⟩
      · have hab := (List.isChain_cons_cons.mp hc).1
        obtain ⟨c, hcm, hcn⟩ := ih (List.isChain_cons_cons.mp hc).2 (by simp) n
          (by simpa using (show b.first ≤ n by omega)) (by simpa using hhi)
        exact ⟨c, List.mem_cons_of_mem a hcm, hcn⟩

theorem sourceCount_band_exists (r : TrialOuterCertificateData)
    (hshape : TrialSourceCountTableShape r)
    (X : Fin 39 → FiniteMeasure ℝ)
    (hDomain : TrialSourceDomain r.cover X) :
    ∃ b : Fin r.counts.length, (r.counts.get b).first ≤ trialSourceCountIndex r X ∧
      trialSourceCountIndex r X ≤ (r.counts.get b).last := by
  rcases hDomain.2 with ⟨p, hp, hpu, _⟩
  have hspan := (hshape.2.2.2 p).2
  have hb : trialSourceCountFirst r ≤ trialSourceCountIndex r X ∧
      trialSourceCountIndex r X ≤ trialSourceCountLast r := by
    by_cases hc : r.countCoarse = true
    · change (if r.countCoarse then _ else _) at hspan
      simp only [hc, ite_true] at hspan
      simp only [trialSourceCountIndex, hc, ite_true]
      have hq := trialSource_coarse_index_bounds X
      omega
    · change (if r.countCoarse then _ else _) at hspan
      simp only [hc] at hspan
      simpa [trialSourceCountIndex, hc] using
        (show trialSourceCountFirst r ≤ trialSourceCellSum X ∧
          trialSourceCellSum X ≤ trialSourceCountLast r from
          ⟨hspan.1.trans hp, hpu.trans hspan.2⟩)
  have hh := sourceCountBands_cover r.counts hshape.2.1
    (by have := hshape.1; exact List.ne_nil_of_length_pos this)
    (trialSourceCountIndex r X) hb.1 hb.2
  exact List.exists_mem_iff_get.mp hh

theorem trialSourceCount_band_exists (j : Fin 60)
    (X : Fin 39 → FiniteMeasure ℝ)
    (hDomain : TrialSourceDomain (trialOuterCertificates j).cover X) :
    ∃ b : Fin (trialOuterCertificates j).counts.length,
      ((trialOuterCertificates j).counts.get b).first ≤
          trialSourceCountIndex (trialOuterCertificates j) X ∧
        trialSourceCountIndex (trialOuterCertificates j) X ≤
          ((trialOuterCertificates j).counts.get b).last :=
  sourceCount_band_exists (trialOuterCertificates j) (trialSourceCountTable_shape j) X hDomain

#print axioms trialSourceCountBand_dominates
#print axioms trialSourceCount_band_exists

#print axioms source_finite_count_endpoint_bound
#print axioms trialSourceEligible_threshold
#print axioms trialSourceOwner_midpoint_budget

end PrimeGap182
