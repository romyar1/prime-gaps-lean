import Tuple182
import BandRadialArrays182

/-! The terminal reduction from actual positive Selberg moments to prime
translates and consecutive prime gaps. The moment uses the canonical
39-coordinate sampled array, the actual presieving modulus, and the
closed integer interval already used by the arithmetic moment estimates.

The positive-moment premise is explicit. No DHL or prime-gap conclusion
is assumed. The generic weighted detection and integer-translation
lemmas from the pinned public proof have only standard axioms; its
forty-coordinate arithmetic wrappers and terminal axioms are not used. -/

noncomputable section
open Filter PrimeGap186
open scoped BigOperators Topology

namespace PrimeGap182Analytic

open Classical in
def bandPrimeMoment182 {m : ℕ} (H : Finset ℕ) (a : Fin (m + 2) → ℝ)
    (h : Fin 39 → ℕ) (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (x : ℝ) (res : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
    if Nat.ModEq (presievingModulus H x) n res then
      (((H.filter (fun h => (n + h).Prime)).card : ℝ) - 1) *
        sampledSelbergRoot (canonicalBandArray182 H a F x) (fun k => n + h k) ^ 2 else 0

theorem two_prime_translates_of_bandPrimeMoment_pos {m : ℕ} (H : Finset ℕ)
    (a : Fin (m + 2) → ℝ) (h : Fin 39 → ℕ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (x : ℝ) (res : ℕ)
    (hpos : 0 < bandPrimeMoment182 H a h F x res) :
    ∃ n : ℕ, ⌈x⌉₊ ≤ n ∧ n ≤ ⌊2 * x⌋₊ ∧
      Nat.ModEq (presievingModulus H x) n res ∧
        2 ≤ (H.filter (fun h => (n + h).Prime)).card := by
  classical
  let s := (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter
    (fun n => Nat.ModEq (presievingModulus H x) n res)
  let w : ℕ → ℝ := fun n =>
    sampledSelbergRoot (canonicalBandArray182 H a F x) (fun k => n + h k) ^ 2
  have hm : 0 < ∑ n ∈ s, (((H.filter (fun h => (n + h).Prime)).card : ℝ) - 1) * w n := by
    simpa only [s, w, Finset.sum_filter, bandPrimeMoment182] using hpos
  obtain ⟨n, hn, htwo⟩ := PrimeGap186.weighted_prime_detection s w (fun _ _ => sq_nonneg _) hm
  obtain ⟨hn, hmod⟩ := Finset.mem_filter.mp hn
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
  exact ⟨n, hlo, hhi, hmod, htwo⟩

theorem infinite_two_prime_translates_of_positive_band_moments182
    {H : Finset ℕ} (hH : H.card = 39) {m : ℕ} (a : Fin (m + 2) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hlarge : ∀ N : ℕ, ∃ x : ℝ, (N : ℝ) < x ∧ ∃ res : ℕ,
      0 < bandPrimeMoment182 H a (H.orderEmbOfFin hH) F x res) :
    Set.Infinite {n : ℕ | 2 ≤ (H.filter (fun h => (n + h).Prime)).card} := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨x, hNx, res, hpos⟩ := hlarge N
  obtain ⟨n, hxn, _, _, htwo⟩ := two_prime_translates_of_bandPrimeMoment_pos
    H a (H.orderEmbOfFin hH) F x res hpos
  refine ⟨n, htwo, ?_⟩
  exact_mod_cast hNx.trans_le ((Nat.le_ceil x).trans (Nat.cast_le.mpr hxn))

theorem infinite_two_prime_translates_of_eventually_positive_band_moments182
    {H : Finset ℕ} (hH : H.card = 39) {m : ℕ} (a : Fin (m + 2) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hevent : ∀ᶠ x : ℝ in atTop, ∃ res : ℕ,
      0 < bandPrimeMoment182 H a (H.orderEmbOfFin hH) F x res) :
    Set.Infinite {n : ℕ | 2 ≤ (H.filter (fun h => (n + h).Prime)).card} := by
  apply infinite_two_prime_translates_of_positive_band_moments182 hH a F
  intro N
  exact ((eventually_gt_atTop (N : ℝ)).and hevent).exists

def PositiveBandMoments182 (H : Finset ℕ) (hH : H.card = 39) : Prop :=
  ∃ (m : ℕ) (a : Fin (m + 2) → ℝ) (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ),
    ∀ N : ℕ, ∃ x : ℝ, (N : ℝ) < x ∧ ∃ res : ℕ,
      0 < bandPrimeMoment182 H a (H.orderEmbOfFin hH) F x res

theorem infinite_nat_prime_translates_of_band_moments182
    (H : Finset ℕ) (hH : H.card = 39) (hmom : PositiveBandMoments182 H hH) :
    Set.Infinite {n : ℕ | 2 ≤ (H.filter (fun h => (n + h).Prime)).card} := by
  obtain ⟨m, a, F, hlarge⟩ := hmom
  exact infinite_two_prime_translates_of_positive_band_moments182 hH a F hlarge

theorem infinite_int_prime_translates_of_band_moments182
    (hmom : ∀ (H : Finset ℕ) (hH : H.card = 39),
      (∀ p : ℕ, p.Prime → ∃ a ∈ Finset.range p, a ∉ H.image (fun h => h % p)) →
        PositiveBandMoments182 H hH)
    (H : Finset ℤ) (hH : H.card = 39)
    (hadm : ∀ p : ℕ, p.Prime → ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a) :
    Set.Infinite {n : ℤ | 2 ≤ (H.filter (fun h => (n + h).toNat.Prime)).card} :=
  PrimeGap186.infinite_int_prime_translates_of_nat
    (fun H hH hadm => infinite_nat_prime_translates_of_band_moments182 H hH (hmom H hH hadm))
    H hH hadm

theorem prime_pair_of_tuple182_translates (n : ℕ)
    (hcount : 2 ≤ (tuple182.filter (fun h => (n + h).Prime)).card) :
    ∃ p q : ℕ, n ≤ p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q - p ≤ 182 := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp
    (show 1 < _ from Nat.lt_of_succ_le hcount)
  obtain ⟨ha, hpa⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb, hpb⟩ := Finset.mem_filter.mp hb
  have ha_bound := tuple182_endpoints.2.2 a ha
  have hb_bound := tuple182_endpoints.2.2 b hb
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact ⟨n + a, n + b, by omega, by omega, hpa, hpb, by omega⟩
  · exact ⟨n + b, n + a, by omega, by omega, hpb, hpa, by omega⟩

theorem consecutive_prime_pairs_of_infinite_tuple182_translates
    (hinf : Set.Infinite {n : ℕ | 2 ≤ (tuple182.filter (fun h => (n + h).Prime)).card}) :
    ∀ N : ℕ, ∃ p q : ℕ, N ≤ p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q - p ≤ 182 ∧
      ∀ r : ℕ, p < r → r < q → ¬r.Prime := by
  intro N
  obtain ⟨n, hn, hNn⟩ := hinf.exists_gt N
  obtain ⟨p, q, hnp, hpq, hp, hq, hgap⟩ := prime_pair_of_tuple182_translates n hn
  have hex : ∃ r : ℕ, p < r ∧ r.Prime := ⟨q, hpq, hq⟩
  have hmin := Nat.find_min' hex ⟨hpq, hq⟩
  refine ⟨p, Nat.find hex, hNn.le.trans hnp, (Nat.find_spec hex).1,
    hp, (Nat.find_spec hex).2, (Nat.sub_le_sub_right hmin p).trans hgap, ?_⟩
  intro r hpr hrs hr
  exact Nat.find_min hex hrs ⟨hpr, hr⟩

theorem primeGapLiminf_le_182_of_infinite_tuple182_translates
    (hinf : Set.Infinite {n : ℕ | 2 ≤ (tuple182.filter (fun h => (n + h).Prime)).card}) :
    PrimeGap186.primeGapLiminf ≤ (182 : EReal) := by
  apply Filter.liminf_le_of_frequently_le'
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨n, hn, hNn⟩ := hinf.exists_gt (Nat.nth Nat.Prime N)
  obtain ⟨p, q, hnp, hpq, hp, hq, hgap⟩ := prime_pair_of_tuple182_translates n hn
  have hqbound : q ≤ p + 182 := by omega
  have hnext : Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1) ≤ q := by
    rw [← Nat.nth_count hq]
    exact Nat.nth_monotone Nat.infinite_setOfPred_prime (Nat.count_strict_mono hp hpq)
  refine ⟨Nat.count Nat.Prime p, ?_, ?_⟩
  · apply (Nat.nth_le_nth Nat.infinite_setOfPred_prime).mp
    rw [Nat.nth_count hp]
    exact hNn.le.trans hnp
  · rw [Nat.nth_count hp]
    apply EReal.sub_le_of_le_add'
    exact_mod_cast hnext.trans hqbound

theorem consecutive_prime_pairs_le_182_of_band_moments
    (hmom : PositiveBandMoments182 tuple182 tuple182_card) :
    ∀ N : ℕ, ∃ p q : ℕ, N ≤ p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q - p ≤ 182 ∧
      ∀ r : ℕ, p < r → r < q → ¬r.Prime :=
  consecutive_prime_pairs_of_infinite_tuple182_translates
    (infinite_nat_prime_translates_of_band_moments182 tuple182 tuple182_card hmom)

theorem infinite_consecutive_prime_pairs_le_182_of_band_moments
    (hmom : PositiveBandMoments182 tuple182 tuple182_card) :
    Set.Infinite {p : ℕ | p.Prime ∧ ∃ q : ℕ, p < q ∧ q.Prime ∧ q - p ≤ 182 ∧
      ∀ r : ℕ, p < r → r < q → ¬r.Prime} := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, q, hNp, hpq, hp, hq, hgap, hbetween⟩ :=
    consecutive_prime_pairs_le_182_of_band_moments hmom (N + 1)
  exact ⟨p, ⟨hp, q, hpq, hq, hgap, hbetween⟩, hNp⟩

theorem primeGapLiminf_le_182_of_band_moments
    (hmom : PositiveBandMoments182 tuple182 tuple182_card) :
    PrimeGap186.primeGapLiminf ≤ (182 : EReal) :=
  primeGapLiminf_le_182_of_infinite_tuple182_translates
    (infinite_nat_prime_translates_of_band_moments182 tuple182 tuple182_card hmom)

#print axioms two_prime_translates_of_bandPrimeMoment_pos
#print axioms infinite_two_prime_translates_of_positive_band_moments182
#print axioms infinite_int_prime_translates_of_band_moments182
#print axioms consecutive_prime_pairs_le_182_of_band_moments
#print axioms infinite_consecutive_prime_pairs_le_182_of_band_moments
#print axioms primeGapLiminf_le_182_of_band_moments

end PrimeGap182Analytic
