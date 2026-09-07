import BandRadialGeometry182

/-!
The actual sampled arrays for the finite-band radial profiles. Their
squarefree support, prime cap and separate radial cutoffs are derived
from the sampling formula. The amplitude and harmonic limits use the
checked 39/38-coordinate Selberg development.
-/

noncomputable section
open scoped BigOperators ENNReal Topology
open Filter MeasureTheory PrimeGap186

namespace PrimeGap182Analytic

open Classical in
def canonicalBandArray182 {d m : ℕ} (H : Finset ℕ) (a : Fin (m + 2) → ℝ)
    (F : (Fin d → Fin (m + 1) → ℝ) → ℝ) (x : ℝ) : (Fin d → ℕ) →₀ ℝ :=
  ∑ r ∈ (Fintype.piFinset (fun _ : Fin d => (selbergPrimorial182 H x).divisors)).filter
      (fun r => Squarefree (∏ k, r k)),
    Finsupp.single r (F (fun k => fragmentBandMasses a
      (primeLogConfiguration (x ^ selbergRho182) (r k))) / selbergNormalizer182 H x ^ d)

def erasedBandArray182 {m : ℕ} (H : Finset ℕ) (a : Fin (m + 2) → ℝ) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (x : ℝ) : (Fin 38 → ℕ) →₀ ℝ :=
  canonicalBandArray182 H a G x + selbergErasedArray39 i (canonicalBandArray182 H a F x)

def radialBandArray182 {m : ℕ} (H : Finset ℕ) (a : Fin (m + 2) → ℝ) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (b : Fin 512) (x : ℝ) : (Fin 38 → ℕ) →₀ ℝ :=
  erasedBandArray182 H a i (bandBlockFace182 G b) (bandBlockProfile182 F i b) x

theorem canonicalBandArray182_support_data {d m : ℕ} (H : Finset ℕ) (a : Fin (m + 2) → ℝ)
    (F : (Fin d → Fin (m + 1) → ℝ) → ℝ) (x : ℝ) (r : Fin d → ℕ)
    (hr : r ∈ (canonicalBandArray182 H a F x).support) :
    Squarefree (∏ k, r k) ∧ (∀ k, r k ∈ (selbergPrimorial182 H x).divisors) ∧
      F (fun k => fragmentBandMasses a (primeLogConfiguration (x ^ selbergRho182) (r k))) ≠ 0 := by
  classical
  let T := (Fintype.piFinset (fun _ : Fin d => (selbergPrimorial182 H x).divisors)).filter
    (fun r => Squarefree (∏ k, r k))
  have hv : canonicalBandArray182 H a F x r =
      if r ∈ T then F (fun k => fragmentBandMasses a
        (primeLogConfiguration (x ^ selbergRho182) (r k))) / selbergNormalizer182 H x ^ d else 0 := by
    simp [canonicalBandArray182, T, Finsupp.finsetSum_apply, Finsupp.single_apply]
  have hne := Finsupp.mem_support_iff.mp hr
  rw [hv] at hne
  obtain ⟨ht, hval⟩ := ite_ne_right_iff.mp hne
  exact ⟨(Finset.mem_filter.mp ht).2, Fintype.mem_piFinset.mp (Finset.mem_filter.mp ht).1,
    (div_ne_zero_iff.mp hval).1⟩

theorem selbergErasedArray39_support_witness (i : Fin 39) (y : (Fin 39 → ℕ) →₀ ℝ)
    (r : Fin 38 → ℕ) (hr : r ∈ (selbergErasedArray39 i y).support) :
    ∃ s ∈ y.support, (fun k => s (i.succAbove k)) = r := by
  have hmem := Finsupp.support_sum hr
  obtain ⟨s, hs, hsr⟩ := Finset.mem_biUnion.mp hmem
  exact ⟨s, hs, (Finset.mem_singleton.mp (Finsupp.support_single_subset hsr)).symm⟩

theorem radialBandArray182_support_data {m : ℕ} (H : Finset ℕ) (a : Fin (m + 2) → ℝ)
    (i : Fin 39) (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (b : Fin 512) (x : ℝ) (r : Fin 38 → ℕ)
    (hr : r ∈ (radialBandArray182 H a i G F b x).support) :
    Squarefree (∏ k, r k) ∧ (∀ k, r k ∈ (selbergPrimorial182 H x).divisors) ∧
      bandFaceBlockMask182 b (fun k => fragmentBandMasses a
        (primeLogConfiguration (x ^ selbergRho182) (r k))) = 1 := by
  classical
  have hmem := Finsupp.support_add hr
  rcases Finset.mem_union.mp hmem with hw | he
  · obtain ⟨hsf, hdiv, hval⟩ := canonicalBandArray182_support_data H a (bandBlockFace182 G b) x r hw
    have hm : bandFaceBlockMask182 b (fun k => fragmentBandMasses a
        (primeLogConfiguration (x ^ selbergRho182) (r k))) ≠ 0 := (mul_ne_zero_iff.mp hval).1
    exact ⟨hsf, hdiv, (bandFaceBlockMask182_values b _).resolve_left hm⟩
  · obtain ⟨s, hs, hsr⟩ := selbergErasedArray39_support_witness i
      (canonicalBandArray182 H a (bandBlockProfile182 F i b) x) r he
    obtain ⟨hsf, hdiv, hval⟩ := canonicalBandArray182_support_data H a (bandBlockProfile182 F i b) x s hs
    have hrdvd : (∏ k, r k) ∣ ∏ k, s k := by
      rw [← hsr, Fin.prod_univ_succAbove _ i]
      exact dvd_mul_left _ _
    have hrdiv : ∀ k, r k ∈ (selbergPrimorial182 H x).divisors := by
      intro k
      simpa only [← hsr] using hdiv (i.succAbove k)
    have hm : bandFaceBlockMask182 b (i.removeNth (fun k => fragmentBandMasses a
        (primeLogConfiguration (x ^ selbergRho182) (s k)))) ≠ 0 := (mul_ne_zero_iff.mp hval).1
    have hmask := (bandFaceBlockMask182_values b _).resolve_left hm
    refine ⟨hsf.squarefree_of_dvd hrdvd, hrdiv, ?_⟩
    rw [← hsr]
    exact hmask

/-- A divisor of the fragment primorial has its actual configuration in
the recorded band interval. This is the generic finite-prime argument from
the baseline source-support bridge, with no source-row specialization. -/
theorem primeLogConfiguration_restrict_of_fragment_divisor (W : ℕ) (R κ : ℝ)
    (hR : 1 < R) (hκ : 0 < κ) (s : ℕ)
    (hs : s ∈ (∏ p ∈ fragmentPrimes W R κ, p).divisors) :
    (primeLogConfiguration R s).restrict (Set.Ioc (0 : ℝ) κ) = primeLogConfiguration R s := by
  have hd := (mem_fragment_divisors_iff W R κ (Real.one_le_rpow hR.le hκ.le) s).mp hs
  have hmark (p : ℕ) (hp : p ∈ s.primeFactors) :
      Real.log p / Real.log R ∈ Set.Ioc (0 : ℝ) κ := by
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpR : (p : ℝ) ≤ R ^ κ :=
      (Nat.cast_le.mpr ((Finset.le_sup (f := id) hp).trans (le_max_right 1 _))).trans hd.2.2
    refine ⟨div_pos (Real.log_pos (by exact_mod_cast hprime.one_lt)) (Real.log_pos hR), ?_⟩
    exact (div_le_iff₀ (Real.log_pos hR)).mpr
      ((Real.le_rpow_iff_log_le (by exact_mod_cast hprime.pos) (zero_lt_one.trans hR)).mp hpR)
  apply FiniteMeasure.toMeasure_injective
  simp only [FiniteMeasure.restrict_measure_eq, primeLogConfiguration, FiniteMeasure.toMeasure_sum]
  change (Measure.restrictₗ (Set.Ioc (0 : ℝ) κ)) _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  change ((Real.log p / Real.log R).toNNReal • Measure.dirac (Real.log p / Real.log R)).restrict
    (Set.Ioc (0 : ℝ) κ) = _
  rw [Measure.restrict_smul, restrict_dirac, ite_eq_left (hmark p hp)]
  rfl

theorem radialBandArray182_radius {m : ℕ} (H : Finset ℕ) (a : Fin (m + 2) → ℝ)
    (ha : StrictMono a) (ha0 : a 0 = 0) (haLast : a (Fin.last (m + 1)) = selbergFragmentCap182)
    (i : Fin 39) (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (b : Fin 512) (x : ℝ) (hx : 1 < x)
    (r : Fin 38 → ℕ) (hr : r ∈ (radialBandArray182 H a i G F b x).support) :
    ((∏ k, r k : ℕ) : ℝ) ≤ x ^ radialSieveRadius182 b := by
  obtain ⟨hsf, hdiv, hmask⟩ := radialBandArray182_support_data H a i G F b x r hr
  have hρ : 0 < selbergRho182 := by norm_num [selbergRho182]
  have hκ : 0 < selbergFragmentCap182 := by norm_num [selbergFragmentCap182, selbergRho182]
  have hR : 1 < x ^ selbergRho182 := Real.one_lt_rpow hx hρ
  have hc (k : Fin 38) : (primeLogConfiguration (x ^ selbergRho182) (r k)).restrict
      (Set.Ioc (a 0) (a (Fin.last (m + 1)))) = primeLogConfiguration (x ^ selbergRho182) (r k) := by
    rw [ha0, haLast]
    exact primeLogConfiguration_restrict_of_fragment_divisor (presievingModulus H x)
      (x ^ selbergRho182) selbergFragmentCap182 hR hκ (r k) (hdiv k)
  have hp := bandFaceBlockMask182_pullback a ha.monotone
    (fun k => primeLogConfiguration (x ^ selbergRho182) (r k)) hc b
  rw [hp] at hmask
  have hm := radialSieveRadius182_covers_block b _ hmask
  have hrho : (PrimeGap182.trialRhoStar : ℝ) = selbergRho182 := by
    norm_num [PrimeGap182.trialRhoStar, selbergRho182]
  rw [hrho, primeLogConfiguration_total_mass 38 _ hR r hsf] at hm
  have hlog : logSize (x ^ selbergRho182) (∏ k, r k) ≤ radialSieveRadius182 b / selbergRho182 :=
    (le_div_iff₀' hρ).mpr hm
  have hsize := (Real.logb_le_iff_le_rpow hR
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hsf.ne_zero))).mp hlog
  have heq : (x ^ selbergRho182) ^ (radialSieveRadius182 b / selbergRho182) =
      x ^ radialSieveRadius182 b := by
    rw [← Real.rpow_mul (zero_lt_one.trans hx).le, ← mul_div_assoc,
      mul_div_cancel_left₀ _ hρ.ne']
  exact hsize.trans_eq heq

theorem erasedBandArray182_amplitude {H : Finset ℕ} (hH : H.card = 39) {m : ℕ}
    (a : Fin (m + 2) → ℝ) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hbG : Bornology.IsBounded (Set.range G)) (hbF : Bornology.IsBounded (Set.range F)) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ x : ℝ in atTop, ∀ r,
      |erasedBandArray182 H a i G F x r| ≤ M / selbergNormalizer182 H x ^ 38 := by
  obtain ⟨M, hM, hm⟩ := PrimeGap182.Selberg.canonical_and_erased_diagonal_amplitude
    (𝓗 := H) (h𝓗_card := hH) i selbergFragmentCap182
    (by norm_num [selbergFragmentCap182, selbergRho182]) a G F hbG hbF
  refine ⟨M, hM, ?_⟩
  filter_upwards [hm] with x hx
  have hbound := hx.2.2.2.2.2.2.2.2.2
  simpa only [erasedBandArray182, canonicalBandArray182, selbergErasedArray39,
    selbergNormalizer182, selbergPrimorial182, selbergRho182, finPiFinset_eq_classical] using hbound

#print axioms radialBandArray182_support_data
#print axioms radialBandArray182_radius
#print axioms erasedBandArray182_amplitude

end PrimeGap182Analytic
