import BandPrimeGram182
import WeightMeans182

/-! The exact coherent discrepancy interface for the sampled 39/38 trial.
The modulus set is the image of compatible pairs having nonzero Selberg
coefficients, and the arithmetic sequence is the actual shifted prime,
sharp-minorant or sharp-defect sequence. Carrier support and roughness
are proved here; the distribution estimate is an explicit hypothesis. -/

noncomputable section
open MeasureTheory Filter PrimeGap186
open scoped BigOperators Topology

namespace PrimeGap182Analytic

def selbergCarrier182 (H : Finset ℕ) (x : ℝ) : Finset ℕ :=
  (presievingModulus H x).primeFactors ∪
    fragmentPrimes (presievingModulus H x) (x ^ selbergRho182) selbergFragmentCap182

open Classical in
def selbergModuliSupport182 (H : Finset ℕ) (x : ℝ)
    (z z' : (Fin 38 → ℕ) →₀ ℝ) : Finset ℕ :=
  (((selbergDivisorSupport182 z).product (selbergDivisorSupport182 z')).filter
    (fun de => SelbergCompatible182 de.1 de.2 ∧
      PrimeGap182.Selberg.selbergCoefficient z de.1 ≠ 0 ∧
      PrimeGap182.Selberg.selbergCoefficient z' de.2 ≠ 0)).image
    (fun de => Nat.lcm (presievingModulus H x)
      (Nat.lcm (∏ j, de.1 j) (∏ j, de.2 j)))

open Classical in
def selbergShiftedSequence182 (w : Fin 3) (h : ℕ) (x : ℝ) : ℕ →₀ ℂ :=
  ∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).image (fun n => n + h),
    Finsupp.single n (selbergWeight182 w x n : ℂ)

open Classical in
def bandWeightedBilinear182 (H : Finset ℕ) (h : Fin 39 → ℕ) (i : Fin 39)
    (w : Fin 3) (z z' : (Fin 38 → ℕ) →₀ ℝ) (x : ℝ) (res : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
    if Nat.ModEq (presievingModulus H x) n res then
      selbergWeight182 w x (n + h i) *
        sampledSelbergRoot z (fun j => n + h (i.succAbove j)) *
        sampledSelbergRoot z' (fun j => n + h (i.succAbove j)) else 0

/-- Uniform constants and thresholds are independent of the coherent residue.
This is a pending distribution input, not a theorem asserted here. -/
def BandCoherentDiscrepancy182 (H : Finset ℕ) (h : Fin 39 → ℕ) (i : Fin 39)
    (w : Fin 3) (z z' : ℝ → (Fin 38 → ℕ) →₀ ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
    ∀ a : ℕ, Nat.Coprime a (∏ p ∈ selbergCarrier182 H x, p) →
      (∑ q ∈ selbergModuliSupport182 H x (z x) (z' x),
        (q.divisors.card : ℝ) ^ 13 *
          ‖fullDiscrepancy (selbergShiftedSequence182 w (h i) x) q a‖) ≤
        K * x / (Real.log x) ^ (A + 2)

theorem selbergCarrier182_data (H : Finset ℕ) (x : ℝ) :
    (∀ p ∈ selbergCarrier182 H x, p.Prime) ∧
      (∏ p ∈ selbergCarrier182 H x, p) = presievingModulus H x * selbergPrimorial182 H x ∧
      0 < ∏ p ∈ selbergCarrier182 H x, p :=
  (PrimeGap182.Selberg.canonical39_presieving_fragment_carrier
    (𝓗 := H) x (x ^ selbergRho182) selbergFragmentCap182).2

theorem selbergCarrier182_prime_cap (H : Finset ℕ) :
    ∀ᶠ x : ℝ in atTop, 1 < x ∧ ∀ p ∈ selbergCarrier182 H x,
      (p : ℝ) ≤ x ^ (17277 / 100000 : ℝ) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_presieving_factor_lt_rpow H (17277 / 100000) (by norm_num)] with x hx hW
  refine ⟨hx, ?_⟩
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact (hW p hp).le
  · have hprime := Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
    have hb := (Nat.le_floor_iff' hprime.ne_zero).mp
      (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).1
    have heq : (x ^ selbergRho182) ^ selbergFragmentCap182 =
        x ^ (17277 / 100000 : ℝ) := by
      rw [← Real.rpow_mul (zero_lt_one.trans hx).le]
      norm_num [selbergRho182, selbergFragmentCap182]
    exact heq ▸ hb

theorem selbergWeight182_coprime (w : Fin 3) (x : ℝ) (hx : 1 < x)
    (n q : ℕ) (hxn : x ≤ (n : ℝ))
    (hcap : ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ x ^ (17277 / 100000 : ℝ))
    (hn : selbergWeight182 w x n ≠ 0) : Nat.Coprime n q := by
  classical
  have hs : n.Prime ∨ SharpExceptional x (41361 / 100000) n := by
    by_contra hs
    push Not at hs
    fin_cases w <;> simp [selbergWeight182, primeIndicator, sharpMinorant,
      sharpDefect, hs.1, hs.2] at hn
  rcases hs with hp | he
  · apply hp.coprime_iff_not_dvd.mpr
    intro hq
    have hlt : x ^ (17277 / 100000 : ℝ) < x := by
      simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hx
        (by norm_num : (17277 / 100000 : ℝ) < 1)
    exact (not_lt_of_ge hxn) ((hcap n hp hq).trans_lt hlt)
  · apply sharpExceptional_coprime_of_prime_cap x (41361 / 100000) hx n q hxn he
    intro p hp hpq
    exact (hcap p hp hpq).trans (Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num))

theorem erasedBandArray182_lcm_dvd_carrier {m : ℕ} (H : Finset ℕ)
    (a : Fin (m + 2) → ℝ) (i : Fin 39)
    (G G' : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F F' : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (x : ℝ)
    (d : Fin 38 → ℕ) (hd : d ∈ selbergDivisorSupport182 (erasedBandArray182 H a i G F x))
    (e : Fin 38 → ℕ) (he : e ∈ selbergDivisorSupport182 (erasedBandArray182 H a i G' F' x)) :
    Nat.lcm (presievingModulus H x) (Nat.lcm (∏ j, d j) (∏ j, e j)) ∣
      ∏ p ∈ selbergCarrier182 H x, p := by
  rw [(selbergCarrier182_data H x).2.1]
  exact Nat.lcm_dvd (dvd_mul_right _ _)
    ((Nat.lcm_dvd (erasedBandArray182_divisor_support_data H a i G F x d hd).2.2
      (erasedBandArray182_divisor_support_data H a i G' F' x e he).2.2).trans (dvd_mul_left _ _))

theorem erasedBandArray182_moduli_subset {m : ℕ} (H : Finset ℕ)
    (a : Fin (m + 2) → ℝ) (i : Fin 39)
    (G G' : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F F' : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (x : ℝ) :
    selbergModuliSupport182 H x (erasedBandArray182 H a i G F x)
        (erasedBandArray182 H a i G' F' x) ⊆ (∏ p ∈ selbergCarrier182 H x, p).divisors := by
  classical
  intro q hq
  obtain ⟨⟨d,e⟩, hde, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hd, he⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hde).1
  exact Nat.mem_divisors.mpr ⟨erasedBandArray182_lcm_dvd_carrier H a i G G' F F' x d hd e he,
    (selbergCarrier182_data H x).2.2.ne'⟩

set_option maxHeartbeats 2000000 in
open Classical in
theorem erasedBandArray182_finite_weighted_moment {H : Finset ℕ} (hH : H.card = 39)
    {m : ℕ} (a : Fin (m + 2) → ℝ) (i : Fin 39) (w : Fin 3)
    (G G' : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F F' : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (x : ℝ) (hx : 1 < x)
    (hcap : ∀ p ∈ selbergCarrier182 H x, (p : ℝ) ≤ x ^ (17277 / 100000 : ℝ))
    (C C' Err : ℝ) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hb : ∀ d, |PrimeGap182.Selberg.selbergCoefficient (erasedBandArray182 H a i G F x) d| ≤ C)
    (hb' : ∀ d, |PrimeGap182.Selberg.selbergCoefficient (erasedBandArray182 H a i G' F' x) d| ≤ C')
    (hSource : ∀ b : ℕ, Nat.Coprime b (∏ p ∈ selbergCarrier182 H x, p) →
      (∑ q ∈ selbergModuliSupport182 H x (erasedBandArray182 H a i G F x)
          (erasedBandArray182 H a i G' F' x),
        (q.divisors.card : ℝ) ^ 13 *
          ‖fullDiscrepancy (selbergShiftedSequence182 w (H.orderEmbOfFin hH i) x) q b‖) ≤ Err)
    (res : ℕ) (hres : Nat.Coprime (res + H.orderEmbOfFin hH i) (presievingModulus H x)) :
    |bandWeightedBilinear182 H (H.orderEmbOfFin hH) i w
        (erasedBandArray182 H a i G F x) (erasedBandArray182 H a i G' F' x) x res -
      ((∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊, selbergWeight182 w x (n + H.orderEmbOfFin hH i)) /
        ((presievingModulus H x).totient : ℝ)) *
          selbergPrimeGram182 (erasedBandArray182 H a i G F x)
            (erasedBandArray182 H a i G' F' x)| ≤ C * C' * Err := by
  let z := erasedBandArray182 H a i G F x
  let z' := erasedBandArray182 H a i G' F' x
  let h := H.orderEmbOfFin hH
  have hcover : ∀ j k : Fin 39, h j ≠ h k → ∀ p : ℕ,
      p.Prime → p ∣ Nat.dist (h j) (h k) → p ∣ presievingModulus H x := by
    intro j k hjk p hp hpd
    exact PrimeGap182.Selberg.difference_prime_dvd_presieving H x
      (H.orderEmbOfFin_mem hH j) (H.orderEmbOfFin_mem hH k) hjk hp hpd
  have hweight (d : Fin 38 → ℕ) (hd : d ∈ selbergDivisorSupport182 z)
      (e : Fin 38 → ℕ) (he : e ∈ selbergDivisorSupport182 z')
      (_hc : ∀ j k : Fin 38, j ≠ k → Nat.Coprime (d j) (e k))
      (n : ℕ) (hn : n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊)
      (hne : selbergWeight182 w x (n + h i) ≠ 0) :
      Nat.Coprime (n + h i)
        (Nat.lcm (presievingModulus H x) (Nat.lcm (∏ j, d j) (∏ j, e j))) := by
    apply selbergWeight182_coprime w x hx (n + h i) _
      ((Nat.le_of_ceil_le (Finset.mem_Icc.mp hn).1).trans (by exact_mod_cast Nat.le_add_right n (h i))) _ hne
    intro p hp hpd
    have hdvd := hpd.trans (erasedBandArray182_lcm_dvd_carrier H a i G G' F F' x d hd e he)
    obtain ⟨r, hr, hpr⟩ := hp.prime.exists_mem_finset_dvd hdvd
    have heq := (Nat.prime_dvd_prime_iff_eq hp ((selbergCarrier182_data H x).1 r hr)).mp hpr
    exact heq ▸ hcap r hr
  have hmoduli (d : Fin 38 → ℕ) (hd : d ∈ selbergDivisorSupport182 z)
      (e : Fin 38 → ℕ) (he : e ∈ selbergDivisorSupport182 z')
      (hc : ∀ j k : Fin 38, j ≠ k → Nat.Coprime (d j) (e k))
      (hdne : PrimeGap182.Selberg.selbergCoefficient z d ≠ 0)
      (hene : PrimeGap182.Selberg.selbergCoefficient z' e ≠ 0) :
      Nat.lcm (presievingModulus H x) (Nat.lcm (∏ j, d j) (∏ j, e j)) ∈
        selbergModuliSupport182 H x z z' :=
    Finset.mem_image.mpr ⟨(d,e), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hd,he⟩, hc, hdne, hene⟩, rfl⟩
  have hraw := PrimeGap182.Selberg.selberg38_coherent_weighted_moment_bound h h.injective i
    (selbergDivisorSupport182 z) (selbergDivisorSupport182 z')
    (PrimeGap182.Selberg.selbergCoefficient z) (PrimeGap182.Selberg.selbergCoefficient z')
    (presievingModulus H x) res (presieving_pos H x)
    (fun d hd => ⟨(erasedBandArray182_divisor_support_data H a i G F x d hd).1,
      (erasedBandArray182_divisor_support_data H a i G F x d hd).2.1⟩)
    (fun e he => ⟨(erasedBandArray182_divisor_support_data H a i G' F' x e he).1,
      (erasedBandArray182_divisor_support_data H a i G' F' x e he).2.1⟩)
    hcover hres (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊) (selbergWeight182 w x) hweight
    C C' Err hC hC' (fun d _ => hb d) (fun e _ => hb' e)
    (selbergCarrier182 H x) (selbergCarrier182_data H x).1
    (selbergModuliSupport182 H x z z') (erasedBandArray182_moduli_subset H a i G G' F F' x)
    hmoduli hSource
  simpa only [bandWeightedBilinear182, sampledSelbergRoot_fin, selbergPrimeGram182,
    selbergDivisorSupport182, z, z', h,
    finPiFinset_eq_classical] using hraw

#print axioms selbergCarrier182_prime_cap
#print axioms selbergWeight182_coprime
#print axioms erasedBandArray182_moduli_subset
#print axioms erasedBandArray182_finite_weighted_moment

end PrimeGap182Analytic
