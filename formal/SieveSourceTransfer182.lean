import BoundedSourceTools182

/-! The actual closed and shifted source interfaces used by the sieve.
Arbitrary divisor weights and fixed shifts are derived from an unweighted
closed-interval estimate. The modulus carrier and the coherent residue
remain uniform throughout. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic

open Classical in
def sourceModuli182 (j : ℕ) («ω» δ : ℝ) (L0 : ℝ → ℝ) (x : ℝ) (I : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω») * L0 x⌋₊).filter (fun q =>
    q ∣ ∏ p ∈ I, p ∧ Nonempty (DenseDivisibilityWitness
      ⟨max 1 (x ^ δ), by exact le_max_left (1 : ℝ) (x ^ δ)⟩ j q))

def ClosedSourceLogSaving182 (w : Fin 3) (j : ℕ) («ω» δ : ℝ) (L0 : ℝ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ 1 < X ∧
    ∀ x : ℝ, X ≤ x → ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
    ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
      (∑ q ∈ sourceModuli182 j «ω» δ L0 x I,
        ‖fullDiscrepancy (selbergClosedSequence182 w x) q a‖) ≤ K * x / (Real.log x) ^ A

def ShiftedSourceLogSaving182 (w : Fin 3) (j : ℕ) («ω» δ : ℝ)
    (L0 : ℝ → ℝ) (h J : ℕ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ 1 < X ∧
    ∀ x : ℝ, X ≤ x → ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
    ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
      (∑ q ∈ sourceModuli182 j «ω» δ L0 x I,
        (q.divisors.card : ℝ) ^ J *
          ‖fullDiscrepancy (selbergShiftedSequence182 w h x) q a‖) ≤
        K * x / (Real.log x) ^ A

theorem subpower_source_modulus_bound182 («ω» : ℝ)
    (L0 : ℝ → ℝ) (hL0 : ∀ x, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0))
    (θ : ℝ) (hgap : 1 / 2 + 2 * «ω» < θ) :
    ∀ᶠ x : ℝ in atTop, x ^ (1 / 2 + 2 * «ω») * L0 x ≤ x ^ θ := by
  have hsmall := (tendsto_order.mp hL0sub).2 _ (sub_pos.mpr hgap)
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with x hsmallx hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hL : L0 x ≤ x ^ (θ - (1 / 2 + 2 * «ω»)) := by
    apply (Real.log_le_log_iff (hL0 x) (Real.rpow_pos_of_pos hx0 _)).mp
    rw [Real.log_rpow hx0]
    exact ((div_lt_iff₀ (Real.log_pos hx)).mp hsmallx).le
  calc
    _ ≤ x ^ (1 / 2 + 2 * «ω») * x ^ (θ - (1 / 2 + 2 * «ω»)) :=
      mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg hx0.le _)
    _ = x ^ θ := by rw [← Real.rpow_add hx0]; congr 1; ring

theorem ClosedSourceLogSaving182.shifted_weighted
    {w : Fin 3} {j : ℕ} {«ω» δ : ℝ} {L0 : ℝ → ℝ}
    (hraw : ClosedSourceLogSaving182 w j «ω» δ L0)
    (hω : 0 < «ω») (hωupper : «ω» < 1 / 4)
    (hL0 : ∀ x, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0))
    (h J : ℕ) : ShiftedSourceLogSaving182 w j «ω» δ L0 h J := by
  classical
  let θ : ℝ := (1 + (1 / 2 + 2 * «ω»)) / 2
  have hθ0 : 0 < θ := by dsimp only [θ]; linarith only [hω]
  have hθ1 : θ < 1 := by dsimp only [θ]; linarith only [hωupper]
  have hgap : 1 / 2 + 2 * «ω» < θ := by dsimp only [θ]; linarith only [hωupper]
  obtain ⟨Xq, hXq⟩ := eventually_atTop.mp
    (subpower_source_modulus_bound182 «ω» L0 hL0 hL0sub θ hgap)
  intro A hA
  obtain ⟨P, Kc, Xc, hKc, _hXc, hcrude⟩ :=
    selbergWeight_divisor_weight_log_growth θ hθ0 hθ1 (2 * J)
  have hrequested : 0 < 2 * A + (P : ℝ) := by positivity
  obtain ⟨Ks, Xs, hKs, hXs, hsmall⟩ := hraw (2 * A + (P : ℝ)) hrequested
  obtain ⟨Xe, hXe⟩ := eventually_atTop.mp
    (selbergWeight_shifted_discrepancy_divisor_weight_eventually h θ hθ1 J A)
  refine ⟨Ks + Kc + 1, max Xs (max Xc (max Xq Xe)), by positivity,
    hXs.trans_le (le_max_left _ _), ?_⟩
  intro x hx I hI a ha
  have hxs : Xs ≤ x := (le_max_left _ _).trans hx
  have hxc : Xc ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxq : Xq ≤ x := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  have hxe : Xe ≤ x := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  have hx1 : 1 < x := hXs.trans_le hxs
  let Q := sourceModuli182 j «ω» δ L0 x I
  have hQ : Q ⊆ Finset.Icc 1 ⌊x ^ θ⌋₊ := by
    intro q hq
    have hmem := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
    exact Finset.mem_Icc.mpr ⟨hmem.1, hmem.2.trans (Nat.floor_mono (hXq x hxq))⟩
  have haq (q : ℕ) (hq : q ∈ Q) : Nat.Coprime a q :=
    ha.of_dvd_right (Finset.mem_filter.mp hq).2.1
  have hunweighted := hsmall x hxs I hI a ha
  have hgrowth := hcrude x hxc w Q hQ (fun _ => a) haq
  have hweighted := sum_divisor_weighted_log_saving_of_two_bounds
    Q J (fun q => ‖fullDiscrepancy (selbergClosedSequence182 w x) q a‖)
    (fun q _ => norm_nonneg _) x (Real.log x) A Ks Kc P
    (zero_lt_one.trans hx1).le (Real.log_pos hx1) hKs hKc hunweighted hgrowth
  have herror := hXe x hxe w Q hQ (fun _ => a)
  calc
    _ ≤ ∑ q ∈ Q, (q.divisors.card : ℝ) ^ J *
        (‖fullDiscrepancy (selbergClosedSequence182 w x) q a‖ +
          ‖fullDiscrepancy (selbergShiftedSequence182 w h x) q a -
            fullDiscrepancy (selbergClosedSequence182 w x) q a‖) := by
      apply Finset.sum_le_sum
      intro q _
      have hb := norm_le_norm_add_norm_sub
        (fullDiscrepancy (selbergClosedSequence182 w x) q a)
        (fullDiscrepancy (selbergShiftedSequence182 w h x) q a)
      rw [norm_sub_rev] at hb
      exact mul_le_mul_of_nonneg_left hb (pow_nonneg (Nat.cast_nonneg _) _)
    _ = (∑ q ∈ Q, (q.divisors.card : ℝ) ^ J *
        ‖fullDiscrepancy (selbergClosedSequence182 w x) q a‖) +
        ∑ q ∈ Q, (q.divisors.card : ℝ) ^ J *
          ‖fullDiscrepancy (selbergShiftedSequence182 w h x) q a -
            fullDiscrepancy (selbergClosedSequence182 w x) q a‖ := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ (Ks + Kc) * x / (Real.log x) ^ A + x / (Real.log x) ^ A :=
      add_le_add hweighted herror
    _ = _ := by ring

theorem selbergClosedSequence182_defect (x : ℝ) :
    selbergClosedSequence182 2 x = selbergClosedSequence182 0 x - selbergClosedSequence182 1 x := by
  classical
  unfold selbergClosedSequence182
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finsupp.single_sub]
  congr 1
  simp only [selbergWeight182, Matrix.cons_val_zero, sharpMinorant,
    primeIndicator]
  push_cast
  ring

#print axioms ClosedSourceLogSaving182.shifted_weighted
#print axioms selbergClosedSequence182_defect

end PrimeGap182Analytic
