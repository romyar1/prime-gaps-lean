import HarmanAnalyticInterfaces182
import HarmanHBGeometry182

/-! Actual localized Heath-Brown products transferred to the new global
interfaces. The convolution, profiles, coefficient envelopes, coherent
residues, and coprimality-filtered Siegel--Walfisz bounds are constructed
and proved. Adapted from Apache-2.0 PrimeGaps186 at the pinned source hash.
No global estimate is asserted without its explicit interface argument. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

open Classical in
theorem sourceT3_middle_slots_log_saving_of_bilinear
    (density : ℕ) (orders : Fin 3 → Fin 5) (D : ℕ) (hD : 1 ≤ D)
    («ω» δ σclass σdist C0 : ℝ)
    (_hω : 0 < «ω») (_hδ : 0 < δ) (hσclass : 0 < σclass)
    (hσclassHalf : σclass < 1 / 2) (hσσ : σclass < σdist)
    (hσdistHalf : σdist < 1 / 2) (hC0 : 1 ≤ C0)
    (hdist : SourceBilinearEstimate density «ω» δ σdist) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ Real.exp 1 ≤ X ∧
      ∀ x : ℝ, X ≤ x →
        let Θ : ℝ := 1 + (Real.log x) ^ (-(D : ℝ))
        ∀ t : Fin 3 → ℝ, (∀ c, 0 ≤ t c) → (∀ c, t c ≤ 10) →
        ∀ ν : (c : Fin 3) → Fin (2 * ((orders c).val + 1)) → ℕ,
          let ιr := Σ c : Fin 3, Fin (2 * ((orders c).val + 1))
          let Ni : ιr → ℝ := fun s => Θ ^ ν s.1 s.2
          let β : ιr → MonoidAlgebra ℂ ℕ := fun s =>
            minorantHBLocalizedSlot ((orders s.1).val + 1) (x ^ (9 / 100 : ℝ))
              Θ (t s.1) (ν s.1) s.2
          x / C0 ≤ (∏ s, Ni s) → (∏ s, Ni s) ≤ C0 * x →
          ∀ S T : Finset ιr,
            Disjoint S T → S ∪ T = Finset.univ → S.Nonempty → T.Nonempty →
            x ^ (1 / 2 - σclass) / C0 < (∏ s ∈ S, Ni s) →
            (∏ s ∈ S, Ni s) ≤ (∏ s ∈ T, Ni s) →
          ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
          ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
            (∑ q ∈ (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
                q ∣ (∏ p ∈ I, p) ∧
                  Nonempty (DenseDivisibilityWitness
                    ⟨max 1 (x ^ δ), by exact le_max_left (1 : ℝ) (x ^ δ)⟩ density q)),
              ‖fullDiscrepancy (∏ s, β s).coeff q a‖) ≤
                K * x / (Real.log x) ^ A := by
  let ιr := Σ c : Fin 3, Fin (2 * ((orders c).val + 1))
  let Params : Type := (Fin 3 → ℝ) × ((c : Fin 3) → Fin (2 * ((orders c).val + 1)) → ℕ)
  let tclip : Params → Fin 3 → ℝ := fun v c => max 0 (min (v.1 c) 10)
  have htclip (v : Params) (c : Fin 3) : 0 ≤ tclip v c ∧ tclip v c ≤ 10 :=
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
  have hcard30 : Fintype.card ιr ≤ 30 := by
    rw [Fintype.card_sigma]
    calc
      (∑ c : Fin 3, Fintype.card (Fin (2 * ((orders c).val + 1)))) ≤
          ∑ _c : Fin 3, (10 : ℕ) :=
        Finset.sum_le_sum fun c _ => by
          simp only [Fintype.card_fin]
          have hc := (orders c).isLt
          omega
      _ = 30 := by norm_num
  have hσdist : 0 < σdist ∧ σdist < 1 / 2 :=
    ⟨hσclass.trans hσσ, hσdistHalf⟩
  have hC0pos : 0 < C0 := zero_lt_one.trans_le hC0
  let d : ℝ := (1 / 2 - σclass) / 2
  have hd : 0 < d := by dsimp only [d]; linarith only [hσclassHalf]
  have hgap : 0 < σdist - σclass := sub_pos.mpr hσσ
  have hlarge : ∀ᶠ x : ℝ in Filter.atTop,
      C0 ≤ x ^ (σdist - σclass) ∧ C0 ≤ x ^ d :=
    ((tendsto_rpow_atTop hgap).eventually_ge_atTop C0).and
      ((tendsto_rpow_atTop hd).eventually_ge_atTop C0)
  obtain ⟨Xbase, hXbase⟩ := Filter.eventually_atTop.1 hlarge
  let X0 : ℝ := max (Real.exp 1) (max C0 Xbase)
  have hX0 : Real.exp 1 ≤ X0 := le_max_left _ _
  have hC0X0 : C0 ≤ X0 := (le_max_left _ _).trans (le_max_right _ _)
  have hbaseX0 : Xbase ≤ X0 := (le_max_right _ _).trans (le_max_right _ _)
  have hxpos (x : ℝ) (hx : X0 ≤ x) : 0 < x :=
    (Real.exp_pos 1).trans_le (hX0.trans hx)
  have hxone (x : ℝ) (hx : X0 ≤ x) : 1 ≤ x :=
    (Real.one_le_exp zero_le_one).trans (hX0.trans hx)
  have hlog (x : ℝ) (hx : X0 ≤ x) : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos 1) (hX0.trans hx)
  have hlargeX (x : ℝ) (hx : X0 ≤ x) :
      C0 ≤ x ^ (σdist - σclass) ∧ C0 ≤ x ^ d :=
    hXbase x (hbaseX0.trans hx)
  let Θ : ℝ → ℝ := fun x => 1 + (Real.log x) ^ (-(D : ℝ))
  let U : ℝ → ℝ := fun x => x ^ (9 / 100 : ℝ)
  let η : ℝ → ℝ → ℝ := fun x => minorantHBProfile (Θ x)
  let μU : ℝ → ArithmeticFunction ℝ := fun x =>
    arithmeticFunctionLowCutoff (U x)
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
  let f : ℝ → ιr → ArithmeticFunction ℝ := fun x s =>
    minorantHBSlot ((orders s.1).val + 1) (U x) s.2
  let scale : ℝ → Params → ιr → ℝ := fun x v s => Θ x ^ v.2 s.1 s.2
  let slot : ℝ → Params → ιr → MonoidAlgebra ℂ ℕ := fun x v s =>
    minorantHBLocalizedSlot ((orders s.1).val + 1) (U x)
      (Θ x) (tclip v s.1) (v.2 s.1) s.2
  let P : ℝ → Params → ℝ := fun x ν => ∏ i, scale x ν i
  let Q : ℝ → Params → Finset (ιr) → ℝ :=
    fun x ν G => ∏ i ∈ G, scale x ν i
  let coeff : ℝ → Params → Finset (ιr) → ℕ →₀ ℂ :=
    fun x ν G => (∏ i ∈ G, slot x ν i).coeff
  have hΘ (x : ℝ) (hx : X0 ≤ x) : 1 < Θ x ∧ Θ x ≤ 2 := by
    have hℓpos : 0 < Real.log x := zero_lt_one.trans_le (hlog x hx)
    have hsmall : (Real.log x) ^ (-(D : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (hlog x hx)
        (neg_nonpos.mpr (by exact_mod_cast (Nat.zero_le 1).trans hD))
    dsimp only [Θ]
    exact ⟨lt_add_of_pos_right 1 (Real.rpow_pos_of_pos hℓpos _), by linarith⟩
  have hscaleone (x : ℝ) (hx : X0 ≤ x) (ν : Params)
      (i : ιr) : 1 ≤ scale x ν i :=
    one_le_pow₀ (hΘ x hx).1.le
  have hQone (x : ℝ) (hx : X0 ≤ x) (ν : Params)
      (G : Finset (ιr)) : 1 ≤ Q x ν G :=
    Finset.one_le_prod fun i _hi => hscaleone x hx ν i
  have hcard40 (G : Finset ιr) : G.card ≤ 40 :=
    (Finset.card_le_univ G).trans (hcard30.trans (by norm_num))
  let B2 : ℝ := (2 : ℝ) ^ 40
  let c : ℝ := 1 / B2
  let Cf : ℝ := B2 * C0 ^ 2
  let W : ℝ := (4 : ℝ) ^ 40
  have hB2pos : 0 < B2 := by positivity
  have hB2one : 1 ≤ B2 := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hc : 0 < c := div_pos zero_lt_one hB2pos
  have hC0sq : C0 ≤ C0 ^ 2 := le_self_pow₀ hC0 (by decide)
  have hC0Cf : C0 ≤ Cf :=
    hC0sq.trans (le_mul_of_one_le_left (sq_nonneg C0) hB2one)
  have hCf : 1 ≤ Cf := hC0.trans hC0Cf
  have hW : 0 ≤ W := by positivity
  have hgeometry (x P' PS PT : ℝ) (hx : X0 ≤ x)
      (hPSone : 1 ≤ PS) (hPTone : 1 ≤ PT) (hprod : PS * PT = P')
      (hPlower : x / C0 ≤ P') (hPupper : P' ≤ C0 * x)
      (hPSlower : x ^ (1 / 2 - σclass) / C0 < PS) (hST : PS ≤ PT) :
      (x / Cf ≤ PT * min PS (Real.sqrt x) ∧
        PT * min PS (Real.sqrt x) ≤ Cf * x ∧
        x ^ (1 / 2 - σdist) ≤ min PS (Real.sqrt x) ∧
        min PS (Real.sqrt x) ≤ x ^ (1 / 2 : ℝ)) ∧
      PS ≤ C0 * min PS (Real.sqrt x) ∧ x ^ d ≤ PS ∧ PS ≤ x ^ (2 : ℝ) := by
    have hPSpos : 0 < PS := zero_lt_one.trans_le hPSone
    have hPTpos : 0 < PT := zero_lt_one.trans_le hPTone
    have hPSsq : PS ^ 2 ≤ C0 * x := by
      calc
        PS ^ 2 = PS * PS := pow_two PS
        _ ≤ PS * PT := mul_le_mul_of_nonneg_left hST hPSpos.le
        _ = P' := hprod
        _ ≤ C0 * x := hPupper
    have hPSroot : PS ≤ C0 * Real.sqrt x := by
      calc
        PS ≤ Real.sqrt (C0 * x) := Real.le_sqrt_of_sq_le hPSsq
        _ = Real.sqrt C0 * Real.sqrt x := Real.sqrt_mul hC0pos.le x
        _ ≤ C0 * Real.sqrt x :=
          mul_le_mul_of_nonneg_right
            (Real.sqrt_le_self_iff.mpr (Or.inr hC0)) (Real.sqrt_nonneg x)
    have hPSN : PS ≤ C0 * min PS (Real.sqrt x) := by
      rw [mul_min_of_nonneg _ _ hC0pos.le]
      exact le_min (le_mul_of_one_le_left hPSpos.le hC0) hPSroot
    have hpolyLower : x ^ d ≤ PS := by
      have hh : x ^ d * C0 ≤ x ^ (1 / 2 - σclass) := by
        calc
          x ^ d * C0 ≤ x ^ d * x ^ d :=
            mul_le_mul_of_nonneg_left (hlargeX x hx).2
              (Real.rpow_nonneg (hxpos x hx).le d)
          _ = x ^ (1 / 2 - σclass) := by
            rw [← Real.rpow_add (hxpos x hx)]
            congr 1
            dsimp only [d]
            ring
      exact ((le_div_iff₀ hC0pos).2 hh).trans hPSlower.le
    have hpolyUpper : PS ≤ x ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      calc
        PS ≤ PS * PT := le_mul_of_one_le_right hPSpos.le hPTone
        _ = P' := hprod
        _ ≤ C0 * x := hPupper
        _ ≤ x * x := mul_le_mul_of_nonneg_right (hC0X0.trans hx) (hxpos x hx).le
        _ = x ^ 2 := (pow_two x).symm
    have hNlower : x ^ (1 / 2 - σdist) ≤ min PS (Real.sqrt x) := by
      apply le_min
      · have hh : x ^ (1 / 2 - σdist) * C0 ≤ x ^ (1 / 2 - σclass) := by
          calc
            x ^ (1 / 2 - σdist) * C0 ≤
                x ^ (1 / 2 - σdist) * x ^ (σdist - σclass) :=
              mul_le_mul_of_nonneg_left (hlargeX x hx).1
                (Real.rpow_nonneg (hxpos x hx).le _)
            _ = x ^ (1 / 2 - σclass) := by
              rw [← Real.rpow_add (hxpos x hx)]
              congr 1
              ring
        exact ((le_div_iff₀ hC0pos).2 hh).trans hPSlower.le
      · rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le (hxone x hx)
          (sub_le_self _ hσdist.1.le)
    have hMNlower : x / C0 ≤ PT * min PS (Real.sqrt x) := by
      by_cases hh : PS ≤ Real.sqrt x
      · calc
          x / C0 ≤ P' := hPlower
          _ = PT * min PS (Real.sqrt x) := by
            rw [min_eq_left hh, mul_comm, hprod]
      · have hh' : Real.sqrt x ≤ PS := (lt_of_not_ge hh).le
        calc
          x / C0 ≤ x := div_le_self (hxpos x hx).le hC0
          _ = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt (hxpos x hx).le).symm
          _ ≤ PT * Real.sqrt x :=
            mul_le_mul_of_nonneg_right (hh'.trans hST) (Real.sqrt_nonneg x)
          _ = PT * min PS (Real.sqrt x) := by rw [min_eq_right hh']
    have hMNupper : PT * min PS (Real.sqrt x) ≤ C0 * x := by
      calc
        PT * min PS (Real.sqrt x) ≤ PT * PS :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hPTpos.le
        _ = P' := (mul_comm PT PS).trans hprod
        _ ≤ C0 * x := hPupper
    refine ⟨⟨?_, ?_, hNlower, ?_⟩, hPSN, hpolyLower, hpolyUpper⟩
    · exact (div_le_div_of_nonneg_left (hxpos x hx).le hC0pos hC0Cf).trans hMNlower
    · exact hMNupper.trans (mul_le_mul_of_nonneg_right hC0Cf (hxpos x hx).le)
    · simpa only [Real.sqrt_eq_rpow] using min_le_right PS (Real.sqrt x)
  have hbox (x : ℝ) (hx : X0 ≤ x) (ν : Params)
      (hPupper : P x ν ≤ C0 * x) (G : Finset (ιr)) (hG : G.Nonempty) :
      (∀ n ∈ (coeff x ν G).support,
        Q x ν G / (2 : ℝ) ^ G.card ≤ (n : ℝ) ∧
          (n : ℝ) ≤ (2 : ℝ) ^ G.card * Q x ν G) ∧
      ∀ n : ℕ, ‖coeff x ν G n‖ ≤
        W * (n.divisors.card : ℝ) ^ 40 * (Real.log x) ^ 40 := by
    have hslotData (s : ιr) :
        (∀ n ∈ (slot x ν s).coeff.support,
          scale x ν s / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * scale x ν s) ∧
        ∀ n : ℕ, ‖(slot x ν s).coeff n‖ ≤ 1 + Real.log (n : ℝ) :=
      sourceT3_localized_slot_support_norm ((orders s.1).val + 1) (U x)
        (Θ x) (tclip ν s.1) (ν.2 s.1) s.2 (hΘ x hx).1 (hΘ x hx).2 (htclip ν s.1).1
    have hslotNorm (s : ιr) (n : ℕ) : ‖(slot x ν s).coeff n‖ ≤ 4 * Real.log x := by
      by_cases hn : n ∈ (slot x ν s).coeff.support
      · have hNi : scale x ν s ≤ x ^ (2 : ℕ) := by
          calc
            scale x ν s ≤ ∏ u, scale x ν u :=
              Multiset.mem_le_prod_of_one_le (s := Finset.univ.val)
                (hscaleone x hx ν) (Finset.mem_univ s)
            _ ≤ C0 * x := hPupper
            _ ≤ x * x := mul_le_mul_of_nonneg_right (hC0X0.trans hx) (hxpos x hx).le
            _ = x ^ 2 := (pow_two x).symm
        have hns := (hslotData s).1 n hn
        have hnpos : 0 < (n : ℝ) :=
          (div_pos (zero_lt_one.trans_le (hscaleone x hx ν s)) zero_lt_two).trans_le hns.1
        have hnup : (n : ℝ) ≤ 2 * x ^ (2 : ℕ) :=
          hns.2.trans (mul_le_mul_of_nonneg_left hNi zero_le_two)
        have hln := Real.log_le_log hnpos hnup
        rw [Real.log_mul two_ne_zero (pow_ne_zero 2 (hxpos x hx).ne'), Real.log_pow] at hln
        norm_num only [Nat.cast_ofNat] at hln
        have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        exact ((hslotData s).2 n).trans (by linarith [hlog x hx])
      · rw [Finsupp.notMem_support_iff.mp hn, norm_zero]
        exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (zero_le_one.trans (hlog x hx))
    have hℓ : 1 ≤ Real.log x := hlog x hx
    have hbase : 1 ≤ 4 * Real.log x := by linarith
    have hraw := heathBrown_box_product_support_norm_bound G hG
      (slot x ν) (scale x ν) (4 * Real.log x) (zero_le_one.trans hbase)
      (fun i _hi => hscaleone x hx ν i)
      (fun i _hi => (hslotData i).1) (fun i _hi => hslotNorm i)
    change (∀ n ∈ (coeff x ν G).support,
      Q x ν G / (2 : ℝ) ^ G.card ≤ (n : ℝ) ∧
        (n : ℝ) ≤ (2 : ℝ) ^ G.card * Q x ν G) ∧
      (∀ n : ℕ, ‖coeff x ν G n‖ ≤
        (4 * Real.log x) ^ G.card * (n.divisors.card : ℝ) ^ (G.card - 1)) at hraw
    have hzero : coeff x ν G 0 = 0 := by
      apply Finsupp.notMem_support_iff.mp
      intro hn
      have hh := (hraw.1 0 hn).1
      have hpos : 0 < Q x ν G / (2 : ℝ) ^ G.card :=
        div_pos (zero_lt_one.trans_le (hQone x hx ν G)) (pow_pos zero_lt_two _)
      exact hpos.not_ge (by simpa only [Nat.cast_zero] using hh)
    refine ⟨hraw.1, ?_⟩
    intro n
    by_cases hn : n = 0
    · subst n
      simp [hzero]
    · have hdv : 1 ≤ (n.divisors.card : ℝ) := by
        exact_mod_cast Finset.one_le_card.mpr (Nat.nonempty_divisors.mpr hn)
      calc
        ‖coeff x ν G n‖ ≤ (4 * Real.log x) ^ G.card *
            (n.divisors.card : ℝ) ^ (G.card - 1) := hraw.2 n
        _ ≤ (4 * Real.log x) ^ 40 * (n.divisors.card : ℝ) ^ 40 :=
          mul_le_mul (pow_le_pow_right₀ hbase (hcard40 G))
            (pow_le_pow_right₀ hdv ((Nat.sub_le _ _).trans (hcard40 G)))
            (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (zero_le_one.trans hbase) _)
        _ = W * (n.divisors.card : ℝ) ^ 40 * (Real.log x) ^ 40 := by
          dsimp only [W]
          rw [mul_pow]
          ring
  have hsupportTransfer (x : ℝ) (hx : X0 ≤ x) (ν : Params)
      (G : Finset (ιr)) (L : ℝ) (hL : 0 ≤ L)
      (hLQ : L ≤ Q x ν G) (hQL : Q x ν G ≤ C0 * L)
      (hs : ∀ n ∈ (coeff x ν G).support,
        Q x ν G / (2 : ℝ) ^ G.card ≤ (n : ℝ) ∧
          (n : ℝ) ≤ (2 : ℝ) ^ G.card * Q x ν G) :
      ∀ n ∈ (coeff x ν G).support, c * L ≤ (n : ℝ) ∧ (n : ℝ) ≤ Cf * L := by
    have hQ : 0 ≤ Q x ν G := zero_le_one.trans (hQone x hx ν G)
    have hpow : (2 : ℝ) ^ G.card ≤ B2 :=
      pow_le_pow_right₀ (by norm_num) (hcard40 G)
    intro n hn
    constructor
    · calc
        c * L = L / B2 := by dsimp only [c]; ring
        _ ≤ Q x ν G / B2 := div_le_div_of_nonneg_right hLQ hB2pos.le
        _ ≤ Q x ν G / (2 : ℝ) ^ G.card :=
          div_le_div_of_nonneg_left hQ (pow_pos zero_lt_two _) hpow
        _ ≤ (n : ℝ) := (hs n hn).1
    · calc
        (n : ℝ) ≤ (2 : ℝ) ^ G.card * Q x ν G := (hs n hn).2
        _ ≤ B2 * Q x ν G := mul_le_mul_of_nonneg_right hpow hQ
        _ ≤ B2 * (C0 * L) := mul_le_mul_of_nonneg_left hQL hB2pos.le
        _ ≤ B2 * (C0 ^ 2 * L) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hC0sq hL) hB2pos.le
        _ = Cf * L := by dsimp only [Cf]; ring
  let Index : Type := Params ×
    (Finset (ιr) × Finset (ιr))
  let Active : ℝ → Index → Prop := fun x z =>
    x / C0 ≤ P x z.1 ∧ P x z.1 ≤ C0 * x ∧
      Disjoint z.2.1 z.2.2 ∧ z.2.1 ∪ z.2.2 = Finset.univ ∧
      z.2.1.Nonempty ∧ z.2.2.Nonempty ∧
      x ^ (1 / 2 - σclass) / C0 < Q x z.1 z.2.1 ∧
      Q x z.1 z.2.1 ≤ Q x z.1 z.2.2
  let MFamily : ℝ → Index → ℝ := fun x z =>
    if Active x z then Q x z.1 z.2.2 else Real.sqrt x
  let NFamily : ℝ → Index → ℝ := fun x z =>
    if Active x z then min (Q x z.1 z.2.1) (Real.sqrt x) else Real.sqrt x
  let αFamily : ℝ → Index → ℕ →₀ ℂ := fun x z =>
    if Active x z then coeff x z.1 z.2.2 else 0
  let βFamily : ℝ → Index → ℕ →₀ ℂ := fun x z =>
    if Active x z then coeff x z.1 z.2.1 else 0
  have hgeom (x : ℝ) (hx : X0 ≤ x) (z : Index) (hz : Active x z) :
      (x / Cf ≤ MFamily x z * NFamily x z ∧
        MFamily x z * NFamily x z ≤ Cf * x ∧
        x ^ (1 / 2 - σdist) ≤ NFamily x z ∧
        NFamily x z ≤ x ^ (1 / 2 : ℝ)) ∧
      Q x z.1 z.2.1 ≤ C0 * NFamily x z ∧
        x ^ d ≤ Q x z.1 z.2.1 ∧ Q x z.1 z.2.1 ≤ x ^ (2 : ℝ) := by
    have hact := hz
    rcases hact with ⟨hPlower, hPupper, hdisj, hunion, _, _, hPSlower, hST⟩
    have hprod : Q x z.1 z.2.1 * Q x z.1 z.2.2 = P x z.1 := by
      dsimp only [Q, P]
      rw [← Finset.prod_union hdisj, hunion]
    simpa only [MFamily, NFamily, ite_eq_left hz] using
      hgeometry x (P x z.1) (Q x z.1 z.2.1) (Q x z.1 z.2.2) hx
        (hQone x hx z.1 z.2.1) (hQone x hx z.1 z.2.2)
        hprod hPlower hPupper hPSlower hST
  have hscaleFamily : ∀ x : ℝ, X0 ≤ x → ∀ z : Index,
      x / Cf ≤ MFamily x z * NFamily x z ∧
        MFamily x z * NFamily x z ≤ Cf * x ∧
        x ^ (1 / 2 - σdist) ≤ NFamily x z ∧
        NFamily x z ≤ x ^ (1 / 2 : ℝ) := by
    intro x hx z
    by_cases hz : Active x z
    · exact (hgeom x hx z hz).1
    · simp only [MFamily, NFamily, ite_eq_right hz]
      simp only [Real.mul_self_sqrt (hxpos x hx).le]
      refine ⟨div_le_self (hxpos x hx).le hCf,
        le_mul_of_one_le_left (hxpos x hx).le hCf, ?_, ?_⟩
      · rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le (hxone x hx)
          (sub_le_self _ hσdist.1.le)
      · exact (Real.sqrt_eq_rpow x).le
  have hsupportFamily : ∀ x : ℝ, X0 ≤ x → ∀ z : Index,
      (∀ n ∈ (αFamily x z).support,
        c * MFamily x z ≤ (n : ℝ) ∧ (n : ℝ) ≤ Cf * MFamily x z) ∧
      (∀ n ∈ (βFamily x z).support,
        c * NFamily x z ≤ (n : ℝ) ∧ (n : ℝ) ≤ Cf * NFamily x z) := by
    intro x hx z
    by_cases hz : Active x z
    · have hact := hz
      rcases hact with ⟨_, hPupper, _, _, hSne, hTne, _, _⟩
      have hs := (hbox x hx z.1 hPupper z.2.1 hSne).1
      have ht := (hbox x hx z.1 hPupper z.2.2 hTne).1
      have hgg := hgeom x hx z hz
      have hTnonneg : 0 ≤ Q x z.1 z.2.2 := zero_le_one.trans (hQone x hx z.1 z.2.2)
      have hNnonneg : 0 ≤ NFamily x z :=
        (Real.rpow_nonneg (hxpos x hx).le _).trans hgg.1.2.2.1
      constructor
      · simpa only [αFamily, MFamily, ite_eq_left hz] using
          hsupportTransfer x hx z.1 z.2.2 (Q x z.1 z.2.2) hTnonneg le_rfl
            (le_mul_of_one_le_left hTnonneg hC0) ht
      · have hNQ : NFamily x z ≤ Q x z.1 z.2.1 := by
          simp only [NFamily, ite_eq_left hz]
          exact min_le_left _ _
        simpa only [βFamily, ite_eq_left hz] using
          hsupportTransfer x hx z.1 z.2.1 (NFamily x z) hNnonneg hNQ hgg.2.1 hs
    · have hαzero : αFamily x z = 0 := ite_eq_right hz
      have hβzero : βFamily x z = 0 := ite_eq_right hz
      rw [hαzero, hβzero, Finsupp.support_zero]
      exact ⟨fun n hn => (Finset.notMem_empty n hn).elim,
        fun n hn => (Finset.notMem_empty n hn).elim⟩
  have hcoeffFamily : ∀ x : ℝ, X0 ≤ x → ∀ z : Index, ∀ n : ℕ,
      ‖αFamily x z n‖ ≤ W * (n.divisors.card : ℝ) ^ 40 * (Real.log x) ^ 40 ∧
      ‖βFamily x z n‖ ≤ W * (n.divisors.card : ℝ) ^ 40 * (Real.log x) ^ 40 := by
    intro x hx z n
    by_cases hz : Active x z
    · have hact := hz
      rcases hact with ⟨_, hPupper, _, _, hSne, hTne, _, _⟩
      simpa only [αFamily, βFamily, ite_eq_left hz] using
        And.intro ((hbox x hx z.1 hPupper z.2.2 hTne).2 n)
          ((hbox x hx z.1 hPupper z.2.1 hSne).2 n)
    · have hℓ : 0 ≤ Real.log x := zero_le_one.trans (hlog x hx)
      have hαzero : αFamily x z = 0 := ite_eq_right hz
      have hβzero : βFamily x z = 0 := ite_eq_right hz
      rw [hαzero, hβzero, Finsupp.zero_apply, norm_zero]
      have hbound : 0 ≤ W * (n.divisors.card : ℝ) ^ 40 * (Real.log x) ^ 40 :=
        mul_nonneg (mul_nonneg hW (pow_nonneg (Nat.cast_nonneg _) _))
          (pow_nonneg hℓ _)
      exact ⟨hbound, hbound⟩
  have hSWFamily : ∀ Asw : ℝ, 0 < Asw →
      ∃ KSW XSW : ℝ, 0 < KSW ∧ X0 ≤ XSW ∧
        ∀ x : ℝ, XSW ≤ x → ∀ z : Index,
        ∀ q r a : ℕ, 0 < q → 0 < r → Nat.Coprime a q →
          ‖fullDiscrepancy
              ((βFamily x z).filter (fun n : ℕ => Nat.Coprime n r)) q a‖ ≤
            KSW * ((q * r).divisors.card : ℝ) ^ 2 * NFamily x z /
              (Real.log x) ^ Asw := by
    intro Asw hAsw
    have hDpos : (0 : ℝ) < (D : ℝ) := by
      exact_mod_cast (show 0 < D by omega)
    obtain ⟨Csw, Xsw, hCsw, _, hsw⟩ :=
      heathBrown_localized_products_fixedPower_siegelWalfisz
        40 (by norm_num) d 2 hd (by norm_num) (D : ℝ) hDpos Asw hAsw
    refine ⟨Csw * C0, max X0 Xsw, mul_pos hCsw hC0pos, le_max_left _ _, ?_⟩
    intro x hx z q r a hq hr ha
    have hx0 : X0 ≤ x := (le_max_left _ _).trans hx
    have hxsw : Xsw ≤ x := (le_max_right _ _).trans hx
    have hℓpos : 0 < Real.log x := zero_lt_one.trans_le (hlog x hx0)
    by_cases hz : Active x z
    · have hact := hz
      rcases hact with ⟨_, _, _, _, hSne, _, _, _⟩
      let S : Finset (ιr) := z.2.1
      let ν : Params := z.1
      let G : ℕ →₀ ℂ := coeff x ν S
      let e : Fin S.card ≃ S := S.equivFin.symm
      have hNprod :
          (∏ b : Fin S.card, scale x ν (e b)) = Q x ν S :=
        (e.prod_comp (fun i : S => scale x ν i)).trans
          (Finset.prod_coe_sort S (scale x ν))
      let role : Fin S.card → Fin 4 := fun b =>
        if (e b).1.2.val < (orders (e b).1.1).val + 1 then 0
        else if (e b).1.2.val + 1 = 2 * ((orders (e b).1.1).val + 1) then 3 else 2
      let fsw : Fin S.card → ℕ → ℝ := fun b n =>
        if role b = 0 then μU x n else if role b = 1 then |μU x n|
        else if role b = 2 then (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n
        else ArithmeticFunction.log n
      have hfsw (b : Fin S.card) (n : ℕ) : fsw b n = f x (e b) n := by
        by_cases hμ : (e b).1.2.val < (orders (e b).1.1).val + 1
        · simp only [fsw, role, hμ, ↓reduceIte, f, minorantHBSlot, μU]
        · by_cases hln : (e b).1.2.val + 1 = 2 * ((orders (e b).1.1).val + 1)
          · simp only [fsw, role, hμ, hln, ↓reduceIte, f, minorantHBSlot]
            norm_num [Fin.ext_iff]
          · simp only [fsw, role, hμ, hln, ↓reduceIte, f, minorantHBSlot]
            norm_num [Fin.ext_iff]
      let βsw : Fin S.card → MonoidAlgebra ℂ ℕ := fun b =>
        ∑ n ∈ Finset.Icc (max 1 (1 : ℕ)) ⌊Θ x * scale x ν (e b)⌋₊,
          MonoidAlgebra.single n
            (((η x ((n : ℝ) / scale x ν (e b)) *
              Real.rpow (n : ℝ) (-(tclip ν (e b).1.1)) * fsw b n : ℝ) : ℂ))
      have hβsw (b : Fin S.card) : βsw b = slot x ν (e b) := by
        simp only [βsw, slot, minorantHBLocalizedSlot, max_self, hfsw, η, scale, f]
      have hβprod : (∏ b : Fin S.card, βsw b) = ∏ i ∈ S, slot x ν i := by
        calc
          _ = ∏ b : Fin S.card, slot x ν (e b) :=
            Finset.prod_congr rfl fun b _hb => hβsw b
          _ = _ := (e.prod_comp (fun i : S => slot x ν i)).trans
            (Finset.prod_coe_sort S (slot x ν))
      have hR (b : Fin S.card) :
          (⌊Θ x * scale x ν (e b)⌋₊ : ℝ) ≤ 2 * scale x ν (e b) :=
        (Nat.floor_le
          (mul_nonneg (zero_lt_one.trans (hΘ x hx0).1).le
            (zero_le_one.trans (hscaleone x hx0 ν (e b))))).trans
          (mul_le_mul_of_nonneg_right (hΘ x hx0).2
            (zero_le_one.trans (hscaleone x hx0 ν (e b))))
      have hfilter :
          G.filter (fun n : ℕ => 0 ≤ n ∧ n ≤ G.support.sup id) = G := by
        apply (Finsupp.filter_eq_self_iff _ _).2
        intro n hn
        exact ⟨Nat.zero_le n,
          Finset.le_sup (f := id) (Finsupp.mem_support_iff.mpr hn)⟩
      have hgg := hgeom x hx0 z hz
      have hraw := hsw x hxsw S.card hSne.card_pos (hcard40 S)
        (fun b => scale x ν (e b)) (fun _ => U x) (fun b => tclip ν (e b).1.1)
        (fun b => hscaleone x hx0 ν (e b))
        (by simpa only [hNprod] using hgg.2.2.1)
        (by simpa only [hNprod] using hgg.2.2.2)
        (fun b => htclip ν (e b).1.1) role (fun _ => 1)
        (fun b => ⌊Θ x * scale x ν (e b)⌋₊) hR 0 (G.support.sup id)
      have hh := hraw.2.2 q r a hq hr ha
      change
        ‖fullDiscrepancy
          (((∏ b : Fin S.card, βsw b).coeff.filter
            (fun n : ℕ => 0 ≤ n ∧ n ≤ G.support.sup id)).filter
              (fun n => Nat.Coprime n r)) q a‖ ≤
          Csw * ((q * r).divisors.card : ℝ) ^ 2 *
            (∏ b : Fin S.card, scale x ν (e b)) / (Real.log x) ^ Asw at hh
      rw [hNprod, hβprod] at hh
      change ‖fullDiscrepancy
          ((G.filter (fun n : ℕ => 0 ≤ n ∧ n ≤ G.support.sup id)).filter
            (fun n => Nat.Coprime n r)) q a‖ ≤
          Csw * ((q * r).divisors.card : ℝ) ^ 2 * Q x ν S /
            (Real.log x) ^ Asw at hh
      rw [hfilter] at hh
      have hmain : ‖fullDiscrepancy (G.filter (fun n => Nat.Coprime n r)) q a‖ ≤
          (Csw * C0) * ((q * r).divisors.card : ℝ) ^ 2 * NFamily x z /
            (Real.log x) ^ Asw := by
        calc
          _ ≤ Csw * ((q * r).divisors.card : ℝ) ^ 2 * Q x ν S /
              (Real.log x) ^ Asw := hh
          _ ≤ Csw * ((q * r).divisors.card : ℝ) ^ 2 * (C0 * NFamily x z) /
              (Real.log x) ^ Asw :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hgg.2.1
                (mul_nonneg hCsw.le (sq_nonneg _)))
              (Real.rpow_pos_of_pos hℓpos Asw).le
          _ = (Csw * C0) * ((q * r).divisors.card : ℝ) ^ 2 * NFamily x z /
              (Real.log x) ^ Asw := by ring
      simpa only [βFamily, ite_eq_left hz] using hmain
    · have hNinactive : NFamily x z = Real.sqrt x := ite_eq_right hz
      have hNnonneg : 0 ≤ NFamily x z := hNinactive.symm ▸ Real.sqrt_nonneg x
      have hβzero : βFamily x z = 0 := ite_eq_right hz
      have hzero : fullDiscrepancy
          ((βFamily x z).filter (fun n : ℕ => Nat.Coprime n r)) q a = 0 := by
        rw [hβzero, Finsupp.filter_zero]
        simp only [fullDiscrepancy, progressionMass, reducedMass,
          Finsupp.support_zero, Finset.sum_empty, zero_div, sub_self]
      rw [hzero, norm_zero]
      exact div_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg hCsw.le hC0pos.le)
            (sq_nonneg (((q * r).divisors.card : ℝ)))) hNnonneg)
        (Real.rpow_pos_of_pos hℓpos Asw).le
  intro A hAsave
  have hinput : ∃ K X : ℝ, 0 < K ∧ X0 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ z : Index,
      ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
      ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
        (∑ q ∈ (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
            q ∣ (∏ p ∈ I, p) ∧
              Nonempty (DenseDivisibilityWitness
                ⟨max 1 (x ^ δ), by exact le_max_left (1 : ℝ) (x ^ δ)⟩ density q)),
          ‖fullDiscrepancy (finiteConvolution (αFamily x z) (βFamily x z)) q a‖) ≤
            K * x / (Real.log x) ^ A := by
    exact hdist MFamily NFamily αFamily βFamily c Cf W X0 40 2
      hc hCf hW hX0 hscaleFamily hsupportFamily hcoeffFamily hSWFamily A hAsave
  obtain ⟨K, X, hK, hXX0, hbound⟩ := hinput
  refine ⟨K, X, hK, hX0.trans hXX0, ?_⟩
  intro x hx Θ' t ht htten ν ι' Ni' β' hPlower hPupper
    S T hdisj hunion hSne hTne hPSlower hST I hI a ha
  let v : Params := (t, ν)
  have hslotEq (s : ιr) : slot x v s = β' s := by
    dsimp only [slot, tclip, v, β']
    rw [min_eq_left (htten s.1), max_eq_right (ht s.1)]
  let z : Index := (v, S, T)
  have hz : Active x z := ⟨hPlower, hPupper, hdisj, hunion, hSne, hTne, hPSlower, hST⟩
  have hfactor : finiteConvolution (αFamily x z) (βFamily x z) =
      (∏ i, slot x v i).coeff := by
    simp only [αFamily, βFamily, ite_eq_left hz]
    change ((∏ i ∈ T, slot x v i) * (∏ i ∈ S, slot x v i)).coeff =
      (∏ i, slot x v i).coeff
    apply congrArg (fun w : MonoidAlgebra ℂ ℕ => w.coeff)
    rw [← Finset.prod_union hdisj.symm, Finset.union_comm, hunion]
  simpa only [hfactor, hslotEq] using hbound x hx z I hI a ha

open Classical in
theorem sourceT3_three_smooth_slots_log_saving_of_global
    (density : ℕ) (hdensity : 1 ≤ density) (D : ℕ) (hD : 1 ≤ D)
    («ω» δ σ C0 : ℝ) (_hω : 0 < «ω») (_hωupper : «ω» < 1 / 12)
    (hδ : 0 < δ) (hσhalf : σ < 1 / 2) (hC0 : 1 ≤ C0)
    (hTypeIII : PrimeGap182.TypeIII.PositiveSmoothTypeIIIGlobalEstimate «ω» δ σ) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ Real.exp 1 ≤ X ∧
      ∀ x : ℝ, X ≤ x →
        let Θ : ℝ := 1 + (Real.log x) ^ (-(D : ℝ))
        ∀ r : Fin 3 → Fin 5, ∀ t : Fin 3 → ℝ,
          (∀ c, 0 ≤ t c) → (∀ c, t c ≤ 10) →
        ∀ ν : (c : Fin 3) → Fin (2 * ((r c).val + 1)) → ℕ,
          let ιr := Σ c : Fin 3, Fin (2 * ((r c).val + 1))
          let Ni : ιr → ℝ := fun s => Θ ^ ν s.1 s.2
          let β : ιr → MonoidAlgebra ℂ ℕ := fun s =>
            minorantHBLocalizedSlot ((r s.1).val + 1) (x ^ (9 / 100 : ℝ))
              Θ (t s.1) (ν s.1) s.2
          x / C0 ≤ (∏ s, Ni s) → (∏ s, Ni s) ≤ C0 * x →
          ∀ s₁ s₂ s₃ : ιr,
            s₁ ≠ s₂ → s₁ ≠ s₃ → s₂ ≠ s₃ →
            (r s₁.1).val + 1 ≤ s₁.2.val →
            (r s₂.1).val + 1 ≤ s₂.2.val →
            (r s₃.1).val + 1 ≤ s₃.2.val →
            x ^ (1 / 2 + σ) / C0 ≤ Ni s₁ * Ni s₂ →
            x ^ (1 / 2 + σ) / C0 ≤ Ni s₁ * Ni s₃ →
            x ^ (1 / 2 + σ) / C0 ≤ Ni s₂ * Ni s₃ →
            Ni s₁ ≤ C0 * x ^ (1 / 2 - σ) →
            Ni s₂ ≤ C0 * x ^ (1 / 2 - σ) →
            Ni s₃ ≤ C0 * x ^ (1 / 2 - σ) →
          ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) →
          ∀ a : ℕ, Nat.Coprime a (∏ p ∈ P, p) →
            (∑ q ∈ (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
                q ∣ (∏ p ∈ P, p) ∧
                  Nonempty (DenseDivisibilityWitness
                    ⟨max 1 (x ^ δ), by exact le_max_left (1 : ℝ) (x ^ δ)⟩ density q)),
              ‖fullDiscrepancy (∏ s, β s).coeff q a‖) ≤
                K * x / (Real.log x) ^ A := by
  let C : ℝ := (2 : ℝ) ^ 30 * C0
  have hC0pos : 0 < C0 := zero_lt_one.trans_le hC0
  have hC0C : C0 ≤ C := by
    exact le_mul_of_one_le_left hC0pos.le (one_le_pow₀ (by norm_num))
  have hCtwo : 2 ≤ C := by
    have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ 30 := by norm_num
    exact htwo.trans (le_mul_of_one_le_right (by positivity) hC0)
  have hC : 1 ≤ C := one_le_two.trans hCtwo
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  obtain ⟨εcap, hεcap, hTypeIII⟩ := hTypeIII
  let ε : ℝ := min (1 / 100) εcap
  have hε : 0 < ε := lt_min (by norm_num) hεcap
  have hεle : ε ≤ εcap := min_le_right _ _
  let κ : ℝ := ε / 4
  have hκ : 0 ≤ κ := (div_pos hε (by norm_num)).le
  let J : ℕ := Nat.ceil (22 / ε)
  let E : ℝ := ((D * (J + 2) + 1 : ℕ) : ℝ)
  obtain ⟨Cder, hCder, hprofiles⟩ := sourceT3_smooth_slot_profiles
  let Lder : ℝ := 3 * (1 + ∑ r ∈ Finset.range (J + 2 + 1), Cder r)
  have hLder : 0 < Lder := by
    have hsum : 0 ≤ ∑ r ∈ Finset.range (J + 2 + 1), Cder r :=
      Finset.sum_nonneg fun r _ => (hCder r).le
    dsimp only [Lder]
    positivity
  intro A hA
  obtain ⟨K0, X0, hK0, hX0, hglobal⟩ :=
    hTypeIII C E 30 30 hC ε hε hεle A hA
  refine ⟨K0 * ((4 : ℝ) ^ 30 * Lder * Lder * Lder), max X0 C0,
    by positivity, hX0.trans (le_max_left _ _), ?_⟩
  intro x hx Θ r t ht htten ν ιr Ni β hlo hhi i₁ i₂ i₃ h12 h13 h23 hi₁ hi₂ hi₃
    hpair12 hpair13 hpair23 hupper₁ hupper₂ hupper₃ I hI a ha
  have hx0 : X0 ≤ x := (le_max_left _ _).trans hx
  have hC0x : C0 ≤ x := (le_max_right _ _).trans hx
  have hxexp : Real.exp 1 ≤ x := hX0.trans hx0
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hxexp
  have hxone : 1 ≤ x := (Real.one_le_exp (by norm_num)).trans hxexp
  have hlog : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hxexp
  have hlogpos : 0 < Real.log x := zero_lt_one.trans_le hlog
  have hΘ : 1 < Θ :=
    lt_add_of_pos_right 1 (Real.rpow_pos_of_pos hlogpos _)
  have hΘtwo : Θ ≤ 2 := by
    have hh : (Real.log x) ^ (-(D : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hlog
        (neg_nonpos.mpr (by exact_mod_cast (Nat.zero_le 1).trans hD))
    change 1 + (Real.log x) ^ (-(D : ℝ)) ≤ 2
    linarith
  have hNi (i : ιr) : 1 ≤ Ni i := one_le_pow₀ hΘ.le
  have hNiupper (i : ιr) : Ni i ≤ x ^ 2 := by
    calc
      Ni i ≤ ∏ l, Ni l :=
        Multiset.mem_le_prod_of_one_le (s := Finset.univ.val) hNi (Finset.mem_univ i)
      _ ≤ C0 * x := hhi
      _ ≤ x * x := mul_le_mul_of_nonneg_right hC0x hxpos.le
      _ = x ^ 2 := (sq x).symm
  have hslotdata (s : ιr) :
      (∀ n ∈ (β s).coeff.support,
        Ni s / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Ni s) ∧
        ∀ n : ℕ, ‖(β s).coeff n‖ ≤ 1 + Real.log (n : ℝ) :=
    sourceT3_localized_slot_support_norm ((r s.1).val + 1)
      (x ^ (9 / 100 : ℝ)) Θ (t s.1) (ν s.1) s.2 hΘ hΘtwo (ht s.1)
  have hslots (s : ιr) : ∀ n ∈ (β s).coeff.support,
      Ni s / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Ni s := (hslotdata s).1
  have hslotnorm (s : ιr) (n : ℕ) : ‖(β s).coeff n‖ ≤ 4 * Real.log x := by
    by_cases hn : n ∈ (β s).coeff.support
    · have hNpos : 0 < Ni s := zero_lt_one.trans_le (hNi s)
      have hnpos : 0 < (n : ℝ) :=
        (div_pos hNpos zero_lt_two).trans_le (hslots s n hn).1
      have hlogN := Real.log_le_log hNpos (hNiupper s)
      rw [Real.log_pow x 2] at hlogN
      norm_num only [Nat.cast_ofNat] at hlogN
      have hlogn := Real.log_le_log hnpos (hslots s n hn).2
      rw [Real.log_mul two_ne_zero hNpos.ne'] at hlogn
      have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      exact ((hslotdata s).2 n).trans (by linarith only [hlogn, hlogN, hlog2, hlog])
    · rw [Finsupp.notMem_support_iff.mp hn, norm_zero]
      linarith only [hlog]
  have hcardι : Fintype.card ιr = ∑ c : Fin 3, 2 * ((r c).val + 1) := by
    change Fintype.card (Σ c : Fin 3, Fin (2 * ((r c).val + 1))) = _
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
  have hcardLower : 6 ≤ Fintype.card ιr := by
    rw [hcardι]
    calc
      6 = ∑ _c : Fin 3, (2 : ℕ) := by norm_num
      _ ≤ ∑ c : Fin 3, 2 * ((r c).val + 1) :=
        Finset.sum_le_sum (fun c _ => by omega)
  have hcardUpper : Fintype.card ιr ≤ 30 := by
    rw [hcardι]
    calc
      (∑ c : Fin 3, 2 * ((r c).val + 1)) ≤ ∑ _c : Fin 3, (10 : ℕ) := by
        apply Finset.sum_le_sum
        intro c _
        have hc := (r c).isLt
        omega
      _ = 30 := by norm_num
  let T : Finset ιr := Finset.univ \ {i₁, i₂, i₃}
  have hselectedCard : ({i₁, i₂, i₃} : Finset ιr).card = 3 := by
    simp [h12, h13, h23]
  have hTcardEq : T.card + 3 = Fintype.card ιr := by
    simpa only [T, hselectedCard, Finset.card_univ] using
      Finset.card_sdiff_add_card_eq_card
        (Finset.subset_univ ({i₁, i₂, i₃} : Finset ιr))
  have hTne : T.Nonempty := by
    apply Finset.card_pos.mp
    omega
  have hTcard : T.card ≤ 30 := by omega
  let M : ℝ := ∏ i ∈ T, Ni i
  let α : ℕ →₀ ℂ := (∏ i ∈ T, β i).coeff
  have hM : 1 ≤ M := Finset.one_le_prod fun i _ => hNi i
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hsplitN : (∏ i, Ni i) = M * (Ni i₁ * Ni i₂ * Ni i₃) := by
    simpa [M, T, h12, h13, h23, mul_assoc] using
      (Finset.prod_sdiff (f := Ni)
        (Finset.subset_univ ({i₁, i₂, i₃} : Finset (ιr)))).symm
  have hsplitβ : (∏ i, β i) = (∏ i ∈ T, β i) * (β i₁ * β i₂ * β i₃) := by
    simpa [T, h12, h13, h23, mul_assoc] using
      (Finset.prod_sdiff (f := β)
        (Finset.subset_univ ({i₁, i₂, i₃} : Finset (ιr)))).symm
  have hfactor : (∏ i, β i).coeff =
      finiteConvolution α (finiteConvolution (β i₁).coeff
        (finiteConvolution (β i₂).coeff (β i₃).coeff)) := by
    simpa only [finiteConvolution, α, MonoidAlgebra.ofCoeff_coeff, mul_assoc] using
      congrArg (fun v : MonoidAlgebra ℂ ℕ => v.coeff) hsplitβ
  obtain ⟨hαsupport, hαnorm⟩ :=
    heathBrown_box_product_support_norm_bound T hTne β Ni (4 * Real.log x)
      (by positivity) (fun i _ => hNi i) (fun i _ => hslots i) (fun i _ => hslotnorm i)
  change ∀ n ∈ α.support,
    M / (2 : ℝ) ^ T.card ≤ (n : ℝ) ∧ (n : ℝ) ≤ (2 : ℝ) ^ T.card * M at hαsupport
  change ∀ n, ‖α n‖ ≤ (4 * Real.log x) ^ T.card *
    (n.divisors.card : ℝ) ^ (T.card - 1) at hαnorm
  have htwoCard : (2 : ℝ) ^ T.card ≤ C :=
    (pow_le_pow_right₀ one_le_two hTcard).trans
      (le_mul_of_one_le_right (by positivity) hC0)
  have hαwindow (n : ℕ) (hn : n ∈ α.support) :
      M / C ≤ (n : ℝ) ∧ (n : ℝ) ≤ C * M :=
    ⟨(div_le_div_of_nonneg_left hMpos.le (pow_pos zero_lt_two _) htwoCard).trans
        (hαsupport n hn).1,
      (hαsupport n hn).2.trans (mul_le_mul_of_nonneg_right htwoCard hMpos.le)⟩
  have hαgrowth (n : ℕ) (hn : n ∈ α.support) :
      ‖α n‖ ≤ (4 : ℝ) ^ 30 * (n.divisors.card : ℝ) ^ 30 * (Real.log x) ^ (30 : ℝ) := by
    have hnpos : 0 < n := by
      exact_mod_cast (div_pos hMpos (pow_pos zero_lt_two T.card)).trans_le
        (hαsupport n hn).1
    have hτ : 1 ≤ (n.divisors.card : ℝ) := by
      exact_mod_cast Finset.one_le_card.mpr (Nat.nonempty_divisors.mpr hnpos.ne')
    have hFour : (4 : ℝ) ^ T.card ≤ (4 : ℝ) ^ 30 :=
      pow_le_pow_right₀ (by norm_num) hTcard
    have hL : (Real.log x) ^ T.card ≤ (Real.log x) ^ 30 :=
      pow_le_pow_right₀ hlog hTcard
    have hτpow : (n.divisors.card : ℝ) ^ (T.card - 1) ≤
        (n.divisors.card : ℝ) ^ 30 :=
      pow_le_pow_right₀ hτ ((Nat.sub_le _ _).trans hTcard)
    calc
      ‖α n‖ ≤ (4 * Real.log x) ^ T.card *
          (n.divisors.card : ℝ) ^ (T.card - 1) := hαnorm n
      _ = (4 : ℝ) ^ T.card * (Real.log x) ^ T.card *
          (n.divisors.card : ℝ) ^ (T.card - 1) := by rw [mul_pow]
      _ ≤ (4 : ℝ) ^ 30 * (Real.log x) ^ 30 * (n.divisors.card : ℝ) ^ 30 :=
        mul_le_mul
          (mul_le_mul hFour hL (pow_nonneg hlogpos.le _)
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)) hτpow
          (pow_nonneg (Nat.cast_nonneg _) _)
          (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)
            (pow_nonneg hlogpos.le _))
      _ = (4 : ℝ) ^ 30 * (n.divisors.card : ℝ) ^ 30 *
          (Real.log x) ^ (30 : ℝ) := by
        simpa only [Real.rpow_ofNat] using
          (mul_right_comm ((4 : ℝ) ^ (30 : ℕ)) ((Real.log x) ^ (30 : ℕ))
            ((n.divisors.card : ℝ) ^ (30 : ℕ)))
  obtain ⟨ψ₁, hψ₁, hsupp₁, hβ₁, hder₁⟩ :=
    hprofiles Θ hΘ hΘtwo ((r i₁.1).val + 1) (x ^ (9 / 100 : ℝ))
      (t i₁.1) (ν i₁.1) i₁.2 hi₁ (ht i₁.1) (htten i₁.1) C hCtwo
  obtain ⟨ψ₂, hψ₂, hsupp₂, hβ₂, hder₂⟩ :=
    hprofiles Θ hΘ hΘtwo ((r i₂.1).val + 1) (x ^ (9 / 100 : ℝ))
      (t i₂.1) (ν i₂.1) i₂.2 hi₂ (ht i₂.1) (htten i₂.1) C hCtwo
  obtain ⟨ψ₃, hψ₃, hsupp₃, hβ₃, hder₃⟩ :=
    hprofiles Θ hΘ hΘtwo ((r i₃.1).val + 1) (x ^ (9 / 100 : ℝ))
      (t i₃.1) (ν i₃.1) i₃.2 hi₃ (ht i₃.1) (htten i₃.1) C hCtwo
  change (β i₁).coeff = positiveCompactProfileSequence ψ₁ C (Ni i₁) 0 at hβ₁
  change (β i₂).coeff = positiveCompactProfileSequence ψ₂ C (Ni i₂) 0 at hβ₂
  change (β i₃).coeff = positiveCompactProfileSequence ψ₃ C (Ni i₃) 0 at hβ₃
  have hderivative (s : ιr) (ψ : ℝ → ℂ)
      (hh : ∀ ℓ u, ‖iteratedDeriv ℓ ψ u‖ ≤
        Cder ℓ * (1 + Real.log (Ni s)) / (Θ - 1) ^ ℓ) :
      ∀ ℓ : ℕ, ℓ ≤ J + 2 → ∀ u : ℝ,
        ‖iteratedDeriv ℓ ψ u‖ ≤ Lder * (Real.log x) ^ E := by
    simpa only [Lder, E, Real.rpow_natCast] using
      heathBrown_geometric_derivatives_log_bound Cder (fun ℓ => (hCder ℓ).le)
        D (J + 2) x (Ni s) hxexp (hNi s) (hNiupper s) ψ hh
  have hpair {u v : ℝ} (h : x ^ (1 / 2 + σ) / C0 ≤ u * v) :
      x ^ (1 / 2 + σ - κ) / C ≤ u * v := by
    calc
      x ^ (1 / 2 + σ - κ) / C ≤ x ^ (1 / 2 + σ) / C :=
        div_le_div_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hxone (by linarith)) hCpos.le
      _ ≤ x ^ (1 / 2 + σ) / C0 :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hxpos.le _) hC0pos hC0C
      _ ≤ u * v := h
  have hupper {u : ℝ} (h : u ≤ C0 * x ^ (1 / 2 - σ)) :
      u ≤ C * x ^ (1 / 2 - σ + κ) :=
    h.trans (mul_le_mul hC0C
      (Real.rpow_le_rpow_of_exponent_le hxone (by linarith))
      (zero_le_one.trans (Real.one_le_rpow hxone (sub_pos.mpr hσhalf).le)) hCpos.le)
  have htotalLower : x / C ≤ M * (Ni i₁ * Ni i₂ * Ni i₃) := by
    rw [← hsplitN]
    exact (div_le_div_of_nonneg_left hxpos.le hC0pos hC0C).trans hlo
  have htotalUpper : M * (Ni i₁ * Ni i₂ * Ni i₃) ≤ C * x := by
    rw [← hsplitN]
    exact hhi.trans (mul_le_mul_of_nonneg_right hC0C hxpos.le)
  let Y : Set.Ici (1 : ℝ) := ⟨max 1 (x ^ δ), by exact le_max_left (1 : ℝ) (x ^ δ)⟩
  have hY : (Y : ℝ) = x ^ δ := max_eq_right (Real.one_le_rpow hxone hδ.le)
  let S : Finset ℕ := (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
      q ∣ (∏ p ∈ I, p) ∧
        Nonempty (DenseDivisibilityWitness
          Y density q))
  change (∑ q ∈ S, ‖fullDiscrepancy (∏ i, β i).coeff q a‖) ≤
    (K0 * ((4 : ℝ) ^ 30 * Lder * Lder * Lder)) * x / (Real.log x) ^ A
  have hSdata (q : ℕ) (hq : q ∈ S) :
      1 ≤ q ∧ q ≤ ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊ ∧ q ∣ (∏ p ∈ I, p) ∧
        Nonempty (DenseDivisibilityWitness Y density q) := by
    change q ∈ (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter
      (fun q => q ∣ (∏ p ∈ I, p) ∧
        Nonempty (DenseDivisibilityWitness Y density q)) at hq
    obtain ⟨hqIcc, hqdvd, hqdd⟩ := Finset.mem_filter.mp hq
    exact ⟨(Finset.mem_Icc.mp hqIcc).1, (Finset.mem_Icc.mp hqIcc).2, hqdvd, hqdd⟩
  let lift : {q // q ∈ S} → ℕ+ := fun q =>
    ⟨q.val, lt_of_lt_of_le Nat.zero_lt_one (hSdata q.val q.property).1⟩
  let Qset : Finset ℕ+ := S.attach.image lift
  have hlift : Function.Injective lift := by
    intro q r h
    apply Subtype.ext
    exact congrArg (fun z : ℕ+ => (z : ℕ)) h
  have hIcf : Squarefree (∏ p ∈ I, p) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime
      (fun p hp q hq hpq => ?_) (fun p hp => (hI p hp).squarefree)
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hI p hp) (hI q hq)).2 hpq)
  have hQset (q : ℕ+) (hq : q ∈ Qset) :
      Squarefree (q : ℕ) ∧
      Nonempty (DenseDivisibilityWitness Y 1 (q : ℕ)) ∧
      (q : ℝ) ≤ C * x ^ (1 / 2 + 2 * «ω» + κ) := by
    rcases Finset.mem_image.mp hq with ⟨r, _, rfl⟩
    obtain ⟨_, hrupper, hrdvd, hrdd⟩ := hSdata r.val r.property
    refine ⟨hIcf.squarefree_of_dvd hrdvd,
      denseDivisibility_mono_order hrdd hdensity, ?_⟩
    calc
      ((lift r : ℕ+) : ℝ) = (r.val : ℝ) := rfl
      _ ≤ (⌊x ^ (1 / 2 + 2 * «ω»)⌋₊ : ℝ) := Nat.cast_le.mpr hrupper
      _ ≤ x ^ (1 / 2 + 2 * «ω») := Nat.floor_le (Real.rpow_nonneg hxpos.le _)
      _ ≤ x ^ (1 / 2 + 2 * «ω» + κ) :=
        Real.rpow_le_rpow_of_exponent_le hxone (by linarith)
      _ ≤ C * x ^ (1 / 2 + 2 * «ω» + κ) :=
        le_mul_of_one_le_left (Real.rpow_nonneg hxpos.le _) hC
  have haunit (q : ℕ+) (hq : q ∈ Qset) : IsUnit ((a : ℤ) : ZMod (q : ℕ)) := by
    rcases Finset.mem_image.mp hq with ⟨r, _, rfl⟩
    change IsUnit ((a : ℤ) : ZMod r.val)
    simpa only [Int.cast_natCast] using
      (ZMod.isUnit_iff_coprime a r.val).mpr
        (ha.of_dvd_right (hSdata r.val r.property).2.2.1)
  have hphysical := hglobal x hx0 M (Ni i₁) (Ni i₂) (Ni i₃)
    hM (hNi i₁) (hNi i₂) (hNi i₃) htotalLower htotalUpper
    (hpair hpair12) (hpair hpair13) (hpair hpair23)
    (hupper hupper₁) (hupper hupper₂) (hupper hupper₃)
    Y hY Qset hQset ((4 : ℝ) ^ 30) Lder Lder Lder
    (by positivity) hLder.le hLder.le hLder.le α hαwindow hαgrowth
    ψ₁ ψ₂ ψ₃ hψ₁ hψ₂ hψ₃ hsupp₁ hsupp₂ hsupp₃
    (hderivative i₁ ψ₁ hder₁) (hderivative i₂ ψ₂ hder₂) (hderivative i₃ ψ₃ hder₃)
    (fun _ => (a : ℤ)) ⟨haunit, ⟨(a : ℤ), fun _ _ => rfl⟩⟩
  have hf : finiteConvolution α
      (finiteConvolution (positiveCompactProfileSequence ψ₁ C (Ni i₁) 0)
        (finiteConvolution (positiveCompactProfileSequence ψ₂ C (Ni i₂) 0)
          (positiveCompactProfileSequence ψ₃ C (Ni i₃) 0))) =
        (∏ i, β i).coeff := by
    rw [← hβ₁, ← hβ₂, ← hβ₃, ← hfactor]
  rw [hf] at hphysical
  have hdisc (q : ℕ+) :
      ((∑ n ∈ (∏ i, β i).coeff.support,
          if (n : ZMod (q : ℕ)) = ((a : ℤ) : ZMod (q : ℕ)) then
            (∏ i, β i).coeff n else 0) -
        ((q : ℕ).totient : ℂ)⁻¹ *
          (∑ n ∈ (∏ i, β i).coeff.support,
            if Nat.Coprime n (q : ℕ) then (∏ i, β i).coeff n else 0)) =
        fullDiscrepancy (∏ i, β i).coeff (q : ℕ) a := by
    simp only [fullDiscrepancy, progressionMass, reducedMass, Int.cast_natCast,
      ZMod.natCast_eq_natCast_iff', div_eq_mul_inv, mul_comm]
  simp only [hdisc] at hphysical
  have hsum : (∑ q ∈ Qset, ‖fullDiscrepancy (∏ i, β i).coeff (q : ℕ) a‖) =
      ∑ q ∈ S, ‖fullDiscrepancy (∏ i, β i).coeff q a‖ := by
    change (∑ q ∈ S.attach.image lift,
      ‖fullDiscrepancy (∏ i, β i).coeff (q : ℕ) a‖) = _
    rw [Finset.sum_image hlift.injOn]
    exact Finset.sum_attach S (fun q => ‖fullDiscrepancy (∏ i, β i).coeff q a‖)
  rw [hsum] at hphysical
  exact hphysical

#print axioms sourceT3_middle_slots_log_saving_of_bilinear
#print axioms sourceT3_three_smooth_slots_log_saving_of_global

end PrimeGap182Analytic.Harman
