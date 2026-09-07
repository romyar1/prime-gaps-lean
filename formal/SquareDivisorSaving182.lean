import SquareDivisorCRT182

/-! Arbitrary logarithmic saving, with divisor weights, for the actual
large-square support needed by the new five-prime sources. The modulus
range is all q <= x^.53, larger than every application range. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186 Classical

namespace PrimeGap182Analytic

theorem square_supported_weighted_bound
    (N r P Q J : ℕ) (hr : 2 ≤ r) (D : Finset ℕ) (hD : D ⊆ Finset.Icc r P)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q) (a : ℕ → ℕ)
    (ha : ∀ q ∈ S, Nat.Coprime (a q) q) (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hv : ∀ q ∈ S, (q.divisors.card : ℝ) ^ (J + 1) ≤ V)
    (e : ℕ → ℂ) (hb : ∀ n ∈ Finset.Icc 1 N, ‖e n‖ ≤ U)
    (hs : ∀ n ∈ Finset.Icc 1 N, e n ≠ 0 → ∃ p ∈ D, p ^ 2 ∣ n) :
    (∑ q ∈ S, (q.divisors.card : ℝ) ^ J *
      ‖fullDiscrepancy (∑ n ∈ Finset.Icc 1 N, Finsupp.single n (e n)) q (a q)‖) ≤
      2 * U * V * ((N : ℝ) / ((r - 1 : ℕ) : ℝ) * (1 + Real.log (Q : ℝ)) + (P : ℝ) * Q) := by
  let A : ℝ := (N : ℝ) / ((r - 1 : ℕ) : ℝ)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hpw (q : ℕ) (hq : q ∈ S) :
      (q.divisors.card : ℝ) ^ J ≤ V ∧
      (q.divisors.card : ℝ) ^ J / (q.totient : ℝ) ≤ V / q := by
    have hqpos : 0 < q := (Finset.mem_Icc.mp (hS hq)).1
    have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hqpos
    have hd : (1 : ℝ) ≤ q.divisors.card := by
      exact_mod_cast Finset.one_le_card.mpr ⟨1, Nat.one_mem_divisors.mpr hqpos.ne'⟩
    constructor
    · exact (pow_le_pow_right₀ hd (Nat.le_succ J)).trans (hv q hq)
    · calc
        _ = ((q.divisors.card : ℝ) ^ J / q) * ((q : ℝ) / (q.totient : ℝ)) := by
          field_simp
        _ ≤ ((q.divisors.card : ℝ) ^ J / q) * q.divisors.card :=
          mul_le_mul_of_nonneg_left (div_totient_le_card_divisors q) (by positivity)
        _ = (q.divisors.card : ℝ) ^ (J + 1) / q := by rw [pow_succ]; ring
        _ ≤ V / q := div_le_div_of_nonneg_right (hv q hq) hqR.le
  have hpoint (q : ℕ) (hq : q ∈ S) :
      (q.divisors.card : ℝ) ^ J *
        ‖fullDiscrepancy (∑ n ∈ Finset.Icc 1 N, Finsupp.single n (e n)) q (a q)‖ ≤
      2 * U * V * (A / q + P) := by
    have hraw := square_supported_band_fullDiscrepancy_le N r P hr D hD U hU e hb hs
      q (a q) (Finset.mem_Icc.mp (hS hq)).1 (ha q hq)
    obtain ⟨hw, hwφ⟩ := hpw q hq
    calc
      _ ≤ (q.divisors.card : ℝ) ^ J * (2 * U * (A / (q.totient : ℝ) + P)) :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
      _ = 2 * U * (A * ((q.divisors.card : ℝ) ^ J / (q.totient : ℝ)) +
          (P : ℝ) * (q.divisors.card : ℝ) ^ J) := by ring
      _ ≤ 2 * U * (A * (V / q) + (P : ℝ) * V) := by
        exact mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left hwφ hA)
          (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg P))) (mul_nonneg zero_le_two hU)
      _ = _ := by ring
  have hsum : (∑ q ∈ Finset.Icc 1 Q, (A / (q : ℝ) + P)) =
      A * (harmonic Q : ℝ) + (P : ℝ) * Q := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.sum_add_distrib,
      Finset.mul_sum, div_eq_mul_inv, Finset.sum_const, nsmul_eq_mul, Nat.card_Icc,
      Nat.add_sub_cancel]
    ring
  calc
    _ ≤ ∑ q ∈ S, 2 * U * V * (A / (q : ℝ) + P) := Finset.sum_le_sum hpoint
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, 2 * U * V * (A / (q : ℝ) + P) :=
      Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)
    _ = 2 * U * V * (A * (harmonic Q : ℝ) + (P : ℝ) * Q) := by
      rw [← Finset.mul_sum, hsum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log Q) hA) le_rfl)
      (by positivity)

theorem square_supported_log_saving182 (k J : ℕ) (A : ℝ) (_hA : 0 < A) :
    ∃ K X : ℝ, 0 < K ∧ Real.exp 1 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 ⌊x ^ ((53 : ℝ) / 100)⌋₊ →
      ∀ a : ℕ → ℕ, (∀ q ∈ S, Nat.Coprime (a q) q) →
      ∀ e : ℕ → ℂ,
      (∀ n ∈ Finset.Icc 1 ⌊2 * x⌋₊, ‖e n‖ ≤ (n.divisors.card : ℝ) ^ k) →
      (∀ n ∈ Finset.Icc 1 ⌊2 * x⌋₊, e n ≠ 0 →
        ∃ p : ℕ, p.Prime ∧ x ^ ((8639 : ℝ) / 50000) ≤ (p : ℝ) ∧
          (p : ℝ) ≤ x ^ ((31 : ℝ) / 100) ∧ p ^ 2 ∣ n) →
      (∑ q ∈ S, (q.divisors.card : ℝ) ^ J *
        ‖fullDiscrepancy (∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊, Finsupp.single n (e n)) q (a q)‖) ≤
          K * x / (Real.log x) ^ A := by
  let ε : ℝ := 1 / 100
  have hε : 0 < ε := by norm_num [ε]
  obtain ⟨Cf, hCf, hf⟩ := exists_divisorPower_bound k hε
  obtain ⟨Cq, hCq, hqbound⟩ := exists_divisorPower_bound (J + 1) hε
  let C : ℝ := Cf * (2 : ℝ) ^ ε
  let K : ℝ := 18 * C * Cq
  have hC : 0 < C := by dsimp only [C]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  obtain ⟨Xlog, hXlog⟩ := ((isLittleO_log_rpow_rpow_atTop (A + 1) hε).eventuallyLE).exists_forall_of_atTop
  obtain ⟨Xroot, hXroot⟩ := ((tendsto_rpow_atTop
    (by norm_num : (0 : ℝ) < (8639 : ℝ) / 50000)).eventually_ge_atTop 2).exists_forall_of_atTop
  let X : ℝ := max (Real.exp 1) (max Xlog Xroot)
  refine ⟨K, X, hK, le_max_left _ _, ?_⟩
  intro x hx S hS a ha e hb hs
  have hxExp : Real.exp 1 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hxExp
  have hx1 : 1 ≤ x := (Real.one_le_exp zero_le_one).trans hxExp
  have hlog1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxExp
  have hlog0 : 0 < Real.log x := zero_lt_one.trans_le hlog1
  have hlogA : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hlog0 A
  have hlog : (Real.log x) ^ (A + 1) ≤ x ^ ε := by
    have ht := hXlog x ((le_max_left _ _).trans ((le_max_right _ _).trans hx))
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hlog0.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] using ht
  have hlog' : (Real.log x) ^ A ≤ x ^ ε :=
    (Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)).trans hlog
  have hroot : 2 ≤ x ^ ((8639 : ℝ) / 50000) :=
    hXroot x ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  let N : ℕ := ⌊2 * x⌋₊
  let r : ℕ := ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
  let P : ℕ := ⌊x ^ ((31 : ℝ) / 100)⌋₊
  let Q : ℕ := ⌊x ^ ((53 : ℝ) / 100)⌋₊
  let D := (Finset.Icc r P).filter Nat.Prime
  let U : ℝ := C * x ^ ε
  let V : ℝ := Cq * x ^ ε
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hr : 2 ≤ r := by
    have hh := hroot.trans (Nat.le_ceil (x ^ ((8639 : ℝ) / 50000)))
    exact_mod_cast hh
  have hden : x ^ ((8639 : ℝ) / 50000) / 2 ≤ ((r - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
    have hh : x ^ ((8639 : ℝ) / 50000) ≤ (r : ℝ) := Nat.le_ceil _
    linarith only [hh, hroot]
  have hN : (N : ℝ) ≤ 2 * x := Nat.floor_le (by positivity)
  have hQpos : 0 < Q := by
    have hh : 1 ≤ Q := Nat.le_floor (by simpa only [Nat.cast_one] using
      (Real.one_le_rpow hx1 (by norm_num : (0 : ℝ) ≤ 53 / 100)))
    exact hh
  have hQx : (Q : ℝ) ≤ x :=
    (Nat.floor_le (Real.rpow_nonneg hx0.le _)).trans
      (Real.rpow_le_self_of_one_le hx1 (by norm_num : (53 : ℝ) / 100 ≤ 1))
  have hLQ : 1 + Real.log (Q : ℝ) ≤ 2 * Real.log x := by
    have hh := Real.log_le_log (Nat.cast_pos.mpr hQpos) hQx
    linarith only [hh, hlog1]
  have hLQA : (1 + Real.log (Q : ℝ)) * (Real.log x) ^ A ≤ 2 * x ^ ε := by
    calc
      _ ≤ (2 * Real.log x) * (Real.log x) ^ A := mul_le_mul_of_nonneg_right hLQ hlogA.le
      _ = 2 * (Real.log x) ^ (A + 1) := by rw [Real.rpow_add hlog0, Real.rpow_one]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog zero_le_two
  have hNr : (N : ℝ) / ((r - 1 : ℕ) : ℝ) ≤ 4 * x ^ (1 - (8639 : ℝ) / 50000) := by
    calc
      _ ≤ (2 * x) / ((r - 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hN (Nat.cast_nonneg _)
      _ ≤ (2 * x) / (x ^ ((8639 : ℝ) / 50000) / 2) :=
        div_le_div_of_nonneg_left (by positivity)
          (half_pos (Real.rpow_pos_of_pos hx0 _)) hden
      _ = _ := by rw [Real.rpow_sub hx0, Real.rpow_one]; ring
  have hPQ : (P : ℝ) * Q ≤ x ^ ((31 : ℝ) / 100 + 53 / 100) := by
    rw [Real.rpow_add hx0]
    exact mul_le_mul (Nat.floor_le (Real.rpow_nonneg hx0.le _))
      (Nat.floor_le (Real.rpow_nonneg hx0.le _)) (Nat.cast_nonneg Q) (Real.rpow_nonneg hx0.le _)
  have heU : ∀ n ∈ Finset.Icc 1 N, ‖e n‖ ≤ U := by
    intro n hn
    have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1
    have hnx : (n : ℝ) ≤ 2 * x := (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans hN
    calc
      _ ≤ (n.divisors.card : ℝ) ^ k := hb n hn
      _ ≤ Cf * (n : ℝ) ^ ε := hf n hn0
      _ ≤ Cf * (2 * x) ^ ε := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hnx hε.le) hCf.le
      _ = U := by dsimp only [U, C]; rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx0.le]; ring
  have heD : ∀ n ∈ Finset.Icc 1 N, e n ≠ 0 → ∃ p ∈ D, p ^ 2 ∣ n := by
    intro n hn hne
    obtain ⟨p, hp, hlo, hhi, hdiv⟩ := hs n hn hne
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hlo, Nat.le_floor hhi⟩, hp⟩, hdiv⟩
  have hv : ∀ q ∈ S, (q.divisors.card : ℝ) ^ (J + 1) ≤ V := by
    intro q hq
    have hqr := Finset.mem_Icc.mp (hS hq)
    have hqx : (q : ℝ) ≤ x := (Nat.cast_le.mpr hqr.2).trans hQx
    exact (hqbound q (Nat.one_le_iff_ne_zero.mp hqr.1)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hqx hε.le) hCq.le)
  have hraw := square_supported_weighted_bound N r P Q J hr D (Finset.filter_subset _ _)
    S hS a ha U V hU hV hv e heU heD
  apply (le_div_iff₀ hlogA).mpr
  have hbound :
      (2 * U * V * ((N : ℝ) / ((r - 1 : ℕ) : ℝ) * (1 + Real.log (Q : ℝ)) + (P : ℝ) * Q)) *
          (Real.log x) ^ A ≤
        2 * U * V * (4 * x ^ (1 - (8639 : ℝ) / 50000) * (2 * x ^ ε) +
          x ^ ((31 : ℝ) / 100 + 53 / 100) * x ^ ε) := by
    have hid :
        (2 * U * V * ((N : ℝ) / ((r - 1 : ℕ) : ℝ) * (1 + Real.log (Q : ℝ)) + (P : ℝ) * Q)) *
            (Real.log x) ^ A =
          2 * U * V * ((N : ℝ) / ((r - 1 : ℕ) : ℝ) *
            ((1 + Real.log (Q : ℝ)) * (Real.log x) ^ A) + ((P : ℝ) * Q) * (Real.log x) ^ A) := by ring
    rw [hid]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add
      (mul_le_mul hNr hLQA (by positivity) (by positivity))
      (mul_le_mul hPQ hlog' hlogA.le (Real.rpow_nonneg hx0.le _))
  have hid :
      2 * U * V * (4 * x ^ (1 - (8639 : ℝ) / 50000) * (2 * x ^ ε) +
        x ^ ((31 : ℝ) / 100 + 53 / 100) * x ^ ε) =
      2 * C * Cq * (8 * x ^ (1 - (8639 : ℝ) / 50000 + 3 * ε) +
        x ^ ((31 : ℝ) / 100 + 53 / 100 + 3 * ε)) := by
    dsimp only [U, V]
    rw [show 3 * ε = ε + ε + ε by ring]
    simp only [Real.rpow_add hx0]
    ring
  have hp0 : x ^ (1 - (8639 : ℝ) / 50000 + 3 * ε) ≤ x :=
    Real.rpow_le_self_of_one_le hx1 (by norm_num [ε])
  have hp1 : x ^ ((31 : ℝ) / 100 + 53 / 100 + 3 * ε) ≤ x :=
    Real.rpow_le_self_of_one_le hx1 (by norm_num [ε])
  have hfinal : 2 * C * Cq * (8 * x ^ (1 - (8639 : ℝ) / 50000 + 3 * ε) +
      x ^ ((31 : ℝ) / 100 + 53 / 100 + 3 * ε)) ≤ K * x := by
    have hh := mul_le_mul_of_nonneg_left (show
      8 * x ^ (1 - (8639 : ℝ) / 50000 + 3 * ε) +
        x ^ ((31 : ℝ) / 100 + 53 / 100 + 3 * ε) ≤ 9 * x by linarith only [hp0, hp1])
      (show 0 ≤ 2 * C * Cq by positivity)
    have heq : 2 * C * Cq * (9 * x) = K * x := by
      dsimp only [K]
      ring
    exact hh.trans_eq heq
  exact (mul_le_mul_of_nonneg_right hraw hlogA.le).trans (hbound.trans (hid ▸ hfinal))

#print axioms square_supported_weighted_bound
#print axioms square_supported_log_saving182

end PrimeGap182Analytic
