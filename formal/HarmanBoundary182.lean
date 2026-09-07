import PrimeGaps186

/-! Original-coordinate Heath-Brown boundary errors on [.23,.42].
The short-interval divisor estimates, carrier widths, telescoping identity,
and actual weighted discrepancies are rechecked. The new upper endpoint
remains below the five-fold HB cutoff .45 and below 1−.53.
Adapted from Apache-2.0 PrimeGaps186 at the source hash in the generator. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

theorem hbBoundary_original_mesh_smallness (D₀ : ℕ) :
    ∃ X : ℝ, Real.exp 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → ∀ D : ℕ, D₀ + 2 ≤ D →
      ∀ N : ℝ, x ^ ((23 : ℝ) / 100) ≤ N →
      let u : ℝ := (Real.log x) ^ (-(D : ℝ))
      0 < u ∧ u ≤ 1 ∧ 1 < 1 + u ∧ 1 + u ≤ 2 ∧ (1 + u) ^ 60 ≤ 2 ∧
        (2 : ℝ) ^ 61 * N * u + 1 ≤ N / (Real.log x) ^ D₀ := by
  let C : ℝ := (2 : ℝ) ^ 61
  have hC : 0 < C := by positivity
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop (D₀ : ℝ)
      (by norm_num : (0 : ℝ) < 23 / 100)).const_mul_left (2 : ℝ)).eventuallyLE
  refine ⟨max X₀ (Real.exp (max 1 (2 * C))), ?_, ?_⟩
  · exact (Real.exp_monotone (le_max_left _ _)).trans (le_max_right _ _)
  intro x hx D hD N hNlo u
  let Θ : ℝ := 1 + u
  have hx₀ : X₀ ≤ x := (le_max_left _ _).trans hx
  have hxexp : Real.exp (max 1 (2 * C)) ≤ x := (le_max_right _ _).trans hx
  have hxpos : 0 < x := (Real.exp_pos _).trans_le hxexp
  have hxone : 1 ≤ x := (Real.one_le_exp (zero_le_one.trans (le_max_left _ _))).trans hxexp
  have hloglarge : max 1 (2 * C) ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hxexp
  let L : ℝ := Real.log x
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hloglarge
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  have hLlarge : 2 * C ≤ L := (le_max_right _ _).trans hloglarge
  have hN1 : 1 ≤ N := (Real.one_le_rpow hxone (by norm_num : (0 : ℝ) ≤ 23 / 100)).trans hNlo
  have hNpos : 0 < N := zero_lt_one.trans_le hN1
  have hu : 0 < u := Real.rpow_pos_of_pos hLpos _
  have hu1 : u ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (neg_nonpos.mpr (Nat.cast_nonneg D))
  have hΘ : Θ = 1 + u := rfl
  have hΘgt : 1 < Θ := by rw [hΘ]; linarith
  have hΘtwo : Θ ≤ 2 := by rw [hΘ]; linarith
  have hLp : 0 < L ^ D₀ := pow_pos hLpos _
  have hLp1 : 1 ≤ L ^ D₀ := one_le_pow₀ hL1
  have hloghalf : L ^ D₀ ≤ N / 2 := by
    have he := hX₀ x hx₀
    have hnlog : 0 ≤ 2 * (Real.log x) ^ (D₀ : ℝ) := by positivity
    have htwor : 2 * (Real.log x) ^ (D₀ : ℝ) ≤ x ^ ((23 : ℝ) / 100) := by
      simpa only [Real.norm_of_nonneg hnlog,
        Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le _)] using he
    have htwo : 2 * L ^ D₀ ≤ x ^ ((23 : ℝ) / 100) := by
      simpa only [Real.rpow_natCast] using htwor
    linarith
  have huSmall : u ≤ (L ^ (D₀ + 2))⁻¹ := by
    change L ^ (-(D : ℝ)) ≤ (L ^ (D₀ + 2))⁻¹
    have hDreal : ((D₀ + 2 : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    calc
      L ^ (-(D : ℝ)) ≤ L ^ (-((D₀ + 2 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (neg_le_neg hDreal)
      _ = _ := by rw [Real.rpow_neg hLpos.le, Real.rpow_natCast]
  have hCscaled : C * u * L ^ D₀ ≤ (1 / 2 : ℝ) := by
    calc
      C * u * L ^ D₀ ≤ C * (L ^ (D₀ + 2))⁻¹ * L ^ D₀ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huSmall hC.le) hLp.le
      _ = C / L ^ 2 := by
        rw [pow_add]
        field_simp [hLpos.ne']
      _ ≤ (1 / 2 : ℝ) := by
        apply (div_le_iff₀ (pow_pos hLpos 2)).mpr
        have hsq : 2 * C ≤ L ^ 2 := hLlarge.trans (le_self_pow₀ hL1 (by decide))
        linarith
  have hCu : C * u ≤ (1 / 2 : ℝ) :=
    (le_mul_of_one_le_right (mul_nonneg hC.le hu.le) hLp1).trans hCscaled
  have hwidth := minorantHB_radial_power_sixty_width Θ u hΘ hu.le hu1
  have hpowbound : Θ ^ 60 ≤ 2 := by
    have hC60 : (2 : ℝ) ^ 60 ≤ C := pow_le_pow_right₀ (by norm_num) (by decide)
    have hs := (mul_le_mul_of_nonneg_right hC60 hu.le).trans hCu
    linarith
  have hbound : C * N * u + 1 ≤ N / L ^ D₀ := by
    apply (le_div_iff₀ hLp).mpr
    calc
      (C * N * u + 1) * L ^ D₀ = N * (C * u * L ^ D₀) + L ^ D₀ := by ring
      _ ≤ N * (1 / 2) + N / 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hCscaled hNpos.le) hloghalf
      _ = N := by ring
  exact ⟨hu, hu1, hΘgt, hΘtwo, hpowbound, hbound⟩

theorem minorantHB_original_mesh_carrier_widths (D₀ : ℕ) :
    ∃ X : ℝ, Real.exp 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → ∀ D : ℕ, D₀ + 2 ≤ D →
      ∀ N : ℝ, x ^ ((23 : ℝ) / 100) ≤ N → N ≤ x ^ ((42 : ℝ) / 100) →
      ∀ A B : ℝ, N ≤ A → A ≤ B → B ≤ 2 * N →
      let Θ : ℝ := 1 + (Real.log x) ^ (-(D : ℝ))
      1 < Θ ∧ Θ ≤ 2 ∧ Θ ^ 60 ≤ 2 ∧ B ≤ (x ^ ((9 : ℝ) / 100)) ^ (5 : ℕ) ∧
      (1 ≤ ⌈A / Θ ^ 60⌉₊ ∧ ⌈A / Θ ^ 60⌉₊ ≤ ⌊A⌋₊ + 1 ∧
        ⌊A⌋₊ + 1 ≤ ⌈8 * N⌉₊ + 1 ∧
        ((⌊A⌋₊ + 1 - ⌈A / Θ ^ 60⌉₊ : ℕ) : ℝ) ≤ N / (Real.log x) ^ D₀) ∧
      (1 ≤ ⌈B⌉₊ ∧ ⌈B⌉₊ ≤ ⌊B * Θ ^ 60⌋₊ + 1 ∧
        ⌊B * Θ ^ 60⌋₊ + 1 ≤ ⌈8 * N⌉₊ + 1 ∧
        ((⌊B * Θ ^ 60⌋₊ + 1 - ⌈B⌉₊ : ℕ) : ℝ) ≤ N / (Real.log x) ^ D₀) := by
  obtain ⟨X₀, hX₀, hsmall⟩ := hbBoundary_original_mesh_smallness D₀
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 100)).eventually_ge_atTop (2 : ℝ))
  refine ⟨max X₀ X₁, hX₀.trans (le_max_left _ _), ?_⟩
  intro x hx D hD N hNlo hNhi A B hNA hAB hBN Θ
  have hx₀ : X₀ ≤ x := (le_max_left _ _).trans hx
  have hx₁ : X₁ ≤ x := (le_max_right _ _).trans hx
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le (hX₀.trans hx₀)
  have hNpos : 0 < N := (Real.rpow_pos_of_pos hxpos _).trans_le hNlo
  have hApos : 0 < A := hNpos.trans_le hNA
  have hBpos : 0 < B := hApos.trans_le hAB
  let C : ℝ := (2 : ℝ) ^ 61
  let u : ℝ := (Real.log x) ^ (-(D : ℝ))
  have hΘ : Θ = 1 + u := rfl
  obtain ⟨hu, hu1, hΘgt, hΘtwo, hpowbound, hbound⟩ := hsmall x hx₀ D hD N hNlo
  have hwidth := minorantHB_radial_power_sixty_width Θ u hΘ hu.le hu1
  have hpowpos : 0 < Θ ^ 60 := pow_pos (zero_lt_one.trans hΘgt) _
  have hpowone : 1 ≤ Θ ^ 60 := one_le_pow₀ hΘgt.le
  have hloLe : A / Θ ^ 60 ≤ A := div_le_self hApos.le hpowone
  have hhiLe : B ≤ B * Θ ^ 60 := le_mul_of_one_le_right hBpos.le hpowone
  have hAupper : A ≤ 8 * N := by linarith
  have hBupper : B * Θ ^ 60 ≤ 8 * N := by
    calc
      B * Θ ^ 60 ≤ (2 * N) * 2 :=
        mul_le_mul hBN hpowbound hpowpos.le (mul_nonneg zero_le_two hNpos.le)
      _ ≤ 8 * N := by nlinarith only [hNpos]
  have hlowWidth : A - A / Θ ^ 60 ≤ C * N * u := by
    calc
      A - A / Θ ^ 60 = A * (Θ ^ 60 - 1) / Θ ^ 60 := by
        rw [mul_sub, mul_one, sub_div, mul_div_cancel_right₀ _ hpowpos.ne']
      _ ≤ A * (Θ ^ 60 - 1) := div_le_self (mul_nonneg hApos.le hwidth.1) hpowone
      _ ≤ (2 * N) * ((2 : ℝ) ^ 60 * u) :=
        mul_le_mul (hAB.trans hBN) hwidth.2 hwidth.1 (by positivity)
      _ = C * N * u := by dsimp only [C]; rw [pow_succ]; ring
  have hhighWidth : B * Θ ^ 60 - B ≤ C * N * u := by
    calc
      B * Θ ^ 60 - B = B * (Θ ^ 60 - 1) := by ring
      _ ≤ (2 * N) * ((2 : ℝ) ^ 60 * u) :=
        mul_le_mul hBN hwidth.2 hwidth.1 (by positivity)
      _ = C * N * u := by dsimp only [C]; rw [pow_succ]; ring
  have hBU : B ≤ (x ^ ((9 : ℝ) / 100)) ^ (5 : ℕ) := by
    have hsmall := hX₁ x hx₁
    have hmul : x ^ ((3 : ℝ) / 100) * x ^ ((42 : ℝ) / 100) =
        (x ^ ((9 : ℝ) / 100)) ^ (5 : ℕ) := by
      rw [← Real.rpow_add hxpos, ← Real.rpow_mul_natCast hxpos.le]
      congr 1
      norm_num
    calc
      B ≤ 2 * N := hBN
      _ ≤ x ^ ((3 : ℝ) / 100) * x ^ ((42 : ℝ) / 100) :=
        mul_le_mul hsmall hNhi hNpos.le (Real.rpow_nonneg hxpos.le _)
      _ = _ := hmul
  have hlo := minorantHB_closed_interval_carrier_width
    (A / Θ ^ 60) A (by positivity) hloLe
  have hhi := minorantHB_closed_interval_carrier_width B (B * Θ ^ 60) hBpos.le hhiLe
  refine ⟨hΘgt, hΘtwo, hpowbound, hBU, ?_, ?_⟩
  · exact ⟨Nat.ceil_pos.mpr (by positivity),
      (Nat.ceil_mono hloLe).trans (Nat.ceil_le_floor_add_one _),
      Nat.add_le_add_right ((Nat.floor_mono hAupper).trans (Nat.floor_le_ceil _)) 1,
      hlo.2.trans ((add_le_add hlowWidth le_rfl).trans hbound)⟩
  · exact ⟨Nat.ceil_pos.mpr hBpos,
      (Nat.ceil_mono hhiLe).trans (Nat.ceil_le_floor_add_one _),
      Nat.add_le_add_right ((Nat.floor_mono hBupper).trans (Nat.floor_le_ceil _)) 1,
      hhi.2.trans ((add_le_add hhighWidth le_rfl).trans hbound)⟩

open Classical in
theorem finite_product_sample_filter {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (w : ι → ℕ → ℂ) (R : ℕ → Prop) :
    ((∏ i, (MonoidAlgebra.ofCoeff (∑ n ∈ S i, Finsupp.single n (w i n)) :
      MonoidAlgebra ℂ ℕ)).coeff).filter R =
      ∑ p ∈ (Fintype.piFinset S).filter (fun p => R (∏ i, p i)),
        Finsupp.single (∏ i, p i) (∏ i, w i (p i)) := by
  simp only [MonoidAlgebra.ofCoeff_sum, MonoidAlgebra.ofCoeff_single]
  rw [Finset.prod_univ_sum]
  simp only [MonoidAlgebra.prod_single, MonoidAlgebra.coeff_sum,
    MonoidAlgebra.coeff_single, Finsupp.filter_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases h : R (∏ i, p i) <;> simp [h]

theorem minorantHB_original_boundary_pair_moduli_log_saving
    (J : ℕ) (saving : ℝ) (hsaving : 0 < saving) :
    ∃ D₀ : ℕ, 1 ≤ D₀ ∧ ∃ K X : ℝ, 0 < K ∧ Real.exp 1 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ D : ℕ, D₀ ≤ D →
      ∀ N A B t : Fin 3 → ℝ,
        (∀ i, x ^ ((23 : ℝ) / 100) ≤ N i ∧ N i ≤ x ^ ((42 : ℝ) / 100)) →
        (∀ i, N i ≤ A i ∧ A i ≤ B i ∧ B i ≤ 2 * N i) →
        (∀ i, 0 ≤ t i ∧ t i ≤ 10) →
      ∀ c d k : Fin 3, ∀ e f : Bool,
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 ⌊x ^ ((53 : ℝ) / 100)⌋₊ →
      ∀ a : ℕ → ℕ, (∀ q ∈ S, Nat.Coprime (a q) q) →
      let Θ : ℝ := 1 + (Real.log x) ^ (-(D : ℝ))
      let U : ℝ := x ^ ((9 : ℝ) / 100)
      let H : Fin 3 → Bool → ℕ →₀ ℂ := fun i b =>
        if b then minorantHBUnmaskedFive (A i) (B i) U Θ (t i)
        else minorantHBClosedMangoldt (A i) (B i) (t i)
      let E : ℕ →₀ ℂ := H c true - H c false
      let P : ℕ →₀ ℂ :=
        ((MonoidAlgebra.ofCoeff (H d e) : MonoidAlgebra ℂ ℕ) *
          MonoidAlgebra.ofCoeff (H k f)).coeff
      let R : ℕ →₀ ℂ :=
        ((MonoidAlgebra.ofCoeff E : MonoidAlgebra ℂ ℕ) *
          MonoidAlgebra.ofCoeff P).coeff.filter
            (fun n : ℕ => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x)
      (∑ q ∈ S, (q.divisors.card : ℝ) ^ J * ‖fullDiscrepancy R q (a q)‖) ≤
        K * x / (Real.log x) ^ saving := by
  classical
  obtain ⟨D₁, hD₁, K₀, X₀, hK₀, hX₀, hAP⟩ :=
    original_factor_short_interval_moduli_log_saving
      ((23 : ℝ) / 100) ((42 : ℝ) / 100) ((53 : ℝ) / 100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      9 19 3 J 8 saving (by norm_num) hsaving
  obtain ⟨X₁, hX₁, hmesh⟩ := minorantHB_original_mesh_carrier_widths D₁
  let L : ℝ := 31 * 1024 * 8
  have hL : 0 < L := by norm_num [L]
  refine ⟨D₁ + 2, by omega, 2 * K₀ * L, max X₀ X₁, by positivity,
    hX₀.trans (le_max_left _ _), ?_⟩
  intro x hx D hD N A B t hN hAB ht c d k e f S hS a ha Θ U H E P R
  have hx₀ : X₀ ≤ x := (le_max_left _ _).trans hx
  have hx₁ : X₁ ≤ x := (le_max_right _ _).trans hx
  have hxExp : Real.exp 1 ≤ x := hX₀.trans hx₀
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hxExp
  have hxone : 1 ≤ x := (Real.one_le_exp zero_le_one).trans hxExp
  have hlogone : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hxExp
  have hN1 (i : Fin 3) : 1 ≤ N i :=
    (Real.one_le_rpow hxone (by norm_num : (0 : ℝ) ≤ 23 / 100)).trans (hN i).1
  have hNpos (i : Fin 3) : 0 < N i := zero_lt_one.trans_le (hN1 i)
  have hA1 (i : Fin 3) : 1 ≤ A i := (hN1 i).trans (hAB i).1
  have hBpos (i : Fin 3) : 0 < B i :=
    zero_lt_one.trans_le ((hA1 i).trans (hAB i).2.1)
  have hm (i : Fin 3) := hmesh x hx₁ D hD (N i) (hN i).1 (hN i).2
    (A i) (B i) (hAB i).1 (hAB i).2.1 (hAB i).2.2
  change ∀ i : Fin 3,
    1 < Θ ∧ Θ ≤ 2 ∧ Θ ^ 60 ≤ 2 ∧ B i ≤ U ^ 5 ∧
      (1 ≤ ⌈A i / Θ ^ 60⌉₊ ∧ ⌈A i / Θ ^ 60⌉₊ ≤ ⌊A i⌋₊ + 1 ∧
        ⌊A i⌋₊ + 1 ≤ ⌈8 * N i⌉₊ + 1 ∧
        ((⌊A i⌋₊ + 1 - ⌈A i / Θ ^ 60⌉₊ : ℕ) : ℝ) ≤
          N i / (Real.log x) ^ D₁) ∧
      (1 ≤ ⌈B i⌉₊ ∧ ⌈B i⌉₊ ≤ ⌊B i * Θ ^ 60⌋₊ + 1 ∧
        ⌊B i * Θ ^ 60⌋₊ + 1 ≤ ⌈8 * N i⌉₊ + 1 ∧
        ((⌊B i * Θ ^ 60⌋₊ + 1 - ⌈B i⌉₊ : ℕ) : ℝ) ≤
          N i / (Real.log x) ^ D₁) at hm
  have hΘ : 1 < Θ := (hm c).1
  have hΘpos : 0 < Θ := zero_lt_one.trans hΘ
  have hΘtwo : Θ ≤ 2 := (hm c).2.1
  have hpow : Θ ^ 20 ≤ Θ ^ 60 := pow_le_pow_right₀ hΘ.le (by decide)
  have h60pos : 0 < Θ ^ 60 := pow_pos hΘpos _
  have hApos : 0 < A c := zero_lt_one.trans_le (hA1 c)
  have hAlow : A c / Θ ^ 60 ≤ A c / Θ ^ 20 :=
    div_le_div_of_nonneg_left hApos.le (pow_pos hΘpos _) hpow
  have hQuarter : N c / 4 ≤ A c / Θ ^ 60 := by
    apply (le_div_iff₀ h60pos).mpr
    have hh := mul_le_mul_of_nonneg_left (hm c).2.2.1
      (div_nonneg (hNpos c).le (by norm_num : (0 : ℝ) ≤ 4))
    nlinarith [(hAB c).1]
  have hboundary := minorantHB_five_boundary (A c) (B c) U Θ (t c)
    (hA1 c) (hAB c).2.1 (Real.rpow_nonneg hxpos.le _) (hm c).2.2.2.1
    hΘ hΘtwo (ht c).1 (ht c).2
  change (∀ n ∈ E.support,
    (A c / Θ ^ 20 ≤ (n : ℝ) ∧ (n : ℝ) < A c) ∨
      (B c < (n : ℝ) ∧ (n : ℝ) ≤ B c * Θ ^ 20)) ∧
    ∀ n : ℕ, ‖E n‖ ≤ 31 * (n.divisors.card : ℝ) ^ 9 * Real.log (n : ℝ)
    at hboundary
  have hcofactor := minorantHB_two_original_cofactor_norm_le A B t U Θ hA1
    (fun i => (hAB i).2.1) (Real.rpow_nonneg hxpos.le _)
    (fun i => (hm i).2.2.2.1) hΘ hΘtwo (fun i => (ht i).1)
    (fun i => (ht i).2) d k e f
  change (∀ m : ℕ, ‖P m‖ ≤
    1024 * (m.divisors.card : ℝ) ^ 19 * (Real.log (m : ℝ)) ^ 2) ∧ P 0 = 0
    at hcofactor
  let E₀ : ℕ →₀ ℂ := E.filter (fun n : ℕ => (n : ℝ) < A c)
  let E₁ : ℕ →₀ ℂ := E.filter (fun n : ℕ => B c < (n : ℝ))
  have hsplit : E = E₀ + E₁ := by
    ext n
    by_cases hlo : (n : ℝ) < A c
    · have hhi : ¬B c < (n : ℝ) := by linarith [(hAB c).2.1]
      simp only [E₀, E₁, Finsupp.add_apply, Finsupp.filter_apply,
        ite_eq_left hlo, ite_eq_right hhi, add_zero]
    · by_cases hhi : B c < (n : ℝ)
      · simp only [E₀, E₁, Finsupp.add_apply, Finsupp.filter_apply,
          ite_eq_right hlo, ite_eq_left hhi, zero_add]
      · have hn : E n = 0 := by
          by_contra hn
          rcases hboundary.1 n (Finsupp.mem_support_iff.mpr hn) with hn | hn
          · exact hlo hn.2
          · exact hhi hn.1
        simp only [E₀, E₁, Finsupp.add_apply, Finsupp.filter_apply,
          ite_eq_right hlo, ite_eq_right hhi, hn, add_zero]
  have hsupp₀ (n : ℕ) (hn : n ∈ E₀.support) :
      n ∈ Finset.Ico ⌈A c / Θ ^ 60⌉₊ (⌊A c⌋₊ + 1) ∧ N c / 4 ≤ (n : ℝ) := by
    change n ∈ E.support.filter (fun n : ℕ => (n : ℝ) < A c) at hn
    obtain ⟨hnE, hnA⟩ := Finset.mem_filter.mp hn
    have hnlo : A c / Θ ^ 20 ≤ (n : ℝ) := by
      rcases hboundary.1 n hnE with h | h
      · exact h.1
      · linarith [(hAB c).2.1]
    have hn60 := hAlow.trans hnlo
    refine ⟨Finset.mem_Ico.mpr ⟨Nat.ceil_le.mpr hn60, ?_⟩, hQuarter.trans hn60⟩
    exact Nat.lt_succ_of_le ((Nat.le_floor_iff hApos.le).mpr hnA.le)
  have hsupp₁ (n : ℕ) (hn : n ∈ E₁.support) :
      n ∈ Finset.Ico ⌈B c⌉₊ (⌊B c * Θ ^ 60⌋₊ + 1) ∧ N c / 4 ≤ (n : ℝ) := by
    change n ∈ E.support.filter (fun n : ℕ => B c < (n : ℝ)) at hn
    obtain ⟨hnE, hnB⟩ := Finset.mem_filter.mp hn
    have hnhi : (n : ℝ) ≤ B c * Θ ^ 20 := by
      rcases hboundary.1 n hnE with h | h
      · linarith [(hAB c).2.1]
      · exact h.2
    have hn60 := hnhi.trans (mul_le_mul_of_nonneg_left hpow (hBpos c).le)
    refine ⟨Finset.mem_Ico.mpr ⟨Nat.ceil_le.mpr hnB.le, ?_⟩, ?_⟩
    · exact Nat.lt_succ_of_le ((Nat.le_floor_iff
        (mul_nonneg (hBpos c).le h60pos.le)).mpr hn60)
    · linarith [(hAB c).1, (hAB c).2.1, (hNpos c)]
  have hpart (T : ℕ → Prop) (lo hi : ℕ) (hlo : 1 ≤ lo) (hlohi : lo ≤ hi)
      (hhi : hi ≤ ⌈8 * N c⌉₊ + 1)
      (hwidth : ((hi - lo : ℕ) : ℝ) ≤ N c / (Real.log x) ^ D₁)
      (hsupp : ∀ n ∈ (E.filter T).support,
        n ∈ Finset.Ico lo hi ∧ N c / 4 ≤ (n : ℝ)) :
      (∑ q ∈ S, (q.divisors.card : ℝ) ^ J *
        ‖fullDiscrepancy
          (((MonoidAlgebra.ofCoeff (E.filter T) : MonoidAlgebra ℂ ℕ) *
            MonoidAlgebra.ofCoeff P).coeff.filter
              (fun n : ℕ => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x)) q (a q)‖) ≤
        K₀ * L * x / (Real.log x) ^ saving := by
    rw [minorantHB_boundary_filtered_pair_rectangle (E.filter T) P x (N c)
      hxpos (hNpos c) (Finset.Ico lo hi) hsupp]
    apply hAP x hx₀ L hL.le (N c) (hN c).1 (hN c).2
      lo hi hlo hlohi hhi hwidth S hS a ha
    intro n hn m hm'
    exact hbBoundary_masked_pair_norm E P x hxpos hlogone hboundary.2 hcofactor.1
      T n m (hlo.trans (Finset.mem_Ico.mp hn).1) (Finset.mem_Icc.mp hm').1
  let R₀ : ℕ →₀ ℂ :=
    ((MonoidAlgebra.ofCoeff E₀ : MonoidAlgebra ℂ ℕ) *
      MonoidAlgebra.ofCoeff P).coeff.filter
        (fun n : ℕ => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x)
  let R₁ : ℕ →₀ ℂ :=
    ((MonoidAlgebra.ofCoeff E₁ : MonoidAlgebra ℂ ℕ) *
      MonoidAlgebra.ofCoeff P).coeff.filter
        (fun n : ℕ => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x)
  have hR : R = R₀ + R₁ := by
    change ((MonoidAlgebra.ofCoeff E : MonoidAlgebra ℂ ℕ) *
      MonoidAlgebra.ofCoeff P).coeff.filter _ = _
    rw [hsplit, MonoidAlgebra.ofCoeff_add, add_mul, MonoidAlgebra.coeff_add,
      Finsupp.filter_add]
  have hlo := (hm c).2.2.2.2.1
  have hhi := (hm c).2.2.2.2.2
  have hR₀ := hpart (fun n : ℕ => (n : ℝ) < A c)
    ⌈A c / Θ ^ 60⌉₊ (⌊A c⌋₊ + 1) hlo.1 hlo.2.1 hlo.2.2.1 hlo.2.2.2 hsupp₀
  have hR₁ := hpart (fun n : ℕ => B c < (n : ℝ))
    ⌈B c⌉₊ (⌊B c * Θ ^ 60⌋₊ + 1) hhi.1 hhi.2.1 hhi.2.2.1 hhi.2.2.2 hsupp₁
  rw [hR]
  calc
    _ ≤ (∑ q ∈ S, (q.divisors.card : ℝ) ^ J * ‖fullDiscrepancy R₀ q (a q)‖) +
        ∑ q ∈ S, (q.divisors.card : ℝ) ^ J * ‖fullDiscrepancy R₁ q (a q)‖ :=
      hbBoundary_weighted_discrepancy_add_le R₀ R₁ S a J
    _ ≤ K₀ * L * x / (Real.log x) ^ saving +
        K₀ * L * x / (Real.log x) ^ saving := add_le_add hR₀ hR₁
    _ = _ := by ring

open Classical in
theorem minorantHB_three_original_boundary_moduli_log_saving
    (J : ℕ) (saving : ℝ) (hSaving : 0 < saving) :
    ∃ D₀ : ℕ, 1 ≤ D₀ ∧ ∃ K X : ℝ, 0 < K ∧ Real.exp 1 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ D : ℕ, D₀ ≤ D →
      ∀ N A B t : Fin 3 → ℝ,
        (∀ c, x ^ ((23 : ℝ) / 100) ≤ N c ∧ N c ≤ x ^ ((42 : ℝ) / 100)) →
        (∀ c, N c ≤ A c ∧ A c ≤ B c ∧ B c ≤ 2 * N c) →
        (∀ c, 0 ≤ t c ∧ t c ≤ 10) →
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 ⌊x ^ ((53 : ℝ) / 100)⌋₊ →
      ∀ a : ℕ → ℕ, (∀ q ∈ S, Nat.Coprime (a q) q) →
        let Θ : ℝ := 1 + (Real.log x) ^ (-(D : ℝ))
        let U : ℝ := x ^ ((9 : ℝ) / 100)
        let R : ℕ →₀ ℂ :=
          ((∏ c : Fin 3, (MonoidAlgebra.ofCoeff
              (minorantHBUnmaskedFive (A c) (B c) U Θ (t c)) : MonoidAlgebra ℂ ℕ)).coeff -
            (∏ c : Fin 3, (MonoidAlgebra.ofCoeff
              (minorantHBClosedMangoldt (A c) (B c) (t c)) : MonoidAlgebra ℂ ℕ)).coeff).filter
                (fun n : ℕ => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x)
        (∑ q ∈ S, (q.divisors.card : ℝ) ^ J * ‖fullDiscrepancy R q (a q)‖) ≤
          K * x / (Real.log x) ^ saving := by
  obtain ⟨D₀, hD₀, K, X, hK, hX, hpair⟩ :=
    minorantHB_original_boundary_pair_moduli_log_saving J saving hSaving
  refine ⟨D₀, hD₀, 3 * K, X, by positivity, hX, ?_⟩
  intro x hx D hD N A B t hN hAB ht S hS a ha Θ U R
  let H (c : Fin 3) (b : Bool) : ℕ →₀ ℂ :=
    if b then minorantHBUnmaskedFive (A c) (B c) U Θ (t c)
    else minorantHBClosedMangoldt (A c) (B c) (t c)
  let T (c d k : Fin 3) (e f : Bool) : ℕ →₀ ℂ :=
    ((MonoidAlgebra.ofCoeff (minorantHBUnmaskedFive (A c) (B c) U Θ (t c) -
        minorantHBClosedMangoldt (A c) (B c) (t c)) *
      MonoidAlgebra.ofCoeff ((MonoidAlgebra.ofCoeff (H d e) *
        MonoidAlgebra.ofCoeff (H k f) : MonoidAlgebra ℂ ℕ).coeff) :
          MonoidAlgebra ℂ ℕ).coeff).filter
            (fun n : ℕ => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x)
  have hb (c d k : Fin 3) (e f : Bool) :
      (∑ q ∈ S, (q.divisors.card : ℝ) ^ J * ‖fullDiscrepancy (T c d k e f) q (a q)‖) ≤
        K * x / (Real.log x) ^ saving :=
    hpair x hx D hD N A B t hN hAB ht c d k e f S hS a ha
  have hR : R = T 0 1 2 true true + T 1 0 2 false true + T 2 0 1 false false := by
    simpa only [R, T, H, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false,
      MonoidAlgebra.ofCoeff_coeff] using
      minorantHB_three_original_boundary_telescope A B t U Θ
        (fun n : ℕ => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x)
  rw [hR]
  calc
    _ ≤ (∑ q ∈ S, (q.divisors.card : ℝ) ^ J *
          ‖fullDiscrepancy (T 0 1 2 true true + T 1 0 2 false true) q (a q)‖) +
        ∑ q ∈ S, (q.divisors.card : ℝ) ^ J *
          ‖fullDiscrepancy (T 2 0 1 false false) q (a q)‖ :=
      hbBoundary_weighted_discrepancy_add_le _ _ S a J
    _ ≤ ((∑ q ∈ S, (q.divisors.card : ℝ) ^ J *
          ‖fullDiscrepancy (T 0 1 2 true true) q (a q)‖) +
        ∑ q ∈ S, (q.divisors.card : ℝ) ^ J *
          ‖fullDiscrepancy (T 1 0 2 false true) q (a q)‖) +
        ∑ q ∈ S, (q.divisors.card : ℝ) ^ J *
          ‖fullDiscrepancy (T 2 0 1 false false) q (a q)‖ :=
      add_le_add (hbBoundary_weighted_discrepancy_add_le _ _ S a J) le_rfl
    _ ≤ (K * x / (Real.log x) ^ saving + K * x / (Real.log x) ^ saving) +
        K * x / (Real.log x) ^ saving :=
      add_le_add (add_le_add (hb 0 1 2 true true) (hb 1 0 2 false true)) (hb 2 0 1 false false)
    _ = _ := by ring

#print axioms hbBoundary_original_mesh_smallness
#print axioms minorantHB_original_mesh_carrier_widths
#print axioms minorantHB_original_boundary_pair_moduli_log_saving
#print axioms minorantHB_three_original_boundary_moduli_log_saving

end PrimeGap182Analytic.Harman
