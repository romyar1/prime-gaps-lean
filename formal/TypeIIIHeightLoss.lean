import TypeIIIFiveScaleBound

/-! Uniform absorption of the explicit logarithmic and arithmetic losses. -/

open scoped BigOperators Classical
open PrimeGap186 Filter

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

theorem exists_log_power_subpower (C : ℝ) (hC : 0 ≤ C) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, 2 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      1 ≤ Real.log x ∧ C * (Real.log x) ^ n ≤ x ^ ε := by
  have ht : ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ 1 ≤ Real.log x ∧ C * (Real.log x) ^ n ≤ x ^ ε := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
      ((isLittleO_log_rpow_rpow_atTop (n : ℝ) hε).const_mul_left C).eventuallyLE]
      with x hx hlog hb
    refine ⟨hx, hlog, ?_⟩
    simpa only [Real.rpow_natCast, Real.norm_of_nonneg
      (mul_nonneg hC (pow_nonneg (zero_le_one.trans hlog) n)),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) ε)] using hb
  obtain ⟨X, hX⟩ := ht.exists_forall_of_atTop
  exact ⟨X, (hX X le_rfl).1, fun x hx => (hX x hx).2⟩

theorem exists_firstMomentLogBound_rpow {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) :
    ∃ X : ℝ, 2 ≤ X ∧ ∀ x : ℝ, X ≤ x → ∀ H S : ℝ,
      0 < H → H ≤ x ^ K → 1 ≤ S → S ≤ x ^ K →
      firstMomentLogBound H (2 * S) ≤ x ^ ε * H := by
  obtain ⟨X, hX, hb⟩ := exists_log_power_subpower (2 * (K + 2) ^ 16) (by positivity) 16 hε
  refine ⟨X, hX, ?_⟩
  intro x hx H S hH hHX hS hSX
  obtain ⟨hlogx, hsmall⟩ := hb x hx
  have hx2 : 2 ≤ x := hX.trans hx
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hHmax : max 1 H ≤ x ^ K := max_le (Real.one_le_rpow hx1 hK.le) hHX
  have hlogH := Real.log_le_log (zero_lt_one.trans_le (le_max_left (1 : ℝ) H)) hHmax
  rw [Real.log_rpow hx0] at hlogH
  have h2S : 2 * S ≤ x ^ (K + 1) := by
    rw [Real.rpow_add_one hx0.ne']
    simpa only [mul_comm] using mul_le_mul hx2 hSX (zero_le_one.trans hS) hx0.le
  have hlogS := Real.log_le_log (by linarith : 0 < 2 * S) h2S
  rw [Real.log_rpow hx0] at hlogS
  have hA : 1 + Real.log (max 1 H) ≤ (K + 2) * Real.log x := by
    nlinarith only [hlogH, hlogx]
  have hB : 1 + Real.log (2 * S) ≤ (K + 2) * Real.log x := by
    nlinarith only [hlogS, hlogx]
  have hA₀ : 0 ≤ 1 + Real.log (max 1 H) :=
    add_nonneg zero_le_one (Real.log_nonneg (le_max_left _ _))
  have hB₀ : 0 ≤ 1 + Real.log (2 * S) :=
    add_nonneg zero_le_one (Real.log_nonneg (by linarith : 1 ≤ 2 * S))
  have hprod := mul_le_mul (pow_le_pow_left₀ hA₀ hA 15) hB hB₀ (by positivity)
  have hbound := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 2 * H)
  have hlast := mul_le_mul_of_nonneg_right hsmall hH.le
  unfold firstMomentLogBound
  calc
    _ ≤ (2 * H) * (((K + 2) * Real.log x) ^ 15 * ((K + 2) * Real.log x)) := by
      simpa only [mul_assoc] using hbound
    _ = (2 * (K + 2) ^ 16 * (Real.log x) ^ 16) * H := by ring
    _ ≤ _ := hlast

theorem selectionSubpower_le_rpow {x K N Q ε : ℝ}
    (hx : 2 ≤ x) (hK : 0 ≤ K) (hN : 0 ≤ N) (hQ : 0 ≤ Q)
    (hNX : N ≤ x ^ K) (hQX : Q ≤ x ^ K) (hε : 0 ≤ ε) :
    selectionSubpower N Q ε ≤ x ^ ((5 * K + 10) * ε) := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hXone : 1 ≤ x ^ K := Real.one_le_rpow hx1 hK
  have hXzero : 0 ≤ x ^ K := by positivity
  have hthree : (5 : ℝ) ≤ x ^ 3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 3
    norm_num at hh
    linarith
  have hseven : (65 : ℝ) ≤ x ^ 7 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 7
    norm_num at hh
    linarith
  have hA : 1 + 4 * Q ≤ x ^ (K + 3) := by
    calc
      _ ≤ 5 * x ^ K := by linarith only [hQX, hXone]
      _ ≤ x ^ 3 * x ^ K := mul_le_mul_of_nonneg_right hthree hXzero
      _ = _ := by rw [Real.rpow_add hx0, Real.rpow_ofNat]; ring
  have hB : 1 + N * (4 * Q) ^ 3 ≤ x ^ (4 * K + 7) := by
    have hfour : 1 ≤ (x ^ K) ^ 4 := one_le_pow₀ hXone
    calc
      _ ≤ 1 + x ^ K * (4 * x ^ K) ^ 3 := by gcongr
      _ ≤ 65 * (x ^ K) ^ 4 := by nlinarith only [hfour]
      _ ≤ x ^ 7 * (x ^ K) ^ 4 := mul_le_mul_of_nonneg_right hseven (by positivity)
      _ = _ := by
        rw [← Real.rpow_mul_natCast hx0.le, Real.rpow_add hx0, Real.rpow_ofNat]
        norm_num only [Nat.cast_ofNat]
        rw [mul_comm K (4 : ℝ)]
        ring
  have hpow := mul_le_mul (Real.rpow_le_rpow (by positivity) hA hε)
    (Real.rpow_le_rpow (by positivity) hB hε) (by positivity) (by positivity)
  apply hpow.trans_eq
  rw [← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
  congr 1
  ring

theorem exists_dyadicFactorCells_sq_rpow {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) :
    ∃ X : ℝ, 2 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      ∀ (D : Finset ℕ+) (ρ σ : ℕ+ → ℕ+), (∀ d ∈ D, d = ρ d * σ d) →
      (∀ d ∈ D, (d : ℝ) ≤ x ^ K) →
      ((dyadicFactorCells D ρ σ).card : ℝ) ^ 2 ≤ x ^ ε := by
  let A : ℝ := (K + 2) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨X, hX, hb⟩ := exists_log_power_subpower (A ^ 4) (by positivity) 4 hε
  refine ⟨X, hX, ?_⟩
  intro x hx D ρ σ hfactor hD
  obtain ⟨_, hsmall⟩ := hb x hx
  have hx2 : 2 ≤ x := hX.trans hx
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hXone : 1 ≤ x ^ K := Real.one_le_rpow hx1 hK.le
  let U : ℕ := ⌈x ^ K⌉₊
  have hU : 0 < U := Nat.ceil_pos.mpr (by positivity)
  have hUbound : (U : ℝ) ≤ 2 * x ^ K := by
    have hh := (Nat.ceil_lt_add_one (by positivity : 0 ≤ x ^ K)).le
    dsimp only [U]
    linarith only [hh, hXone]
  have hρ : ∀ d ∈ D, (ρ d : ℕ) ≤ U := by
    intro d hd
    have hh : (ρ d : ℕ) ≤ (d : ℕ) := by
      calc
        _ ≤ (ρ d : ℕ) * (σ d : ℕ) := Nat.le_mul_of_pos_right _ (σ d).pos
        _ = _ := congrArg PNat.val (hfactor d hd).symm
    exact Nat.cast_le.mp ((Nat.cast_le.mpr hh).trans ((hD d hd).trans (Nat.le_ceil _)))
  have hσ : ∀ d ∈ D, (σ d : ℕ) ≤ U := by
    intro d hd
    have hh : (σ d : ℕ) ≤ (d : ℕ) := by
      calc
        _ ≤ (ρ d : ℕ) * (σ d : ℕ) := Nat.le_mul_of_pos_left _ (ρ d).pos
        _ = _ := congrArg PNat.val (hfactor d hd).symm
    exact Nat.cast_le.mp ((Nat.cast_le.mpr hh).trans ((hD d hd).trans (Nat.le_ceil _)))
  have hcard : ((dyadicFactorCells D ρ σ).card : ℝ) ≤ ((Nat.log 2 U + 1 : ℕ) : ℝ) ^ 2 := by
    have hh := dyadicFactorCells_card_le D ρ σ U U hρ hσ
    simpa only [pow_two, Nat.cast_mul] using (Nat.cast_le.mpr hh :
      ((dyadicFactorCells D ρ σ).card : ℝ) ≤ ((Nat.log 2 U + 1) * (Nat.log 2 U + 1) : ℕ))
  have hcount := card_dyadicExponentRange_le_log hU
  simp only [dyadicExponentRange, Finset.card_range] at hcount
  have hlogU : Real.log (2 * (U : ℝ)) ≤ (K + 2) * Real.log x := by
    have hh := Real.log_le_log (by positivity : 0 < 2 * (U : ℝ))
      (mul_le_mul_of_nonneg_left hUbound (by norm_num : (0 : ℝ) ≤ 2))
    have hxlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx2
    have hlogfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      simpa only [Real.log_pow, Nat.cast_ofNat] using congrArg Real.log (by norm_num : (4 : ℝ) = 2 ^ 2)
    have hright : Real.log (4 * x ^ K) = 2 * Real.log 2 + K * Real.log x := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0, hlogfour]
    rw [show 2 * (2 * x ^ K) = 4 * x ^ K by ring, hright] at hh
    nlinarith only [hh, hxlog]
  have hcount' : ((Nat.log 2 U + 1 : ℕ) : ℝ) ≤ A * Real.log x := by
    apply hcount.trans
    apply (div_le_div_of_nonneg_right hlogU hlog2.le).trans_eq
    dsimp only [A]
    ring
  calc
    _ ≤ (((Nat.log 2 U + 1 : ℕ) : ℝ) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
    _ = ((Nat.log 2 U + 1 : ℕ) : ℝ) ^ 4 := by ring
    _ ≤ (A * Real.log x) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount' 4
    _ = A ^ 4 * (Real.log x) ^ 4 := mul_pow _ _ _
    _ ≤ _ := hsmall

#print axioms exists_firstMomentLogBound_rpow
#print axioms selectionSubpower_le_rpow
#print axioms exists_dyadicFactorCells_sq_rpow

end

end PrimeGap182.TypeIII
