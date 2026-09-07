import TypeIIIDenseKernelBound
import TypeIIIFiveScaleHomogeneity
import TypeIIILinearScale

/-!
# The new weighted Kloosterman estimate in the actual fine band

The selected target is min(x^s,Y Q/2). It is available even for small moduli;
the later exponent argument treats its two branches explicitly.
-/

open scoped BigOperators Classical ContDiff
open PrimeGap186 UniqueFactorizationMonoid Filter

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

def cappedExtractionScale (x s Y Q : ℝ) : ℝ := min (x ^ s) (Y * Q / 2)

theorem LocalFourierHypothesis.exists_fineBand_weighted_kl3_estimate
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) {D₀ p₀ : ℕ} (hlocal : LocalFourierHypothesis C₀ D₀ p₀)
    (qExp δ ε C s κ : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hC : 1 ≤ C)
    (hs : 0 < s) (hκ : 0 < κ) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x →
    ∀ M N Q : ℝ, 1 ≤ M → 1 ≤ N → 0 < Q → M * N ≤ C * x → Q ≤ C * x ^ qExp →
    ∀ Y : Set.Ici (1 : ℝ), (Y : ℝ) = x ^ δ →
    ∀ (b : ℕ+) (b₁ b₂ b₃ : ℕ), 0 < b₁ → 0 < b₂ → 0 < b₃ →
      (b : ℕ) = (radical (b₁ * b₂ * b₃) : ℕ) →
    ∀ D : Finset ℕ+,
      (∀ d ∈ D, Squarefree ((b : ℕ) * (d : ℕ)) ∧
        Nonempty (DenseDivisibilityWitness Y 1 ((b : ℕ) * (d : ℕ))) ∧
        Q * (1 - C * x ^ (-ε)) ≤ (b : ℝ) * (d : ℝ) ∧
        (b : ℝ) * (d : ℝ) ≤ Q * (1 + C * x ^ (-ε))) →
    ∀ (a₀ : ℤ) (a : ∀ d : ℕ+, (ZMod ((b : ℕ) * (d : ℕ)))ˣ),
      (∀ d ∈ D, (a d : ZMod ((b : ℕ) * (d : ℕ))) = (a₀ : ZMod ((b : ℕ) * (d : ℕ)))) →
    ∀ M₀ M₁ : ℤ, 0 < M₀ →
      (∀ m ∈ Finset.Icc M₀ M₁, |(m : ℝ)| ≤ C * M) →
    ∀ (η : ℕ → ℂ) (α : ℤ → ℂ) (E W T L : ℝ),
      0 ≤ E → 0 ≤ W → 1 ≤ T → 0 ≤ L →
      (∀ d ∈ D, ‖η ((b : ℕ) * (d : ℕ))‖ ≤ E) →
      (∀ m ∈ Finset.Icc M₀ M₁, ‖α m‖ ≤ W) →
    ∀ (ψ : ℝ → ℝ), ContDiff ℝ ∞ ψ → (∀ t : ℝ, 0 ≤ ψ t) →
      (∀ t ∈ Set.Icc (-1 : ℝ) 1, ψ t = 1) → Function.support ψ ⊆ Set.Icc (-T) T →
      (∀ t : ℝ, ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L) →
      let H : ℝ := Q ^ 3 / N
      let Hb : ℝ := x ^ (3 * ε / 2) * H / ((b₁ * b₂ * b₃ : ℕ) : ℝ)
      let S : ℝ := cappedExtractionScale x s Y Q
      selectedKloostermanL1 b (b₁ * b₂ * b₃) D a (Finset.Icc M₀ M₁) η α Hb ≤
        8 * C * E * W * Real.sqrt ((2 * T + 3) * L) *
          x ^ (κ + 3 * ε / 2) / ((b : ℝ) * Real.sqrt ((b₁ * b₂ * b₃ : ℕ) : ℝ)) *
          linearFiveScale M Q S Y H := by
  let Kheight : ℝ := 4 + 4 * |qExp| + δ + 2 * ε + s
  have hheight : 0 < Kheight := by dsimp only [Kheight]; positivity
  have htwo : 2 ≤ Kheight := by dsimp only [Kheight]; linarith only [abs_nonneg qExp, hδ, hε, hs]
  have hqheight : qExp + 1 ≤ Kheight := by
    dsimp only [Kheight]
    linarith only [le_abs_self qExp, abs_nonneg qExp, hδ, hε, hs]
  have hHheight : 3 * qExp + 3 * ε / 2 + 1 ≤ Kheight := by
    dsimp only [Kheight]
    linarith only [le_abs_self qExp, abs_nonneg qExp, hδ, hε, hs]
  have hsheight : s ≤ Kheight := by dsimp only [Kheight]; linarith only [abs_nonneg qExp, hδ, hε]
  obtain ⟨Xdense, _, hdense⟩ := hlocal.exists_dense_kernel_power_estimate hC₀ hheight
    (show 0 < 2 * κ by positivity)
  have hevent : ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ Xdense ≤ x ∧ 4 * C ^ 3 ≤ x ∧ 4 ≤ x ^ δ ∧ C * x ^ (-ε) ≤ 1 / 3 := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop Xdense,
      eventually_ge_atTop (4 * C ^ 3), (tendsto_rpow_atTop hδ).eventually_ge_atTop 4,
      ((tendsto_rpow_neg_atTop hε).const_mul C).eventually_le_const
        (by norm_num : C * 0 < (1 : ℝ) / 3)] with x hx hxd hxC hxY hband
    exact ⟨hx, hxd, hxC, hxY, hband⟩
  obtain ⟨X, hX⟩ := hevent.exists_forall_of_atTop
  refine ⟨X, by linarith only [(hX X le_rfl).1], ?_⟩
  intro x hx M N Q hM hN hQ hMN hQup Y hY b b₁ b₂ b₃ hb₁ hb₂ hb₃ hb D hD
    a₀ a ha M₀ M₁ hM₀ hMheight η α E W T L hE hW hT hL hη hα
    ψ hψ hψnonneg hψone hsupp hψbound H Hb S
  obtain ⟨hx2, hxd, hxC, hxY, hband⟩ := hX x hx
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast b.pos
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans_le hb1
  let B : ℝ := ((b₁ * b₂ * b₃ : ℕ) : ℝ)
  have hbB : (b : ℝ) ≤ B := by
    change ((b : ℕ) : ℝ) ≤ ((b₁ * b₂ * b₃ : ℕ) : ℝ)
    rw [Nat.cast_le, hb, Nat.radical_le_self_iff]
    positivity
  have hB1 : 1 ≤ B := hb1.trans hbB
  have hB0 : 0 < B := hb0.trans_le hbB
  have hH0 : 0 < H := by dsimp only [H]; positivity
  have hHb0 : 0 < Hb := by dsimp only [Hb]; positivity
  have hY0 : 0 < (Y : ℝ) := zero_lt_one.trans_le Y.property
  have hS0 : 0 < S := by
    change 0 < min (x ^ s) ((Y : ℝ) * Q / 2)
    exact lt_min (by positivity) (by positivity)
  have hT0 := zero_le_one.trans hT
  rcases D.eq_empty_or_nonempty with hDe | hDne
  · have hz : selectedKloostermanL1 b (b₁ * b₂ * b₃) D a (Finset.Icc M₀ M₁) η α Hb = 0 := by
      simp only [selectedKloostermanL1, weightedKernelL1, hDe, Finset.sum_empty, norm_zero,
        mul_zero, Finset.sum_const_zero]
    rw [hz]
    exact mul_nonneg (by positivity) (linearFiveScale_nonneg hM0.le hQ.le hS0.le hY0.le hH0.le)
  have hupper : ∀ d ∈ D, (b : ℝ) * (d : ℝ) ≤ 2 * Q := by
    intro d hd
    have hh := mul_le_mul_of_nonneg_left hband hQ.le
    exact (hD d hd).2.2.2.trans (by nlinarith only [hh, hQ.le])
  have hQhalf : (1 / 2 : ℝ) ≤ Q := by
    obtain ⟨d, hd⟩ := hDne
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast d.pos
    have hh := (one_le_mul_of_one_le_of_one_le hb1 hd1).trans (hupper d hd)
    linarith only [hh]
  let Qlo : ℝ := Q * (1 - C * x ^ (-ε))
  have hQlohalf : Q / 2 ≤ Qlo := by
    dsimp only [Qlo]
    have hh := mul_le_mul_of_nonneg_left hband hQ.le
    nlinarith only [hh, hQ.le]
  have hQlo : 0 < Qlo := (by positivity : 0 < Q / 2).trans_le hQlohalf
  have hQlohi : Qlo ≤ 2 * Q := by
    have hh : 0 ≤ C * x ^ (-ε) := by positivity
    dsimp only [Qlo]
    nlinarith only [mul_nonneg hQ.le hh, hQ.le]
  have hS : 1 ≤ S := by
    change 1 ≤ min (x ^ s) ((Y : ℝ) * Q / 2)
    refine le_min (Real.one_le_rpow hx1 hs.le) ?_
    have hh := mul_le_mul (show 4 ≤ (Y : ℝ) by simpa only [hY] using hxY) hQhalf
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by positivity : 0 ≤ (Y : ℝ))
    linarith only [hh]
  have hSrange : S ≤ (Y : ℝ) * Qlo := by
    calc
      _ ≤ (Y : ℝ) * Q / 2 := min_le_right _ _
      _ = (Y : ℝ) * (Q / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hQlohalf hY0.le
  have hCcube : C ≤ C ^ 3 := le_self_pow₀ hC three_ne_zero
  have hCsqcube : C ^ 2 ≤ C ^ 3 := pow_le_pow_right₀ hC (by norm_num)
  have htwoC : 2 * C ≤ x := by linarith only [hCcube, hxC, hC]
  have htwoCsq : 2 * C ^ 2 ≤ x := by nlinarith only [hCsqcube, hxC, sq_nonneg C]
  have hCcubeX : C ^ 3 ≤ x := by linarith only [hxC, hCcube, hC]
  have hcoeff (a p : ℝ) (ha : a ≤ x) (hp : p + 1 ≤ Kheight) : a * x ^ p ≤ x ^ Kheight := by
    calc
      _ ≤ x * x ^ p := mul_le_mul_of_nonneg_right ha (by positivity)
      _ = x ^ (p + 1) := by rw [Real.rpow_add_one hx0.ne']; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 hp
  have hQheight : (2 * Q) / (b : ℝ) ≤ x ^ Kheight := by
    calc
      _ ≤ 2 * Q := div_le_self (by positivity) hb1
      _ ≤ (2 * C) * x ^ qExp := by nlinarith only [hQup]
      _ ≤ _ := hcoeff _ _ htwoC hqheight
  have hSheight : S ≤ x ^ Kheight :=
    (min_le_left _ _).trans (Real.rpow_le_rpow_of_exponent_le hx1 hsheight)
  have hHbheight : Hb ≤ x ^ Kheight := by
    have hQpow : Q ^ 3 ≤ C ^ 3 * x ^ (3 * qExp) := by
      have hh := pow_le_pow_left₀ hQ.le hQup 3
      rw [mul_pow, ← Real.rpow_mul_natCast hx0.le] at hh
      norm_num only [Nat.cast_ofNat] at hh
      simpa only [mul_comm qExp (3 : ℝ)] using hh
    calc
      Hb ≤ x ^ (3 * ε / 2) * H := div_le_self (by positivity) hB1
      _ ≤ x ^ (3 * ε / 2) * Q ^ 3 :=
        mul_le_mul_of_nonneg_left (div_le_self (by positivity) hN) (by positivity)
      _ ≤ x ^ (3 * ε / 2) * (C ^ 3 * x ^ (3 * qExp)) :=
        mul_le_mul_of_nonneg_left hQpow (by positivity)
      _ = C ^ 3 * x ^ (3 * qExp + 3 * ε / 2) := by rw [Real.rpow_add hx0]; ring
      _ ≤ _ := hcoeff _ _ hCcubeX hHheight
  let Nrow : ℕ := ⌈C * M⌉₊
  have hNrow : 0 < Nrow := Nat.ceil_pos.mpr (mul_pos hC0 hM0)
  have hNrowM : (Nrow : ℝ) ≤ (2 * C) * M := by
    have hCM := one_le_mul_of_one_le_of_one_le hC hM
    have hh := (Nat.ceil_lt_add_one (mul_nonneg hC0.le hM0.le)).le
    dsimp only [Nrow]
    linarith only [hh, hCM]
  have hMupper : M ≤ C * x := (le_mul_of_one_le_right hM0.le hN).trans hMN
  have hNrowheight : (Nrow : ℝ) ≤ x ^ Kheight := by
    calc
      _ ≤ (2 * C) * M := hNrowM
      _ ≤ (2 * C ^ 2) * x ^ (1 : ℝ) := by
        rw [Real.rpow_one]
        have hh := mul_le_mul_of_nonneg_left hMupper (by positivity : 0 ≤ 2 * C)
        nlinarith only [hh]
      _ ≤ _ := hcoeff _ _ htwoCsq (by simpa only [one_add_one_eq_two] using htwo)
  have hI : Finset.Icc M₀ M₁ ⊆ Finset.Ico 1 (1 + (Nrow : ℤ)) := by
    intro m hm
    have hmpos := hM₀.trans_le (Finset.mem_Icc.mp hm).1
    have hmreal : (m : ℝ) ≤ (Nrow : ℝ) :=
      (le_abs_self _).trans ((hMheight m hm).trans (Nat.le_ceil _))
    have hmrow : m ≤ (Nrow : ℤ) := by exact_mod_cast hmreal
    exact Finset.mem_Ico.mpr ⟨hmpos, by omega⟩
  have hquad := hdense x hxd b b₁ b₂ b₃ hb₁ hb₂ hb₃ hb Y Qlo (2 * Q) S hQlo hQlohi
    hS hSrange hQheight hSheight D
    (fun d hd => ⟨(hD d hd).1, (hD d hd).2.1, (hD d hd).2.2.1, hupper d hd⟩)
    Nrow hNrow hNrowheight a₀ a ha (Finset.Icc M₀ M₁) hI η α E W T L Hb
    hE hW hT hL hHb0 hHbheight hη hα ψ hψ hψnonneg hψone hsupp hψbound
  have hscale : fiveScale Nrow ((2 * Q) / (b : ℝ)) S ((b : ℝ) * Y) Hb ≤
      (32 * C ^ 2) * fiveScale M (Q / (b : ℝ)) S ((b : ℝ) * Y) Hb := by
    have hm := fiveScale_mono_NQ (Nat.cast_nonneg Nrow) hNrowM
      (by positivity : 0 ≤ (2 * Q) / (b : ℝ))
      (le_of_eq (by ring : (2 * Q) / (b : ℝ) = 2 * (Q / (b : ℝ)))) hS0.le
      (by positivity : 0 ≤ (b : ℝ) * (Y : ℝ)) hHb0.le
    have hh := fiveScale_dilate_NQ hM0.le (by positivity : 0 ≤ Q / (b : ℝ)) hS0.le
      (by positivity : 0 ≤ (b : ℝ) * (Y : ℝ)) hHb0.le (by linarith : 1 ≤ 2 * C)
      (by norm_num : (1 : ℝ) ≤ 2)
    apply (hm.trans hh).trans_eq
    ring
  have hquad' : selectedKloostermanL1 b (b₁ * b₂ * b₃) D a (Finset.Icc M₀ M₁) η α Hb ^ 2 ≤
      (32 * C ^ 2 * (T * L)) * (E * W) ^ 2 * x ^ (2 * κ) * Hb *
        fiveScale M (Q / (b : ℝ)) S ((b : ℝ) * Y) Hb := by
    apply hquad.trans
    have hh := mul_le_mul_of_nonneg_left hscale
      (by positivity : 0 ≤ (T * L) * (E * W) ^ 2 * x ^ (2 * κ) * Hb)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hh
  have hnormalized := kernelSquare_normalize hx1 hε.le hM0 hQ hS0 hY0 hH0 hb1 hbB rfl
    (by positivity : 0 ≤ 32 * C ^ 2 * (T * L)) hE hW hquad'
  have henv : 0 ≤ (2 * T + 3) * L := by positivity
  have hTL : T * L ≤ (2 * T + 3) * L := by nlinarith only [mul_nonneg hT0 hL, hL]
  have hA : 32 * C ^ 2 * (T * L) ≤ (8 * C * Real.sqrt ((2 * T + 3) * L)) ^ 2 := by
    have hh := mul_le_mul (show 32 * C ^ 2 ≤ 64 * C ^ 2 by nlinarith [sq_nonneg C]) hTL
      (mul_nonneg hT0 hL) (by positivity)
    simpa only [mul_pow, Real.sq_sqrt henv, show (8 : ℝ) ^ 2 = 64 by norm_num] using hh
  have hsqrt := Real.sqrt_le_sqrt hA
  rw [Real.sqrt_sq (by positivity : 0 ≤ 8 * C * Real.sqrt ((2 * T + 3) * L))] at hsqrt
  apply hnormalized.trans
  have hlin := linearFiveScale_nonneg hM0.le hQ.le hS0.le hY0.le hH0.le
  calc
    _ ≤ (8 * C * Real.sqrt ((2 * T + 3) * L)) * E * W *
        x ^ ((2 * κ) / 2 + 3 * ε / 2) / ((b : ℝ) * Real.sqrt B) * linearFiveScale M Q S Y H := by
      gcongr
    _ = _ := by rw [show (2 * κ) / 2 + 3 * ε / 2 = κ + 3 * ε / 2 by ring]; ring

#print axioms LocalFourierHypothesis.exists_fineBand_weighted_kl3_estimate

end

end PrimeGap182.TypeIII
