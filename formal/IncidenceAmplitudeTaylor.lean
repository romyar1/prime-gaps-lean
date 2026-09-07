import IncidenceFrequencyCoefficients

/-!
# Taylor separation of the actual two-factor source amplitude

This proof adapts the derivative and Taylor estimates in the unchanged
PrimeGaps186 baseline, `sourcePhi_fourfold_common_cutoff_taylor` (lines
82643--82929), to the two factors before the positive square is expanded.
It proves the actual row-independent coefficient arrays and the actual
remainder. No positivity or rank-one property of four-factor pair
coefficients is assumed.
-/

noncomputable section
namespace PrimeGap182Audit
open PrimeGap186
open scoped BigOperators ContDiff

set_option maxHeartbeats 1000000 in
theorem incidenceSourcePhi_twofold_taylor (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ι : Type*) [DecidableEq ι] (I : Finset ι)
        (c T M H L d₀ δ D : ℝ)
        (_ : 0 < c) (_ : c ≤ T) (_ : 0 < M)
        (_ : 0 ≤ H) (_ : 0 ≤ L) (_ : 0 < d₀) (_ : 0 < δ) (_ : 0 ≤ D)
        (ψ : ℝ → ℝ) (_ : Function.support ψ ⊆ Set.Icc c T)
        (_ : ∀ t : ℝ, |ψ t| ≤ L)
        (r₁ q₀ u₁ v₁ v₂ q₂ : ℕ)
        (_ : 0 < r₁ * q₀ * u₁ * v₁ * q₂ ∧
          0 < r₁ * q₀ * u₁ * v₂ * q₂)
        (h : ι → Fin 2 → ℤ) (_ : ∀ a ∈ I, ∀ i, |(h a i : ℝ)| ≤ H),
      let R₁ : ℕ := r₁ * q₀ * u₁ * v₁ * q₂
      let R₂ : ℕ := r₁ * q₀ * u₁ * v₂ * q₂
      let F : ι → ℝ → ℂ := fun a d =>
        sourcePhiRealFactor ψ M R₁ (h a 0) d *
          star (sourcePhiRealFactor ψ M R₂ (h a 1) d)
      let S : ℝ := δ / d₀ *
        (1 + T * M * H / d₀ * ((R₁ : ℝ)⁻¹ + (R₂ : ℝ)⁻¹))
      let coeff : ι → ℕ → ℂ := fun a j =>
        (δ ^ j / (j.factorial : ℝ)) • iteratedDeriv j (F a) d₀
      (∀ a ∈ I, ∀ j ≤ J, ‖coeff a j‖ ≤ C * (T * L) ^ 2 * S ^ j) ∧
      ∀ (χ : ℝ → ℝ) (_ : Function.support χ ⊆ Set.Icc 0 (D * δ))
        (A : ℝ → ι → ℂ) (d : ℝ),
        ‖(χ (d - d₀) : ℂ) * (∑ a ∈ I, A d a * F a d) -
          ∑ j ∈ Finset.range (J + 1),
            ((χ (d - d₀) * ((d - d₀) / δ) ^ j : ℝ) : ℂ) *
              (∑ a ∈ I, A d a * coeff a j)‖ ≤
          |χ (d - d₀)| * C * (T * L) ^ 2 * (D * S) ^ (J + 1) *
            (∑ a ∈ I, ‖A d a‖) := by
  let N : ℕ := J + 1
  let K : ℝ := (N.factorial : ℝ) ^ (N + 1) * (1 + 2 * Real.pi) ^ N
  let C : ℝ := 2 ^ N * K ^ 2
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hCpos : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hCpos, ?_⟩
  intro ι _ I c T M H L d₀ δ D hc hcT hM hH hL hd₀ hδ hD ψ hsupport
    hbound r₁ q₀ u₁ v₁ v₂ q₂ hperiods h hh R₁ R₂ F S coeff
  have hT : 0 < T := hc.trans_le hcT
  have hTL : 0 ≤ T * L := mul_nonneg hT.le hL
  have hTMH : 0 ≤ T * M * H := by positivity
  have hR₁ : 0 < (R₁ : ℝ) := Nat.cast_pos.mpr hperiods.1
  have hR₂ : 0 < (R₂ : ℝ) := Nat.cast_pos.mpr hperiods.2
  let G : ℝ := 1 + T * M * H / d₀ * ((R₁ : ℝ)⁻¹ + (R₂ : ℝ)⁻¹)
  let Z : ℝ := G / d₀
  have hGpos : 0 < G := by dsimp [G]; positivity
  have hZpos : 0 < Z := div_pos hGpos hd₀
  have hS : S = δ * Z := by dsimp [S, Z, G]; ring
  have hfac (j : ℕ) : (1 : ℝ) ≤ (j.factorial : ℝ) :=
    Nat.one_le_cast.mpr (Nat.factorial_pos j)
  have hKbound (j : ℕ) (hj : j ≤ N) :
      (j.factorial : ℝ) ^ (j + 1) * (1 + 2 * Real.pi) ^ j ≤ K := by
    have hjN : (j.factorial : ℝ) ≤ (N.factorial : ℝ) :=
      Nat.cast_le.mpr (Nat.factorial_le hj)
    calc
      _ ≤ (N.factorial : ℝ) ^ (j + 1) * (1 + 2 * Real.pi) ^ j := by gcongr
      _ ≤ (N.factorial : ℝ) ^ (N + 1) * (1 + 2 * Real.pi) ^ N :=
        mul_le_mul (pow_le_pow_right₀ (hfac N) (Nat.add_le_add_right hj 1))
          (pow_le_pow_right₀ (by linarith [Real.pi_pos]) hj) (by positivity) (by positivity)
  have hmul (f g : ℝ → ℂ) (U V P Q x : ℝ)
      (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
      (hbf : ∀ i ≤ N, ‖iteratedDeriv i f x‖ ≤ U * P ^ i)
      (hbg : ∀ i ≤ N, ‖iteratedDeriv i g x‖ ≤ V * Q ^ i) :
      ∀ j ≤ N, ‖iteratedDeriv j (fun y => f y * g y) x‖ ≤
        U * V * (P + Q) ^ j := by
    intro j hj
    rw [iteratedDeriv_fun_mul (n := j) (hf.of_le (by simp)) (hg.of_le (by simp))]
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * (U * P ^ i) * (V * Q ^ (j - i)) := by
        apply norm_sum_le_of_le
        intro i hi
        have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        exact norm_mul_le_of_le
          (norm_mul_le_of_le (le_of_eq (Complex.norm_natCast (j.choose i)))
            (hbf i (hij.trans hj)))
          (hbg (j - i) ((Nat.sub_le j i).trans hj))
      _ = U * V * (P + Q) ^ j := by
        rw [add_pow, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hstar (f : ℝ → ℂ) (x : ℝ) (j : ℕ) :
      ‖iteratedDeriv j (fun y => star (f y)) x‖ = ‖iteratedDeriv j f x‖ := by
    simpa only [Function.comp_def, Complex.conjLIE_apply, Complex.star_def,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
      Complex.conjLIE.norm_iteratedFDeriv_comp_left f x j
  have hphase (R : ℕ) (hR : 0 < R)
      (hRi : (R : ℝ)⁻¹ ≤ (R₁ : ℝ)⁻¹ + (R₂ : ℝ)⁻¹)
      (k : ℤ) (hk : |(k : ℝ)| ≤ H) :
      ContDiffOn ℝ ∞ (sourcePhiRealFactor ψ M R k) (Set.Ioi 0) ∧
      ∀ x : ℝ, d₀ ≤ x → ∀ j ≤ N,
        ‖iteratedDeriv j (sourcePhiRealFactor ψ M R k) x‖ ≤ T * L * K * Z ^ j := by
    refine ⟨(sourcePhiRealFactor_iteratedDeriv_bound 0 c T M H L hc hcT hM hH hL
      ψ hsupport hbound R hR k hk).1, ?_⟩
    intro x hx j hj
    have hxpos : 0 < x := hd₀.trans_le hx
    have hRpos : 0 < (R : ℝ) := Nat.cast_pos.mpr hR
    have hratio : 1 + T * M * H / (x * (R : ℝ)) ≤ G := by
      have hden : T * M * H / (x * (R : ℝ)) ≤
          T * M * H / d₀ * ((R₁ : ℝ)⁻¹ + (R₂ : ℝ)⁻¹) := by
        calc
          _ = T * M * H * x⁻¹ * (R : ℝ)⁻¹ := by
            simp only [div_eq_mul_inv, mul_inv_rev]
            ring
          _ ≤ T * M * H * d₀⁻¹ * (R : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (inv_anti₀ hd₀ hx) hTMH)
              (inv_nonneg.mpr hRpos.le)
          _ ≤ T * M * H * d₀⁻¹ * ((R₁ : ℝ)⁻¹ + (R₂ : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left hRi (mul_nonneg hTMH (inv_nonneg.mpr hd₀.le))
          _ = _ := by rw [div_eq_mul_inv]
      exact add_le_add_right hden 1
    have hraw := (sourcePhiRealFactor_iteratedDeriv_bound j c T M H L hc hcT hM
      hH hL ψ hsupport hbound R hR k hk).2 x hxpos
    have hscaled :
        d₀ ^ j * ‖iteratedDeriv j (sourcePhiRealFactor ψ M R k) x‖ ≤
          T * L * K * G ^ j := by
      calc
        _ ≤ x ^ j * ‖iteratedDeriv j (sourcePhiRealFactor ψ M R k) x‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd₀.le hx j) (norm_nonneg _)
        _ ≤ T * L * (j.factorial : ℝ) ^ (j + 1) * (1 + 2 * Real.pi) ^ j *
            (1 + T * M * H / (x * (R : ℝ))) ^ j := hraw
        _ = T * L * ((j.factorial : ℝ) ^ (j + 1) * (1 + 2 * Real.pi) ^ j) *
            (1 + T * M * H / (x * (R : ℝ))) ^ j := by ring
        _ ≤ T * L * K * G ^ j :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hKbound j hj) hTL)
            (pow_le_pow_left₀ (by positivity) hratio j) (by positivity) (by positivity)
    dsimp only [Z]
    rw [div_pow, ← mul_div_assoc]
    exact (le_div_iff₀ (pow_pos hd₀ j)).2 (by simpa [mul_comm] using hscaled)
  have hF :
      ∀ a ∈ I, ContDiffOn ℝ ∞ (F a) (Set.Ioi 0) ∧
        ∀ x : ℝ, d₀ ≤ x → ∀ j ≤ N,
          ‖iteratedDeriv j (F a) x‖ ≤ C * (T * L) ^ 2 * Z ^ j := by
    intro a ha
    let f₀ : ℝ → ℂ := sourcePhiRealFactor ψ M R₁ (h a 0)
    let f₁ : ℝ → ℂ := sourcePhiRealFactor ψ M R₂ (h a 1)
    rcases hphase R₁ hperiods.1 (le_add_of_nonneg_right (inv_nonneg.mpr hR₂.le))
      (h a 0) (hh a ha 0) with ⟨hf₀, hb₀⟩
    rcases hphase R₂ hperiods.2 (le_add_of_nonneg_left (inv_nonneg.mpr hR₁.le))
      (h a 1) (hh a ha 1) with ⟨hf₁, hb₁⟩
    have hs₁ : ContDiffOn ℝ ∞ (fun x => star (f₁ x)) (Set.Ioi 0) := by
      simpa only [Function.comp_def, Complex.conjCLE_apply, Complex.star_def] using
        Complex.conjCLE.contDiff.comp_contDiffOn hf₁
    refine ⟨hf₀.mul hs₁, ?_⟩
    intro x hx j hj
    have hxpos : 0 < x := hd₀.trans_le hx
    have hat₀ := hf₀.contDiffAt (isOpen_Ioi.mem_nhds hxpos)
    have hat₁ := hs₁.contDiffAt (isOpen_Ioi.mem_nhds hxpos)
    have hsbound₁ : ∀ i ≤ N,
        ‖iteratedDeriv i (fun y => star (f₁ y)) x‖ ≤ T * L * K * Z ^ i := by
      intro i hi
      rw [hstar]
      exact hb₁ x hx i hi
    have htwo := hmul f₀ (fun y => star (f₁ y)) (T * L * K) (T * L * K) Z Z x
      hat₀ hat₁ (hb₀ x hx) hsbound₁ j hj
    calc
      _ ≤ (T * L * K) * (T * L * K) * (Z + Z) ^ j := htwo
      _ = (T * L) ^ 2 * K ^ 2 * (2 : ℝ) ^ j * Z ^ j := by
        rw [show Z + Z = 2 * Z by ring, mul_pow]
        ring
      _ ≤ (T * L) ^ 2 * K ^ 2 * (2 : ℝ) ^ N * Z ^ j := by
        have htwopow : (2 : ℝ) ^ j ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hj
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htwopow (by positivity)) (by positivity)
      _ = C * (T * L) ^ 2 * Z ^ j := by dsimp [C]; ring
  refine ⟨?_, ?_⟩
  · intro a ha j hj
    have hb := (hF a ha).2 d₀ le_rfl j (hj.trans (Nat.le_succ J))
    dsimp only [coeff]
    rw [norm_smul_of_nonneg (by positivity)]
    calc
      _ ≤ δ ^ j * (C * (T * L) ^ 2 * Z ^ j) :=
        mul_le_mul (div_le_self (pow_nonneg hδ.le j) (hfac j)) hb
          (norm_nonneg _) (pow_nonneg hδ.le j)
      _ = C * (T * L) ^ 2 * S ^ j := by
        rw [hS, mul_pow δ Z j]
        exact mul_left_comm (δ ^ j) (C * (T * L) ^ 2) (Z ^ j)
  · intro χ hχ A d
    by_cases hχd : χ (d - d₀) = 0
    · simp [hχd]
    have hsχ : d - d₀ ∈ Set.Icc 0 (D * δ) := hχ hχd
    have hstep : 0 ≤ d - d₀ := hsχ.1
    let b : ℝ := d₀ + (D + 1) * δ
    have hb : d₀ < b := by
      dsimp [b]
      exact lt_add_of_pos_right d₀ (mul_pos (by linarith) hδ)
    have hd : d ∈ Set.Icc d₀ b := by
      refine ⟨sub_nonneg.mp hsχ.1, ?_⟩
      dsimp [b]
      nlinarith [hsχ.2]
    have hwithin (a : ι) (ha : a ∈ I) (j : ℕ) (y : ℝ)
        (hy : y ∈ Set.Icc d₀ b) :
        iteratedDerivWithin j (F a) (Set.Icc d₀ b) y = iteratedDeriv j (F a) y :=
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hb)
        (((hF a ha).1.contDiffAt
          (isOpen_Ioi.mem_nhds (hd₀.trans_le hy.1))).of_le (by simp)) hy
    have htaylor (a : ι) (ha : a ∈ I) :
        ‖F a d - taylorWithinEval (F a) J (Set.Icc d₀ b) d₀ d‖ ≤
          C * (T * L) ^ 2 * (D * S) ^ (J + 1) := by
      have hf : ContDiffOn ℝ (J + 1) (F a) (Set.Icc d₀ b) :=
        ((hF a ha).1.mono (fun y hy => hd₀.trans_le hy.1)).of_le (by simp)
      have hderiv : ∀ y ∈ Set.Icc d₀ b,
          ‖iteratedDerivWithin (J + 1) (F a) (Set.Icc d₀ b) y‖ ≤
            C * (T * L) ^ 2 * Z ^ (J + 1) := by
        intro y hy
        rw [hwithin a ha (J + 1) y hy]
        exact (hF a ha).2 y hy.1 (J + 1) le_rfl
      have hraw := taylor_mean_remainder_bound hb.le hf hd hderiv
      calc
        _ ≤ C * (T * L) ^ 2 * Z ^ (J + 1) * (d - d₀) ^ (J + 1) /
            (J.factorial : ℝ) := hraw
        _ ≤ C * (T * L) ^ 2 * Z ^ (J + 1) * (d - d₀) ^ (J + 1) :=
          div_le_self (by positivity) (hfac J)
        _ ≤ C * (T * L) ^ 2 * Z ^ (J + 1) * (D * δ) ^ (J + 1) := by
          gcongr
          exact hsχ.2
        _ = C * (T * L) ^ 2 * (D * S) ^ (J + 1) := by
          rw [hS]
          simp only [mul_pow]
          ring
    have hpoly (a : ι) (ha : a ∈ I) :
        taylorWithinEval (F a) J (Set.Icc d₀ b) d₀ d =
          ∑ j ∈ Finset.range (J + 1), (((d - d₀) / δ) ^ j : ℝ) • coeff a j := by
      rw [taylor_within_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [hwithin a ha j d₀ ⟨le_rfl, hb.le⟩]
      dsimp only [coeff]
      rw [smul_smul]
      congr 1
      rw [div_pow, div_mul_div_cancel₀ (pow_ne_zero j hδ.ne'),
        div_eq_mul_inv, mul_comm]
    have hsum :
        (∑ j ∈ Finset.range (J + 1),
          ((χ (d - d₀) * ((d - d₀) / δ) ^ j : ℝ) : ℂ) *
            (∑ a ∈ I, A d a * coeff a j)) =
          (χ (d - d₀) : ℂ) *
            ∑ a ∈ I, A d a * taylorWithinEval (F a) J (Set.Icc d₀ b) d₀ d := by
      simp_rw [Complex.ofReal_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [hpoly a ha]
      simp only [Finset.mul_sum, Complex.real_smul, mul_assoc, mul_left_comm]
    rw [hsum, ← mul_sub, ← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |χ (d - d₀)| * ∑ a ∈ I, ‖A d a‖ *
          (C * (T * L) ^ 2 * (D * S) ^ (J + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply norm_sum_le_of_le
        intro a ha
        exact norm_mul_le_of_le le_rfl (htaylor a ha)
      _ = |χ (d - d₀)| * C * (T * L) ^ 2 * (D * S) ^ (J + 1) *
          (∑ a ∈ I, ‖A d a‖) := by
        rw [← Finset.sum_mul]
        ring

#print axioms incidenceSourcePhi_twofold_taylor

end PrimeGap182Audit
