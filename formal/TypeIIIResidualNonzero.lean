import TypeIIIResidualInterval

/-!
# The actual nonzero-frequency estimate on gcd-repartitioned intervals

The interval is exactly R ≤ gu ≤ 2R, expressed through its proved start and length.
All completion-width comparisons and the possibly empty interval are handled internally.
-/

open scoped BigOperators Classical FourierTransform ContDiff

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

attribute [local instance] familyProductNeZero

def residualProfileNonzeroMass (w : ℕ) [NeZero w] (a A B : ℤ) (M R g : ℕ)
    (α : ℕ → ℕ → IntegerIntervalIndex A M → ℂ)
    (β : ℕ → ℕ → IntegerIntervalIndex B M → ℂ) (T H t₀ : ℝ) (ψ : ℝ → ℂ) : ℝ :=
  sharedProfileNonzeroMass w a A B M (residualLength R g)
    (residualStart R g) (residualStart R g)
    (fun x y => α ((residualStart R g : ℕ) + x) ((residualStart R g : ℕ) + y))
    (fun x y => β ((residualStart R g : ℕ) + x) ((residualStart R g : ℕ) + y)) T H t₀ ψ

theorem LocalFourierHypothesis.exists_residual_nonzero_estimate
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {ι : Type} [Fintype ι] (q : ι → ℕ) [∀ i, Fact (q i).Prime],
      Pairwise (fun i j => (q i).Coprime (q j)) →
      ∀ (a A B : ℤ), IsUnit (a : ZMod (∏ i, q i)) →
      ∀ (M R g : ℕ), 0 < R → 0 < g → ∀ (L₁ L₂ T L H t₀ : ℝ),
      0 ≤ L₁ → 0 ≤ L₂ → 0 ≤ T → 0 ≤ L → 0 < H →
      ∀ (ψ : ℝ → ℂ), ContDiff ℝ ∞ ψ →
      Function.support ψ ⊆ Set.Icc (-T) T →
      (∀ t : ℝ, ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L) →
      ∀ (α : ℕ → ℕ → IntegerIntervalIndex A M → ℂ)
        (β : ℕ → ℕ → IntegerIntervalIndex B M → ℂ),
      (∀ u ∈ residualRange R g, ∀ v ∈ residualRange R g, ∀ m, ‖α u v m‖ ≤ L₁) →
      (∀ u ∈ residualRange R g, ∀ v ∈ residualRange R g, ∀ n, ‖β u v n‖ ≤ L₂) →
      residualProfileNonzeroMass (∏ i, q i) a A B M R g α β T H t₀ ψ ≤
        K * (T * L) * (L₁ * L₂) * ((R : ℝ) / (g : ℝ)) ^ ε * ((∏ i, q i : ℕ) : ℝ) ^ ε *
          dyadicNonzeroScale M ((R : ℝ) / (g : ℝ)) ((∏ i, q i : ℕ) : ℝ) := by
  obtain ⟨K, hK, hb⟩ := hlocal.exists_completed_nonzero_block_estimate hC hε
  refine ⟨128 * K * (4 : ℝ) ^ (1 + ε), by positivity, ?_⟩
  intro ι _ q _ hcp a A B ha M R g hR hg L₁ L₂ T L H t₀
    hL₁ hL₂ hT hL hH ψ hψ hsupp hbound α β hα hβ
  let w : ℕ := ∏ i, q i
  let U := residualStart R g
  let N := residualLength R g
  let r : ℝ := (R : ℝ) / (g : ℝ)
  have hr : 0 < r := div_pos (Nat.cast_pos.mpr hR) (Nat.cast_pos.mpr hg)
  have hw : (0 : ℝ) < w := by exact_mod_cast NeZero.pos w
  by_cases hN : N = 0
  · have he : residualLength R g = 0 := hN
    simp only [residualProfileNonzeroMass, sharedProfileNonzeroMass, he,
      Finset.range_zero, Finset.sum_empty]
    exact mul_nonneg (by positivity) (dyadicNonzeroScale_nonneg (Nat.cast_nonneg M) hr.le hw.le)
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
    let κ : ℝ := 4 * r ^ 2 * (w : ℝ) / H
    have hκ : 0 < κ := by dsimp only [κ]; positivity
    have hκH : κ * H = 4 * r ^ 2 * (w : ℝ) := div_mul_cancel₀ _ hH.ne'
    have hUV (x : ℕ) (hx : x ∈ Finset.range N) :
        r ≤ (positiveOuterIndex U x : ℝ) ∧ (positiveOuterIndex U x : ℝ) ≤ 2 * r := by
      change (R : ℝ) / (g : ℝ) ≤ (((residualStart R g : ℕ) + x : ℕ) : ℝ) ∧
        (((residualStart R g : ℕ) + x : ℕ) : ℝ) ≤ 2 * ((R : ℝ) / (g : ℝ))
      simpa only [mul_div_assoc] using
        residualRange_real_bounds hg (residualStart_add_mem R g x hR hg hx)
    have hup (x : ℕ) (hx : x ∈ Finset.range N) (y : ℕ) (hy : y ∈ Finset.range N) :
        ((positiveOuterIndex U x * (positiveOuterIndex U y * w) : ℕ) : ℝ) ≤ κ * H := by
      rw [hκH, Nat.cast_mul, Nat.cast_mul]
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul (hUV x hx).2 (hUV y hy).2
        (by positivity) (by positivity)) hw.le
      convert! hh using 1 <;> ring
    have hlo (x : ℕ) (hx : x ∈ Finset.range N) (y : ℕ) (hy : y ∈ Finset.range N) :
        κ * H ≤ 4 * ((positiveOuterIndex U x * (positiveOuterIndex U y * w) : ℕ) : ℝ) := by
      rw [hκH, Nat.cast_mul, Nat.cast_mul]
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul (hUV x hx).1 (hUV y hy).1
        hr.le (by positivity)) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hw.le)
      convert! hh using 1 <;> ring
    let α' (x y : ℕ) := α ((U : ℕ) + x) ((U : ℕ) + y)
    let β' (x y : ℕ) := β ((U : ℕ) + x) ((U : ℕ) + y)
    have hα' : ∀ x ∈ Finset.range N, ∀ y ∈ Finset.range N, ∀ m, ‖α' x y m‖ ≤ L₁ :=
      fun x hx y hy m => hα _ (residualStart_add_mem R g x hR hg hx)
        _ (residualStart_add_mem R g y hR hg hy) m
    have hβ' : ∀ x ∈ Finset.range N, ∀ y ∈ Finset.range N, ∀ n, ‖β' x y n‖ ≤ L₂ :=
      fun x hx y hy n => hβ _ (residualStart_add_mem R g x hR hg hx)
        _ (residualStart_add_mem R g y hR hg hy) n
    have hX : (U : ℝ) + (N : ℝ) ≤ 4 * r := residualInterval_upper_scale hg hNpos
    have hh := hb q hcp a A B ha M N hNpos U U (4 * r) L₁ L₂ T L H t₀ κ 4
      hX hX hL₁ hL₂ hT hL hH hκ (by norm_num) hup hlo ψ hψ hsupp hbound α' β' hα' hβ'
    apply hh.trans
    have houter := outer_matrix_scale_comparison (Nat.cast_nonneg M) hw.le hNreal hr
      (show (N : ℝ) ≤ 2 * r by
        simpa only [N, r, mul_div_assoc] using residualLength_real_le (R := R) hg)
    let F : ℝ := (32 * T * L) * (K * (M : ℝ) * (L₁ * L₂) * (4 * r) ^ (1 + ε) * (w : ℝ) ^ ε)
    have hF : 0 ≤ F := by dsimp only [F]; positivity
    calc
      _ = F * ((N : ℝ) ^ 2 * matrixThreeScale M N w) := by dsimp only [F]; ring
      _ ≤ F * (4 * (r ^ 2 * matrixThreeScale M r w)) := mul_le_mul_of_nonneg_left houter hF
      _ = _ := by
        dsimp only [F, dyadicNonzeroScale]
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hr.le,
          Real.rpow_add hr, Real.rpow_one]
        ring

/-- The residual-interval theorem for every actual squarefree shared modulus. -/
theorem LocalFourierHypothesis.exists_squarefree_residual_nonzero_estimate
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : ℕ) [NeZero w], Squarefree w →
      ∀ (a A B : ℤ), IsUnit (a : ZMod w) →
      ∀ (M R g : ℕ), 0 < R → 0 < g → ∀ (L₁ L₂ T L H t₀ : ℝ),
      0 ≤ L₁ → 0 ≤ L₂ → 0 ≤ T → 0 ≤ L → 0 < H →
      ∀ (ψ : ℝ → ℂ), ContDiff ℝ ∞ ψ →
      Function.support ψ ⊆ Set.Icc (-T) T →
      (∀ t : ℝ, ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L) →
      ∀ (α : ℕ → ℕ → IntegerIntervalIndex A M → ℂ)
        (β : ℕ → ℕ → IntegerIntervalIndex B M → ℂ),
      (∀ u ∈ residualRange R g, ∀ v ∈ residualRange R g, ∀ m, ‖α u v m‖ ≤ L₁) →
      (∀ u ∈ residualRange R g, ∀ v ∈ residualRange R g, ∀ n, ‖β u v n‖ ≤ L₂) →
      residualProfileNonzeroMass w a A B M R g α β T H t₀ ψ ≤
        K * (T * L) * (L₁ * L₂) * ((R : ℝ) / (g : ℝ)) ^ ε * (w : ℝ) ^ ε *
          dyadicNonzeroScale M ((R : ℝ) / (g : ℝ)) w := by
  obtain ⟨K, hK, hb⟩ := hlocal.exists_residual_nonzero_estimate hC hε
  refine ⟨K, hK, ?_⟩
  intro w _ hw a A B ha M R g hR hg L₁ L₂ T L H t₀ hL₁ hL₂ hT hL hH ψ hψ hsupp hbound α β hα hβ
  let ι := {p : ℕ // p ∈ w.primeFactors}
  let q (i : ι) : ℕ := i.1
  have : ∀ i : ι, Fact (q i).Prime := fun i => ⟨Nat.prime_of_mem_primeFactors i.2⟩
  have hcp : Pairwise (fun i j : ι => (q i).Coprime (q j)) := by
    intro i j hij
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors i.2)
      (Nat.prime_of_mem_primeFactors j.2)).2 (Subtype.coe_ne_coe.mpr hij)
  have hprod : (∏ i : ι, q i) = w := by
    exact (Finset.prod_coe_sort w.primeFactors (fun p : ℕ => p)).trans
      (Nat.prod_primeFactors_of_squarefree hw)
  have ha' : IsUnit (a : ZMod (∏ i : ι, q i)) :=
    (congrArg (fun k : ℕ => IsUnit (a : ZMod k)) hprod).mpr ha
  have hh := hb q hcp a A B ha' M R g hR hg L₁ L₂ T L H t₀ hL₁ hL₂ hT hL hH
    ψ hψ hsupp hbound α β hα hβ
  simpa only [hprod] using hh

#print axioms LocalFourierHypothesis.exists_residual_nonzero_estimate
#print axioms LocalFourierHypothesis.exists_squarefree_residual_nonzero_estimate

end

end PrimeGap182.TypeIII
