import TypeIIICompletedBlock

/-!
# Actual dyadic modulus blocks

The completion-width comparisons are discharged here for u,v in [R,2R). The result
retains the three terms later summed over the gcd and shared-factor variables.
-/

open scoped BigOperators Classical FourierTransform ContDiff

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

attribute [local instance] familyProductNeZero

def dyadicNonzeroScale (M R w : ℝ) : ℝ := M * R ^ 3 * matrixThreeScale M R w

theorem dyadicNonzeroScale_nonneg {M R w : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) (hw : 0 ≤ w) :
    0 ≤ dyadicNonzeroScale M R w := by
  exact mul_nonneg (mul_nonneg hM (pow_nonneg hR 3)) (matrixThreeScale_nonneg hM hR hw)

theorem positiveOuterIndex_dyadic (R : ℕ+) (x : ℕ) (hx : x ∈ Finset.range R) :
    (R : ℝ) ≤ (positiveOuterIndex R x : ℝ) ∧
      (positiveOuterIndex R x : ℝ) ≤ 2 * (R : ℝ) := by
  have hx' : (x : ℝ) ≤ R := by exact_mod_cast (Finset.mem_range.mp hx).le
  change (R : ℝ) ≤ (((R : ℕ) + x : ℕ) : ℝ) ∧
    (((R : ℕ) + x : ℕ) : ℝ) ≤ 2 * (R : ℝ)
  rw [Nat.cast_add]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) x]

/-- The actual smooth physical sum on a dyadic block, with no completion-width
comparability hypotheses remaining. -/
theorem LocalFourierHypothesis.exists_dyadic_nonzero_estimate
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {ι : Type} [Fintype ι] (q : ι → ℕ) [∀ i, Fact (q i).Prime],
      Pairwise (fun i j => (q i).Coprime (q j)) →
      ∀ (a A B : ℤ), IsUnit (a : ZMod (∏ i, q i)) →
      ∀ (M : ℕ) (R : ℕ+) (L₁ L₂ T L H t₀ : ℝ),
      0 ≤ L₁ → 0 ≤ L₂ → 0 ≤ T → 0 ≤ L → 0 < H →
      ∀ (ψ : ℝ → ℂ), ContDiff ℝ ∞ ψ →
      Function.support ψ ⊆ Set.Icc (-T) T →
      (∀ t : ℝ, ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L) →
      ∀ (α : ℕ → ℕ → IntegerIntervalIndex A M → ℂ)
        (β : ℕ → ℕ → IntegerIntervalIndex B M → ℂ),
      (∀ x ∈ Finset.range R, ∀ y ∈ Finset.range R, ∀ m, ‖α x y m‖ ≤ L₁) →
      (∀ x ∈ Finset.range R, ∀ y ∈ Finset.range R, ∀ n, ‖β x y n‖ ≤ L₂) →
      sharedProfileNonzeroMass (∏ i, q i) a A B M R R R α β T H t₀ ψ ≤
        K * (T * L) * (L₁ * L₂) * (R : ℝ) ^ ε * ((∏ i, q i : ℕ) : ℝ) ^ ε *
          dyadicNonzeroScale M R ((∏ i, q i : ℕ) : ℝ) := by
  obtain ⟨K, hK, hb⟩ := hlocal.exists_completed_nonzero_block_estimate hC hε
  refine ⟨32 * K * (2 : ℝ) ^ (1 + ε), by positivity, ?_⟩
  intro ι _ q _ hcp a A B ha M R L₁ L₂ T L H t₀ hL₁ hL₂ hT hL hH ψ hψ hsupp hbound α β hα hβ
  let w : ℕ := ∏ i, q i
  have hw : (0 : ℝ) < w := by exact_mod_cast (NeZero.pos w)
  have hR : (0 : ℝ) < R := by exact_mod_cast R.pos
  let κ : ℝ := 4 * (R : ℝ) ^ 2 * (w : ℝ) / H
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hκH : κ * H = 4 * (R : ℝ) ^ 2 * (w : ℝ) := div_mul_cancel₀ _ hH.ne'
  have hup (x : ℕ) (hx : x ∈ Finset.range R) (y : ℕ) (hy : y ∈ Finset.range R) :
      ((positiveOuterIndex R x * (positiveOuterIndex R y * w) : ℕ) : ℝ) ≤ κ * H := by
    rw [hκH, Nat.cast_mul, Nat.cast_mul]
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul (positiveOuterIndex_dyadic R x hx).2 (positiveOuterIndex_dyadic R y hy).2
        (by positivity) (by positivity)) hw.le
    convert! hh using 1 <;> ring
  have hlo (x : ℕ) (hx : x ∈ Finset.range R) (y : ℕ) (hy : y ∈ Finset.range R) :
      κ * H ≤ 4 * ((positiveOuterIndex R x * (positiveOuterIndex R y * w) : ℕ) : ℝ) := by
    rw [hκH, Nat.cast_mul, Nat.cast_mul]
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul (positiveOuterIndex_dyadic R x hx).1 (positiveOuterIndex_dyadic R y hy).1
        hR.le (by positivity)) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hw.le)
    convert! hh using 1 <;> ring
  have hh := hb q hcp a A B ha M R R.pos R R (2 * R) L₁ L₂ T L H t₀ κ 4
    (by linarith) (by linarith) hL₁ hL₂ hT hL hH hκ (by norm_num)
    hup hlo ψ hψ hsupp hbound α β hα hβ
  apply hh.trans_eq
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hR.le,
    Real.rpow_add hR, Real.rpow_one]
  dsimp only [dyadicNonzeroScale]
  ring

/-- Prime-factorization gives the same actual theorem for every squarefree shared
modulus, rather than requiring a prime-family representation from the caller. -/
theorem LocalFourierHypothesis.exists_squarefree_dyadic_nonzero_estimate
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : ℕ) [NeZero w], Squarefree w →
      ∀ (a A B : ℤ), IsUnit (a : ZMod w) →
      ∀ (M : ℕ) (R : ℕ+) (L₁ L₂ T L H t₀ : ℝ),
      0 ≤ L₁ → 0 ≤ L₂ → 0 ≤ T → 0 ≤ L → 0 < H →
      ∀ (ψ : ℝ → ℂ), ContDiff ℝ ∞ ψ →
      Function.support ψ ⊆ Set.Icc (-T) T →
      (∀ t : ℝ, ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L) →
      ∀ (α : ℕ → ℕ → IntegerIntervalIndex A M → ℂ)
        (β : ℕ → ℕ → IntegerIntervalIndex B M → ℂ),
      (∀ x ∈ Finset.range R, ∀ y ∈ Finset.range R, ∀ m, ‖α x y m‖ ≤ L₁) →
      (∀ x ∈ Finset.range R, ∀ y ∈ Finset.range R, ∀ n, ‖β x y n‖ ≤ L₂) →
      sharedProfileNonzeroMass w a A B M R R R α β T H t₀ ψ ≤
        K * (T * L) * (L₁ * L₂) * (R : ℝ) ^ ε * (w : ℝ) ^ ε *
          dyadicNonzeroScale M R w := by
  obtain ⟨K, hK, hb⟩ := hlocal.exists_dyadic_nonzero_estimate hC hε
  refine ⟨K, hK, ?_⟩
  intro w _ hw a A B ha M R L₁ L₂ T L H t₀ hL₁ hL₂ hT hL hH ψ hψ hsupp hbound α β hα hβ
  let ι := {p : ℕ // p ∈ w.primeFactors}
  let q (i : ι) : ℕ := i.1
  have : ∀ i : ι, Fact (q i).Prime := fun i => ⟨Nat.prime_of_mem_primeFactors i.2⟩
  have hcp : Pairwise (fun i j : ι => (q i).Coprime (q j)) := by
    intro i j hij
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors i.2)
      (Nat.prime_of_mem_primeFactors j.2)).2 (Subtype.coe_ne_coe.mpr hij)
  have hprod : (∏ i : ι, q i) = w := by
    change (∏ i : w.primeFactors, (i : ℕ)) = w
    exact (Finset.prod_coe_sort w.primeFactors (fun p : ℕ => p)).trans
      (Nat.prod_primeFactors_of_squarefree hw)
  have ha' : IsUnit (a : ZMod (∏ i : ι, q i)) :=
    (congrArg (fun k : ℕ => IsUnit (a : ZMod k)) hprod).mpr ha
  have hh := hb q hcp a A B ha' M R L₁ L₂ T L H t₀ hL₁ hL₂ hT hL hH
    ψ hψ hsupp hbound α β hα hβ
  simpa only [hprod] using hh

#print axioms LocalFourierHypothesis.exists_dyadic_nonzero_estimate
#print axioms LocalFourierHypothesis.exists_squarefree_dyadic_nonzero_estimate

end

end PrimeGap182.TypeIII
