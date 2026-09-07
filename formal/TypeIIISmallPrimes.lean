import TypeIIIBaselineBridge
import TypeIIISquarefreeCompletion

/-!
# Removing the fixed small-prime cutoff

The cutoff can be removed using only the trivial norm bound on the actual finite sums.
An optional sharper bound from the existing public pair-correlation inputs is also provided.
The all-prime theorem `remove_small_primes_trivial` requires none of those public inputs.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

theorem fourier₂_norm_le_uniform (s : ℕ) [NeZero s]
    (F : ZMod s → ZMod s → ℂ) (L : ℝ) (hF : ∀ x y, ‖F x y‖ ≤ L)
    (h k : ZMod s) : ‖fourier₂ s F h k‖ ≤ (s : ℝ) ^ 2 * L := by
  unfold fourier₂
  calc
    _ ≤ ∑ _x : ZMod s, ∑ _y : ZMod s, L := by
      apply norm_sum_le_of_le
      intro x hx
      apply norm_sum_le_of_le
      intro y hy
      simpa only [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one] using hF x y
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring

/-- A deliberately coarse estimate from the defining finite sum, with no finite-field input. -/
theorem kl3_norm_le_trivial (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    ‖kl3 p a‖ ≤ (p : ℝ) ^ 2 := by
  have hcard : (Fintype.card (ZMod p)ˣ : ℝ) ≤ p := by
    exact_mod_cast (show Fintype.card (ZMod p)ˣ ≤ p by
      simpa only [ZMod.card] using Fintype.card_le_of_injective
        (fun u : (ZMod p)ˣ => (u : ZMod p)) Units.val_injective)
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (NeZero.one_le : 1 ≤ p)
  have hinv : ‖(p : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ hp
  unfold kl3
  rw [norm_mul]
  calc
    _ ≤ 1 * (Fintype.card (ZMod p)ˣ : ℝ) ^ 2 := by
      apply mul_le_mul hinv _ (norm_nonneg _) zero_le_one
      calc
        _ ≤ ∑ _u : (ZMod p)ˣ, ∑ _v : (ZMod p)ˣ, (1 : ℝ) := by
          apply norm_sum_le_of_le
          intro u hu
          apply norm_sum_le_of_le
          intro v hv
          simp only [ZMod.stdAddChar_apply, Circle.norm_coe, le_refl]
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ _ := by simpa only [one_mul] using pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2

theorem correlation_norm_le_trivial (p : ℕ) [Fact p.Prime] (A B c : ZMod p) :
    ‖correlation p A B c‖ ≤ (p : ℝ) ^ 5 := by
  have hcard : (Fintype.card (ZMod p)ˣ : ℝ) ≤ p := by
    exact_mod_cast (show Fintype.card (ZMod p)ˣ ≤ p by
      simpa only [ZMod.card] using Fintype.card_le_of_injective
        (fun u : (ZMod p)ˣ => (u : ZMod p)) Units.val_injective)
  unfold correlation
  calc
    _ ≤ ∑ _h : (ZMod p)ˣ, (p : ℝ) ^ 2 * (p : ℝ) ^ 2 := by
      apply norm_sum_le_of_le
      intro h hh
      simp only [norm_mul, norm_star, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one]
      exact mul_le_mul (kl3_norm_le_trivial p _) (kl3_norm_le_trivial p _)
        (norm_nonneg _) (by positivity)
    _ = (Fintype.card (ZMod p)ˣ : ℝ) * ((p : ℝ) ^ 2 * (p : ℝ) ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (p : ℝ) * ((p : ℝ) ^ 2 * (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem fourCycle_norm_le_trivial (p : ℕ) [Fact p.Prime]
    (α m m' n n' x y : ZMod p) :
    ‖fourCycle p α m m' n n' x y‖ ≤ (p : ℝ) ^ 20 := by
  have hk (a b : ZMod p) : ‖kernel p α a b x y‖ ≤ (p : ℝ) ^ 5 := by
    unfold kernel
    split_ifs
    · simpa only [norm_zero] using (show 0 ≤ (p : ℝ) ^ 5 by positivity)
    · exact correlation_norm_le_trivial p _ _ _
  calc
    _ ≤ ((p : ℝ) ^ 5) ^ 4 := fourCycle_norm_le_of_kernel p _ (by positivity)
      α m m' n n' x y (hk m n) (hk m' n) (hk m' n') (hk m n')
    _ = _ := by ring

theorem fourCycle_norm_le_baseline_inputs
    (hbase : BaselineLocalInputs) (p : ℕ) [Fact p.Prime]
    (α m m' n n' x y : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    ‖fourCycle p α m m' n n' x y‖ ≤ 6561 * (p : ℝ) ^ 2 := by
  have hk (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :=
    kernel_norm_le_of_baseline_inputs p hbase α a b x y hα ha hb
  calc
    _ ≤ (9 * Real.sqrt (p : ℝ)) ^ 4 := fourCycle_norm_le_of_kernel p _ (by positivity)
      α m m' n n' x y (hk m n hm hn) (hk m' n hm' hn)
        (hk m' n' hm' hn') (hk m n' hm hn')
    _ = _ := by
      rw [mul_pow, show (Real.sqrt (p : ℝ)) ^ 4 = ((Real.sqrt (p : ℝ)) ^ 2) ^ 2 by ring,
        Real.sq_sqrt (Nat.cast_nonneg p)]
      norm_num

theorem FiniteExceptionalFourierBound.mono_constant
    (p : ℕ) [Fact p.Prime] {C C' : ℝ} {D : ℕ} {α m m' n n' : ZMod p}
    (hbound : FiniteExceptionalFourierBound p C D α m m' n n') (hCC' : C ≤ C') :
    FiniteExceptionalFourierBound p C' D α m m' n n' := by
  obtain ⟨Z, hZ, hF⟩ := hbound
  refine ⟨Z, hZ, ?_⟩
  intro h k
  apply (hF h k).trans
  apply mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCC' (by positivity))
  split_ifs <;> positivity

theorem CurveExceptionalFourierBound.mono_constant
    (p : ℕ) [Fact p.Prime] {C C' : ℝ} {D : ℕ} {α m m' n n' : ZMod p}
    (hbound : CurveExceptionalFourierBound p C D α m m' n n') (hCC' : C ≤ C') :
    CurveExceptionalFourierBound p C' D α m m' n n' := by
  obtain ⟨P, hP, hD, hF⟩ := hbound
  refine ⟨P, hP, hD, ?_⟩
  intro h k
  apply (hF h k).trans
  apply mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCC' (by positivity))
  split_ifs <;> positivity

/-- An explicit uniform constant that also covers the finitely many excluded primes. -/
def enlargedLocalConstant (C : ℝ) (p₀ : ℕ) : ℝ := C + 6561 * p₀

theorem enlargedLocalConstant_nonneg {C : ℝ} (hC : 0 ≤ C) (p₀ : ℕ) :
    0 ≤ enlargedLocalConstant C p₀ := by unfold enlargedLocalConstant; positivity

/-- The old public inputs plus the stated new local input prove its all-prime version. -/
theorem LocalFourierHypothesis.remove_small_primes
    (hbase : BaselineLocalInputs) {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ}
    (hlocal : LocalFourierHypothesis C D p₀) :
    LocalFourierHypothesis (enlargedLocalConstant C p₀) D 0 := by
  intro p hp _ α m m' n n' hα hm hm' hn hn'
  have hCC' : C ≤ enlargedLocalConstant C p₀ := by
    unfold enlargedLocalConstant
    exact le_add_of_nonneg_right (by positivity)
  by_cases hlarge : p₀ < p
  · have hh := hlocal p hlarge α m m' n n' hα hm hm' hn hn'
    exact ⟨fun h => (hh.1 h).mono_constant p hCC', fun h => (hh.2 h).mono_constant p hCC'⟩
  · have hp₀ : (p : ℝ) ≤ p₀ := by exact_mod_cast (Nat.le_of_not_gt hlarge)
    have hpoint (h k : ZMod p) :
        ‖fourier₂ p (fourCycle p α m m' n n') h k‖ ≤
          enlargedLocalConstant C p₀ * (p : ℝ) ^ 3 := by
      calc
        _ ≤ (p : ℝ) ^ 2 * (6561 * (p : ℝ) ^ 2) :=
          fourier₂_norm_le_uniform p _ _
            (fun x y => fourCycle_norm_le_baseline_inputs hbase p α m m' n n' x y
              hα hm hm' hn hn') h k
        _ = (6561 * (p : ℝ)) * (p : ℝ) ^ 3 := by ring
        _ ≤ (6561 * (p₀ : ℝ)) * (p : ℝ) ^ 3 := by gcongr
        _ ≤ enlargedLocalConstant C p₀ * (p : ℝ) ^ 3 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact le_add_of_nonneg_left hC
    constructor
    · intro _
      refine ⟨∅, by simp only [Finset.card_empty, Nat.zero_le], ?_⟩
      intro h k
      simpa using hpoint h k
    · intro _
      refine ⟨1, one_ne_zero, by simp only [MvPolynomial.totalDegree_one, Nat.zero_le], ?_⟩
      intro h k
      apply (hpoint h k).trans
      apply le_mul_of_one_le_right
        (mul_nonneg (enlargedLocalConstant_nonneg hC p₀) (by positivity))
      split_ifs <;> nlinarith [Real.sqrt_nonneg (p : ℝ), Nat.cast_nonneg (α := ℝ) p]

/-- A cutoff-dependent constant from the trivial finite sums alone. -/
def trivialEnlargedLocalConstant (C : ℝ) (p₀ : ℕ) : ℝ := C + (p₀ : ℝ) ^ 19

theorem trivialEnlargedLocalConstant_nonneg {C : ℝ} (hC : 0 ≤ C) (p₀ : ℕ) :
    0 ≤ trivialEnlargedLocalConstant C p₀ := by
  unfold trivialEnlargedLocalConstant
  positivity

/-- No baseline Kloosterman bound is needed to remove the finite small-prime cutoff. -/
theorem LocalFourierHypothesis.remove_small_primes_trivial
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ}
    (hlocal : LocalFourierHypothesis C D p₀) :
    LocalFourierHypothesis (trivialEnlargedLocalConstant C p₀) D 0 := by
  intro p hp _ α m m' n n' hα hm hm' hn hn'
  have hCC' : C ≤ trivialEnlargedLocalConstant C p₀ := by
    unfold trivialEnlargedLocalConstant
    exact le_add_of_nonneg_right (by positivity)
  by_cases hlarge : p₀ < p
  · have hh := hlocal p hlarge α m m' n n' hα hm hm' hn hn'
    exact ⟨fun h => (hh.1 h).mono_constant p hCC', fun h => (hh.2 h).mono_constant p hCC'⟩
  · have hp₀ : (p : ℝ) ≤ p₀ := by exact_mod_cast (Nat.le_of_not_gt hlarge)
    have hpoint (h k : ZMod p) :
        ‖fourier₂ p (fourCycle p α m m' n n') h k‖ ≤
          trivialEnlargedLocalConstant C p₀ * (p : ℝ) ^ 3 := by
      calc
        _ ≤ (p : ℝ) ^ 2 * (p : ℝ) ^ 20 :=
          fourier₂_norm_le_uniform p _ _
            (fun x y => fourCycle_norm_le_trivial p α m m' n n' x y) h k
        _ = ((p : ℝ) ^ 19) * (p : ℝ) ^ 3 := by ring
        _ ≤ ((p₀ : ℝ) ^ 19) * (p : ℝ) ^ 3 := by gcongr
        _ ≤ trivialEnlargedLocalConstant C p₀ * (p : ℝ) ^ 3 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact le_add_of_nonneg_left hC
    constructor
    · intro _
      refine ⟨∅, by simp only [Finset.card_empty, Nat.zero_le], ?_⟩
      intro h k
      simpa using hpoint h k
    · intro _
      refine ⟨1, one_ne_zero, by simp only [MvPolynomial.totalDegree_one, Nat.zero_le], ?_⟩
      intro h k
      apply (hpoint h k).trans
      apply le_mul_of_one_le_right
        (mul_nonneg (trivialEnlargedLocalConstant_nonneg hC p₀) (by positivity))
      split_ifs <;> nlinarith [Real.sqrt_nonneg (p : ℝ), Nat.cast_nonneg (α := ℝ) p]

#print axioms fourier₂_norm_le_uniform
#print axioms kl3_norm_le_trivial
#print axioms fourCycle_norm_le_trivial
#print axioms fourCycle_norm_le_baseline_inputs
#print axioms LocalFourierHypothesis.remove_small_primes
#print axioms LocalFourierHypothesis.remove_small_primes_trivial

end

end PrimeGap182.TypeIII
