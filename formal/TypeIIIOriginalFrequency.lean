import TypeIIIFrequencyAverage
import TypeIIISeparatedCoefficients

/-!
# The nonzero-frequency average of the original shared Fourier sums

The coefficient vectors are now the actual one-sided Fourier factors, not free vectors
with a norm bound supplied by the caller. All unit, coprimality, and squarefree restrictions
are retained. The resulting estimate is the fixed-shared-modulus input for the Type III
second moment; smooth Poisson completion and the later `s,g` summation remain separate.
-/

open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

attribute [local instance] familyProductNeZero

/-- The actual structural restrictions on the two relatively prime residual moduli. -/
structure SharedOuterAdmissible (w : ℕ) (a : ℤ) (u v : ℕ) : Prop where
  coprime : u.Coprime v
  left_coprime : u.Coprime w
  right_coprime : v.Coprime w
  left_squarefree : Squarefree u
  right_squarefree : Squarefree v
  left_primitive : IsUnit (a : ZMod u)
  right_primitive : IsUnit (a : ZMod v)

def positiveOuterIndex (U : ℕ+) (x : ℕ) : ℕ+ :=
  ⟨(U : ℕ) + x, Nat.add_pos_left U.pos x⟩

/-- The exact pair of one-sided vectors, with the actual outer arithmetic mask. -/
def maskedSeparatedVectors (w : ℕ) [NeZero w] (a c A B : ℤ) (M : ℕ)
    (U V : ℕ+) (x y : ℕ) (α : IntegerIntervalIndex A M → ℂ)
    (β : IntegerIntervalIndex B M → ℂ) :
    EuclideanSpace ℂ (IntegerIntervalIndex A M) × EuclideanSpace ℂ (IntegerIntervalIndex B M) :=
  let u := positiveOuterIndex U x
  let v := positiveOuterIndex V y
  if SharedOuterAdmissible w a u v then
    (separatedFourierVector u w a ((c : ZMod u) * ((v * w : ℕ) : ZMod u)⁻¹) A M α,
      separatedFourierVector v w a (-((c : ZMod v) * ((u * w : ℕ) : ZMod v)⁻¹)) B M β)
  else (0, 0)

/-- The original signed inner sum is normed only after all matrix coefficients have been
combined, while the two positive outer intervals are summed explicitly. -/
def maskedSharedOriginalMass (w : ℕ) [NeZero w] (a c A B : ℤ) (M R : ℕ)
    (U V : ℕ+) (α : ℕ → ℕ → IntegerIntervalIndex A M → ℂ)
    (β : ℕ → ℕ → IntegerIntervalIndex B M → ℂ) : ℝ :=
  ∑ x ∈ Finset.range R, ∑ y ∈ Finset.range R,
    if SharedOuterAdmissible w a (positiveOuterIndex U x) (positiveOuterIndex V y) then
      ‖sharedOriginalCoefficientSum (positiveOuterIndex U x) (positiveOuterIndex V y)
        w a c A B M M (α x y) (β x y)‖
    else 0

theorem maskedSharedOriginalMass_eq_matrix {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, Fact (q i).Prime]
    (hcp : Pairwise (fun i j => (q i).Coprime (q j)))
    (a c A B : ℤ) (ha : IsUnit (a : ZMod (∏ i, q i))) (M R : ℕ) (U V : ℕ+)
    (α : ℕ → ℕ → IntegerIntervalIndex A M → ℂ)
    (β : ℕ → ℕ → IntegerIntervalIndex B M → ℂ) :
    maskedSharedOriginalMass (∏ i, q i) a c A B M R U V α β =
      sharedCoefficientMass q a c A B U V M R
        (fun x y => (maskedSeparatedVectors (∏ i, q i) a c A B M U V x y (α x y) (β x y)).1)
        (fun x y => (maskedSeparatedVectors (∏ i, q i) a c A B M U V x y (α x y) (β x y)).2) := by
  unfold maskedSharedOriginalMass sharedCoefficientMass
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : SharedOuterAdmissible (∏ i, q i) a (positiveOuterIndex U x) (positiveOuterIndex V y)
  · simp only [ite_eq_left h, maskedSeparatedVectors]
    have hh := sharedOriginalCoefficientSum_eq_matrix q hcp
      (positiveOuterIndex U x) (positiveOuterIndex V y) h.coprime h.left_coprime h.right_coprime
      a c A B ha M M (α x y) (β x y)
    have hidx (Z : ℕ+) (k : ℕ) :
        ((positiveOuterIndex Z k : ℕ) : ℤ) = (Z : ℤ) + (k : ℤ) := by
      change (((Z : ℕ) + k : ℕ) : ℤ) = ((Z : ℕ) : ℤ) + (k : ℤ)
      exact Nat.cast_add _ _
    rw [hidx U x, hidx V y] at hh
    exact congrArg norm hh
  · simp only [ite_eq_right h, maskedSeparatedVectors]
    simp only [matrixCoefficientSum, PiLp.zero_apply, zero_mul, Finset.sum_const_zero, norm_zero]

/-- The actual two-sided Fourier sums satisfy the full nonzero-frequency average.
No norm estimate for hidden coefficient vectors is left as a hypothesis. -/
theorem LocalFourierHypothesis.exists_original_frequency_estimate
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    {decay ε : ℝ} (hdecay : 1 < decay) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {ι : Type} [Fintype ι] (q : ι → ℕ) [∀ i, Fact (q i).Prime],
      Pairwise (fun i j => (q i).Coprime (q j)) →
      ∀ (a A B : ℤ), IsUnit (a : ZMod (∏ i, q i)) →
      ∀ (M R : ℕ), 0 < R → ∀ (U V : ℕ+) (T L₁ L₂ κ : ℝ),
      (U : ℝ) + R ≤ T → (V : ℝ) + R ≤ T → 0 ≤ L₁ → 0 ≤ L₂ → 0 < κ →
      ∀ (α : ℤ → ℕ → ℕ → IntegerIntervalIndex A M → ℂ)
        (β : ℤ → ℕ → ℕ → IntegerIntervalIndex B M → ℂ),
      (∀ c : ℤ, ∀ x ∈ Finset.range R, ∀ y ∈ Finset.range R, ∀ m, ‖α c x y m‖ ≤ L₁) →
      (∀ c : ℤ, ∀ x ∈ Finset.range R, ∀ y ∈ Finset.range R, ∀ n, ‖β c x y n‖ ≤ L₂) →
      Summable (fun c : ℤ => (integerFrequencyDecay κ⁻¹ decay c / κ) *
        maskedSharedOriginalMass (∏ i, q i) a c A B M R U V (α c) (β c)) ∧
      (∑' c : ℤ, (integerFrequencyDecay κ⁻¹ decay c / κ) *
        maskedSharedOriginalMass (∏ i, q i) a c A B M R U V (α c) (β c)) ≤
        K * (M : ℝ) * (L₁ * L₂) * T ^ (1 + ε) * (R : ℝ) ^ 2 *
          ((∏ i, q i : ℕ) : ℝ) ^ ε * matrixThreeScale M R ((∏ i, q i : ℕ) : ℝ) := by
  obtain ⟨K₁, hK₁, hb₁⟩ := hlocal.exists_shared_frequency_tsum_estimate hC hdecay hε
  obtain ⟨K₂, hK₂, hb₂⟩ := exists_separatedFourierVector_pair_bound hε
  refine ⟨K₁ * K₂, mul_pos hK₁ hK₂, ?_⟩
  intro ι _ q _ hcp a A B ha M R hR U V T L₁ L₂ κ hUT hVT hL₁ hL₂ hκ α β hα hβ
  let W : ℝ := K₂ * (M : ℝ) * (L₁ * L₂) * T ^ (1 + ε)
  have hT : 0 < T := by
    have hU : (0 : ℝ) < U := by exact_mod_cast U.pos
    linarith [Nat.cast_nonneg (α := ℝ) R]
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  let f (c : ℤ) (x y : ℕ) :=
    (maskedSeparatedVectors (∏ i, q i) a c A B M U V x y (α c x y) (β c x y)).1
  let g (c : ℤ) (x y : ℕ) :=
    (maskedSeparatedVectors (∏ i, q i) a c A B M U V x y (α c x y) (β c x y)).2
  have hfg (c : ℤ) (x : ℕ) (hx : x ∈ Finset.range R) (y : ℕ) (hy : y ∈ Finset.range R) :
      ‖f c x y‖ * ‖g c x y‖ ≤ W := by
    by_cases h : SharedOuterAdmissible (∏ i, q i) a (positiveOuterIndex U x) (positiveOuterIndex V y)
    · dsimp only [f, g, maskedSeparatedVectors]
      rw [ite_eq_left h]
      have hux : ((positiveOuterIndex U x : ℕ) : ℝ) ≤ T := by
        have hx' : (x : ℝ) ≤ R := by exact_mod_cast (Finset.mem_range.mp hx).le
        change (((U : ℕ) + x : ℕ) : ℝ) ≤ T
        rw [Nat.cast_add]
        linarith
      have hvy : ((positiveOuterIndex V y : ℕ) : ℝ) ≤ T := by
        have hy' : (y : ℝ) ≤ R := by exact_mod_cast (Finset.mem_range.mp hy).le
        change (((V : ℕ) + y : ℕ) : ℝ) ≤ T
        rw [Nat.cast_add]
        linarith
      exact hb₂ (positiveOuterIndex U x) (positiveOuterIndex V y) (∏ i, q i)
        h.left_coprime h.right_coprime h.left_squarefree h.right_squarefree a
        h.left_primitive h.right_primitive _ _ A B M (α c x y) (β c x y)
        L₁ L₂ T hL₁ hL₂ hux hvy (hα c x hx y hy) (hβ c x hx y hy)
    · simp only [f, g, maskedSeparatedVectors, ite_eq_right h, norm_zero, zero_mul]
      exact hW
  have hh := hb₁ q hcp a A B U V ha M R hR W κ hW hκ f g hfg
  have heq (c : ℤ) :
      sharedCoefficientMass q a c A B U V M R (f c) (g c) =
        maskedSharedOriginalMass (∏ i, q i) a c A B M R U V (α c) (β c) :=
    (maskedSharedOriginalMass_eq_matrix q hcp a c A B ha M R U V (α c) (β c)).symm
  simp only [heq] at hh
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  dsimp only [W]
  ring

#print axioms maskedSharedOriginalMass_eq_matrix
#print axioms LocalFourierHypothesis.exists_original_frequency_estimate

end

end PrimeGap182.TypeIII
