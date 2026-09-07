import TypeIIIFiveScaleBound

/-!
# Recombination of the actual dyadic selected sums

The partition occurs in the original modulus sum. Cauchy is applied inside each
cell only afterward; the cardinal factor accounts for recombination. Thus pairs
of different dyadic cells have not silently been discarded.
-/

open scoped BigOperators Classical ContDiff
open PrimeGap186 UniqueFactorizationMonoid

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem selectedKloostermanL1_dyadic_sq_le (b : ℕ+) (B : ℕ) (D : Finset ℕ+)
    (a : ∀ d : ℕ+, (ZMod ((b : ℕ) * (d : ℕ)))ˣ)
    (M : Finset ℤ) (η : ℕ → ℂ) (α : ℤ → ℂ) (H : ℝ) (ρ σ : ℕ+ → ℕ+)
    (Z : ℝ) (hcell : ∀ j ∈ dyadicFactorCells D ρ σ,
      selectedKloostermanL1 b B (dyadicFactorBlock D ρ σ j) a M η α H ^ 2 ≤ Z) :
    selectedKloostermanL1 b B D a M η α H ^ 2 ≤
      ((dyadicFactorCells D ρ σ).card : ℝ) ^ 2 * Z := by
  have hpartition := weightedKernelL1_dyadic_le D (selectedFrequencyRange H)
    ternaryDivisorWeight (fun _ _ => Nat.cast_nonneg _)
    (selectedKloostermanTerm b B a M η α) ρ σ
  change selectedKloostermanL1 b B D a M η α H ≤
    ∑ j ∈ dyadicFactorCells D ρ σ,
      selectedKloostermanL1 b B (dyadicFactorBlock D ρ σ j) a M η α H at hpartition
  calc
    _ ≤ (∑ j ∈ dyadicFactorCells D ρ σ,
        selectedKloostermanL1 b B (dyadicFactorBlock D ρ σ j) a M η α H) ^ 2 :=
      pow_le_pow_left₀ (selectedKloostermanL1_nonneg b B D a M η α H) hpartition 2
    _ ≤ ((dyadicFactorCells D ρ σ).card : ℝ) *
        ∑ j ∈ dyadicFactorCells D ρ σ,
          selectedKloostermanL1 b B (dyadicFactorBlock D ρ σ j) a M η α H ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ ((dyadicFactorCells D ρ σ).card : ℝ) *
        ∑ _j ∈ dyadicFactorCells D ρ σ, Z :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (Nat.cast_nonneg _)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- Full selected-modulus bound with a common extraction window and explicit
dyadic, logarithmic, and subpower factors. -/
theorem LocalFourierHypothesis.exists_dyadic_kernel_square_estimate
    {C : ℝ} (hC : 0 ≤ C) {D₀ p₀ : ℕ} (hlocal : LocalFourierHypothesis C D₀ p₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (b : ℕ+) (b₁ b₂ b₃ : ℕ), 0 < b₁ → 0 < b₂ → 0 < b₃ →
      (b : ℕ) = (radical (b₁ * b₂ * b₃) : ℕ) →
    ∀ (D : Finset ℕ+), (∀ d ∈ D, Squarefree ((b : ℕ) * (d : ℕ))) →
    ∀ (ρ σ : ℕ+ → ℕ+), (∀ d ∈ D, d = ρ d * σ d) →
    ∀ (N : ℕ), 0 < N → ∀ Q S y : ℝ, 0 < Q → 1 ≤ S → 0 < y →
      (∀ d ∈ D, (d : ℝ) ≤ Q) →
      (∀ d ∈ D, S / y ≤ (σ d : ℝ) ∧ (σ d : ℝ) ≤ S) →
    ∀ (a₀ : ℤ) (a : ∀ d : ℕ+, (ZMod ((b : ℕ) * (d : ℕ)))ˣ),
      (∀ d ∈ D, (a d : ZMod ((b : ℕ) * (d : ℕ))) = (a₀ : ZMod ((b : ℕ) * (d : ℕ)))) →
    ∀ (M : Finset ℤ), M ⊆ Finset.Ico 1 (1 + (N : ℤ)) →
    ∀ (η : ℕ → ℂ) (α : ℤ → ℂ) (E W T L H : ℝ),
      0 ≤ E → 0 ≤ W → 1 ≤ T → 0 ≤ L → 0 < H →
      (∀ d ∈ D, ‖η ((b : ℕ) * (d : ℕ))‖ ≤ E) → (∀ m ∈ M, ‖α m‖ ≤ W) →
    ∀ (ψ : ℝ → ℝ), ContDiff ℝ ∞ ψ → (∀ t : ℝ, 0 ≤ ψ t) →
      (∀ t ∈ Set.Icc (-1 : ℝ) 1, ψ t = 1) → Function.support ψ ⊆ Set.Icc (-T) T →
      (∀ t : ℝ, ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L) →
      selectedKloostermanL1 b (b₁ * b₂ * b₃) D a M η α H ^ 2 ≤
        ((dyadicFactorCells D ρ σ).card : ℝ) ^ 2 * K * (T * L) * (E * W) ^ 2 *
          firstMomentLogBound H (2 * S) * selectionSubpower N Q ε * fiveScale N Q S y H := by
  obtain ⟨K, hK, hkernel⟩ := hlocal.exists_selected_kernel_square_estimate hC hε
  refine ⟨16 * K, by positivity, ?_⟩
  intro b b₁ b₂ b₃ hb₁ hb₂ hb₃ hb D hD ρ σ hfactor N hN Q S y hQ hS hy hDQ hσ
    a₀ a ha M hM η α E W T L H hE hW hT hL hH hη hα ψ hψ hψnonneg hψone hsupp hψbound
  let Z : ℝ := K * (T * L) * (E * W) ^ 2 * firstMomentLogBound H (2 * S) *
    (16 * selectionSubpower N Q ε * fiveScale N Q S y H)
  have hcell : ∀ j ∈ dyadicFactorCells D ρ σ,
      selectedKloostermanL1 b (b₁ * b₂ * b₃) (dyadicFactorBlock D ρ σ j) a M η α H ^ 2 ≤ Z := by
    intro j hj
    let Dj := dyadicFactorBlock D ρ σ j
    have hsub : Dj ⊆ D := Finset.filter_subset _ _
    have hne : Dj.Nonempty := by
      obtain ⟨d, hd, hlabel⟩ := Finset.mem_image.mp hj
      exact ⟨d, Finset.mem_filter.mpr ⟨hd, hlabel⟩⟩
    have hr : 0 < 2 ^ j.1 := by positivity
    have hs : 0 < 2 * 2 ^ j.2 := by positivity
    have hρj : ∀ d ∈ Dj, 2 ^ j.1 ≤ (ρ d : ℕ) ∧ (ρ d : ℕ) ≤ 2 * 2 ^ j.1 := by
      intro d hd
      obtain ⟨hrlo, hrhi, _, _⟩ := dyadicFactorBlock_bounds D ρ σ j d hd
      exact ⟨hrlo, hrhi.le⟩
    have hσj : ∀ d ∈ Dj, (σ d : ℕ) ≤ 2 * 2 ^ j.2 := by
      intro d hd
      exact (dyadicFactorBlock_bounds D ρ σ j d hd).2.2.2.le
    have hk := hkernel b b₁ b₂ b₃ hb₁ hb₂ hb₃ hb Dj (fun d hd => hD d (hsub hd))
      ρ σ (fun d hd => hfactor d (hsub hd)) N (2 ^ j.1) (2 * 2 ^ j.2)
      hN hr hs hρj hσj a₀ a (fun d hd => ha d (hsub hd)) M hM η α E W T L H
      hE hW hT hL hH (fun d hd => hη d (hsub hd)) hα
      ψ hψ hψnonneg hψone hsupp hψbound
    obtain ⟨hRS, hSlo, hShi⟩ := dyadicFactorBlock_scale_bounds D ρ σ hfactor j hne Q (S / y) S
      hDQ (fun d hd => (hσ d hd).1) (fun d hd => (hσ d hd).2)
    have hscale := selectedMomentScale_dyadic_le (Nat.cast_nonneg N)
      (Nat.cast_nonneg (2 ^ j.1)) (show (1 : ℝ) ≤ ((2 * 2 ^ j.2 : ℕ) : ℝ) by exact_mod_cast hs)
      hQ (zero_lt_one.trans_le hS) hy hH.le hε.le hRS hSlo hShi
    have hlog := firstMomentLogBound_mono_S hH.le
      (show (0 : ℝ) < ((2 * 2 ^ j.2 : ℕ) : ℝ) by exact_mod_cast hs) hShi
    have hmoment : 0 ≤ selectedMomentScale N (2 ^ j.1 : ℕ) (2 * 2 ^ j.2 : ℕ) H ε := by
      unfold selectedMomentScale nonzeroSGScale zeroSGScale
      positivity
    have hlogtop : 0 ≤ firstMomentLogBound H (2 * S) := by
      have hlogS : 0 ≤ Real.log (2 * S) := Real.log_nonneg (by linarith : 1 ≤ 2 * S)
      have hlogH : 0 ≤ Real.log (max 1 H) := Real.log_nonneg (le_max_left _ _)
      unfold firstMomentLogBound
      positivity
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul hlog hscale hmoment hlogtop)
      (by have hT₀ := zero_le_one.trans hT; positivity : 0 ≤ K * (T * L) * (E * W) ^ 2)
    exact hk.trans (by simpa only [Z, mul_assoc] using hh)
  have hh := selectedKloostermanL1_dyadic_sq_le b (b₁ * b₂ * b₃) D a M η α H ρ σ Z hcell
  apply hh.trans_eq
  dsimp only [Z]
  ring

#print axioms selectedKloostermanL1_dyadic_sq_le
#print axioms LocalFourierHypothesis.exists_dyadic_kernel_square_estimate

end

end PrimeGap182.TypeIII
