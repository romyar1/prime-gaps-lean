import TypeIIIKernelPowerBound

/-! Actual dense-divisor selection applied to the new signed kernel bound. -/

open scoped BigOperators Classical ContDiff
open PrimeGap186 UniqueFactorizationMonoid

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

theorem LocalFourierHypothesis.exists_dense_kernel_power_estimate
    {C : ℝ} (hC : 0 ≤ C) {D₀ p₀ : ℕ} (hlocal : LocalFourierHypothesis C D₀ p₀)
    {Kheight κ : ℝ} (hheight : 0 < Kheight) (hκ : 0 < κ) :
    ∃ X : ℝ, 2 ≤ X ∧ ∀ x : ℝ, X ≤ x →
    ∀ (b : ℕ+) (b₁ b₂ b₃ : ℕ), 0 < b₁ → 0 < b₂ → 0 < b₃ →
      (b : ℕ) = (radical (b₁ * b₂ * b₃) : ℕ) →
    ∀ (Y : Set.Ici (1 : ℝ)) (Qlo Qhi S : ℝ), 0 < Qlo → Qlo ≤ Qhi →
      1 ≤ S → S ≤ (Y : ℝ) * Qlo → Qhi / (b : ℝ) ≤ x ^ Kheight → S ≤ x ^ Kheight →
    ∀ (D : Finset ℕ+),
      (∀ d ∈ D, Squarefree ((b : ℕ) * (d : ℕ)) ∧
        Nonempty (DenseDivisibilityWitness Y 1 ((b : ℕ) * (d : ℕ))) ∧
        Qlo ≤ (b : ℝ) * (d : ℝ) ∧ (b : ℝ) * (d : ℝ) ≤ Qhi) →
    ∀ (N : ℕ), 0 < N → (N : ℝ) ≤ x ^ Kheight →
    ∀ (a₀ : ℤ) (a : ∀ d : ℕ+, (ZMod ((b : ℕ) * (d : ℕ)))ˣ),
      (∀ d ∈ D, (a d : ZMod ((b : ℕ) * (d : ℕ))) = (a₀ : ZMod ((b : ℕ) * (d : ℕ)))) →
    ∀ (M : Finset ℤ), M ⊆ Finset.Ico 1 (1 + (N : ℤ)) →
    ∀ (η : ℕ → ℂ) (α : ℤ → ℂ) (E W T L H : ℝ),
      0 ≤ E → 0 ≤ W → 1 ≤ T → 0 ≤ L → 0 < H → H ≤ x ^ Kheight →
      (∀ d ∈ D, ‖η ((b : ℕ) * (d : ℕ))‖ ≤ E) → (∀ m ∈ M, ‖α m‖ ≤ W) →
    ∀ (ψ : ℝ → ℝ), ContDiff ℝ ∞ ψ → (∀ t : ℝ, 0 ≤ ψ t) →
      (∀ t ∈ Set.Icc (-1 : ℝ) 1, ψ t = 1) → Function.support ψ ⊆ Set.Icc (-T) T →
      (∀ t : ℝ, ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L) →
      selectedKloostermanL1 b (b₁ * b₂ * b₃) D a M η α H ^ 2 ≤
        (T * L) * (E * W) ^ 2 * x ^ κ * H * fiveScale N (Qhi / (b : ℝ)) S ((b : ℝ) * Y) H := by
  obtain ⟨X, hX, hpower⟩ := hlocal.exists_selected_kernel_power_estimate hC hheight hκ
  refine ⟨X, hX, ?_⟩
  intro x hx b b₁ b₂ b₃ hb₁ hb₂ hb₃ hb Y Qlo Qhi S hQlo hQhi hS hSrange hQX hSX
    D hD N hN hNX a₀ a ha M hM η α E W T L H hE hW hT hL hH hHX hη hα
    ψ hψ hψnonneg hψone hsupp hψbound
  obtain ⟨ρ, σ, hselected⟩ := typeIII_dense_factor_selection b Y D Qlo Qhi S hQlo hQhi hS hSrange hD
  have hbpos : (0 : ℝ) < b := by exact_mod_cast b.pos
  have hYpos : 0 < (Y : ℝ) := zero_lt_one.trans_le Y.property
  apply hpower x hx b b₁ b₂ b₃ hb₁ hb₂ hb₃ hb D (fun d hd => (hD d hd).1)
    ρ σ (fun d hd => (hselected d hd).1) N hN hNX (Qhi / (b : ℝ)) S ((b : ℝ) * Y)
    (div_pos (hQlo.trans_le hQhi) hbpos) hQX hS hSX (mul_pos hbpos hYpos)
    (fun d hd => (le_div_iff₀' hbpos).mpr (hD d hd).2.2.2) ?_
    a₀ a ha M hM η α E W T L H hE hW hT hL hH hHX hη hα
    ψ hψ hψnonneg hψone hsupp hψbound
  intro d hd
  obtain ⟨_, _, _, _, _, hlo, hhi, _, _⟩ := hselected d hd
  exact ⟨hlo, hhi⟩

#print axioms LocalFourierHypothesis.exists_dense_kernel_power_estimate

end

end PrimeGap182.TypeIII
