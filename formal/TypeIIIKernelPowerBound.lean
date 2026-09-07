import TypeIIIDyadicKernelBound
import TypeIIIHeightLoss

/-! The actual selected Kloosterman sum with a uniformly arbitrarily small power loss. -/

open scoped BigOperators Classical ContDiff
open PrimeGap186 UniqueFactorizationMonoid Filter

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem LocalFourierHypothesis.exists_selected_kernel_power_estimate
    {C : ℝ} (hC : 0 ≤ C) {D₀ p₀ : ℕ} (hlocal : LocalFourierHypothesis C D₀ p₀)
    {Kheight κ : ℝ} (hheight : 0 < Kheight) (hκ : 0 < κ) :
    ∃ X : ℝ, 2 ≤ X ∧ ∀ x : ℝ, X ≤ x →
    ∀ (b : ℕ+) (b₁ b₂ b₃ : ℕ), 0 < b₁ → 0 < b₂ → 0 < b₃ →
      (b : ℕ) = (radical (b₁ * b₂ * b₃) : ℕ) →
    ∀ (D : Finset ℕ+), (∀ d ∈ D, Squarefree ((b : ℕ) * (d : ℕ))) →
    ∀ (ρ σ : ℕ+ → ℕ+), (∀ d ∈ D, d = ρ d * σ d) →
    ∀ (N : ℕ), 0 < N → (N : ℝ) ≤ x ^ Kheight →
    ∀ Q S y : ℝ, 0 < Q → Q ≤ x ^ Kheight → 1 ≤ S → S ≤ x ^ Kheight → 0 < y →
      (∀ d ∈ D, (d : ℝ) ≤ Q) →
      (∀ d ∈ D, S / y ≤ (σ d : ℝ) ∧ (σ d : ℝ) ≤ S) →
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
        (T * L) * (E * W) ^ 2 * x ^ κ * H * fiveScale N Q S y H := by
  let ε : ℝ := κ / (4 * (5 * Kheight + 10))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hquarter : 0 < κ / 4 := by positivity
  obtain ⟨K, hK, hkernel⟩ := hlocal.exists_dyadic_kernel_square_estimate hC hε
  obtain ⟨Xcard, hXcard, hcard⟩ := exists_dyadicFactorCells_sq_rpow hheight hquarter
  obtain ⟨Xfirst, _, hfirst⟩ := exists_firstMomentLogBound_rpow hheight hquarter
  obtain ⟨Xconstant, hconstant⟩ :=
    ((tendsto_rpow_atTop hquarter).eventually_ge_atTop K).exists_forall_of_atTop
  refine ⟨max Xcard (max Xfirst Xconstant), hXcard.trans (le_max_left _ _), ?_⟩
  intro x hx b b₁ b₂ b₃ hb₁ hb₂ hb₃ hb D hD ρ σ hfactor N hN hNX Q S y hQ hQX hS hSX
    hy hDQ hσ a₀ a ha M hM η α E W T L H hE hW hT hL hH hHX hη hα
    ψ hψ hψnonneg hψone hsupp hψbound
  have hxcard : Xcard ≤ x := (le_max_left _ _).trans hx
  have hxfirst : Xfirst ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxconstant : Xconstant ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hx2 : 2 ≤ x := hXcard.trans hxcard
  have hx0 : 0 < x := by linarith
  have hcb := hcard x hxcard D ρ σ hfactor (fun d hd => (hDQ d hd).trans hQX)
  have hfb := hfirst x hxfirst H S hH hHX hS hSX
  have hkb := hconstant x hxconstant
  have hsb : selectionSubpower N Q ε ≤ x ^ (κ / 4) := by
    have hh := selectionSubpower_le_rpow hx2 hheight.le (Nat.cast_nonneg N) hQ.le hNX hQX hε.le
    apply hh.trans_eq
    congr 1
    dsimp only [ε]
    field_simp
  have hbound := hkernel b b₁ b₂ b₃ hb₁ hb₂ hb₃ hb D hD ρ σ hfactor N hN Q S y
    hQ hS hy hDQ hσ a₀ a ha M hM η α E W T L H hE hW hT hL hH hη hα
    ψ hψ hψnonneg hψone hsupp hψbound
  have hlog : 0 ≤ firstMomentLogBound H (2 * S) := by
    have hlogS : 0 ≤ Real.log (2 * S) := Real.log_nonneg (by linarith : 1 ≤ 2 * S)
    have hlogH : 0 ≤ Real.log (max 1 H) := Real.log_nonneg (le_max_left _ _)
    unfold firstMomentLogBound
    positivity
  have hsp := selectionSubpower_nonneg (Nat.cast_nonneg N) hQ.le (ε := ε)
  have h₁ := mul_le_mul hcb hkb hK.le (by positivity)
  have h₂ := mul_le_mul hfb hsb hsp (by positivity)
  have h₃ := mul_le_mul h₁ h₂ (mul_nonneg hlog hsp) (by positivity)
  have hloss : (((dyadicFactorCells D ρ σ).card : ℝ) ^ 2 * K) *
      (firstMomentLogBound H (2 * S) * selectionSubpower N Q ε) ≤ x ^ κ * H := by
    apply h₃.trans_eq
    calc
      _ = (x ^ (κ / 4)) ^ 4 * H := by ring
      _ = x ^ ((κ / 4) * 4) * H := by
        rw [← Real.rpow_mul_natCast hx0.le]
        norm_num only [Nat.cast_ofNat]
      _ = _ := by congr 2; ring
  have hT₀ := zero_le_one.trans hT
  have hpf : 0 ≤ (T * L) * (E * W) ^ 2 * fiveScale N Q S y H :=
    mul_nonneg (by positivity) (fiveScale_nonneg (Nat.cast_nonneg N) hQ.le
      (zero_le_one.trans hS) hy.le hH.le)
  calc
    _ ≤ ((dyadicFactorCells D ρ σ).card : ℝ) ^ 2 * K * (T * L) * (E * W) ^ 2 *
        firstMomentLogBound H (2 * S) * selectionSubpower N Q ε * fiveScale N Q S y H := hbound
    _ = ((T * L) * (E * W) ^ 2 * fiveScale N Q S y H) *
        ((((dyadicFactorCells D ρ σ).card : ℝ) ^ 2 * K) *
          (firstMomentLogBound H (2 * S) * selectionSubpower N Q ε)) := by ring
    _ ≤ ((T * L) * (E * W) ^ 2 * fiveScale N Q S y H) * (x ^ κ * H) :=
      mul_le_mul_of_nonneg_left hloss hpf
    _ = _ := by ring

#print axioms LocalFourierHypothesis.exists_selected_kernel_power_estimate

end

end PrimeGap182.TypeIII
