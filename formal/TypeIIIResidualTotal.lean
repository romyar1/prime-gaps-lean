import TypeIIIResidualNonzero
import TypeIIINonzeroSummation

/-!
# The actual completed nonzero contribution summed over shared factors and gcds

The two local subpower losses combine to `(R*s)^ε`, so the gcd summation remains
convergent. Every summand below is an actual compact-profile coefficient sum with
its zero frequency removed. Unsupported shared moduli contribute zero explicitly.
-/

open scoped BigOperators Classical ContDiff

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

/-- The actual nonzero mass, restricted to squarefree primitive shared moduli. -/
def admissibleResidualNonzeroMass (a A B : ℤ) (M R s g : ℕ)
    (α : ℕ → ℕ → IntegerIntervalIndex A M → ℂ)
    (β : ℕ → ℕ → IntegerIntervalIndex B M → ℂ) (T H t₀ : ℝ) (ψ : ℝ → ℂ) : ℝ :=
  if h : s * g ≠ 0 then
    letI : NeZero (s * g) := ⟨h⟩
    if Squarefree (s * g) ∧ IsUnit (a : ZMod (s * g)) then
      residualProfileNonzeroMass (s * g) a A B M R g α β T H t₀ ψ
    else 0
  else 0

theorem shared_subpower_loss_le (R s g S : ℕ) (hg : 0 < g) (hsS : s ≤ S)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ((R : ℝ) / (g : ℝ)) ^ ε * ((s * g : ℕ) : ℝ) ^ ε ≤
      ((R : ℝ) * (S : ℝ)) ^ ε := by
  rw [← Real.mul_rpow (by positivity : (0 : ℝ) ≤ (R : ℝ) / (g : ℝ))
    (Nat.cast_nonneg (s * g)), Nat.cast_mul]
  have he : (R : ℝ) / (g : ℝ) * ((s : ℝ) * (g : ℝ)) = (R : ℝ) * (s : ℝ) := by
    have hg' : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hg)
    field_simp
  rw [he]
  exact Real.rpow_le_rpow (by positivity)
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hsS) (Nat.cast_nonneg R)) hε

/-- The nonzero part of the actual signed residual correlations has the three stated
global scales. The bound is uniform in the gcd cutoff, including cutoffs larger than R. -/
theorem LocalFourierHypothesis.exists_residual_nonzero_total_estimate
    {C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ} (hlocal : LocalFourierHypothesis C D p₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a A B : ℤ) (M R S G : ℕ), 0 < M → 0 < R →
      ∀ (L₁ L₂ T L H t₀ : ℝ), 0 ≤ L₁ → 0 ≤ L₂ → 0 ≤ T → 0 ≤ L → 0 < H →
      ∀ (ψ : ℝ → ℂ), ContDiff ℝ ∞ ψ →
      Function.support ψ ⊆ Set.Icc (-T) T →
      (∀ t : ℝ, ‖ψ t‖ ≤ L ∧ ‖deriv ψ t‖ ≤ L ∧ ‖deriv (deriv ψ) t‖ ≤ L) →
      ∀ (α : ℕ → ℕ → ℕ → ℕ → IntegerIntervalIndex A M → ℂ)
        (β : ℕ → ℕ → ℕ → ℕ → IntegerIntervalIndex B M → ℂ),
      (∀ s ∈ Finset.Icc 1 S, ∀ g ∈ Finset.Icc 1 G,
        ∀ u ∈ residualRange R g, ∀ v ∈ residualRange R g, ∀ m, ‖α s g u v m‖ ≤ L₁) →
      (∀ s ∈ Finset.Icc 1 S, ∀ g ∈ Finset.Icc 1 G,
        ∀ u ∈ residualRange R g, ∀ v ∈ residualRange R g, ∀ n, ‖β s g u v n‖ ≤ L₂) →
      (∑ s ∈ Finset.Icc 1 S, ∑ g ∈ Finset.Icc 1 G,
        (s : ℝ) * admissibleResidualNonzeroMass a A B M R s g
          (α s g) (β s g) T H t₀ ψ) ≤
        K * (T * L) * (L₁ * L₂) * ((R : ℝ) * (S : ℝ)) ^ ε *
          nonzeroSGScale M R S := by
  obtain ⟨K₁, hK₁, hb⟩ := hlocal.exists_squarefree_residual_nonzero_estimate hC hε
  obtain ⟨K₂, hK₂, hsum⟩ := exists_nonzero_sg_sum_bound
  refine ⟨K₁ * K₂, mul_pos hK₁ hK₂, ?_⟩
  intro a A B M R S G hM hR L₁ L₂ T L H t₀ hL₁ hL₂ hT hL hH ψ hψ hsupp hbound α β hα hβ
  let F : ℝ := K₁ * (T * L) * (L₁ * L₂) * ((R : ℝ) * (S : ℝ)) ^ ε
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hpoint (s : ℕ) (hs : s ∈ Finset.Icc 1 S) (g : ℕ) (hg : g ∈ Finset.Icc 1 G) :
      admissibleResidualNonzeroMass a A B M R s g (α s g) (β s g) T H t₀ ψ ≤
        F * dyadicNonzeroScale M ((R : ℝ) / (g : ℝ)) ((s : ℝ) * (g : ℝ)) := by
    have hspos : 0 < s := (Finset.mem_Icc.mp hs).1
    have hgpos : 0 < g := (Finset.mem_Icc.mp hg).1
    have hsg : s * g ≠ 0 := mul_ne_zero (Nat.ne_of_gt hspos) (Nat.ne_of_gt hgpos)
    unfold admissibleResidualNonzeroMass
    rw [dite_eq_left hsg]
    let : NeZero (s * g) := ⟨hsg⟩
    split_ifs with hgood
    · have hh := hb (s * g) hgood.1 a A B hgood.2 M R g hR hgpos
        L₁ L₂ T L H t₀ hL₁ hL₂ hT hL hH ψ hψ hsupp hbound
        (α s g) (β s g) (hα s hs g hg) (hβ s hs g hg)
      apply hh.trans
      have hloss := shared_subpower_loss_le R s g S hgpos (Finset.mem_Icc.mp hs).2 hε.le
      have hd : 0 ≤ dyadicNonzeroScale M ((R : ℝ) / (g : ℝ)) ((s * g : ℕ) : ℝ) :=
        dyadicNonzeroScale_nonneg (Nat.cast_nonneg M) (by positivity) (Nat.cast_nonneg (s * g))
      have hh' := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hloss
          (show 0 ≤ K₁ * (T * L) * (L₁ * L₂) by positivity)) hd
      simpa only [F, Nat.cast_mul, mul_assoc] using hh'
    · exact mul_nonneg hF
        (dyadicNonzeroScale_nonneg (Nat.cast_nonneg M) (by positivity) (by positivity))
  calc
    _ ≤ ∑ s ∈ Finset.Icc 1 S, ∑ g ∈ Finset.Icc 1 G,
        (s : ℝ) * (F * dyadicNonzeroScale M ((R : ℝ) / (g : ℝ)) ((s : ℝ) * (g : ℝ))) := by
      exact Finset.sum_le_sum (fun s hs => Finset.sum_le_sum (fun g hg =>
        mul_le_mul_of_nonneg_left (hpoint s hs g hg) (Nat.cast_nonneg s)))
    _ = F * (∑ s ∈ Finset.Icc 1 S, ∑ g ∈ Finset.Icc 1 G,
        (s : ℝ) * dyadicNonzeroScale M ((R : ℝ) / (g : ℝ)) ((s : ℝ) * (g : ℝ))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ ≤ F * (K₂ * nonzeroSGScale M R S) := mul_le_mul_of_nonneg_left
      (hsum M R (Nat.cast_pos.mpr hM) (Nat.cast_pos.mpr hR) S G) hF
    _ = _ := by dsimp only [F]; ring

#print axioms shared_subpower_loss_le
#print axioms LocalFourierHypothesis.exists_residual_nonzero_total_estimate

end

end PrimeGap182.TypeIII
