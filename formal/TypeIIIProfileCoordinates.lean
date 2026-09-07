import TypeIIIResidualProfile

/-! Exact natural-number coordinates for the whole signed residual profile mass. -/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

def guardedProfilePairMass (a : ℤ) (M s g u v : ℕ)
    (α β : IntegerIntervalIndex 1 M → ℂ) (T H t₀ : ℝ) (ψ : ℝ → ℂ) : ℝ :=
  if hsg : s * g ≠ 0 then
    letI : NeZero (s * g) := ⟨hsg⟩
    if hu : u ≠ 0 then
      letI : NeZero u := ⟨hu⟩
      if hv : v ≠ 0 then
        letI : NeZero v := ⟨hv⟩
        if Squarefree (s * g) ∧ IsUnit (a : ZMod (s * g)) then
          if SharedOuterAdmissible (s * g) a u v then
            ‖sharedProfileCoefficientSum u v (s * g) a 1 1 M M α β T H t₀ ψ‖
          else 0
        else 0
      else 0
    else 0
  else 0

theorem guardedProfilePairMass_nonneg (a : ℤ) (M s g u v : ℕ)
    (α β : IntegerIntervalIndex 1 M → ℂ) (T H t₀ : ℝ) (ψ : ℝ → ℂ) :
    0 ≤ guardedProfilePairMass a M s g u v α β T H t₀ ψ := by
  unfold guardedProfilePairMass
  split_ifs
  · exact norm_nonneg _
  all_goals exact le_rfl

theorem guardedProfilePairMass_eq (a : ℤ) (M s g u v : ℕ)
    [NeZero s] [NeZero g] [NeZero u] [NeZero v]
    (α β : IntegerIntervalIndex 1 M → ℂ) (T H t₀ : ℝ) (ψ : ℝ → ℂ) :
    guardedProfilePairMass a M s g u v α β T H t₀ ψ =
      if Squarefree (s * g) ∧ IsUnit (a : ZMod (s * g)) then
        if SharedOuterAdmissible (s * g) a u v then
          ‖sharedProfileCoefficientSum u v (s * g) a 1 1 M M α β T H t₀ ψ‖
        else 0
      else 0 := by
  unfold guardedProfilePairMass
  rw [dite_eq_left (mul_ne_zero (NeZero.ne s) (NeZero.ne g)),
    dite_eq_left (NeZero.ne u), dite_eq_left (NeZero.ne v)]

/-- The interval-based actual profile mass equals its natural residual coordinates. -/
theorem admissibleResidualProfileMass_eq_sum (a : ℤ) (M R s g : ℕ)
    (hR : 0 < R) (hs : 0 < s) (hg : 0 < g)
    (α β : ℕ → ℕ → IntegerIntervalIndex 1 M → ℂ)
    (T H t₀ : ℝ) (ψ : ℝ → ℂ) :
    admissibleResidualProfileMass a M R s g α β T H t₀ ψ =
      ∑ u ∈ residualRange R g, ∑ v ∈ residualRange R g,
        guardedProfilePairMass a M s g u v (α u v) (β u v) T H t₀ ψ := by
  let : NeZero s := ⟨hs.ne'⟩
  let : NeZero g := ⟨hg.ne'⟩
  let U := residualStart R g
  let N := residualLength R g
  have hre : (∑ u ∈ residualRange R g, ∑ v ∈ residualRange R g,
        guardedProfilePairMass a M s g u v (α u v) (β u v) T H t₀ ψ) =
      ∑ x ∈ Finset.range N, ∑ y ∈ Finset.range N,
        guardedProfilePairMass a M s g (positiveOuterIndex U x) (positiveOuterIndex U y)
          (α (positiveOuterIndex U x) (positiveOuterIndex U y))
          (β (positiveOuterIndex U x) (positiveOuterIndex U y)) T H t₀ ψ := by
    rw [sum_residualRange_eq_sum_range R g hR hg]
    apply Finset.sum_congr rfl
    intro x _
    rw [sum_residualRange_eq_sum_range R g hR hg]
    rfl
  rw [hre]
  simp_rw [guardedProfilePairMass_eq]
  unfold admissibleResidualProfileMass
  rw [dite_eq_left (mul_ne_zero hs.ne' hg.ne')]
  by_cases hgood : Squarefree (s * g) ∧ IsUnit (a : ZMod (s * g))
  · simp only [ite_eq_left hgood, residualProfileFullMass, U, N]
  · simp only [ite_eq_right hgood, Finset.sum_const_zero]

#print axioms guardedProfilePairMass_eq
#print axioms admissibleResidualProfileMass_eq_sum

end

end PrimeGap182.TypeIII
