import TypeIIIPrimitiveRamificationFromGeneralKatzTheory

/-!
# Natural Swan conductor from the same finite upper-break profile

Each break component has a nonnegative integral Swan contribution by the
existing general break-profile data. Its finite sum therefore defines a
natural conductor. Isoclinic support computes the conductor as slope times
profile rank. These are finite arithmetic applications only; identifying a
chosen local profile with a continuous-inertia sheaf remains external.
-/
noncomputable section
open scoped Classical BigOperators

namespace PrimeGap182.TypeIII.NaturalSwanFromFiniteBreakProfile
open PrimitiveRamificationFromGeneralKatzTheory

/-- The sum of the existing integral component conductors is integral. -/
theorem swan_integral (b : BreakProfile) : ∃ n : ℕ, (n : ℚ) = b.swan := by
  classical
  let component (r : ℚ) : ℕ := if hr : r ∈ b.multiplicity.support then
    Classical.choose (b.integral r hr) else 0
  refine ⟨∑ r ∈ b.multiplicity.support, component r, ?_⟩
  simp only [Nat.cast_sum, BreakProfile.swan]
  apply Finset.sum_congr rfl
  intro r hr
  dsimp only [component]
  rw [dite_eq_left hr]
  exact Classical.choose_spec (b.integral r hr)

/-- A computed natural conductor of the actual supplied finite profile. -/
def naturalSwan (b : BreakProfile) : ℕ := Classical.choose (swan_integral b)

/-- The natural conductor has exactly the original rational Swan value. -/
theorem naturalSwan_cast (b : BreakProfile) : (naturalSwan b : ℚ) = b.swan :=
  Classical.choose_spec (swan_integral b)

/-- Every single-slope profile has Swan equal to slope times profile rank. -/
theorem swan_of_isoclinic (b : BreakProfile) (s : ℚ)
    (h : ∀ r ∈ b.multiplicity.support, r = s) : b.swan = s * (b.rank : ℚ) := by
  calc
    b.swan = ∑ r ∈ b.multiplicity.support, s * (b.multiplicity r : ℚ) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [h r hr]
    _ = s * ∑ r ∈ b.multiplicity.support, (b.multiplicity r : ℚ) :=
      (Finset.mul_sum _ _ _).symm
    _ = s * (b.rank : ℚ) := by simp only [BreakProfile.rank, Nat.cast_sum]

/-- Slope one computes the natural conductor as the same profile rank. -/
theorem naturalSwan_of_isoclinic_one (b : BreakProfile)
    (h : ∀ r ∈ b.multiplicity.support, r = 1) : naturalSwan b = b.rank := by
  apply Nat.cast_injective (R := ℚ)
  rw [naturalSwan_cast, swan_of_isoclinic b 1 h, one_mul]

/-- A profile supported at the tame break has zero natural conductor. -/
theorem naturalSwan_of_tame_support (b : BreakProfile)
    (h : ∀ r ∈ b.multiplicity.support, r = 0) : naturalSwan b = 0 := by
  apply Nat.cast_injective (R := ℚ)
  rw [naturalSwan_cast, swan_of_isoclinic b 0 h, zero_mul, Nat.cast_zero]

end PrimeGap182.TypeIII.NaturalSwanFromFiniteBreakProfile
