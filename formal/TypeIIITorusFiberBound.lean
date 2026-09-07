import TypeIIITraceIdentity

/-!
# Fiber bounds for the exact Type III torus map

Every fiber of the monomial map (x,y) ↦ (y/x²,x/y²) on unit pairs
has at most three elements.  Its first coordinate is determined by a cubic,
and its second coordinate is then uniquely determined.  The resulting
finite-sum estimate transfers absolute error bounds through this map for
every prime, without assuming that cubing is a permutation.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- A fiber of the exact monomial map, with both coordinates units. -/
def exactUnitTorusFiber (ab : (ZMod p)ˣ × (ZMod p)ˣ) :
    Finset ((ZMod p)ˣ × (ZMod p)ˣ) :=
  Finset.univ.filter (fun xy => exactUnitTorusMap p xy = ab)

/-- The first coordinate of any point in a torus fiber satisfies a cubic. -/
theorem exactUnitTorusMap_cubic_identity (xy : (ZMod p)ˣ × (ZMod p)ˣ) :
    (((exactUnitTorusMap p xy).1 : ZMod p) ^ 2 *
      ((exactUnitTorusMap p xy).2 : ZMod p)) * (xy.1 : ZMod p) ^ 3 = 1 := by
  simp only [exactUnitTorusMap, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
  field_simp

/-- The determinant-three torus map has fibers of size at most three,
including in characteristics two and three. -/
theorem exactUnitTorusMap_fiber_card_le_three (ab : (ZMod p)ˣ × (ZMod p)ˣ) :
    (exactUnitTorusFiber p ab).card ≤ 3 := by
  have hcard : (exactUnitTorusFiber p ab).card ≤
      (toricOriginCubicFiber p
        ((ab.1 : ZMod p) ^ 2 * (ab.2 : ZMod p)) (-1)).card := by
    apply Finset.card_le_card_of_injOn (f := Prod.fst)
    · intro xy hxy
      have hxy' := (Finset.mem_filter.mp hxy).2
      have h := exactUnitTorusMap_cubic_identity p xy
      rw [hxy'] at h
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [sub_eq_add_neg] using sub_eq_zero.mpr h
    · intro xy hxy uv huv hfirst
      refine Prod.ext hfirst ?_
      have h₁ := congrArg Prod.fst ((Finset.mem_filter.mp hxy).2)
      have h₂ := congrArg Prod.fst ((Finset.mem_filter.mp huv).2)
      change xy.2 / xy.1 ^ 2 = ab.1 at h₁
      change uv.2 / uv.1 ^ 2 = ab.1 at h₂
      have heq := h₁.trans h₂.symm
      rw [hfirst] at heq
      exact div_left_inj.mp heq
  exact hcard.trans (toricOriginCubicFiber_card_le_three p _ _
    (Or.inr (neg_ne_zero.mpr one_ne_zero)))

/-- An exact change of variables weighted by the cardinality of each fiber. -/
theorem sum_exactUnitTorusMap_eq_sum_fibers
    (g : ((ZMod p)ˣ × (ZMod p)ˣ) → ℝ) :
    (∑ xy, g (exactUnitTorusMap p xy)) =
      ∑ ab, ((exactUnitTorusFiber p ab).card : ℝ) * g ab := by
  simpa only [exactUnitTorusFiber, Finset.sum_const, nsmul_eq_mul] using
    (Finset.sum_fiberwise' Finset.univ (exactUnitTorusMap p) g).symm

/-- A nonnegative function increases its total mass by at most three
under pullback through the exact torus map. -/
theorem sum_exactUnitTorusMap_le_three
    (g : ((ZMod p)ˣ × (ZMod p)ˣ) → ℝ) (hg : ∀ ab, 0 ≤ g ab) :
    (∑ xy, g (exactUnitTorusMap p xy)) ≤ 3 * ∑ ab, g ab := by
  rw [sum_exactUnitTorusMap_eq_sum_fibers, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ab _
  apply mul_le_mul_of_nonneg_right ?_ (hg ab)
  exact_mod_cast exactUnitTorusMap_fiber_card_le_three p ab

/-- Arbitrary complex weights of norm at most one preserve the same
threefold bound for the absolute error after the nonlinear substitution. -/
theorem norm_sum_exactUnitTorusMap_mul_le_three
    (f w : ((ZMod p)ˣ × (ZMod p)ˣ) → ℂ)
    (hw : ∀ xy, ‖w xy‖ ≤ 1) :
    ‖∑ xy, f (exactUnitTorusMap p xy) * w xy‖ ≤ 3 * ∑ ab, ‖f ab‖ := by
  calc
    _ ≤ ∑ xy, ‖f (exactUnitTorusMap p xy)‖ := by
      apply norm_sum_le_of_le
      intro xy _
      rw [norm_mul]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hw xy) (norm_nonneg (f (exactUnitTorusMap p xy)))
    _ ≤ _ := sum_exactUnitTorusMap_le_three p (fun ab => ‖f ab‖)
      (fun ab => norm_nonneg (f ab))

end

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.exactUnitTorusFiber
#print axioms PrimeGap182.TypeIII.exactUnitTorusMap_cubic_identity
#print axioms PrimeGap182.TypeIII.exactUnitTorusMap_fiber_card_le_three
#print axioms PrimeGap182.TypeIII.sum_exactUnitTorusMap_eq_sum_fibers
#print axioms PrimeGap182.TypeIII.sum_exactUnitTorusMap_le_three
#print axioms PrimeGap182.TypeIII.norm_sum_exactUnitTorusMap_mul_le_three
