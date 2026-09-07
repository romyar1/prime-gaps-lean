import TypeIIIResidualRanges

/-! Exact finite gcd coordinates for the selected outer pairs. -/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The positive gcd coordinates of an ordered pair. -/
def gcdPairIndex (p : ℕ+ × ℕ+) : Σ _g : ℕ, ℕ × ℕ :=
  ⟨Nat.gcd (p.1 : ℕ) (p.2 : ℕ),
    (p.1 : ℕ) / Nat.gcd (p.1 : ℕ) (p.2 : ℕ),
    (p.2 : ℕ) / Nat.gcd (p.1 : ℕ) (p.2 : ℕ)⟩

theorem gcdPairIndex_left (p : ℕ+ × ℕ+) :
    (gcdPairIndex p).1 * (gcdPairIndex p).2.1 = (p.1 : ℕ) := by
  dsimp only [gcdPairIndex]
  rw [mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)]

theorem gcdPairIndex_right (p : ℕ+ × ℕ+) :
    (gcdPairIndex p).1 * (gcdPairIndex p).2.2 = (p.2 : ℕ) := by
  dsimp only [gcdPairIndex]
  rw [mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)]

theorem gcdPairIndex_injective : Function.Injective gcdPairIndex := by
  intro p q hpq
  apply Prod.ext
  · apply PNat.coe_injective
    exact (gcdPairIndex_left p).symm.trans
      ((congrArg (fun t : Σ _g : ℕ, ℕ × ℕ => t.1 * t.2.1) hpq).trans
        (gcdPairIndex_left q))
  · apply PNat.coe_injective
    exact (gcdPairIndex_right p).symm.trans
      ((congrArg (fun t : Σ _g : ℕ, ℕ × ℕ => t.1 * t.2.2) hpq).trans
        (gcdPairIndex_right q))

theorem gcdPairIndex_mem (R : ℕ) (p : ℕ+ × ℕ+)
    (h₁ : R ≤ (p.1 : ℕ) ∧ (p.1 : ℕ) ≤ 2 * R)
    (h₂ : R ≤ (p.2 : ℕ) ∧ (p.2 : ℕ) ≤ 2 * R) :
    gcdPairIndex p ∈ (Finset.Icc 1 (2 * R)).sigma
      (fun g => residualRange R g ×ˢ residualRange R g) := by
  have hg : 0 < Nat.gcd (p.1 : ℕ) (p.2 : ℕ) := Nat.gcd_pos_of_pos_left _ p.1.pos
  refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hg, ?_⟩,
    Finset.mem_product.mpr ⟨?_, ?_⟩⟩
  · exact (Nat.gcd_le_left _ p.1.pos).trans h₁.2
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.div_gcd_pos_of_pos_left _ p.1.pos,
      Nat.div_le_div_right h₁.2⟩, ?_⟩
    exact h₁.1.trans_eq (gcdPairIndex_left p).symm
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.div_gcd_pos_of_pos_right _ p.2.pos,
      Nat.div_le_div_right h₂.2⟩, ?_⟩
    exact h₂.1.trans_eq (gcdPairIndex_right p).symm

/-- A nonnegative outer mass can be enlarged to exactly the residual intervals.
The injection preserves the complete inner signed block; it introduces no rowwise norms. -/
theorem selected_pair_sum_le_gcd_residual (R : ℕ) (Rs : Finset ℕ+)
    (hRs : ∀ r ∈ Rs, R ≤ (r : ℕ) ∧ (r : ℕ) ≤ 2 * R)
    (f : ℕ+ → ℕ+ → ℝ) (F : ℕ → ℕ → ℕ → ℝ)
    (hF : ∀ g ∈ Finset.Icc 1 (2 * R), ∀ u ∈ residualRange R g,
      ∀ v ∈ residualRange R g, 0 ≤ F g u v)
    (hbound : ∀ r₁ ∈ Rs, ∀ r₂ ∈ Rs,
      f r₁ r₂ ≤ F (Nat.gcd (r₁ : ℕ) (r₂ : ℕ))
        ((r₁ : ℕ) / Nat.gcd (r₁ : ℕ) (r₂ : ℕ))
        ((r₂ : ℕ) / Nat.gcd (r₁ : ℕ) (r₂ : ℕ))) :
    (∑ r₁ ∈ Rs, ∑ r₂ ∈ Rs, f r₁ r₂) ≤
      ∑ g ∈ Finset.Icc 1 (2 * R), ∑ u ∈ residualRange R g,
        ∑ v ∈ residualRange R g, F g u v := by
  have hh := Finset.sum_le_sum_of_injOn
    (s := Rs ×ˢ Rs)
    (t := (Finset.Icc 1 (2 * R)).sigma (fun g => residualRange R g ×ˢ residualRange R g))
    (f := fun p : ℕ+ × ℕ+ => f p.1 p.2)
    (g := fun t : Σ _g : ℕ, ℕ × ℕ => F t.1 t.2.1 t.2.2)
    gcdPairIndex gcdPairIndex_injective.injOn
    (by
      rintro t ht
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hp
      exact gcdPairIndex_mem R p (hRs p.1 h₁) (hRs p.2 h₂))
    (by
      intro p hp
      obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hp
      exact hbound p.1 h₁ p.2 h₂)
    (by
      intro t ht _
      obtain ⟨hg, huv⟩ := Finset.mem_sigma.mp ht
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
      exact hF t.1 hg t.2.1 hu t.2.2 hv)
  simpa only [Finset.sum_product, Finset.sum_sigma] using hh

#print axioms gcdPairIndex_injective
#print axioms selected_pair_sum_le_gcd_residual

end

end PrimeGap182.TypeIII
