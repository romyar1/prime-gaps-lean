import TypeIIIOriginalCompletion

/-! Exact reindexing of the actual positive integer coefficient interval. -/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem positiveIntegerInterval_nonneg (M : ℕ) (m : IntegerIntervalIndex 1 M) :
    0 ≤ m.1 := le_trans (by norm_num) (Finset.mem_Ico.mp m.2).1

theorem positiveIntegerInterval_cast_toNat (M : ℕ) (m : IntegerIntervalIndex 1 M) :
    (m.1.toNat : ℤ) = m.1 := Int.toNat_of_nonneg (positiveIntegerInterval_nonneg M m)

/-- This reindexes the actual integer subtype, not merely its cardinality. -/
theorem sum_positiveIntegerInterval_toNat {E : Type*} [AddCommMonoid E]
    (M : ℕ) (f : ℕ → E) :
    (∑ m : IntegerIntervalIndex 1 M, f m.1.toNat) = ∑ m ∈ Finset.Icc 1 M, f m := by
  rw [Finset.sum_coe_sort (Finset.Ico (1 : ℤ) (1 + M)) (fun m : ℤ => f m.toNat)]
  symm
  apply Finset.sum_bij (fun (m : ℕ) _ => (m : ℤ))
  · intro m hm
    obtain ⟨hm₁, hm₂⟩ := Finset.mem_Icc.mp hm
    apply Finset.mem_Ico.mpr
    constructor
    · exact_mod_cast hm₁
    · have hm₂' : (m : ℤ) ≤ M := by exact_mod_cast hm₂
      omega
  · intro m _ n _ hmn
    exact_mod_cast hmn
  · intro m hm
    obtain ⟨hm₁, hm₂⟩ := Finset.mem_Ico.mp hm
    have hmnonneg : 0 ≤ m := le_trans (by norm_num) hm₁
    refine ⟨m.toNat, ?_, Int.toNat_of_nonneg hmnonneg⟩
    apply Finset.mem_Icc.mpr
    constructor
    · omega
    · omega
  · intro m _
    simp only [Int.toNat_natCast]

#print axioms sum_positiveIntegerInterval_toNat

end

end PrimeGap182.TypeIII
