import PrimeGaps186
import TypeIIILocal

/-!
# Exact bridge to the public 186 finite-field sums

The conditional theorems use the exact two public local statements as hypotheses. The final
entrywise corollary instantiates them with the public axioms and therefore reports those two
axioms, explicitly. No new exceptional-Fourier input is needed for the entrywise estimate.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

/-- The two precise finite-field statements exposed by the public 186 development. -/
def BaselineLocalInputs : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (c : ZMod p),
    c ≠ 0 → ‖PrimeGap186.normalizedKloosterman3 p c‖ ≤ (3 : ℝ)) ∧
  (∀ (p : ℕ) [Fact p.Prime] (A B : ZMod p),
    A ≠ 0 → B ≠ 0 →
      ‖∑ t : ZMod p, if t ≠ 0 ∧ t ≠ -1 then
        PrimeGap186.unnormalizedKloosterman2 p (A / t) *
          PrimeGap186.unnormalizedKloosterman2 p (B / (t + 1)) else 0‖ ≤
        8 * (p : ℝ) * Real.sqrt (p : ℝ))

variable (p : ℕ) [Fact p.Prime]

/-- Equality of the actual sums, at every argument, including zero. -/
theorem kl3_eq_baseline (t : ZMod p) :
    kl3 p t = PrimeGap186.normalizedKloosterman3 p t := by
  rw [PrimeGap186.normalizedKloosterman3_eq_doubleUnitSum]
  simp only [kl3, PrimeGap186.reciprocalProductCompleteSum, one_mul,
    add_comm, add_left_comm, add_assoc]

/-- The exact zero-frequency identity, with the full constant correction. -/
theorem correlation_zero (A B : ZMod p) (hA : A ≠ 0) (hB : B ≠ 0) :
    correlation p A B 0 =
      (if A = B then (p : ℂ) else 0) - 1 - (p : ℂ)⁻¹ - ((p : ℂ)⁻¹) ^ 2 := by
  simp only [correlation, kl3_eq_baseline, zero_mul, AddChar.map_zero_eq_one, mul_one]
  exact PrimeGap186.normalizedKloosterman3_unit_correlation_zero p A B hA hB

/-- The existing local inputs bound the actual pair correlation at nonzero frequency. -/
theorem correlation_norm_le_of_baseline_inputs (hDeligne : BaselineLocalInputs)
    (A B c : ZMod p) (hA : A ≠ 0) (hB : B ≠ 0) (hc : c ≠ 0) :
    ‖correlation p A B c‖ ≤ 9 * Real.sqrt (p : ℝ) := by
  have hh := (PrimeGap186.normalizedKloosterman3_prime_local_bounds_of_deligne
    hDeligne p).2.2 A B c hA hB
  simpa only [correlation, kl3_eq_baseline, hc, false_and, ite_false] using hh

/-- The actual matrix-entry bound from the existing public inputs. -/
theorem kernel_norm_le_of_baseline_inputs (hDeligne : BaselineLocalInputs)
    (α m n r₁ r₂ : ZMod p) (hα : α ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0) :
    ‖kernel p α m n r₁ r₂‖ ≤ 9 * Real.sqrt (p : ℝ) := by
  apply kernel_norm_le_of_correlation p
    (fun A B hA hB => correlation_norm_le_of_baseline_inputs p hDeligne A B 1 hA hB
      one_ne_zero) α m n r₁ r₂ hα hm hn

/-- This wrapper uses exactly the two already-declared public finite-field axioms.
It does not prove the new finite-exceptional Fourier hypothesis. -/
theorem kernel_norm_le_from_public_inputs
    (α m n r₁ r₂ : ZMod p) (hα : α ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0) :
    ‖kernel p α m n r₁ r₂‖ ≤ 9 * Real.sqrt (p : ℝ) :=
  kernel_norm_le_of_baseline_inputs p
    ⟨PrimeGap186.kloosterman3_bound, PrimeGap186.kloosterman2_correlation_bound⟩
    α m n r₁ r₂ hα hm hn

#print axioms kl3_eq_baseline
#print axioms correlation_zero
#print axioms correlation_norm_le_of_baseline_inputs
#print axioms kernel_norm_le_of_baseline_inputs
#print axioms kernel_norm_le_from_public_inputs

end

end PrimeGap182.TypeIII
