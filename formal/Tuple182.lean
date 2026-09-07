import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! The literal 39 shifts in prime_gaps_182.tex, lines 447--449 of the
frozen source. The finite checks are replayed in the current kernel;
large-prime admissibility follows from cardinality. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace PrimeGap182Analytic

def tuple182 : Finset ℕ :=
  {0, 6, 14, 20, 24, 26, 30, 36, 42, 44, 50, 54, 62, 66, 72, 80, 84, 86, 92, 96,
    104, 110, 114, 120, 126, 132, 134, 140, 146, 150, 152, 156, 162, 164, 170, 174,
    176, 180, 182}

theorem tuple182_card : tuple182.card = 39 := by decide

theorem tuple182_endpoints : 0 ∈ tuple182 ∧ 182 ∈ tuple182 ∧
    ∀ h ∈ tuple182, h ≤ 182 := by decide

private theorem tuple182_small_primes :
    ∀ p : Fin 40, p.val.Prime → ∃ a : Fin p.val, ∀ h ∈ tuple182, h % p.val ≠ a.val := by
  decide

theorem tuple182_omits_residue (p : ℕ) (hp : p.Prime) :
    ∃ a : ℕ, a < p ∧ ∀ h ∈ tuple182, h % p ≠ a := by
  classical
  by_cases hsmall : p < 40
  · obtain ⟨a, ha⟩ := tuple182_small_primes ⟨p, hsmall⟩ hp
    exact ⟨a.val, a.isLt, ha⟩
  · have hc : (tuple182.image (fun h => h % p)).card < (Finset.range p).card := by
      have hle := Finset.card_image_le (s := tuple182) (f := fun h => h % p)
      rw [tuple182_card] at hle
      simpa only [Finset.card_range] using lt_of_le_of_lt hle (by omega : 39 < p)
    obtain ⟨a, ha, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    refine ⟨a, Finset.mem_range.mp ha, ?_⟩
    intro h hh heq
    exact hnot (Finset.mem_image.mpr ⟨h, hh, heq⟩)

theorem tuple182_admissible (p : ℕ) (hp : p.Prime) :
    ∃ a ∈ Finset.range p, a ∉ tuple182.image (fun h => h % p) := by
  classical
  obtain ⟨a, ha, hnot⟩ := tuple182_omits_residue p hp
  refine ⟨a, Finset.mem_range.mpr ha, ?_⟩
  rintro hmem
  obtain ⟨h, hh, heq⟩ := Finset.mem_image.mp hmem
  exact hnot h hh heq

#print axioms tuple182_card
#print axioms tuple182_endpoints
#print axioms tuple182_admissible

end PrimeGap182Analytic
