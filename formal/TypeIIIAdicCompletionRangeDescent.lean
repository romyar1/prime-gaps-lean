import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Original preimages for maps out of an adic completion

If a power of a finitely generated ideal annihilates the target of a
linear map from an adic completion, every value of that map already
comes from the original module. The proof uses the original completion
map and evaluation map, together with Mathlib's proved evaluation-kernel
identity. It imposes no surjectivity or range premise on the linear map.

The coefficient ring and the two modules have independent universes.
No nontriviality, Noetherian, finite-module, or completeness assumptions
are needed. This file proves only the algebraic range statement; it
does not construct a comparison with sections on infinitesimal schemes.
-/

universe u v w

namespace PrimeGap182.TypeIII

variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]
  (I : Ideal R) (n : ℕ) (L : AdicCompletion I M →ₗ[R] N)

/-- Equal evaluations modulo `I ^ n` have equal images under the
original map whenever `I ^ n` annihilates its target. -/
theorem adicCompletion_map_eq_of_eval_eq (hI : I.FG)
    (hN : I ^ n • (⊤ : Submodule R N) = ⊥)
    {x y : AdicCompletion I M}
    (hxy : AdicCompletion.eval I M n x = AdicCompletion.eval I M n y) :
    L x = L y := by
  have hkill : I ^ n • (⊤ : Submodule R (AdicCompletion I M)) ≤ L.ker := by
    refine Submodule.smul_le.mpr ?_
    intro r hr z _hz
    rw [LinearMap.mem_ker, map_smul]
    have hz : r • L z ∈ I ^ n • (⊤ : Submodule R N) :=
      Submodule.smul_mem_smul hr Submodule.mem_top
    simpa only [hN, Submodule.mem_bot] using hz
  have hker : x - y ∈ (AdicCompletion.eval I M n).ker := by
    rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
  rw [← AdicCompletion.pow_smul_top_eq_ker_eval (M := M) (n := n) hI] at hker
  have hzero : L (x - y) = 0 := hkill hker
  simpa only [map_sub, sub_eq_zero] using hzero

/-- Every value of the original map on the completion has a preimage
from the original module, with its original completion map. -/
theorem adicCompletion_exists_original_preimage (hI : I.FG)
    (hN : I ^ n • (⊤ : Submodule R N) = ⊥) (x : AdicCompletion I M) :
    ∃ m : M, L (AdicCompletion.of I M m) = L x := by
  obtain ⟨m, hm⟩ := (I ^ n • (⊤ : Submodule R M)).mkQ_surjective
    (AdicCompletion.eval I M n x)
  refine ⟨m, adicCompletion_map_eq_of_eval_eq I n L hI hN ?_⟩
  change ((AdicCompletion.eval I M n).comp (AdicCompletion.of I M)) m =
    AdicCompletion.eval I M n x
  rw [AdicCompletion.eval_comp_of]
  exact hm

/-- Restricting the original map along the original completion map
does not change its range when a power of `I` annihilates the target. -/
theorem adicCompletion_range_comp_of_eq (hI : I.FG)
    (hN : I ^ n • (⊤ : Submodule R N) = ⊥) :
    LinearMap.range (L.comp (AdicCompletion.of I M)) = LinearMap.range L := by
  apply le_antisymm
  · rintro y ⟨m, rfl⟩
    exact ⟨AdicCompletion.of I M m, rfl⟩
  · rintro y ⟨x, rfl⟩
    obtain ⟨m, hm⟩ := adicCompletion_exists_original_preimage I n L hI hN x
    exact ⟨m, hm⟩

/-- The original-preimage result at the first infinitesimal level. -/
theorem adicCompletion_exists_original_preimage_one (hI : I.FG)
    (hN : I • (⊤ : Submodule R N) = ⊥) (x : AdicCompletion I M) :
    ∃ m : M, L (AdicCompletion.of I M m) = L x :=
  adicCompletion_exists_original_preimage I 1 L hI (by simpa only [pow_one] using hN) x

/-- The range of the original map is already obtained from `M` when
the ideal itself annihilates the target. -/
theorem adicCompletion_range_comp_of_eq_one (hI : I.FG)
    (hN : I • (⊤ : Submodule R N) = ⊥) :
    LinearMap.range (L.comp (AdicCompletion.of I M)) = LinearMap.range L :=
  adicCompletion_range_comp_of_eq I 1 L hI (by simpa only [pow_one] using hN)

#print axioms adicCompletion_map_eq_of_eval_eq
#print axioms adicCompletion_exists_original_preimage
#print axioms adicCompletion_range_comp_of_eq
#print axioms adicCompletion_exists_original_preimage_one
#print axioms adicCompletion_range_comp_of_eq_one

end PrimeGap182.TypeIII
