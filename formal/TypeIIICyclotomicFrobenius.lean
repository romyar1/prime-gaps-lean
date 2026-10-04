import TypeIIICoefficientAutomorphism
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

/-!
# The cyclotomic coefficient action at primes above two

The Galois automorphism of the rational p-th cyclotomic field indexed by
two squares every p-th root and fixes every prime above two. The latter
property uses Mathlib's decomposition-group theorem; it is the input to
extending this same action continuously to the local coefficient field.
-/

noncomputable section
open scoped Pointwise

namespace PrimeGap182.TypeIII.CyclotomicFrobenius

open NumberField IsCyclotomicExtension.Rat

variable (p : ℕ) [Fact p.Prime] (hp : 3 < p)

include hp in
theorem two_coprime : Nat.Coprime 2 p :=
  ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega))).symm

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The explicit Galois element indexed by two. -/
def frobenius : Gal(K/ℚ) :=
  (galEquivZMod p K).symm (ZMod.unitOfCoprime 2 (two_coprime p hp))

theorem frobenius_root (ζ : K) (hζ : ζ ^ p = 1) :
    frobenius p hp K ζ = ζ ^ 2 := by
  have h := galEquivZMod_apply_of_pow_eq p K (frobenius p hp K) hζ
  simpa only [frobenius, MulEquiv.apply_symm_apply, ZMod.coe_unitOfCoprime,
    ZMod.val_natCast, Nat.mod_eq_of_lt (show 2 < p by omega)] using h

variable (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span {(2 : ℤ)})]

theorem frobenius_mem_stabilizer :
    frobenius p hp K ∈ MulAction.stabilizer Gal(K/ℚ) P := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have h := galEquivZMod_stabilizer p K 2 P (two_coprime p hp)
  have hmem : ZMod.unitOfCoprime 2 (two_coprime p hp) ∈
      (galEquivZMod p K).mapSubgroup (MulAction.stabilizer Gal(K/ℚ) P) := by
    rw [h]
    exact Subgroup.mem_zpowers _
  exact Subgroup.mem_map_equiv.mp hmem

theorem frobenius_fixes_prime : frobenius p hp K • P = P :=
  (MulAction.mem_stabilizer_iff).mp (frobenius_mem_stabilizer p hp K P)

end PrimeGap182.TypeIII.CyclotomicFrobenius

#print axioms PrimeGap182.TypeIII.CyclotomicFrobenius.two_coprime
#print axioms PrimeGap182.TypeIII.CyclotomicFrobenius.frobenius
#print axioms PrimeGap182.TypeIII.CyclotomicFrobenius.frobenius_root
#print axioms PrimeGap182.TypeIII.CyclotomicFrobenius.frobenius_mem_stabilizer
#print axioms PrimeGap182.TypeIII.CyclotomicFrobenius.frobenius_fixes_prime
