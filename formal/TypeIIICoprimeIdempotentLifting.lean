import Mathlib.Algebra.Ring.Idempotent
import Mathlib.RingTheory.Coprime.Basic

/-!
# Idempotents from an actual coprime zero product

A Bézout identity for two factors whose product is zero gives an
idempotent.  The original ring homomorphism carries that idempotent to
a prescribed target element when the two factors act on that element
as the identity and zero, respectively.

The power specialization applies to factors reducing to e^N and
(e-1)^N for a positive N and an actual idempotent e.  The existence of
those factors is an explicit input here; the henselian factorization
and finite-algebra annihilator constructions supply it separately.
-/

universe u v

namespace PrimeGap182.TypeIII.CoprimeIdempotentLifting

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- The actual Bézout coefficients give an idempotent with the
specified image under the original coefficient homomorphism. -/
theorem exists_lift (r : A →+* B) (e : B) {f g : A}
    (hcop : IsCoprime f g) (hfg : f * g = 0)
    (hf : r f * e = r f) (hg : r g * e = 0) :
    ∃ a : A, IsIdempotentElem a ∧ r a = e := by
  obtain ⟨u, v, huv⟩ := hcop
  have hprod : (u * f) * (v * g) = 0 := by
    rw [mul_mul_mul_comm, hfg, mul_zero]
  refine ⟨u * f, (IsIdempotentElem.of_mul_add hprod huv).1, ?_⟩
  have h := congrArg (fun a : A => r a * e) huv
  simp only [map_add, map_mul, map_one, add_mul, mul_assoc, hf, hg,
    mul_zero, add_zero, one_mul] at h
  simpa only [map_mul] using h

/-- Positive powers of an idempotent and its difference from one
have exactly the actions required by the original Bézout construction. -/
theorem exists_lift_of_powers (r : A →+* B) (e : B) {f g : A}
    (hcop : IsCoprime f g) (hfg : f * g = 0)
    (N : ℕ) (hN : 0 < N) (he : IsIdempotentElem e)
    (hf : r f = e ^ N) (hg : r g = (e - 1) ^ N) :
    ∃ a : A, IsIdempotentElem a ∧ r a = e := by
  apply exists_lift r e hcop hfg
  · rw [hf, he.pow_eq hN.ne', he.eq]
  · rw [hg]
    calc
      (e - 1) ^ N * e = (e - 1) ^ N * e ^ N := by rw [he.pow_eq hN.ne']
      _ = ((e - 1) * e) ^ N := (mul_pow _ _ _).symm
      _ = 0 := by rw [sub_mul, he.eq, one_mul, sub_self, zero_pow hN.ne']

#print axioms exists_lift
#print axioms exists_lift_of_powers

end PrimeGap182.TypeIII.CoprimeIdempotentLifting
