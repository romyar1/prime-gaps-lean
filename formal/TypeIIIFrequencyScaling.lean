import TypeIIICurveFibers

/-!
# Invertible rescaling of actual exceptional frequency sets

CRT rescales each local frequency by a unit.  These lemmas transport finite cardinality and
the proved bounded-vertical-fiber condition through that actual map.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

/-- Multiplication by an actual residue-ring unit. -/
def unitScale (s : ℕ) [NeZero s] (u : (ZMod s)ˣ) : ZMod s ≃ ZMod s where
  toFun x := (u : ZMod s) * x
  invFun x := (↑u⁻¹ : ZMod s) * x
  left_inv x := by simp only [← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by simp only [← mul_assoc, Units.mul_inv, one_mul]

@[simp] theorem unitScale_apply (s : ℕ) [NeZero s] (u : (ZMod s)ˣ) (x : ZMod s) :
    unitScale s u x = (u : ZMod s) * x := rfl

/-- The pullback of a frequency set under the unit scaling in both coordinates. -/
def scaledPairSet (s : ℕ) [NeZero s] (u : (ZMod s)ˣ)
    (E : Finset (ZMod s × ZMod s)) : Finset (ZMod s × ZMod s) :=
  Finset.univ.filter (fun z => ((u : ZMod s) * z.1, (u : ZMod s) * z.2) ∈ E)

@[simp] theorem mem_scaledPairSet (s : ℕ) [NeZero s] (u : (ZMod s)ˣ)
    (E : Finset (ZMod s × ZMod s)) (z : ZMod s × ZMod s) :
    z ∈ scaledPairSet s u E ↔ ((u : ZMod s) * z.1, (u : ZMod s) * z.2) ∈ E := by
  simp only [scaledPairSet, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem scaledPairSet_card (s : ℕ) [NeZero s] (u : (ZMod s)ˣ)
    (E : Finset (ZMod s × ZMod s)) : (scaledPairSet s u E).card = E.card := by
  apply Finset.card_equiv (Equiv.prodCongr (unitScale s u) (unitScale s u))
  rintro ⟨h, k⟩
  exact mem_scaledPairSet s u E (h, k)

theorem scaledPairSet_boundedVerticalFibers
    (s : ℕ) [NeZero s] (u : (ZMod s)ˣ) (D : ℕ)
    (E : Finset (ZMod s × ZMod s)) (hE : BoundedVerticalFibers s D E) :
    BoundedVerticalFibers s D (scaledPairSet s u E) := by
  obtain ⟨V, hV, hf⟩ := hE
  let V' := Finset.univ.filter (fun h : ZMod s => (u : ZMod s) * h ∈ V)
  have hVcard : V'.card = V.card := by
    apply Finset.card_equiv (unitScale s u)
    intro h
    simp only [V', Finset.mem_filter, Finset.mem_univ, true_and, unitScale_apply]
  refine ⟨V', hVcard.trans_le hV, ?_⟩
  intro h hh
  have hh' : (u : ZMod s) * h ∉ V := by
    simpa only [V', Finset.mem_filter, Finset.mem_univ, true_and] using hh
  have hcard :
      (Finset.univ.filter (fun k : ZMod s => (h, k) ∈ scaledPairSet s u E)).card =
      (Finset.univ.filter (fun k : ZMod s => ((u : ZMod s) * h, k) ∈ E)).card := by
    apply Finset.card_equiv (unitScale s u)
    intro k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_scaledPairSet,
      unitScale_apply]
  exact hcard.trans_le (hf _ hh')

@[simp] theorem scaledPairSet_origin (s : ℕ) [NeZero s] (u : (ZMod s)ˣ) :
    scaledPairSet s u {(0, 0)} = {(0, 0)} := by
  ext z
  simp only [mem_scaledPairSet, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨h, k⟩
    exact Prod.ext ((unitScale s u).injective (by simpa only [unitScale_apply, mul_zero] using h))
      ((unitScale s u).injective (by simpa only [unitScale_apply, mul_zero] using k))
  · intro hz
    subst z
    simp only [mul_zero, and_self]

#print axioms scaledPairSet_card
#print axioms scaledPairSet_boundedVerticalFibers
#print axioms scaledPairSet_origin

end

end PrimeGap182.TypeIII
