import TypeIIIArtinSchreierCharacter
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.LinearAlgebra.Projection

/-!
# Artin--Schreier character projection over a coefficient ring

For a commutative coefficient ring in which p is a unit, the actual
root-function average `⅟p * ∑ a, ψ(-a) v(z+a)` is a projection onto the
existing character submodule.  Its range has an explicit evaluation
equivalence to the coefficient ring when a root is given.  Freeness,
finite generation, and the Frobenius trace are consequences of that
equivalence, not assumptions on a proposed character line.

The value of the projected delta function at its supporting root is
the unit `⅟p`.  This is the relevant generator property over rings:
nonvanishing alone would not suffice.  Geometric Frobenius on functions
has the positive Artin--Schreier sign, through precomposition with the
actual arithmetic Frobenius on roots.  No global sheaf is defined here.
-/

noncomputable section

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

variable (p : ℕ) [Fact p.Prime]
  (K Ω : Type*) [Field K] [Field Ω] [CharP Ω p]
  [Algebra K Ω] [Algebra (ZMod p) Ω]
  (f : K) (E : Type*) [CommRing E] [Invertible (p : E)]
  (ψ : AddChar (ZMod p) E)

/-- The actual normalized character average using the inverse of the
specified unit p in the coefficient ring. -/
def artinSchreierRingCharacterProjection :
    (ArtinSchreierFiber p K Ω f → E) →ₗ[E]
      (ArtinSchreierFiber p K Ω f → E) where
  toFun v z := ⅟(p : E) * ∑ a : ZMod p,
    ψ (-a) * v (artinSchreierFiberTranslate p K Ω f a z)
  map_add' v w := by
    funext z
    change ⅟(p : E) * ∑ a : ZMod p,
        ψ (-a) * (v (artinSchreierFiberTranslate p K Ω f a z) +
          w (artinSchreierFiberTranslate p K Ω f a z)) = _
    simp only [mul_add, Finset.sum_add_distrib, Pi.add_apply]
  map_smul' c v := by
    funext z
    change ⅟(p : E) * ∑ a : ZMod p,
        ψ (-a) * (c * v (artinSchreierFiberTranslate p K Ω f a z)) =
      c * (⅟(p : E) * ∑ a : ZMod p,
        ψ (-a) * v (artinSchreierFiberTranslate p K Ω f a z))
    calc
      _ = ⅟(p : E) * ∑ a : ZMod p,
          c * (ψ (-a) * v (artinSchreierFiberTranslate p K Ω f a z)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = _ := by rw [← Finset.mul_sum]; ring

@[simp] theorem artinSchreierRingCharacterProjection_apply
    (v : ArtinSchreierFiber p K Ω f → E)
    (z : ArtinSchreierFiber p K Ω f) :
    artinSchreierRingCharacterProjection p K Ω f E ψ v z =
      ⅟(p : E) * ∑ a : ZMod p,
        ψ (-a) * v (artinSchreierFiberTranslate p K Ω f a z) := rfl

/-- Reindexing the actual finite sum proves the character relation. -/
theorem artinSchreierRingCharacterProjection_mem
    (v : ArtinSchreierFiber p K Ω f → E) :
    artinSchreierRingCharacterProjection p K Ω f E ψ v ∈
      artinSchreierCharacterSpace p K Ω f E ψ := by
  intro b z
  have hsum :
      (∑ a : ZMod p, ψ (-a) * v (artinSchreierFiberTranslate p K Ω f a
        (artinSchreierFiberTranslate p K Ω f b z))) =
      ψ b * ∑ a : ZMod p, ψ (-a) * v (artinSchreierFiberTranslate p K Ω f a z) := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addRight b) _ _ ?_
    intro a
    change ψ (-a) * v (artinSchreierFiberTranslate p K Ω f a
        (artinSchreierFiberTranslate p K Ω f b z)) =
      ψ b * (ψ (-(a + b)) * v (artinSchreierFiberTranslate p K Ω f (a + b) z))
    rw [← artinSchreierFiberTranslate_add]
    have hψ : ψ b * ψ (-(a + b)) = ψ (-a) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      abel
    rw [← mul_assoc, hψ]
  change ⅟(p : E) * _ = ψ b * (⅟(p : E) * _)
  rw [hsum]
  ring

/-- The average fixes every member of the actual character submodule. -/
theorem artinSchreierRingCharacterProjection_eq_self
    (v : ArtinSchreierFiber p K Ω f → E)
    (hv : v ∈ artinSchreierCharacterSpace p K Ω f E ψ) :
    artinSchreierRingCharacterProjection p K Ω f E ψ v = v := by
  funext z
  rw [artinSchreierRingCharacterProjection_apply]
  calc
    _ = ⅟(p : E) * ∑ _a : ZMod p, v z := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      rw [hv a z, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel,
        AddChar.map_zero_eq_one, one_mul]
    _ = v z := by
      rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
        ← mul_assoc, invOf_mul_self, one_mul]

/-- Both defining properties of this projection follow from the sum. -/
theorem artinSchreierRingCharacterProjection_isProj :
    LinearMap.IsProj (artinSchreierCharacterSpace p K Ω f E ψ)
      (artinSchreierRingCharacterProjection p K Ω f E ψ) :=
  ⟨artinSchreierRingCharacterProjection_mem p K Ω f E ψ,
    artinSchreierRingCharacterProjection_eq_self p K Ω f E ψ⟩

theorem artinSchreierRingCharacterProjection_idempotent :
    (artinSchreierRingCharacterProjection p K Ω f E ψ).comp
        (artinSchreierRingCharacterProjection p K Ω f E ψ) =
      artinSchreierRingCharacterProjection p K Ω f E ψ := by
  apply LinearMap.ext
  intro v
  exact artinSchreierRingCharacterProjection_eq_self p K Ω f E ψ _
    (artinSchreierRingCharacterProjection_mem p K Ω f E ψ v)

/-- The actual range is exactly the existing character submodule. -/
theorem artinSchreierRingCharacterProjection_range :
    LinearMap.range (artinSchreierRingCharacterProjection p K Ω f E ψ) =
      artinSchreierCharacterSpace p K Ω f E ψ :=
  (artinSchreierRingCharacterProjection_isProj p K Ω f E ψ).range

theorem artinSchreierRingCharacterProjection_isCompl :
    IsCompl (artinSchreierCharacterSpace p K Ω f E ψ)
      (LinearMap.ker (artinSchreierRingCharacterProjection p K Ω f E ψ)) :=
  (artinSchreierRingCharacterProjection_isProj p K Ω f E ψ).isCompl

/-- The same average with its codomain restricted by the proved relation. -/
def artinSchreierRingCharacterRetraction :
    (ArtinSchreierFiber p K Ω f → E) →ₗ[E]
      artinSchreierCharacterSpace p K Ω f E ψ :=
  (artinSchreierRingCharacterProjection p K Ω f E ψ).codRestrict _
    (artinSchreierRingCharacterProjection_mem p K Ω f E ψ)

@[simp] theorem artinSchreierRingCharacterRetraction_val
    (v : ArtinSchreierFiber p K Ω f → E) :
    (artinSchreierRingCharacterRetraction p K Ω f E ψ v).val =
      artinSchreierRingCharacterProjection p K Ω f E ψ v := rfl

theorem artinSchreierRingCharacterRetraction_subtype :
    (artinSchreierRingCharacterRetraction p K Ω f E ψ).comp
        (artinSchreierCharacterSpace p K Ω f E ψ).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact artinSchreierRingCharacterProjection_eq_self p K Ω f E ψ v.val v.property

/-- An explicit identification of the projector range with the already
constructed character module; it leaves underlying functions unchanged. -/
def artinSchreierRingCharacterProjection_rangeEquivCharacter :
    LinearMap.range (artinSchreierRingCharacterProjection p K Ω f E ψ) ≃ₗ[E]
      artinSchreierCharacterSpace p K Ω f E ψ where
  toFun v := ⟨v.val, by
    rw [← artinSchreierRingCharacterProjection_range p K Ω f E ψ]
    exact v.property⟩
  invFun v := ⟨v.val, ⟨v.val,
    artinSchreierRingCharacterProjection_eq_self p K Ω f E ψ v.val v.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem artinSchreierRingCharacterProjection_rangeEquivCharacter_val
    (v : LinearMap.range (artinSchreierRingCharacterProjection p K Ω f E ψ)) :
    (artinSchreierRingCharacterProjection_rangeEquivCharacter p K Ω f E ψ v).val =
      v.val := rfl

/-- Actual root evaluation identifies the range with E over any
commutative coefficient ring in which p is a unit. -/
def artinSchreierRingCharacterProjection_rangeEvaluationEquiv
    (z₀ : ArtinSchreierFiber p K Ω f) :
    LinearMap.range (artinSchreierRingCharacterProjection p K Ω f E ψ) ≃ₗ[E] E :=
  (artinSchreierRingCharacterProjection_rangeEquivCharacter p K Ω f E ψ).trans
    (artinSchreierCharacterEvaluationEquiv p K Ω f E ψ z₀)

@[simp] theorem artinSchreierRingCharacterProjection_rangeEvaluationEquiv_apply
    (z₀ : ArtinSchreierFiber p K Ω f)
    (v : LinearMap.range (artinSchreierRingCharacterProjection p K Ω f E ψ)) :
    artinSchreierRingCharacterProjection_rangeEvaluationEquiv p K Ω f E ψ z₀ v =
      v.val z₀ := rfl

theorem artinSchreierRingCharacterProjection_range_free
    (z₀ : ArtinSchreierFiber p K Ω f) :
    Module.Free E (LinearMap.range (artinSchreierRingCharacterProjection p K Ω f E ψ)) :=
  Module.Free.of_equiv
    (artinSchreierRingCharacterProjection_rangeEvaluationEquiv p K Ω f E ψ z₀).symm

theorem artinSchreierRingCharacterProjection_range_finite
    (z₀ : ArtinSchreierFiber p K Ω f) :
    Module.Finite E (LinearMap.range (artinSchreierRingCharacterProjection p K Ω f E ψ)) :=
  Module.Finite.equiv
    (artinSchreierRingCharacterProjection_rangeEvaluationEquiv p K Ω f E ψ z₀).symm

theorem artinSchreierRingCharacterProjection_range_finrank
    (z₀ : ArtinSchreierFiber p K Ω f) :
    Module.finrank E (LinearMap.range (artinSchreierRingCharacterProjection p K Ω f E ψ)) = 1 := by
  rw [(artinSchreierRingCharacterProjection_rangeEvaluationEquiv p K Ω f E ψ z₀).finrank_eq]
  exact CommSemiring.finrank_self E

/-- The self-value of a projected delta function is the unit 1/p. -/
theorem artinSchreierRingCharacterProjection_delta_self
    (z₀ : ArtinSchreierFiber p K Ω f) :
    artinSchreierRingCharacterProjection p K Ω f E ψ
        (fun z => if z = z₀ then 1 else 0) z₀ = ⅟(p : E) := by
  have hf (a : ZMod p) : artinSchreierFiberTranslate p K Ω f a z₀ = z₀ ↔ a = 0 := by
    constructor
    · intro h
      apply (artinSchreierFiberEquiv p K Ω f z₀).injective
      simpa only [artinSchreierFiberEquiv_apply, artinSchreierFiberTranslate_zero] using h
    · rintro rfl
      exact artinSchreierFiberTranslate_zero p K Ω f z₀
  rw [artinSchreierRingCharacterProjection_apply]
  have hs : (∑ a : ZMod p, ψ (-a) *
      (if artinSchreierFiberTranslate p K Ω f a z₀ = z₀ then 1 else 0)) = (1 : E) := by
    rw [Finset.sum_eq_single (0 : ZMod p)]
    · simp only [neg_zero, AddChar.map_zero_eq_one, artinSchreierFiberTranslate_zero,
        ite_true, mul_one]
    · intro a _ha ha
      rw [ite_eq_right ((hf a).not.mpr ha), mul_zero]
    · simp
  rw [hs, mul_one]

/-- The projection commutes with translations on the whole function module. -/
theorem artinSchreierRingCharacterProjection_translate
    (v : ArtinSchreierFiber p K Ω f → E) (b : ZMod p) :
    artinSchreierRingCharacterProjection p K Ω f E ψ
        (fun z => v (artinSchreierFiberTranslate p K Ω f b z)) =
      fun z => artinSchreierRingCharacterProjection p K Ω f E ψ v
        (artinSchreierFiberTranslate p K Ω f b z) := by
  funext z
  simp only [artinSchreierRingCharacterProjection_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [← artinSchreierFiberTranslate_add, ← artinSchreierFiberTranslate_add, add_comm b a]

section Frobenius

variable [Algebra (ZMod p) K]

theorem artinSchreierRingCharacterProjection_frobenius
    (v : ArtinSchreierFiber p K Ω f → E) :
    artinSchreierRingCharacterProjection p K Ω f E ψ
        (fun z => v (artinSchreierArithmeticFrobenius p K Ω f z)) =
      fun z => artinSchreierRingCharacterProjection p K Ω f E ψ v
        (artinSchreierArithmeticFrobenius p K Ω f z) := by
  simpa only [artinSchreierArithmeticFrobenius_eq_translate] using
    artinSchreierRingCharacterProjection_translate p K Ω f E ψ v (Algebra.trace (ZMod p) K f)

/-- The split retraction intertwines the actual function Frobenius action. -/
theorem artinSchreierRingCharacterRetraction_frobenius
    (v : ArtinSchreierFiber p K Ω f → E) :
    artinSchreierRingCharacterRetraction p K Ω f E ψ
        (fun z => v (artinSchreierArithmeticFrobenius p K Ω f z)) =
      artinSchreierCharacterFrobenius p K Ω f E ψ
        (artinSchreierRingCharacterRetraction p K Ω f E ψ v) := by
  apply Subtype.ext
  exact artinSchreierRingCharacterProjection_frobenius p K Ω f E ψ v

/-- The root Frobenius action on the literal range, defined by
precomposition and justified by the proved commutation identity. -/
def artinSchreierRingCharacterRangeFrobenius :
    LinearMap.range (artinSchreierRingCharacterProjection p K Ω f E ψ) →ₗ[E]
      LinearMap.range (artinSchreierRingCharacterProjection p K Ω f E ψ) where
  toFun v := ⟨fun z => v.val (artinSchreierArithmeticFrobenius p K Ω f z), by
    obtain ⟨w, hw⟩ := v.property
    refine ⟨fun z => w (artinSchreierArithmeticFrobenius p K Ω f z), ?_⟩
    rw [artinSchreierRingCharacterProjection_frobenius, hw]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The identity-on-functions range comparison intertwines Frobenius. -/
theorem artinSchreierRingCharacterProjection_rangeEquivCharacter_frobenius
    (v : LinearMap.range (artinSchreierRingCharacterProjection p K Ω f E ψ)) :
    artinSchreierRingCharacterProjection_rangeEquivCharacter p K Ω f E ψ
        (artinSchreierRingCharacterRangeFrobenius p K Ω f E ψ v) =
      artinSchreierCharacterFrobenius p K Ω f E ψ
        (artinSchreierRingCharacterProjection_rangeEquivCharacter p K Ω f E ψ v) := rfl

theorem artinSchreierRingCharacterRangeFrobenius_eq_smul :
    artinSchreierRingCharacterRangeFrobenius p K Ω f E ψ =
      ψ (Algebra.trace (ZMod p) K f) • LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply (artinSchreierRingCharacterProjection_rangeEquivCharacter p K Ω f E ψ).injective
  rw [artinSchreierRingCharacterProjection_rangeEquivCharacter_frobenius,
    artinSchreierCharacterFrobenius_eq_smul]
  exact ((artinSchreierRingCharacterProjection_rangeEquivCharacter p K Ω f E ψ).map_smul
    (ψ (Algebra.trace (ZMod p) K f)) v).symm

/-- The actual Frobenius trace on the proved finite free range. -/
theorem artinSchreierRingCharacterRangeFrobenius_trace
    (z₀ : ArtinSchreierFiber p K Ω f) :
    LinearMap.trace E (LinearMap.range (artinSchreierRingCharacterProjection p K Ω f E ψ))
      (artinSchreierRingCharacterRangeFrobenius p K Ω f E ψ) =
        ψ (Algebra.trace (ZMod p) K f) := by
  let := artinSchreierRingCharacterProjection_range_free p K Ω f E ψ z₀
  let := artinSchreierRingCharacterProjection_range_finite p K Ω f E ψ z₀
  rw [artinSchreierRingCharacterRangeFrobenius_eq_smul, map_smul, LinearMap.trace_id,
    artinSchreierRingCharacterProjection_range_finrank p K Ω f E ψ z₀]
  simp

end Frobenius

#print axioms artinSchreierRingCharacterProjection
#print axioms artinSchreierRingCharacterProjection_apply
#print axioms artinSchreierRingCharacterProjection_mem
#print axioms artinSchreierRingCharacterProjection_eq_self
#print axioms artinSchreierRingCharacterProjection_isProj
#print axioms artinSchreierRingCharacterProjection_idempotent
#print axioms artinSchreierRingCharacterProjection_range
#print axioms artinSchreierRingCharacterProjection_isCompl
#print axioms artinSchreierRingCharacterRetraction
#print axioms artinSchreierRingCharacterRetraction_val
#print axioms artinSchreierRingCharacterRetraction_subtype
#print axioms artinSchreierRingCharacterProjection_rangeEquivCharacter
#print axioms artinSchreierRingCharacterProjection_rangeEquivCharacter_val
#print axioms artinSchreierRingCharacterProjection_rangeEvaluationEquiv
#print axioms artinSchreierRingCharacterProjection_rangeEvaluationEquiv_apply
#print axioms artinSchreierRingCharacterProjection_range_free
#print axioms artinSchreierRingCharacterProjection_range_finite
#print axioms artinSchreierRingCharacterProjection_range_finrank
#print axioms artinSchreierRingCharacterProjection_delta_self
#print axioms artinSchreierRingCharacterProjection_translate
#print axioms artinSchreierRingCharacterProjection_frobenius
#print axioms artinSchreierRingCharacterRetraction_frobenius
#print axioms artinSchreierRingCharacterRangeFrobenius
#print axioms artinSchreierRingCharacterProjection_rangeEquivCharacter_frobenius
#print axioms artinSchreierRingCharacterRangeFrobenius_eq_smul
#print axioms artinSchreierRingCharacterRangeFrobenius_trace

end PrimeGap182.TypeIII
