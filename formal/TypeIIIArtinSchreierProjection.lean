import TypeIIIArtinSchreierCharacter
import Mathlib.LinearAlgebra.Projection

/-!
# Character projection on the actual Artin--Schreier fiber

The averaging operator is defined on all functions on the actual root
fiber by `p⁻¹ ∑ a, ψ(-a) v(z+a)`.  Reindexing by a translation proves that
its values lie in the character submodule.  If `p` is nonzero in the
coefficient field, averaging fixes that entire submodule.  Consequently
the operator is an idempotent with exactly this range, and its kernel is
a complementary submodule.  No chosen root is needed for the projection;
an actual root identifies its range as a line.

The splitting commutes with precomposition by translations and by the
actual arithmetic Frobenius on roots.  These are statements about the
fiber representation; a global sheaf is not defined here.
-/

noncomputable section

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

variable (p : ℕ) [Fact p.Prime]
  (K Ω : Type*) [Field K] [Field Ω] [CharP Ω p]
  [Algebra K Ω] [Algebra (ZMod p) Ω]
  (f : K) (E : Type*) [Field E] (ψ : AddChar (ZMod p) E)

/-- The actual finite character average, as a linear endomorphism of all
functions on the Artin--Schreier root fiber. -/
def artinSchreierCharacterProjection :
    (ArtinSchreierFiber p K Ω f → E) →ₗ[E]
      (ArtinSchreierFiber p K Ω f → E) where
  toFun v z := (p : E)⁻¹ * ∑ a : ZMod p,
    ψ (-a) * v (artinSchreierFiberTranslate p K Ω f a z)
  map_add' v w := by
    funext z
    change (p : E)⁻¹ * ∑ a : ZMod p,
        ψ (-a) * (v (artinSchreierFiberTranslate p K Ω f a z) +
          w (artinSchreierFiberTranslate p K Ω f a z)) = _
    simp only [mul_add, Finset.sum_add_distrib, Pi.add_apply]
  map_smul' c v := by
    funext z
    change (p : E)⁻¹ * ∑ a : ZMod p,
        ψ (-a) * (c * v (artinSchreierFiberTranslate p K Ω f a z)) =
      c * ((p : E)⁻¹ * ∑ a : ZMod p,
        ψ (-a) * v (artinSchreierFiberTranslate p K Ω f a z))
    calc
      _ = (p : E)⁻¹ * ∑ a : ZMod p,
          c * (ψ (-a) * v (artinSchreierFiberTranslate p K Ω f a z)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = _ := by rw [← Finset.mul_sum]; ring

/-- The precise sign and normalization of the averaging formula. -/
@[simp] theorem artinSchreierCharacterProjection_apply
    (v : ArtinSchreierFiber p K Ω f → E)
    (z : ArtinSchreierFiber p K Ω f) :
    artinSchreierCharacterProjection p K Ω f E ψ v z =
      (p : E)⁻¹ * ∑ a : ZMod p,
        ψ (-a) * v (artinSchreierFiberTranslate p K Ω f a z) := rfl

/-- Translation of the averaging index proves that the image satisfies
the actual character transformation law. -/
theorem artinSchreierCharacterProjection_mem
    (v : ArtinSchreierFiber p K Ω f → E) :
    artinSchreierCharacterProjection p K Ω f E ψ v ∈
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
  change (p : E)⁻¹ * _ = ψ b * ((p : E)⁻¹ * _)
  rw [hsum]
  ring

/-- When `p` is invertible in the coefficient field, the average fixes
every function in the actual character space. -/
theorem artinSchreierCharacterProjection_eq_self
    (hpE : (p : E) ≠ 0) (v : ArtinSchreierFiber p K Ω f → E)
    (hv : v ∈ artinSchreierCharacterSpace p K Ω f E ψ) :
    artinSchreierCharacterProjection p K Ω f E ψ v = v := by
  funext z
  rw [artinSchreierCharacterProjection_apply]
  calc
    _ = (p : E)⁻¹ * ∑ _a : ZMod p, v z := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      rw [hv a z, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel,
        AddChar.map_zero_eq_one, one_mul]
    _ = v z := by
      rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
        ← mul_assoc, inv_mul_cancel₀ hpE, one_mul]

/-- The explicit average is a projection onto the actual character
submodule; its defining conditions have both been proved from the sum. -/
theorem artinSchreierCharacterProjection_isProj (hpE : (p : E) ≠ 0) :
    LinearMap.IsProj (artinSchreierCharacterSpace p K Ω f E ψ)
      (artinSchreierCharacterProjection p K Ω f E ψ) :=
  ⟨artinSchreierCharacterProjection_mem p K Ω f E ψ,
    artinSchreierCharacterProjection_eq_self p K Ω f E ψ hpE⟩

/-- Idempotence of the averaging endomorphism, with no idempotence hypothesis. -/
theorem artinSchreierCharacterProjection_idempotent (hpE : (p : E) ≠ 0) :
    (artinSchreierCharacterProjection p K Ω f E ψ).comp
        (artinSchreierCharacterProjection p K Ω f E ψ) =
      artinSchreierCharacterProjection p K Ω f E ψ := by
  apply LinearMap.ext
  intro v
  exact artinSchreierCharacterProjection_eq_self p K Ω f E ψ hpE _
    (artinSchreierCharacterProjection_mem p K Ω f E ψ v)

/-- The image of the explicit average is exactly the character submodule. -/
theorem artinSchreierCharacterProjection_range (hpE : (p : E) ≠ 0) :
    LinearMap.range (artinSchreierCharacterProjection p K Ω f E ψ) =
      artinSchreierCharacterSpace p K Ω f E ψ :=
  (artinSchreierCharacterProjection_isProj p K Ω f E ψ hpE).range

/-- The kernel of this actual operator is a complementary submodule. -/
theorem artinSchreierCharacterProjection_isCompl (hpE : (p : E) ≠ 0) :
    IsCompl (artinSchreierCharacterSpace p K Ω f E ψ)
      (LinearMap.ker (artinSchreierCharacterProjection p K Ω f E ψ)) :=
  (artinSchreierCharacterProjection_isProj p K Ω f E ψ hpE).isCompl

/-- The same explicit average, with codomain restricted to the character
submodule whose defining relation it satisfies. -/
def artinSchreierCharacterRetraction :
    (ArtinSchreierFiber p K Ω f → E) →ₗ[E]
      artinSchreierCharacterSpace p K Ω f E ψ :=
  (artinSchreierCharacterProjection p K Ω f E ψ).codRestrict _
    (artinSchreierCharacterProjection_mem p K Ω f E ψ)

@[simp] theorem artinSchreierCharacterRetraction_val
    (v : ArtinSchreierFiber p K Ω f → E) :
    (artinSchreierCharacterRetraction p K Ω f E ψ v).val =
      artinSchreierCharacterProjection p K Ω f E ψ v := rfl

/-- The restricted average is a left inverse to the actual submodule
inclusion, explicitly exhibiting the splitting. -/
theorem artinSchreierCharacterRetraction_subtype (hpE : (p : E) ≠ 0) :
    (artinSchreierCharacterRetraction p K Ω f E ψ).comp
        (artinSchreierCharacterSpace p K Ω f E ψ).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact artinSchreierCharacterProjection_eq_self p K Ω f E ψ hpE v.val v.property

/-- For a nonempty actual fiber, the projected range has dimension one. -/
theorem artinSchreierCharacterProjection_range_finrank (hpE : (p : E) ≠ 0)
    (z₀ : ArtinSchreierFiber p K Ω f) :
    Module.finrank E (LinearMap.range (artinSchreierCharacterProjection p K Ω f E ψ)) = 1 := by
  rw [artinSchreierCharacterProjection_range p K Ω f E ψ hpE]
  exact artinSchreierCharacterSpace_finrank p K Ω f E ψ z₀

/-- The projection commutes with actual translations on the whole
function representation, not just after restriction to the character line. -/
theorem artinSchreierCharacterProjection_translate
    (v : ArtinSchreierFiber p K Ω f → E) (b : ZMod p) :
    artinSchreierCharacterProjection p K Ω f E ψ
        (fun z => v (artinSchreierFiberTranslate p K Ω f b z)) =
      fun z => artinSchreierCharacterProjection p K Ω f E ψ v
        (artinSchreierFiberTranslate p K Ω f b z) := by
  funext z
  simp only [artinSchreierCharacterProjection_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [← artinSchreierFiberTranslate_add, ← artinSchreierFiberTranslate_add, add_comm b a]

section Frobenius

variable [Algebra (ZMod p) K]

/-- The projection commutes with precomposition by arithmetic Frobenius
on actual roots, hence with its geometric function action. -/
theorem artinSchreierCharacterProjection_frobenius
    (v : ArtinSchreierFiber p K Ω f → E) :
    artinSchreierCharacterProjection p K Ω f E ψ
        (fun z => v (artinSchreierArithmeticFrobenius p K Ω f z)) =
      fun z => artinSchreierCharacterProjection p K Ω f E ψ v
        (artinSchreierArithmeticFrobenius p K Ω f z) := by
  simpa only [artinSchreierArithmeticFrobenius_eq_translate] using
    artinSchreierCharacterProjection_translate p K Ω f E ψ v (Algebra.trace (ZMod p) K f)

/-- The retraction intertwines the full function action with the actual
Frobenius operator on the character submodule. -/
theorem artinSchreierCharacterRetraction_frobenius
    (v : ArtinSchreierFiber p K Ω f → E) :
    artinSchreierCharacterRetraction p K Ω f E ψ
        (fun z => v (artinSchreierArithmeticFrobenius p K Ω f z)) =
      artinSchreierCharacterFrobenius p K Ω f E ψ
        (artinSchreierCharacterRetraction p K Ω f E ψ v) := by
  apply Subtype.ext
  exact artinSchreierCharacterProjection_frobenius p K Ω f E ψ v

end Frobenius

#print axioms artinSchreierCharacterProjection
#print axioms artinSchreierCharacterProjection_apply
#print axioms artinSchreierCharacterProjection_mem
#print axioms artinSchreierCharacterProjection_eq_self
#print axioms artinSchreierCharacterProjection_isProj
#print axioms artinSchreierCharacterProjection_idempotent
#print axioms artinSchreierCharacterProjection_range
#print axioms artinSchreierCharacterProjection_isCompl
#print axioms artinSchreierCharacterRetraction
#print axioms artinSchreierCharacterRetraction_val
#print axioms artinSchreierCharacterRetraction_subtype
#print axioms artinSchreierCharacterProjection_range_finrank
#print axioms artinSchreierCharacterProjection_translate
#print axioms artinSchreierCharacterProjection_frobenius
#print axioms artinSchreierCharacterRetraction_frobenius

end PrimeGap182.TypeIII
