import TypeIIIArtinSchreierFrobenius
import Mathlib.Algebra.Group.AddChar
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Trace

/-!
# The character line on an actual Artin–Schreier fiber

The functions satisfying v(z+a) = ψ(a) v(z) form a free module on one
generator.  Evaluation at a chosen root gives an explicit linear
equivalence to the coefficient ring.  Precomposition with arithmetic
Frobenius on roots is the induced function action of geometric Frobenius;
its scalar and trace are ψ(Tr(f)), with a positive sign.

The coefficient ring is an arbitrary commutative ring; invertibility of
p is not needed for the character module or its trace.  These results
concern the actual character eigenspace and do not assume an equivariant
splitting of the whole permutation representation or a sheaf trace
formula.  The finite-dimensional field specialization is retained.
-/

open scoped Classical

namespace PrimeGap182.TypeIII

noncomputable section

variable (p : ℕ) [Fact p.Prime]
  (K Ω : Type*) [Field K] [Field Ω] [CharP Ω p]
  [Algebra K Ω] [Algebra (ZMod p) Ω]
  (f : K)

section RingCoefficients

variable (E : Type*) [CommRing E] (ψ : AddChar (ZMod p) E)

/-- The character eigenspace of functions on the actual root fiber. -/
def artinSchreierCharacterSpace :
    Submodule E (ArtinSchreierFiber p K Ω f → E) where
  carrier := {v | ∀ (a : ZMod p) (z : ArtinSchreierFiber p K Ω f),
    v (artinSchreierFiberTranslate p K Ω f a z) = ψ a * v z}
  zero_mem' := by
    intro a z
    simp
  add_mem' := by
    intro v w hv hw a z
    change v (artinSchreierFiberTranslate p K Ω f a z) +
        w (artinSchreierFiberTranslate p K Ω f a z) = ψ a * (v z + w z)
    rw [hv a z, hw a z, mul_add]
  smul_mem' := by
    intro c v hv a z
    change c * v (artinSchreierFiberTranslate p K Ω f a z) = ψ a * (c * v z)
    rw [hv a z]
    ring

theorem mem_artinSchreierCharacterSpace
    (v : ArtinSchreierFiber p K Ω f → E) :
    v ∈ artinSchreierCharacterSpace p K Ω f E ψ ↔
      ∀ (a : ZMod p) (z : ArtinSchreierFiber p K Ω f),
        v (artinSchreierFiberTranslate p K Ω f a z) = ψ a * v z :=
  Iff.rfl

/-- Evaluation at a root is a linear functional on the character space. -/
def artinSchreierCharacterEvaluation (z₀ : ArtinSchreierFiber p K Ω f) :
    artinSchreierCharacterSpace p K Ω f E ψ →ₗ[E] E where
  toFun v := v.val z₀
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A value at one actual root determines a unique character function. -/
def artinSchreierCharacterEvaluationEquiv (z₀ : ArtinSchreierFiber p K Ω f) :
    artinSchreierCharacterSpace p K Ω f E ψ ≃ₗ[E] E where
  toFun v := v.val z₀
  invFun c := ⟨fun z => ψ ((artinSchreierFiberEquiv p K Ω f z₀).symm z) * c, by
    intro a z
    change ψ ((artinSchreierFiberEquiv p K Ω f z₀).symm
        (artinSchreierFiberTranslate p K Ω f a z)) * c =
      ψ a * (ψ ((artinSchreierFiberEquiv p K Ω f z₀).symm z) * c)
    rw [artinSchreierFiberCoordinate_translate, AddChar.map_add_eq_mul, mul_assoc]⟩
  left_inv v := by
    apply Subtype.ext
    funext z
    have h := v.property ((artinSchreierFiberEquiv p K Ω f z₀).symm z) z₀
    have hz : artinSchreierFiberTranslate p K Ω f
        ((artinSchreierFiberEquiv p K Ω f z₀).symm z) z₀ = z :=
      (artinSchreierFiberEquiv p K Ω f z₀).apply_symm_apply z
    rw [hz] at h
    exact h.symm
  right_inv c := by
    have h₀ : (artinSchreierFiberEquiv p K Ω f z₀).symm z₀ = 0 := by
      apply (artinSchreierFiberEquiv p K Ω f z₀).injective
      simp
    change ψ ((artinSchreierFiberEquiv p K Ω f z₀).symm z₀) * c = c
    rw [h₀, AddChar.map_zero_eq_one, one_mul]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem artinSchreierCharacterEvaluationEquiv_apply
    (z₀ : ArtinSchreierFiber p K Ω f)
    (v : artinSchreierCharacterSpace p K Ω f E ψ) :
    artinSchreierCharacterEvaluationEquiv p K Ω f E ψ z₀ v = v.val z₀ := rfl

/-- Transport of the singleton basis along the actual root evaluation
equivalence supplies an explicit basis of the character module. -/
def artinSchreierCharacterBasis (z₀ : ArtinSchreierFiber p K Ω f) :
    Module.Basis Unit E (artinSchreierCharacterSpace p K Ω f E ψ) :=
  (Module.Basis.singleton Unit E).map
    (artinSchreierCharacterEvaluationEquiv p K Ω f E ψ z₀).symm

/-- Freeness follows from the constructed evaluation equivalence. -/
theorem artinSchreierCharacterSpace_free (z₀ : ArtinSchreierFiber p K Ω f) :
    Module.Free E (artinSchreierCharacterSpace p K Ω f E ψ) :=
  Module.Free.of_equiv
    (artinSchreierCharacterEvaluationEquiv p K Ω f E ψ z₀).symm

/-- Finite generation follows from the same actual equivalence to E. -/
theorem artinSchreierCharacterSpace_finite (z₀ : ArtinSchreierFiber p K Ω f) :
    Module.Finite E (artinSchreierCharacterSpace p K Ω f E ψ) :=
  Module.Finite.equiv
    (artinSchreierCharacterEvaluationEquiv p K Ω f E ψ z₀).symm

/-- The character space has rank one, proved using the actual fiber torsor. -/
theorem artinSchreierCharacterSpace_finrank (z₀ : ArtinSchreierFiber p K Ω f) :
    Module.finrank E (artinSchreierCharacterSpace p K Ω f E ψ) = 1 := by
  rw [(artinSchreierCharacterEvaluationEquiv p K Ω f E ψ z₀).finrank_eq]
  exact CommSemiring.finrank_self E

/-- Precomposition by an actual translation of roots restricts to the
character space. -/
def artinSchreierCharacterTranslation (a : ZMod p) :
    artinSchreierCharacterSpace p K Ω f E ψ →ₗ[E]
      artinSchreierCharacterSpace p K Ω f E ψ where
  toFun v := ⟨fun z => v.val (artinSchreierFiberTranslate p K Ω f a z), by
    intro b z
    change v.val (artinSchreierFiberTranslate p K Ω f a
        (artinSchreierFiberTranslate p K Ω f b z)) =
      ψ b * v.val (artinSchreierFiberTranslate p K Ω f a z)
    rw [v.property a _, v.property b z, v.property a z]
    ring⟩
  map_add' v w := by
    apply Subtype.ext
    funext z
    rfl
  map_smul' c v := by
    apply Subtype.ext
    funext z
    rfl

/-- The translation operator is scalar multiplication by the positive
character value. -/
theorem artinSchreierCharacterTranslation_eq_smul (a : ZMod p) :
    artinSchreierCharacterTranslation p K Ω f E ψ a =
      ψ a • LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext z
  change v.val (artinSchreierFiberTranslate p K Ω f a z) = ψ a * v.val z
  exact v.property a z

/-- The trace of translation on the actual character line. -/
theorem artinSchreierCharacterTranslation_trace (z₀ : ArtinSchreierFiber p K Ω f)
    (a : ZMod p) :
    LinearMap.trace E (artinSchreierCharacterSpace p K Ω f E ψ)
      (artinSchreierCharacterTranslation p K Ω f E ψ a) = ψ a := by
  let := artinSchreierCharacterSpace_free p K Ω f E ψ z₀
  let := artinSchreierCharacterSpace_finite p K Ω f E ψ z₀
  rw [artinSchreierCharacterTranslation_eq_smul, map_smul, LinearMap.trace_id,
    artinSchreierCharacterSpace_finrank p K Ω f E ψ z₀]
  simp

section Frobenius

variable [Algebra (ZMod p) K]

/-- Geometric Frobenius on functions acts by precomposition with arithmetic
Frobenius on roots.  The imported power-map theorem identifies the latter
with z ↦ z^(card K) when K is finite and the scalar tower is compatible. -/
def artinSchreierCharacterFrobenius :
    artinSchreierCharacterSpace p K Ω f E ψ →ₗ[E]
      artinSchreierCharacterSpace p K Ω f E ψ where
  toFun v := ⟨fun z => v.val (artinSchreierArithmeticFrobenius p K Ω f z), by
    intro a z
    change v.val (artinSchreierArithmeticFrobenius p K Ω f
        (artinSchreierFiberTranslate p K Ω f a z)) =
      ψ a * v.val (artinSchreierArithmeticFrobenius p K Ω f z)
    simp only [artinSchreierArithmeticFrobenius_eq_translate]
    rw [v.property (Algebra.trace (ZMod p) K f) _, v.property a z,
      v.property (Algebra.trace (ZMod p) K f) z]
    ring⟩
  map_add' v w := by
    apply Subtype.ext
    funext z
    rfl
  map_smul' c v := by
    apply Subtype.ext
    funext z
    rfl

@[simp] theorem artinSchreierCharacterFrobenius_apply
    (v : artinSchreierCharacterSpace p K Ω f E ψ)
    (z : ArtinSchreierFiber p K Ω f) :
    (artinSchreierCharacterFrobenius p K Ω f E ψ v).val z =
      v.val (artinSchreierArithmeticFrobenius p K Ω f z) := rfl

/-- The function action is translation by the positive field trace. -/
theorem artinSchreierCharacterFrobenius_eq_translation :
    artinSchreierCharacterFrobenius p K Ω f E ψ =
      artinSchreierCharacterTranslation p K Ω f E ψ (Algebra.trace (ZMod p) K f) := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext z
  rfl

/-- The geometric Frobenius scalar on the character line is ψ(Tr(f)). -/
theorem artinSchreierCharacterFrobenius_eq_smul :
    artinSchreierCharacterFrobenius p K Ω f E ψ =
      ψ (Algebra.trace (ZMod p) K f) • LinearMap.id := by
  rw [artinSchreierCharacterFrobenius_eq_translation,
    artinSchreierCharacterTranslation_eq_smul]

/-- The actual character-space Frobenius trace has the positive
Artin–Schreier sign. -/
theorem artinSchreierCharacterFrobenius_trace (z₀ : ArtinSchreierFiber p K Ω f) :
    LinearMap.trace E (artinSchreierCharacterSpace p K Ω f E ψ)
      (artinSchreierCharacterFrobenius p K Ω f E ψ) =
        ψ (Algebra.trace (ZMod p) K f) := by
  rw [artinSchreierCharacterFrobenius_eq_translation]
  exact artinSchreierCharacterTranslation_trace p K Ω f E ψ z₀ _

/-- On a finite base field, this is literally precomposition with the
q-power map on the actual roots, independently of their coordinate names. -/
theorem artinSchreierCharacterFrobenius_apply_of_pow
    [Fintype K] [IsScalarTower (ZMod p) K Ω]
    (v : artinSchreierCharacterSpace p K Ω f E ψ)
    (z zq : ArtinSchreierFiber p K Ω f)
    (hzq : (zq : Ω) = (z : Ω) ^ Fintype.card K) :
    (artinSchreierCharacterFrobenius p K Ω f E ψ v).val z = v.val zq := by
  rw [artinSchreierCharacterFrobenius_apply]
  apply congrArg v.val
  apply Subtype.ext
  rw [artinSchreierArithmeticFrobenius_val, hzq]

end Frobenius

end RingCoefficients

section FieldCoefficients

variable (E : Type*) [Field E] (ψ : AddChar (ZMod p) E)

/-- A chosen actual root supplies finite dimensionality over a
coefficient field without a finiteness premise on the ambient field. -/
theorem artinSchreierCharacterSpace_finiteDimensional
    (z₀ : ArtinSchreierFiber p K Ω f) :
    FiniteDimensional E (artinSchreierCharacterSpace p K Ω f E ψ) :=
  artinSchreierCharacterSpace_finite p K Ω f E ψ z₀

end FieldCoefficients

end

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.artinSchreierCharacterSpace
#print axioms PrimeGap182.TypeIII.mem_artinSchreierCharacterSpace
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterEvaluation
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterEvaluationEquiv
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterEvaluationEquiv_apply
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterBasis
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterSpace_free
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterSpace_finite
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterSpace_finrank
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterSpace_finiteDimensional
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterTranslation
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterTranslation_eq_smul
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterTranslation_trace
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterFrobenius
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterFrobenius_apply
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterFrobenius_eq_translation
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterFrobenius_eq_smul
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterFrobenius_trace
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterFrobenius_apply_of_pow
