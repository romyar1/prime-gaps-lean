import TypeIIIArtinSchreierCover
import TypeIIIArtinSchreierFrobenius
import TypeIIIArtinSchreierCharacter

/-!
# Geometric points of the actual Artin--Schreier cover

Algebra homomorphisms from the finite étale quotient to an extension field
are identified with the literal roots of `z^p-z=f`. Over an algebraically
closed extension this set is nonempty and has exactly `p` points. Thus the
root torsor and its Frobenius calculation apply to the geometric fiber of
the constructed cover, rather than to an assumed representation.
-/

noncomputable section

open scoped Classical

namespace PrimeGap182.TypeIII

section AlgebraHomFiber

variable (p : ℕ) (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω] (f : K)

/-- Evaluate a geometric point of the actual quotient at its distinguished root. -/
def artinSchreierFiberOfHom (φ : ArtinSchreierCover p K f →ₐ[K] Ω) :
    ArtinSchreierFiber p K Ω f :=
  ⟨φ (artinSchreierRoot p f), by
    have h := congrArg φ (artinSchreierRoot_relation p f)
    simpa only [map_sub, map_pow, AlgHom.commutes] using h⟩

/-- The universal property of the actual quotient turns a root into a
geometric point; no existence assumption about an algebra homomorphism is used. -/
def artinSchreierHomOfFiber (z : ArtinSchreierFiber p K Ω f) :
    ArtinSchreierCover p K f →ₐ[K] Ω :=
  AdjoinRoot.liftAlgHom (artinSchreierPolynomial p f) (Algebra.ofId K Ω) (z : Ω) (by
    simp only [artinSchreierPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    change (z : Ω) ^ p - (z : Ω) - algebraMap K Ω f = 0
    exact sub_eq_zero.mpr z.property)

/-- The affine geometric points of the cover are exactly its polynomial roots. -/
def artinSchreierHomEquivFiber :
    (ArtinSchreierCover p K f →ₐ[K] Ω) ≃ ArtinSchreierFiber p K Ω f where
  toFun := artinSchreierFiberOfHom p K Ω f
  invFun := artinSchreierHomOfFiber p K Ω f
  left_inv φ := by
    apply AdjoinRoot.algHom_ext
    exact AdjoinRoot.liftAlgHom_root (artinSchreierPolynomial p f)
      (Algebra.ofId K Ω) (artinSchreierFiberOfHom p K Ω f φ : Ω) _
  right_inv z := by
    apply Subtype.ext
    exact AdjoinRoot.liftAlgHom_root (artinSchreierPolynomial p f)
      (Algebra.ofId K Ω) (z : Ω) _

@[simp] theorem artinSchreierHomEquivFiber_val
    (φ : ArtinSchreierCover p K f →ₐ[K] Ω) :
    (artinSchreierHomEquivFiber p K Ω f φ : Ω) = φ (artinSchreierRoot p f) := rfl

end AlgebraHomFiber

section ActionsOnGeometricPoints

variable (p : ℕ) [Fact p.Prime]
variable (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]
variable [Algebra (ZMod p) K] [Algebra (ZMod p) Ω] [CharP Ω p]
variable [IsScalarTower (ZMod p) K Ω] (f : K)

/-- The root torsor action is induced by the actual deck automorphisms of
the quotient cover, under its geometric-point identification. -/
theorem artinSchreierHomEquivFiber_translation [CharP K p]
    (a : ZMod p) (φ : ArtinSchreierCover p K f →ₐ[K] Ω) :
    artinSchreierHomEquivFiber p K Ω f
        (φ.comp (artinSchreierCover_translation p f a).toAlgHom) =
      artinSchreierFiberTranslate p K Ω f a (artinSchreierHomEquivFiber p K Ω f φ) := by
  apply Subtype.ext
  simp only [artinSchreierHomEquivFiber_val, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    artinSchreierCover_translation_root, map_add, AlgHom.commutes,
    artinSchreierFiberTranslate_val]
  have hcast : ZMod.castHom (dvd_refl p) K = algebraMap (ZMod p) K := Subsingleton.elim _ _
  rw [hcast, IsScalarTower.algebraMap_apply (ZMod p) K Ω]

/-- Applying actual finite-field Frobenius to a geometric point agrees
with the proved trace-translation permutation of its root. -/
theorem artinSchreierHomEquivFiber_frobenius [Fintype K]
    (φ : ArtinSchreierCover p K f →ₐ[K] Ω) :
    artinSchreierHomEquivFiber p K Ω f ((FiniteField.frobeniusAlgHom K Ω).comp φ) =
      artinSchreierArithmeticFrobenius p K Ω f (artinSchreierHomEquivFiber p K Ω f φ) := by
  apply Subtype.ext
  rw [artinSchreierArithmeticFrobenius_val, artinSchreierHomEquivFiber_val,
    artinSchreierHomEquivFiber_val]
  rfl

end ActionsOnGeometricPoints

section AlgebraicallyClosedFiber

variable (p : ℕ) [Fact p.Prime]
variable (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]
variable [CharP Ω p] [IsAlgClosed Ω] (f : K)

/-- The nonconstant Artin--Schreier polynomial has an actual geometric root. -/
theorem artinSchreierFiber_nonempty : Nonempty (ArtinSchreierFiber p K Ω f) := by
  have hd : (artinSchreierPolynomial p (algebraMap K Ω f)).degree ≠ 0 := by
    apply ne_of_gt
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    rw [artinSchreierPolynomial_natDegree]
    exact (Fact.out : p.Prime).pos
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root
    (artinSchreierPolynomial p (algebraMap K Ω f)) hd
  refine ⟨⟨z, ?_⟩⟩
  simpa only [Polynomial.IsRoot, artinSchreierPolynomial, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using hz

/-- A geometric root may be chosen to trivialize the fiber torsor; all
subsequent character eigenvalues are independent of this choice. -/
def artinSchreierGeometricRoot : ArtinSchreierFiber p K Ω f :=
  Classical.choice (artinSchreierFiber_nonempty p K Ω f)

/-- An explicit geometric point of the constructed quotient algebra. -/
def artinSchreierGeometricPoint : ArtinSchreierCover p K f →ₐ[K] Ω :=
  artinSchreierHomOfFiber p K Ω f (artinSchreierGeometricRoot p K Ω f)

variable [Algebra (ZMod p) Ω]

/-- The actual geometric fiber has exactly `p` distinct points. -/
theorem artinSchreierFiber_card : Nat.card (ArtinSchreierFiber p K Ω f) = p := by
  rw [← Nat.card_congr (artinSchreierFiberEquiv p K Ω f
    (artinSchreierGeometricRoot p K Ω f)), Nat.card_zmod]

/-- This count applies to the geometric points of the finite étale quotient. -/
theorem artinSchreierGeometricPoints_card :
    Nat.card (ArtinSchreierCover p K f →ₐ[K] Ω) = p := by
  rw [Nat.card_congr (artinSchreierHomEquivFiber p K Ω f), artinSchreierFiber_card]

variable [Fintype K] [Algebra (ZMod p) K] [IsScalarTower (ZMod p) K Ω]

/-- The canonical positive trace character is realized by a one-dimensional
space on the actual geometric fiber. The Frobenius permutation is the literal
power map, and the existence of a geometric root has been discharged. This
does not assert a compactly supported cohomology or global sheaf trace formula. -/
theorem artinSchreier_trace_character_realization :
    Module.finrank ℂ (artinSchreierCharacterSpace p K Ω f ℂ ZMod.stdAddChar) = 1 ∧
      (∀ z : ArtinSchreierFiber p K Ω f,
        (artinSchreierArithmeticFrobenius p K Ω f z : Ω) = (z : Ω) ^ Fintype.card K) ∧
      LinearMap.trace ℂ (artinSchreierCharacterSpace p K Ω f ℂ ZMod.stdAddChar)
        (artinSchreierCharacterFrobenius p K Ω f ℂ ZMod.stdAddChar) =
          FiniteFieldSums.traceAddChar p K f := by
  refine ⟨artinSchreierCharacterSpace_finrank p K Ω f ℂ ZMod.stdAddChar
    (artinSchreierGeometricRoot p K Ω f),
    artinSchreierArithmeticFrobenius_val p K Ω f, ?_⟩
  exact artinSchreierCharacterFrobenius_trace p K Ω f ℂ ZMod.stdAddChar
    (artinSchreierGeometricRoot p K Ω f)

end AlgebraicallyClosedFiber

/-- Specializing to the prime field gives exactly the standard additive
character in the original Type III finite sums. -/
theorem artinSchreier_standard_character_trace (p : ℕ) [Fact p.Prime] (f : ZMod p) :
    LinearMap.trace ℂ
      (artinSchreierCharacterSpace p (ZMod p) (AlgebraicClosure (ZMod p)) f ℂ ZMod.stdAddChar)
      (artinSchreierCharacterFrobenius p (ZMod p) (AlgebraicClosure (ZMod p)) f ℂ
        ZMod.stdAddChar) = ZMod.stdAddChar f := by
  have h := (artinSchreier_trace_character_realization p (ZMod p)
    (AlgebraicClosure (ZMod p)) f).2.2
  simpa only [FiniteFieldSums.traceAddChar_prime] using h

#print axioms artinSchreierFiberOfHom
#print axioms artinSchreierHomOfFiber
#print axioms artinSchreierHomEquivFiber
#print axioms artinSchreierHomEquivFiber_val
#print axioms artinSchreierHomEquivFiber_translation
#print axioms artinSchreierHomEquivFiber_frobenius
#print axioms artinSchreierFiber_nonempty
#print axioms artinSchreierGeometricRoot
#print axioms artinSchreierGeometricPoint
#print axioms artinSchreierFiber_card
#print axioms artinSchreierGeometricPoints_card
#print axioms artinSchreier_trace_character_realization
#print axioms artinSchreier_standard_character_trace

end PrimeGap182.TypeIII
