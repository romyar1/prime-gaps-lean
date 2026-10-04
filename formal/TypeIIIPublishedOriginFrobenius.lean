import TypeIIIArithmeticOriginFromScalar
import TypeIIIPublishedPrimitiveSources

/-!
# Origin Frobenius from prime-field published source theorems

The geometric Frobenius over a degree-d finite extension is the d-th
power of prime-field geometric Frobenius on the same invariant stalk.
The general base-change comparison below is an explicit framework law.
Katz GKM 7.4.3 supplies identity on the raw Kloosterman origin invariants.
Section 4.3 supplies identity for the AS stalk at zero (the character
value at zero is one). Both source laws quantify over nontrivial
characters on the same prime-field primitive constructions.
https://web.math.princeton.edu/~nmk/Katz-GKM.pdf

Lean selects the canonical character and derives both identity actions
over every extension, without assuming them separately for each field.
The stalk is (j_* A)_0, not the full nearby representation. The existing
Tate normalization and scalar-invariant comparisons are unchanged.
-/

noncomputable section
open scoped PrimeGap182.TypeIII.TwoAdicComplexEmbedding

namespace PrimeGap182.TypeIII.PublishedOriginFrobenius

open ArithmeticSourcesFromOrigin

universe u z
variable {p : ℕ} [Fact p.Prime] {Line : Type u}
  (O : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], OriginStalks.{u,z} Line)

/-- General invariant-stalk base change with its residue Frobenius action.
All source objects use the same origin functors as the arithmetic proof. -/
structure BaseChange where
  comparison : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ A,
    (O E).fiber A ≃ₗ[ℂ] (O (ZMod p)).fiber A
  frobenius : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ A v,
    comparison E A ((O E).frobenius A v) =
      ((O (ZMod p)).frobenius A ^ Module.finrank (ZMod p) E) (comparison E A v)

variable {O}

/-- Identity prime-field action implies identity over every finite extension. -/
theorem BaseChange.identity_action (R : BaseChange O) (A : Line)
    (h : (O (ZMod p)).frobenius A = 1)
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (v : (O E).fiber A) :
    (O E).frobenius A v = v := by
  apply (R.comparison E A).injective
  rw [R.frobenius, h, one_pow]
  rfl

variable (D : PublishedPrimitiveSources.Data p Line)

/-- The two published prime-field statements and a general base-change
law, retaining the characteristic and nontrivial-character guards. -/
structure Rules (O : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
    OriginStalks.{u,z} Line) extends BaseChange O where
  raw : 3 < p → ∀ ψ, ψ ≠ 1 →
    (O (ZMod p)).frobenius (D.kloosterman3 ψ) = 1
  artinSchreier : 3 < p → ∀ ψ, ψ ≠ 1 →
    (O (ZMod p)).frobenius (D.artinSchreier ψ) = 1

variable {D} (R : Rules D O)

include R

theorem Rules.canonical_rawAction (hp : 3 < p)
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (v : (O E).fiber D.rawKl) :
    (O E).frobenius D.rawKl v = v :=
  BaseChange.identity_action R.toBaseChange D.rawKl
    (R.raw hp _ (CanonicalSourceCharacter.prime_ne_one p)) E v

theorem Rules.canonical_asAction (hp : 3 < p)
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (v : (O E).fiber D.as) :
    (O E).frobenius D.as v = v :=
  BaseChange.identity_action R.toBaseChange D.as
    (R.artinSchreier hp _ (CanonicalSourceCharacter.prime_ne_one p)) E v

end PrimeGap182.TypeIII.PublishedOriginFrobenius

#print axioms PrimeGap182.TypeIII.PublishedOriginFrobenius.BaseChange.identity_action
#print axioms PrimeGap182.TypeIII.PublishedOriginFrobenius.Rules.canonical_rawAction
#print axioms PrimeGap182.TypeIII.PublishedOriginFrobenius.Rules.canonical_asAction
