import TypeIIICanonicalSourceCharacter

/-!
# Applying the published primitive-source theorems at the fixed character

The operations below are the Artin--Schreier and rank-three Kloosterman
constructions for an arbitrary prime-field additive character, together
with Tate twist and the common arithmetic line trace. The seven general
laws are explicit published inputs, not theorems proved about an adic
category in this file. They quantify over every nontrivial character.

Katz, GKM 4.1.1, 4.3 and 11.0.1 give the rank-three, AS and trace laws;
the hypergeometric classification is the standard Kloosterman case used
by QST 7.8. Tate twist does not change the geometric class.
https://web.math.princeton.edu/~nmk/Katz-GKM.pdf
https://arxiv.org/html/2101.00635v4

The application selects the already constructed canonical character,
discharges its nontriviality, and obtains the exact existing source
properties and traces. No Type III family estimate is a field here.
-/

noncomputable section
open scoped PrimeGap182.TypeIII.TwoAdicComplexEmbedding

namespace PrimeGap182.TypeIII.PublishedPrimitiveSources

open CanonicalCurveInput StartingSourceComplexity TwoAdicComplexEmbedding

universe u
variable (p : ℕ) [Fact p.Prime]

/-- Extend any prime-field coefficient character by the actual field trace. -/
def extension (ψ : AddChar (ZMod p) (PadicAlgCl 2))
    (E : Type) [Field E] [Algebra (ZMod p) E] : AddChar E (PadicAlgCl 2) :=
  ψ.compAddMonoidHom (Algebra.trace (ZMod p) E).toAddMonoidHom

def complexCharacter (ψ : AddChar (ZMod p) (PadicAlgCl 2))
    (E : Type) [Field E] [Algebra (ZMod p) E] : AddChar E ℂ :=
  complexEquiv.toMonoidHom.compAddChar (extension p ψ E)

/-- The published finite-extension character becomes the implemented one. -/
theorem complexCharacter_canonical (E : Type) [Field E] [Algebra (ZMod p) E] :
    complexCharacter p (CanonicalSourceCharacter.prime p) E =
      FiniteFieldSums.traceAddChar p E := by
  apply AddChar.ext
  intro z
  exact CanonicalSourceCharacter.extension_complex p E z

/-- General primitive operations on one arithmetic line category. -/
structure Data (Line : Type u) where
  artinSchreier : AddChar (ZMod p) (PadicAlgCl 2) → Line
  kloosterman3 : AddChar (ZMod p) (PadicAlgCl 2) → Line
  twistOne : Line → Line
  trace : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], Line → E → ℂ

variable {p} {Line : Type u} (D : Data p Line)

abbrev Data.rawKl : Line := D.kloosterman3 (CanonicalSourceCharacter.prime p)
abbrev Data.as : Line := D.artinSchreier (CanonicalSourceCharacter.prime p)

/-- Published general statements on those exact operations. The p > 3
guard is retained in the ramification-bearing source properties. Traces
are at units for Kl3 and at every point for AS. -/
structure Rules (L : LineGeometry Line) (C : PrimitiveClasses Line) : Prop where
  kl3 : 3 < p → ∀ ψ, ψ ≠ 1 → Kl3Properties L (D.twistOne (D.kloosterman3 ψ))
  artinSchreier : 3 < p → ∀ ψ, ψ ≠ 1 → ASProperties L (D.artinSchreier ψ)
  hypergeometric : ∀ ψ, ψ ≠ 1 → C.Hypergeometric (D.twistOne (D.kloosterman3 ψ)) 3
  nontrivialAS : ∀ ψ, ψ ≠ 1 → C.NontrivialArtinSchreier (D.artinSchreier ψ)
  rawTrace : ∀ ψ, ψ ≠ 1 →
    ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ z : Eˣ,
      D.trace E (D.kloosterman3 ψ) (z : E) =
        (-1 : ℂ) ^ (3 - 1) * KatzSourceNormalization.rawKl3 (complexCharacter p ψ E) z
  tateTrace : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ A z,
    D.trace E (D.twistOne A) z = (Fintype.card E : ℂ)⁻¹ * D.trace E A z
  asTrace : ∀ ψ, ψ ≠ 1 →
    ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ z : E,
      D.trace E (D.artinSchreier ψ) z = complexEquiv (extension p ψ E z)

variable {D} {L : LineGeometry Line} {C : PrimitiveClasses Line}
  (R : Rules D L C)

include R

theorem Rules.canonical_kl3 (hp : 3 < p) : Kl3Properties L (D.twistOne D.rawKl) :=
  R.kl3 hp _ (CanonicalSourceCharacter.prime_ne_one p)

theorem Rules.canonical_as (hp : 3 < p) : ASProperties L D.as :=
  R.artinSchreier hp _ (CanonicalSourceCharacter.prime_ne_one p)

theorem Rules.canonical_hypergeometric : C.Hypergeometric (D.twistOne D.rawKl) 3 :=
  R.hypergeometric _ (CanonicalSourceCharacter.prime_ne_one p)

theorem Rules.canonical_nontrivialAS : C.NontrivialArtinSchreier D.as :=
  R.nontrivialAS _ (CanonicalSourceCharacter.prime_ne_one p)

theorem Rules.canonical_rawTrace
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (z : Eˣ) :
    D.trace E D.rawKl (z : E) =
      (-1 : ℂ) ^ (3 - 1) * KatzSourceNormalization.rawKl3 (FiniteFieldSums.traceAddChar p E) z := by
  simpa only [complexCharacter_canonical] using
    R.rawTrace _ (CanonicalSourceCharacter.prime_ne_one p) E z

theorem Rules.canonical_asTrace
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (z : E) :
    D.trace E D.as z =
      complexEquiv (CanonicalSourceCharacter.extension p E z) :=
  R.asTrace _ (CanonicalSourceCharacter.prime_ne_one p) E z

end PrimeGap182.TypeIII.PublishedPrimitiveSources

#print axioms PrimeGap182.TypeIII.PublishedPrimitiveSources.complexCharacter_canonical
#print axioms PrimeGap182.TypeIII.PublishedPrimitiveSources.Rules.canonical_kl3
#print axioms PrimeGap182.TypeIII.PublishedPrimitiveSources.Rules.canonical_as
#print axioms PrimeGap182.TypeIII.PublishedPrimitiveSources.Rules.canonical_hypergeometric
#print axioms PrimeGap182.TypeIII.PublishedPrimitiveSources.Rules.canonical_nontrivialAS
#print axioms PrimeGap182.TypeIII.PublishedPrimitiveSources.Rules.canonical_rawTrace
#print axioms PrimeGap182.TypeIII.PublishedPrimitiveSources.Rules.canonical_asTrace
