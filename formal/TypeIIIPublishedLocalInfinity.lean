import TypeIIIPublishedPrimitiveSources
import TypeIIIKloostermanInfinityFromScalar

/-!
# Fu's primitive infinity model at the canonical character

Fu, Proposition 0.8, gives the raw geometric Kloosterman infinity model.
For rank three, trivial multiplicative characters and p > 3 it is
[3]_* AS_psi(3x); the quadratic Kummer factor has even exponent.
https://arxiv.org/pdf/math/0702436v5, printed page 13.

The raw theorem below quantifies over every nontrivial character. Its
right side uses the AS construction for that same character. The general
Tate-inertia law and the raw model are explicit published inputs.
The application composes them at the canonical character to construct
the normalized source model used by the existing scalar/Mackey proof.
Everything here concerns full geometric inertia, before local Fourier.
-/

noncomputable section

namespace PrimeGap182.TypeIII.PublishedLocalInfinity

open PublishedPhaseApplication PublishedMackey

universe u v w
variable {p : ℕ} [Fact p.Prime] {Line : Type u}
  {I : Type v} [Group I] {H : Type w} [Group H]
  (D : PublishedPrimitiveSources.Data p Line) (stalk : Line → FDRep ℂ I)
  (P : CubicCoverData (PhaseField (ZMod p)) ℂ I H)
  (coveringAS : Line → LinearASData (PhaseField (ZMod p)) ℂ H)

/-- General raw source and Tate laws for the same inertia operations.
`coveringAS` is the existing coefficient-map pullback of a line object,
so the character on the right changes with the character on the left. -/
structure Rules where
  tate : ∀ A, Representation.Equiv (stalk (D.twistOne A)).ρ (stalk A).ρ
  rawModel : 3 < p → ∀ ψ, ψ ≠ 1 →
    Representation.Equiv (stalk (D.kloosterman3 ψ)).ρ
      (P.push.obj ((coveringAS (D.artinSchreier ψ)).phase 3)).ρ

variable {D stalk P coveringAS} (R : Rules D stalk P coveringAS)

/-- The exact normalized infinity model for the canonical Kl3 and AS pair. -/
def Rules.normalizedModel (hp : 3 < p) :
    Representation.Equiv (stalk (D.twistOne D.rawKl)).ρ
      (P.push.obj ((coveringAS D.as).phase 3)).ρ :=
  (R.tate D.rawKl).trans (R.rawModel hp _ (CanonicalSourceCharacter.prime_ne_one p))

end PrimeGap182.TypeIII.PublishedLocalInfinity

#print axioms PrimeGap182.TypeIII.PublishedLocalInfinity.Rules.normalizedModel
