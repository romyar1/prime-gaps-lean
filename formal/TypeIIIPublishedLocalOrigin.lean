import TypeIIIPublishedPrimitiveSources
import TypeIIIRegularUnipotentRepresentation

/-!
# Published primitive origin theorems on a common inertia stalk

Katz GKM 7.4.3 gives the raw Kl3 regular-unipotent origin model;
section 4.3 gives AS lissity at zero. The same tame logarithm coordinate
is used in the model. Tate twist is geometrically unramified: its
inertia comparison is general in the source object. See also Milne,
Lectures on Etale Cohomology, 30.5(a), for the constant-field Tate action.
https://web.math.princeton.edu/~nmk/Katz-GKM.pdf
https://www.jmilne.org/math/CourseNotes/LEC.pdf

The source rules below quantify over every nontrivial character. The
application selects the canonical character, composes the Tate and raw
model equivalences, and derives the AS model by rank-one lissity. These
are full geometric nearby representations. No assertion of trivial
arithmetic Frobenius on the full Kloosterman representation is made.
-/

noncomputable section
open scoped PrimeGap182.TypeIII.TwoAdicComplexEmbedding

namespace PrimeGap182.TypeIII.PublishedLocalOrigin

open CanonicalCurveInput RegularUnipotentRepresentation

universe u v
variable {p : ℕ} [Fact p.Prime] {Line : Type u} {G : Type v} [Group G]
  (D : PublishedPrimitiveSources.Data p Line) (LG : LineGeometry Line)
  (stalk : Line → FDRep ℂ G) (tame : G →* Multiplicative ℂ)

/-- General local rules on the same primitive objects and inertia stalk.
`tame` is the chosen standard tame logarithm coordinate; this does not
assert a model for arbitrary unrelated homomorphisms of inertia. -/
structure Rules where
  LisseAtZero : Line → Prop
  lisseRankOne : ∀ A, LisseAtZero A → LG.LisseOnUnits A → LG.rank A = 1 →
    Representation.Equiv (stalk A).ρ (Representation.trivial ℂ G ℂ)
  tate : ∀ A, Representation.Equiv (stalk (D.twistOne A)).ρ (stalk A).ρ
  rawModel : 3 < p → ∀ ψ, ψ ≠ 1 →
    Representation.Equiv (stalk (D.kloosterman3 ψ)).ρ (tameRepresentation tame)
  asLisse : 3 < p → ∀ ψ, ψ ≠ 1 → LisseAtZero (D.artinSchreier ψ)

variable {D LG stalk tame} (R : Rules D LG stalk tame)

/-- Compose the unramified twist comparison with the raw source model. -/
def Rules.normalizedKlModel (hp : 3 < p) :
    Representation.Equiv (stalk (D.twistOne D.rawKl)).ρ (tameRepresentation tame) :=
  (R.tate D.rawKl).trans (R.rawModel hp _ (CanonicalSourceCharacter.prime_ne_one p))

include R in
theorem Rules.canonical_asLisse (hp : 3 < p) : R.LisseAtZero D.as :=
  R.asLisse hp _ (CanonicalSourceCharacter.prime_ne_one p)

/-- Apply rank-one lissity to the same canonical AS source. -/
def Rules.canonical_asModel (hp : 3 < p) (has : ASProperties LG D.as) :
    Representation.Equiv (stalk D.as).ρ (Representation.trivial ℂ G ℂ) :=
  R.lisseRankOne D.as (R.canonical_asLisse hp) has.lisse has.rank

end PrimeGap182.TypeIII.PublishedLocalOrigin

#print axioms PrimeGap182.TypeIII.PublishedLocalOrigin.Rules.normalizedKlModel
#print axioms PrimeGap182.TypeIII.PublishedLocalOrigin.Rules.canonical_asLisse
#print axioms PrimeGap182.TypeIII.PublishedLocalOrigin.Rules.canonical_asModel
