import TypeIIICanonicalLocalCorrelation

/-!
# Scalar Kloosterman infinity models from one published source model

Fu Proposition 0.8 gives the single geometric rank-three source model.
General restriction/pullback compatibility, base change for the cubic
cover, and substitution in a linear AS character supply every nonzero
scalar model. These refer to the same scalar operation used to define
sourceInfinity. No correlation or scalar-family model is assumed.

The intended geometric base is algebraically closed. For rank three with
trivial multiplicative characters the quadratic Kummer factor is trivial;
the normalization Tate twist is unramified. These conventions are part of
the published source interpretation, not proved by this adapter.
https://arxiv.org/pdf/math/0702436v5, Proposition 0.8, p. 13.
-/

noncomputable section
open CategoryTheory
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.KloostermanInfinityFromScalar

open PublishedMackey PublishedPhaseApplication CanonicalLocalCorrelation

universe u v w z a b c d
variable {K : Type u} [Field K] {E : Type v} [Field E]
  {I : Type w} [Group I] {H : Type z} [Group H]

/-- Scalar pullbacks on the base and covering local inertia categories.
The units index x ↦ r*x; no scalar-zero pullback is used. -/
structure ScalarData where
  base : (PhaseField K)ˣ → RepresentationFunctor E I I
  cover : (PhaseField K)ˣ → RepresentationFunctor E H H

variable {C : Type a} [Category.{b} C] [MonoidalCategory C]
  {Q : Type c} [Category.{d} Q]
  (O : SheafOperations (PhaseField K) C Q) (J : C ⥤ FDRep E I)
  (P : CubicCoverData (PhaseField K) E I H)
  (A : LinearASData (PhaseField K) E H) (kl : C)

/-- General scalar comparisons and Fu's single-source model.
All restriction, cover-base-change and AS laws quantify over their
arbitrary input objects or coefficients, not a correlation family. -/
structure ScalarRules where
  scalar : ScalarData (K := K) (E := E) (I := I) (H := H)
  restriction : ∀ r B, Representation.Equiv
    (J.obj ((O.scalar r).obj B)).ρ ((scalar.base r).obj (J.obj B)).ρ
  baseChange : ∀ r B, Representation.Equiv
    ((scalar.base (r ^ 3)).obj (P.push.obj B)).ρ
    (P.push.obj ((scalar.cover r).obj B)).ρ
  linearPullback : ∀ r a, Representation.Equiv
    ((scalar.cover r).obj (A.phase a)).ρ (A.phase (a * (r : PhaseField K))).ρ

/-- The original interface adds the normalized primitive infinity model.
The current published application derives it from Fu's raw model. -/
structure Inputs (p : ℕ) extends ScalarRules O J P A where
  sourceModel : 3 < p → Representation.Equiv (J.obj kl).ρ (P.push.obj (A.phase 3)).ρ

namespace Inputs

variable {O J P A kl} {p : ℕ} (R : Inputs O J P A kl p)

/-- Lift the scalar r^3 on the base to r on the cubic cover and compose
the actual equivariant maps. Both sides use the original source kl. -/
def scalarModel (hp : 3 < p) (r : (PhaseField K)ˣ) :
    Representation.Equiv ((sourceInfinity O J kl).kl ((r : PhaseField K) ^ 3)).ρ
      (P.push.obj (A.phase (3 * (r : PhaseField K)))).ρ := by
  have hs := sourceInfinity_unit O J kl (r ^ 3)
  exact (SelectedTensorTransport.representationEquivOfEq hs).trans
    ((R.restriction (r ^ 3) kl).trans
      (((R.scalar.base (r ^ 3)).mapEquiv (R.sourceModel hp)).trans
        ((R.baseChange r (A.phase 3)).trans
          (P.push.mapEquiv (R.linearPullback r 3)))))

/-- Recover the original published-model interface for every nonzero
root r of c, without assuming that entire scalar-family interface. -/
def kloostermanInfinityRules [CharZero E] [Fact p.Prime] [CharP K p] :
    KloostermanInfinityRules p P A (sourceInfinity O J kl) where
  model hp c r hr hcube := by
    rw [← hcube]
    exact R.scalarModel hp (Units.mk0 r hr)

end Inputs
end PrimeGap182.TypeIII.KloostermanInfinityFromScalar

#print axioms PrimeGap182.TypeIII.KloostermanInfinityFromScalar.Inputs.scalarModel
#print axioms PrimeGap182.TypeIII.KloostermanInfinityFromScalar.Inputs.kloostermanInfinityRules
