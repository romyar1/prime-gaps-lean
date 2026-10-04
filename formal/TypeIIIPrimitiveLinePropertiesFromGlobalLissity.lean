import TypeIIISourceGeometricRulesFromGlobalLissity

/-!
# Primitive line lissity from the SAME ordinary Katz and AS construction

The original normalized Kl3 and AS property records use the actual global
lissity predicate of SAME-U restriction to Gm. Their lissity fields follow
from ALL-field unequal-length Katz lissity and standard AS lissity.
Each record's four rank/purity/local fields remains a separate hypothesis;
no finished primitive-property record or selected lissity is a premise.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.PrimitiveLinePropertiesFromGlobalLissity
open ExactInverseImagesToDerived QSTPrimitiveBridgesFromCommonKatzConstruction
open SourceGlobalLissityFromKatzPullbacks SourceGeometricRulesFromGlobalLissity

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  [∀ X, MonoidalCategory (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (L : ∀ X : Scheme, ObjectProperty (C X))
  [∀ X, (L X).IsClosedUnderIsomorphisms]
  (O : Constructions C)
  (zeroRestriction : ∀ (E : Type) [Field E] (h2 : (2 : E) ≠ 0),
    O.zero E h2 ⋙ U.pull (ArithmeticSourceMaps.localInputMorphism E E) ≅
      𝟭 (C (ArithmeticSourceMaps.fiberScheme E)))
  (unequalKatzLisse : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0)
    (a : KatzIndex E), a.upper.length ≠ a.lower.length →
      L (ArithmeticSourceMaps.fiberScheme E) (member C O E h2 a))
  (lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y),
    L Y A → L X ((U.pull f).obj A))
  (standardASLisse : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0)
    (ψ : AddChar E (PadicAlgCl 2)), ψ ≠ 1 →
      L (StartingSourceMaps.affineLine E) (O.artinSchreier E h2 ψ))
  (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
  (R : RationalPointStalks.Data (CanonicalPrimeFramework.primeSource C U p))
  (observables : LinePurityFromStalks.Observables (C (StartingSourceMaps.affineLine (ZMod p))))
  (ψ : AddChar (ZMod p) (PadicAlgCl 2)) (hψ : ψ ≠ 1)

local notation "LG" => lineGeometry C U L p R observables
local notation "Kl" => Functor.obj (twistOne C O (ZMod p) h2) (rawKloosterman3 C O (ZMod p) h2 ψ hψ)
local notation "AS" => O.artinSchreier (ZMod p) h2 ψ

include zeroRestriction unequalKatzLisse in
/-- The exact original normalized Kl3 record, with four unchanged rank,
purity and ramification hypotheses and derived whole-Gm lissity. -/
theorem kloostermanConstructor
    (rank : (LG).rank Kl = 3)
    (pure : (LG).Pure Kl 0)
    (tame : (LG).TameZero Kl)
    (breaks : (LG).BreaksLE Kl (1 / 3)) : CanonicalCurveInput.Kl3Properties LG Kl where
  lisse := normalizedKl_restriction_lisse (ZMod p) C U L O zeroRestriction unequalKatzLisse h2 ψ hψ
  rank := rank
  pure := pure
  tame := tame
  breaks := breaks

omit [∀ X, (L X).IsClosedUnderIsomorphisms] in
include lissePull standardASLisse hψ in
/-- The exact original standard AS record, with four unchanged rank,
purity and ramification hypotheses and derived SAME-U restriction lissity. -/
theorem artinSchreierConstructor
    (rank : (LG).rank AS = 1)
    (pure : (LG).Pure AS 0)
    (tame : (LG).TameZero AS)
    (slope : (LG).Isoclinic AS 1) : CanonicalCurveInput.ASProperties LG AS where
  lisse := lissePull (ArithmeticSourceMaps.localInputMorphism (ZMod p) (ZMod p)) AS
    (standardASLisse (ZMod p) h2 ψ hψ)
  rank := rank
  pure := pure
  tame := tame
  slope := slope

end PrimeGap182.TypeIII.PrimitiveLinePropertiesFromGlobalLissity
