import TypeIIIRankOneTrivialRepresentationFromActualAction
import TypeIIIGloballyLisseLineRamificationFromKatz
import TypeIIIPublishedLocalOrigin
import TypeIIITensorListRepresentation

/-!
# Origin Rules from universal nearby theorems on the same ordinary objects

The ALL-positive-rank raw Katz input is the actual regular tame basis property
for the chosen standard tame-log coordinate. GKM7.3.2(2),7.4.1 and7.4.3 supply
single-Jordan origin monodromy; identifying the actual continuous coefficient
realization and standard tame coordinate remains an explicit general model
comparison. GKM4.1.1(3) is the infinity statement, not the origin basis theorem.

ALL-integer geometric Tate invariance, globally A1-lisse unramified nearby
action, and globally Gm-lisse local/generic coefficient dimension are general
inputs fixed before the prime. The exact original origin Rules (four laws and the lissity predicate) is
constructed, including full representation equivalences. H/N are intended as
GEOMETRIC inertia at zero on the actual generic stalk, not arithmetic Weil
or global fundamental-group representations. Their recognition is external.
No selected Kl3 or
AS representation equivalence is supplied, and no inertia foundations are
reconstructed. The actual adic realization remains external.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped PrimeGap182.TypeIII.TwoAdicComplexEmbedding

namespace PrimeGap182.TypeIII.LocalOriginRulesFromUniversalNearbyTheorems
open ExactInverseImagesToDerived QSTPrimitiveBridgesFromCommonKatzConstruction
open QSTCompactBridgeFromCompactifiedDerivedPushforward QSTGenericFiberFromActualGenericPoint
open PrimitiveRanksFromComputedGenericLineRank ArithmeticPrimitivesFromCommonKatzConstruction
open RegularTameBasisFromFiniteJordanExponential RankOneTrivialRepresentationFromActualAction

universe mu v
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)
  (L : ∀ X : Scheme, ObjectProperty (C X))
  (O : Constructions C)
  (H : ∀ (K : Type) [Field K], Type v)
  [∀ (K : Type) [Field K], Group (H K)]
  (N : ∀ (K : Type) [Field K],
    C (ArithmeticSourceMaps.fiberScheme K) ⥤ FDRep ℂ (H K))
  (tame : ∀ (K : Type) [Field K], H K →* Multiplicative ℂ)
local instance allLocalizations : ∀ X : Scheme, HasDerivedCategory.{mu} (C X) :=
  fun _ => HasDerivedCategory.standard _

def originFunctor (K : Type) [Field K] :
    C (StartingSourceMaps.affineLine K) ⥤ FDRep ℂ (H K) :=
  U.pull (ArithmeticSourceMaps.localInputMorphism K K) ⋙ N K

variable
  (zeroRestriction : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0),
    O.zero K h2 ⋙ U.pull (ArithmeticSourceMaps.localInputMorphism K K) ≅ 𝟭 _)
  (rawKatzBasis : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n),
    HasRegularTameBasis ((N K).obj
      (O.katz K h2 (kloostermanIndex ψ hψ n hn 0))).ρ (tame K) n)
  (lineTateNearby : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0) (n : ℤ),
    O.lineTate K h2 n ⋙ originFunctor C U H N K ≅ originFunctor C U H N K)
  (smoothOriginAction : ∀ (K : Type) [Field K] (_h2 : (2 : K) ≠ 0)
    (A : C (StartingSourceMaps.affineLine K)), L (StartingSourceMaps.affineLine K) A →
    ∀ g, ((originFunctor C U H N K).obj A).ρ g = 1)
  (lisseNearbyGenericDimension : ∀ (K : Type) [Field K] (_h2 : (2 : K) ≠ 0)
    (A : C (ArithmeticSourceMaps.fiberScheme K)), L (ArithmeticSourceMaps.fiberScheme K) A →
    Module.finrank ℂ ((N K).obj A) =
      Module.finrank ℂ ((rawGenericFiber K C U G).obj ((boundedDegreeZero C _).obj A)))

include zeroRestriction rawKatzBasis in
/-- ALL nontrivial raw rank-three source objects have the full computed model. -/
def rawKloosterman3Equiv (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    Representation.Equiv
      ((originFunctor C U H N K).obj (rawKloosterman3 C O K h2 ψ hψ)).ρ
      (RegularUnipotentRepresentation.tameRepresentation (tame K)) :=
  (TensorListRepresentation.equivOfIso
    ((N K).mapIso ((zeroRestriction K h2).app
      (O.katz K h2 (kloostermanIndex ψ hψ 3 (by decide) 0))))).trans
    (HasRegularTameBasis.threeEquiv _ _ (rawKatzBasis K h2 ψ hψ 3 (by decide)))

include lineTateNearby in
/-- Every integer twist has the actual full nearby representation comparison. -/
def lineTateEquiv (K : Type) [Field K] (h2 : (2 : K) ≠ 0) (n : ℤ)
    (A : C (StartingSourceMaps.affineLine K)) :
    Representation.Equiv
      ((originFunctor C U H N K).obj ((O.lineTate K h2 n).obj A)).ρ
      ((originFunctor C U H N K).obj A).ρ :=
  TensorListRepresentation.equivOfIso ((lineTateNearby K h2 n).app A)

include smoothOriginAction lisseNearbyGenericDimension in
/-- Globally affine-lisse rank-one objects yield the full trivial model. -/
def lisseRankOneEquiv (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    (A : C (StartingSourceMaps.affineLine K))
    (hAffine : L (StartingSourceMaps.affineLine K) A)
    (hUnits : SourceGlobalLissityFromKatzPullbacks.lineLisseOnUnits K C U L A)
    (hRank : canonicalLineRank C U G K A = 1) :
    Representation.Equiv ((originFunctor C U H N K).obj A).ρ
      (Representation.trivial ℂ (H K) ℂ) :=
  rankOneTrivialEquiv _ (smoothOriginAction K h2 A hAffine)
    ((lisseNearbyGenericDimension K h2 _ hUnits).trans hRank)

section OriginalRules
variable [∀ X, MonoidalCategory (C X)]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  [∀ X, (L X).IsClosedUnderIsomorphisms]
  (M : PrimitiveRamificationFromGeneralKatzTheory.LocalRealization C)
  (standardASLisse : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)), ψ ≠ 1 →
      L (StartingSourceMaps.affineLine K) (O.artinSchreier K h2 ψ))
  (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
  (R : RationalPointStalks.Data (CanonicalPrimeFramework.primeSource C U p))

include zeroRestriction rawKatzBasis lineTateNearby smoothOriginAction lisseNearbyGenericDimension standardASLisse in
/-- The complete original Rules is derived on the SAME primitive/line/stalk system. -/
def originRules : PublishedLocalOrigin.Rules
    (RationalPointStalks.PrimitiveOperations.primitive R (primitiveOperations C O p h2))
    (LinePurityFromStalks.geometry R
      (GloballyLisseLineRamificationFromKatz.canonicalObservables C U L M G (ZMod p)))
    (fun A => (originFunctor C U H N (ZMod p)).obj A) (tame (ZMod p)) where
  LisseAtZero := L (StartingSourceMaps.affineLine (ZMod p))
  lisseRankOne A hAffine hUnits hRank :=
    lisseRankOneEquiv C U G L H N smoothOriginAction lisseNearbyGenericDimension
      (ZMod p) h2 A hAffine hUnits hRank
  tate A := lineTateEquiv C U O H N lineTateNearby (ZMod p) h2 1 A
  rawModel _hp ψ hψ :=
    (TensorListRepresentation.equivOfIso (eqToIso
      (congrArg (fun A => (originFunctor C U H N (ZMod p)).obj A)
        (primitiveOperations_kloosterman3_nontrivial C O p h2 ψ hψ)))).trans
      (rawKloosterman3Equiv C U O H N tame zeroRestriction rawKatzBasis
        (ZMod p) h2 ψ hψ)
  asLisse _hp ψ hψ := standardASLisse (ZMod p) h2 ψ hψ
end OriginalRules
end PrimeGap182.TypeIII.LocalOriginRulesFromUniversalNearbyTheorems
