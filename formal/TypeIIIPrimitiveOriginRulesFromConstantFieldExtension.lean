import TypeIIIGenericOriginFractionFieldCoordinates
import TypeIIIScalarLocalPropagationFromFilteredTraits

/-!
# Primitive geometric origin Rules after actual constant-field extension

The raw Katz basis family concerns ALL positive raw ranks, finite base fields,
characters and constant-field extensions, on the actual baseGm pullback and
standard geometric tame-log coordinate. It is the GKM7.4.3 origin theorem
transported by geometric constant extension; identifying this continuous
realization remains general model data. ALL integer Tate invariance, smooth
A1 unramified action, and Gm-lisse local/generic rank comparison have their
actual base-pulled endpoints. These are general published theorem/model
families fixed before the prime, not selected Kl3 or complete Rules premises.

Both the original finite-field primitives and generic boundary use the same
H_E/N_E after E is chosen as the parameter fraction field. No arithmetic Weil
representation or invariant stalk is substituted for geometric nearby inertia.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped PrimeGap182.TypeIII.TwoAdicComplexEmbedding

namespace PrimeGap182.TypeIII.PrimitiveOriginRulesFromConstantFieldExtension
open ExactInverseImagesToDerived QSTPrimitiveBridgesFromCommonKatzConstruction
open QSTCompactBridgeFromCompactifiedDerivedPushforward QSTGenericFiberFromActualGenericPoint
open PrimitiveRanksFromComputedGenericLineRank ArithmeticPrimitivesFromCommonKatzConstruction
open RegularTameBasisFromFiniteJordanExponential RankOneTrivialRepresentationFromActualAction
open ScalarLocalPropagationFromFilteredTraits GenericOriginFractionFieldCoordinates

universe mu v
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)
  (L : ∀ X : Scheme, ObjectProperty (C X))
  (O : Constructions C)
  (H : ∀ (E : Type) [Field E], Type v)
  [∀ (E : Type) [Field E], Group (H E)]
  (N : ∀ (E : Type) [Field E],
    C (ArithmeticSourceMaps.fiberScheme E) ⥤ FDRep ℂ (H E))
  (tame : ∀ (E : Type) [Field E], H E →* Multiplicative ℂ)
local instance allLocalizations : ∀ X : Scheme, HasDerivedCategory.{mu} (C X) :=
  fun _ => HasDerivedCategory.standard _

def baseOriginFunctor (K E : Type) [Field K] [Field E] [Algebra K E] :
    C (StartingSourceMaps.affineLine K) ⥤ FDRep ℂ (H E) :=
  U.pull (ArithmeticSourceMaps.localInputMorphism K E) ⋙ N E

variable
  (zeroRestriction : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0),
    O.zero K h2 ⋙ U.pull (ArithmeticSourceMaps.localInputMorphism K K) ≅ 𝟭 _)
  (rawKatzBaseBasis : ∀ (K E : Type) [Field K] [Fintype K] [Field E] [Algebra K E]
    (hK : (2 : K) ≠ 0) (_hE : (2 : E) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n),
    HasRegularTameBasis ((U.pull (baseGmMorphism K E) ⋙ N E).obj
      (O.katz K hK (kloostermanIndex ψ hψ n hn 0))).ρ (tame E) n)
  (lineTateBaseNearby : ∀ (K E : Type) [Field K] [Field E] [Algebra K E]
    (hK : (2 : K) ≠ 0) (_hE : (2 : E) ≠ 0) (n : ℤ),
    O.lineTate K hK n ⋙ baseOriginFunctor C U H N K E ≅ baseOriginFunctor C U H N K E)
  (smoothBaseOriginAction : ∀ (K E : Type) [Field K] [Field E] [Algebra K E]
    (_hK : (2 : K) ≠ 0) (_hE : (2 : E) ≠ 0)
    (A : C (StartingSourceMaps.affineLine K)), L (StartingSourceMaps.affineLine K) A →
    ∀ g, ((baseOriginFunctor C U H N K E).obj A).ρ g = 1)
  (lisseBaseNearbyGenericDimension : ∀ (K E : Type) [Field K] [Field E] [Algebra K E]
    (_hK : (2 : K) ≠ 0) (_hE : (2 : E) ≠ 0)
    (A : C (ArithmeticSourceMaps.fiberScheme K)), L (ArithmeticSourceMaps.fiberScheme K) A →
    Module.finrank ℂ ((U.pull (baseGmMorphism K E) ⋙ N E).obj A) =
      Module.finrank ℂ ((rawGenericFiber K C U G).obj ((boundedDegreeZero C _).obj A)))

include zeroRestriction rawKatzBaseBasis in
/-- The complete raw Kl3 geometric representation after actual base extension. -/
def rawKloosterman3BaseEquiv (K E : Type) [Field K] [Fintype K] [Field E] [Algebra K E]
    (hK : (2 : K) ≠ 0) (hE : (2 : E) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    Representation.Equiv ((baseOriginFunctor C U H N K E).obj
      (rawKloosterman3 C O K hK ψ hψ)).ρ
      (RegularUnipotentRepresentation.tameRepresentation (tame E)) :=
  (TensorListRepresentation.equivOfIso
    ((N E).mapIso (localInputBaseIso K E C U (rawKloosterman3 C O K hK ψ hψ)) ≪≫
      (N E).mapIso ((U.pull (baseGmMorphism K E)).mapIso
        ((zeroRestriction K hK).app
          (O.katz K hK (kloostermanIndex ψ hψ 3 (by decide) 0)))))).trans
    (HasRegularTameBasis.threeEquiv _ _ (rawKatzBaseBasis K E hK hE ψ hψ 3 (by decide)))

include lineTateBaseNearby in
/-- ALL integer geometric twists compare on the actual base-pulled stalk. -/
def lineTateBaseEquiv (K E : Type) [Field K] [Field E] [Algebra K E]
    (hK : (2 : K) ≠ 0) (hE : (2 : E) ≠ 0) (n : ℤ)
    (A : C (StartingSourceMaps.affineLine K)) :
    Representation.Equiv
      ((baseOriginFunctor C U H N K E).obj ((O.lineTate K hK n).obj A)).ρ
      ((baseOriginFunctor C U H N K E).obj A).ρ :=
  TensorListRepresentation.equivOfIso ((lineTateBaseNearby K E hK hE n).app A)

include smoothBaseOriginAction lisseBaseNearbyGenericDimension in
/-- Smooth rank-one sources give the complete trivial geometric representation. -/
def lisseRankOneBaseEquiv (K E : Type) [Field K] [Field E] [Algebra K E]
    (hK : (2 : K) ≠ 0) (hE : (2 : E) ≠ 0)
    (A : C (StartingSourceMaps.affineLine K))
    (hAffine : L (StartingSourceMaps.affineLine K) A)
    (hUnits : SourceGlobalLissityFromKatzPullbacks.lineLisseOnUnits K C U L A)
    (hRank : canonicalLineRank C U G K A = 1) :
    Representation.Equiv ((baseOriginFunctor C U H N K E).obj A).ρ
      (Representation.trivial ℂ (H E) ℂ) :=
  rankOneTrivialEquiv _ (smoothBaseOriginAction K E hK hE A hAffine)
    ((LinearEquiv.finrank_eq ((FDRep.isoToLinearEquiv
        ((N E).mapIso (localInputBaseIso K E C U A))))).trans
      ((lisseBaseNearbyGenericDimension K E hK hE _ hUnits).trans hRank))

section OriginalRules
variable [∀ X, MonoidalCategory (C X)]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  [∀ X, (L X).IsClosedUnderIsomorphisms]
  (M : PrimitiveRamificationFromGeneralKatzTheory.LocalRealization C)
  (standardASLisse : ∀ (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)), ψ ≠ 1 →
      L (StartingSourceMaps.affineLine K) (O.artinSchreier K hK ψ))
  (p : ℕ) [Fact p.Prime] (hK : (2 : ZMod p) ≠ 0)
  (R : RationalPointStalks.Data (CanonicalPrimeFramework.primeSource C U p))

include zeroRestriction rawKatzBaseBasis lineTateBaseNearby smoothBaseOriginAction lisseBaseNearbyGenericDimension standardASLisse in
/-- Exact original Rules uses the same primitives and nearby functor over ANY E. -/
def originRules (E : Type) [Field E] [Algebra (ZMod p) E] (hE : (2 : E) ≠ 0) :
    PublishedLocalOrigin.Rules
      (RationalPointStalks.PrimitiveOperations.primitive R (primitiveOperations C O p hK))
      (LinePurityFromStalks.geometry R
        (GloballyLisseLineRamificationFromKatz.canonicalObservables C U L M G (ZMod p)))
      (fun A => (baseOriginFunctor C U H N (ZMod p) E).obj A) (tame E) where
  LisseAtZero := L (StartingSourceMaps.affineLine (ZMod p))
  lisseRankOne A hAffine hUnits hRank :=
    lisseRankOneBaseEquiv C U G L H N smoothBaseOriginAction lisseBaseNearbyGenericDimension
      (ZMod p) E hK hE A hAffine hUnits hRank
  tate A := lineTateBaseEquiv C U O H N lineTateBaseNearby (ZMod p) E hK hE 1 A
  rawModel _hp ψ hψ :=
    (TensorListRepresentation.equivOfIso (eqToIso
      (congrArg (fun A => (baseOriginFunctor C U H N (ZMod p) E).obj A)
        (primitiveOperations_kloosterman3_nontrivial C O p hK ψ hψ)))).trans
      (rawKloosterman3BaseEquiv C U O H N tame zeroRestriction rawKatzBaseBasis
        (ZMod p) E hK hE ψ hψ)
  asLisse _hp ψ hψ := standardASLisse (ZMod p) hK ψ hψ
end OriginalRules
end PrimeGap182.TypeIII.PrimitiveOriginRulesFromConstantFieldExtension
