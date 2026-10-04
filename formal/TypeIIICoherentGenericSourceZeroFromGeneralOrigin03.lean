import TypeIIIOriginModelsFromSameComputedCoefficients
import TypeIIIPublishedLocalOrigin

/-!
# Computed generic source zero models from one general origin theory

C/U/M and the coefficient transport are fixed before p. The theorem
record quantifies over ALL finite base fields, ALL nontrivial characters,
ALL positive raw ranks, ANY extension field, ALL integer Tate twists and
ALL tame lisse objects under actual scalar and constant-field pulls.

The generic zero functor and primitive zero functor are literal SAME-U
restrictions through the original parameter fraction field. The two
selected source models ZK/ZA are OUTPUTS. No Kl3 origin Rules, geometric
Inputs, selected regular model, selected scalar equivalence, invariants
substitution, rank-six conclusion, local profile or Application provider
is accepted. Genuine continuous-adic interpretation of M and the general
trait/theorem clauses remains an explicit published-theory boundary.

This NEW source has not been elaborated; it is a bounded specialized
application, not a construction of the adic foundations or final endpoint.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory PrimeGap182.TypeIII.TwoAdicComplexEmbedding

namespace PrimeGap182.TypeIII.CoherentGenericSourceZeroFromGeneralOrigin03
open ExactInverseImagesToDerived PrimitiveRamificationFromGeneralKatzTheory
open OriginModelsFromSameComputedCoefficients PrimitiveOriginRulesFromConstantFieldExtension
open GenericOriginFractionFieldCoordinates RegularTameBasisFromFiniteJordanExponential
open ArithmeticPrimitivesFromCommonKatzConstruction QSTPrimitiveBridgesFromCommonKatzConstruction
open CanonicalCurveInput GenericSourceSpecialization FourierSourcePullbacks
open GeometricOriginFromScalar RegularUnipotentRepresentation

universe mu
variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  [∀ X, MonoidalCategory (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (M : LocalRealization C)
  [∀ (E : Type) [Field E], (M.origin E).Monoidal]
  (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)
  (L : ∀ X : Scheme, ObjectProperty (C X))
  [∀ X, (L X).IsClosedUnderIsomorphisms]
  (O : Constructions C)
  (tame : ∀ (E : Type) [Field E], M.originGroup E →* Multiplicative ℂ)

/-- GENERAL theorem and actual-operation clauses before selecting p.
No field is an assertion about a completed Type III family. -/
structure GeneralOriginApplicationLaws where
  zeroRestriction : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0),
    O.zero K h2 ⋙ U.pull (ArithmeticSourceMaps.localInputMorphism K K) ≅ 𝟭 _
  rawKatzBaseBasis : ∀ (K E : Type) [Field K] [Fintype K] [Field E] [Algebra K E]
    (hK : (2 : K) ≠ 0) (_hE : (2 : E) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n),
    HasRegularTameBasis ((U.pull (ScalarLocalPropagationFromFilteredTraits.baseGmMorphism K E) ⋙
      nearbyOrigin C M E).obj (O.katz K hK (kloostermanIndex ψ hψ n hn 0))).ρ (tame E) n
  lineTateBaseNearby : ∀ (K E : Type) [Field K] [Field E] [Algebra K E]
    (hK : (2 : K) ≠ 0) (_hE : (2 : E) ≠ 0) (n : ℤ),
    O.lineTate K hK n ⋙ baseOriginFunctor C U (fun F => M.originGroup F)
      (nearbyOrigin C M) K E ≅
    baseOriginFunctor C U (fun F => M.originGroup F) (nearbyOrigin C M) K E
  smoothBaseOriginAction : ∀ (K E : Type) [Field K] [Field E] [Algebra K E]
    (_hK : (2 : K) ≠ 0) (_hE : (2 : E) ≠ 0)
    (A : C (StartingSourceMaps.affineLine K)), L (StartingSourceMaps.affineLine K) A →
    ∀ g, ((baseOriginFunctor C U (fun F => M.originGroup F) (nearbyOrigin C M) K E).obj A).ρ g = 1
  lisseBaseNearbyGenericDimension : ∀ (K E : Type) [Field K] [Field E] [Algebra K E]
    (_hK : (2 : K) ≠ 0) (_hE : (2 : E) ≠ 0)
    (A : C (ArithmeticSourceMaps.fiberScheme K)), L (ArithmeticSourceMaps.fiberScheme K) A →
    Module.finrank ℂ ((U.pull (ScalarLocalPropagationFromFilteredTraits.baseGmMorphism K E) ⋙
      nearbyOrigin C M E).obj A) =
    Module.finrank ℂ ((QSTGenericFiberFromActualGenericPoint.rawGenericFiber K C U G).obj
      ((QSTCompactBridgeFromCompactifiedDerivedPushforward.boundedDegreeZero C _).obj A))
  standardASLisse : ∀ (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)), ψ ≠ 1 →
      L (StartingSourceMaps.affineLine K) (O.artinSchreier K hK ψ)
  lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y),
    L Y A → L X ((U.pull f).obj A)
  scalarOriginAutomorphism : ∀ (F : Type) [Field F], (2 : F) ≠ 0 →
    Fˣ → M.originGroup F ≃* M.originGroup F
  scalarOriginComparison : ∀ (F : Type) [Field F] (hF : (2 : F) ≠ 0) (a : Fˣ),
    (L (ArithmeticSourceMaps.fiberScheme F)).ι ⋙
      U.pull (ArithmeticSourceMaps.scalarMorphism F F a) ⋙ M.origin F ≅
    (L (ArithmeticSourceMaps.fiberScheme F)).ι ⋙ M.origin F ⋙
      Action.res (FGModuleCat (PadicAlgCl 2)) (scalarOriginAutomorphism F hF a).toMonoidHom
  scalarOriginTameQuotient : ∀ (F : Type) [Field F] (hF : (2 : F) ≠ 0)
    (a : Fˣ) (g : M.originGroup F), ∃ w : M.wildOrigin F,
      scalarOriginAutomorphism F hF a g = g * w.val
  baseOriginHom : ∀ (F B : Type) [Field F] [Field B] [Algebra F B],
    (2 : F) ≠ 0 → (2 : B) ≠ 0 → M.originGroup B →* M.originGroup F
  baseOriginWild : ∀ (F B : Type) [Field F] [Field B] [Algebra F B]
    (hF : (2 : F) ≠ 0) (hB : (2 : B) ≠ 0) (g : M.wildOrigin B),
    baseOriginHom F B hF hB g.val ∈ M.wildOrigin F
  baseOriginComparison : ∀ (F B : Type) [Field F] [Field B] [Algebra F B]
    (hF : (2 : F) ≠ 0) (hB : (2 : B) ≠ 0),
    (L (ArithmeticSourceMaps.fiberScheme F)).ι ⋙
      U.pull (ScalarLocalPropagationFromFilteredTraits.baseGmMorphism F B) ⋙ M.origin B ≅
    (L (ArithmeticSourceMaps.fiberScheme F)).ι ⋙ M.origin F ⋙
      Action.res (FGModuleCat (PadicAlgCl 2)) (baseOriginHom F B hF hB)

variable (laws : GeneralOriginApplicationLaws C U M G L O tame)
  (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
  (R : RationalPointStalks.Data (CanonicalPrimeFramework.primeSource C U p))

include C U M G L O tame laws p h2 R

/-- The primitive rules are COMPUTED for the actual parameter fraction
field; the extension has no Fintype instance or finite-field restriction. -/
def computedPrimitiveOriginRules :=
  OriginModelsFromSameComputedCoefficients.originRules C U M G L O tame
    laws.zeroRestriction laws.rawKatzBaseBasis laws.lineTateBaseNearby
    laws.smoothBaseOriginAction laws.lisseBaseNearbyGenericDimension
    laws.standardASLisse p h2 R (ParameterFractionField (ZMod p))
    (OriginModelsFromSameComputedCoefficients.fraction_two_ne_zero (ZMod p) h2)

/-- Actual all-tame scalar transport through the SAME parameter field. -/
def computedScalarOriginPullback :=
  OriginModelsFromSameComputedCoefficients.originPullback C U M G L laws.lissePull
    laws.scalarOriginAutomorphism laws.scalarOriginComparison laws.scalarOriginTameQuotient
    laws.baseOriginHom laws.baseOriginWild laws.baseOriginComparison p h2 R

include C U M G L O tame laws p h2 R

/-- Construct the old geometric source Inputs from general theorems and
literal primitives. It is an output, not a selected-family premise. -/
def computedGeometricSourceInputs (hp : 3 < p) :
    GeometricOriginFromScalar.Inputs (ZMod p) (fun f => U.pull f)
      (fun A => Functor.obj (OriginModelsFromSameComputedCoefficients.genericZero C U M (ZMod p)) A) (LinePurityFromStalks.geometry R (GloballyLisseLineRamificationFromKatz.canonicalObservables C U L M G (ZMod p))) (PublishedPrimitiveSources.Data.twistOne (RationalPointStalks.PrimitiveOperations.primitive R (primitiveOperations C O p h2)) (PublishedPrimitiveSources.Data.rawKl (RationalPointStalks.PrimitiveOperations.primitive R (primitiveOperations C O p h2)))) (PublishedPrimitiveSources.Data.as (RationalPointStalks.PrimitiveOperations.primitive R (primitiveOperations C O p h2))) (tame (ParameterFractionField (ZMod p))) where
  primitiveZero A := (OriginModelsFromSameComputedCoefficients.primitiveZero C U M (ZMod p)).obj A
  scalarZero c A hL hA :=
    (computedScalarOriginPullback C U M G L O tame laws p h2 R).scalarZero c A hL hA
  LisseAtZero := L (StartingSourceMaps.affineLine (ZMod p))
  lisseZeroRankOne A hAffine hUnits hRank :=
    (computedPrimitiveOriginRules C U M G L O tame laws p h2 R).lisseRankOne A hAffine hUnits hRank
  klModel := (computedPrimitiveOriginRules C U M G L O tame laws p h2 R).normalizedKlModel hp
  asLisseAtZero :=
    (computedPrimitiveOriginRules C U M G L O tame laws p h2 R).canonical_asLisse hp

variable
  (hkl : Kl3Properties (LinePurityFromStalks.geometry R (GloballyLisseLineRamificationFromKatz.canonicalObservables C U L M G (ZMod p))) (PublishedPrimitiveSources.Data.twistOne (RationalPointStalks.PrimitiveOperations.primitive R (primitiveOperations C O p h2)) (PublishedPrimitiveSources.Data.rawKl (RationalPointStalks.PrimitiveOperations.primitive R (primitiveOperations C O p h2))))) (has : ASProperties (LinePurityFromStalks.geometry R (GloballyLisseLineRamificationFromKatz.canonicalObservables C U L M G (ZMod p))) (PublishedPrimitiveSources.Data.as (RationalPointStalks.PrimitiveOperations.primitive R (primitiveOperations C O p h2))))

include hkl

/-- ZK on the literal local scalar recipe, derived by the actual source
coordinate isomorphism and general tame scalar transport. -/
def computedLocalKlZero (hp : 3 < p) (lambda : (PublishedPhaseApplication.PhaseField (ZMod p))ˣ) :
    Representation.Equiv
      (Functor.obj (OriginModelsFromSameComputedCoefficients.genericZero C U M (ZMod p)) ((localSpecialization (ZMod p)
          (SourceInverseImageSystem.System.geometricPullbacks (CanonicalPrimeFramework.primeSource C U p))
          (SourceInverseImageSystem.System.localPullbacks (CanonicalPrimeFramework.primeSource C U p))).obj
        (((SourceInverseImageSystem.System.localPullbacks
          (CanonicalPrimeFramework.primeSource C U p)).localEnd
            (FourierSourceMaps.scalarMorphism (ZMod p) lambda)).obj
          (localSource (ZMod p)
            (SourceInverseImageSystem.System.geometricPullbacks (CanonicalPrimeFramework.primeSource C U p))
            (SourceInverseImageSystem.System.localPullbacks (CanonicalPrimeFramework.primeSource C U p)) (PublishedPrimitiveSources.Data.twistOne (RationalPointStalks.PrimitiveOperations.primitive R (primitiveOperations C O p h2)) (PublishedPrimitiveSources.Data.rawKl (RationalPointStalks.PrimitiveOperations.primitive R (primitiveOperations C O p h2)))))))).ρ
      (tameRepresentation (tame (ParameterFractionField (ZMod p)))) :=
  (TensorListRepresentation.equivOfIso (Functor.mapIso (OriginModelsFromSameComputedCoefficients.genericZero C U M (ZMod p))
      (GeometricOriginFromScalar.scalarSourceIso (ZMod p)
        (SourceInverseImageSystem.System.geometricPullbacks (CanonicalPrimeFramework.primeSource C U p))
        (SourceInverseImageSystem.System.localPullbacks (CanonicalPrimeFramework.primeSource C U p))
        lambda (PublishedPrimitiveSources.Data.twistOne (RationalPointStalks.PrimitiveOperations.primitive R (primitiveOperations C O p h2)) (PublishedPrimitiveSources.Data.rawKl (RationalPointStalks.PrimitiveOperations.primitive R (primitiveOperations C O p h2))))))).trans
    ((computedGeometricSourceInputs C U M G L O tame laws p h2 R hp).scalarModel hkl
      (GeometricOriginFromScalar.constantCoefficient (ZMod p) lambda))

omit hkl
include has

/-- ZA on the literal AS(T^2*x/s) recipe. The source has smooth rank-one
origin action before any scalar map is selected. -/
def computedAdditiveZero (hp : 3 < p) (s : (PublishedPhaseApplication.PhaseField (ZMod p))ˣ) :
    Representation.Equiv
      (Functor.obj (OriginModelsFromSameComputedCoefficients.genericZero C U M (ZMod p)) (additiveSource (ZMod p)
        (SourceInverseImageSystem.System.geometricPullbacks (CanonicalPrimeFramework.primeSource C U p)) (PublishedPrimitiveSources.Data.as (RationalPointStalks.PrimitiveOperations.primitive R (primitiveOperations C O p h2))) s)).ρ
      (Representation.trivial ℂ (M.originGroup (ParameterFractionField (ZMod p))) ℂ) :=
  (computedGeometricSourceInputs C U M G L O tame laws p h2 R hp).additiveModel has s

end PrimeGap182.TypeIII.CoherentGenericSourceZeroFromGeneralOrigin03

#print axioms PrimeGap182.TypeIII.CoherentGenericSourceZeroFromGeneralOrigin03.computedGeometricSourceInputs
#print axioms PrimeGap182.TypeIII.CoherentGenericSourceZeroFromGeneralOrigin03.computedLocalKlZero
#print axioms PrimeGap182.TypeIII.CoherentGenericSourceZeroFromGeneralOrigin03.computedAdditiveZero
