import TypeIIIPrimitiveOriginRulesFromConstantFieldExtension
import TypeIIITameScalarNearbyFromQuotientAction
import TypeIIIFiniteRepresentationCoefficientMonoidal

/-!
The generic origin and the primitive origin use the same actual parameter
fraction field, the same ordinary inverse images, the same geometric origin
realization, and the already constructed fixed two-adic/complex coefficient
equivalence. Scalar comparison and the published primitive origin rules are
applied on those functors. No independent complex origin functor, selected
Kl3 representation, whole origin Rules or whole PullbackData is a premise.
The general geometric nearby and Katz theorem interpretation remains explicit.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped PrimeGap182.TypeIII.TwoAdicComplexEmbedding
namespace PrimeGap182.TypeIII.OriginModelsFromSameComputedCoefficients
open ExactInverseImagesToDerived PrimitiveRamificationFromGeneralKatzTheory
open GenericOriginFractionFieldCoordinates FiniteRepresentationCoefficientTransport
open PrimitiveOriginRulesFromConstantFieldExtension
open ArithmeticPrimitivesFromCommonKatzConstruction RegularTameBasisFromFiniteJordanExponential
open QSTPrimitiveBridgesFromCommonKatzConstruction

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (M : LocalRealization C)

def coefficientFunctor (E : Type) [Field E] :
    FDRep (PadicAlgCl 2) (M.originGroup E) ⥤ FDRep ℂ (M.originGroup E) :=
  (coefficientEquivalence TwoAdicComplexEmbedding.complexEquiv (M.originGroup E)).functor

def nearbyOrigin (E : Type) [Field E] :
    C (ArithmeticSourceMaps.fiberScheme E) ⥤ FDRep ℂ (M.originGroup E) :=
  M.origin E ⋙ coefficientFunctor C M E

def genericZero (K : Type) [Field K] :
    C (GenericSourceSpecialization.genericScheme K) ⥤
      FDRep ℂ (M.originGroup (ParameterFractionField K)) :=
  genericZeroFunctor K C U (fun E => M.originGroup E) (nearbyOrigin C M)

def primitiveZero (K : Type) [Field K] :
    C (StartingSourceMaps.affineLine K) ⥤
      FDRep ℂ (M.originGroup (ParameterFractionField K)) :=
  primitiveOriginFunctor K C U (fun E => M.originGroup E) (nearbyOrigin C M)

omit [∀ X, Abelian (C X)] in
theorem coefficient_finrank (E : Type) [Field E]
    (V : FDRep (PadicAlgCl 2) (M.originGroup E)) :
    Module.finrank ℂ ((coefficientFunctor C M E).obj V) = Module.finrank (PadicAlgCl 2) V :=
  finrank_eq TwoAdicComplexEmbedding.complexEquiv (M.originGroup E) V

omit [∀ X, Abelian (C X)] in
theorem coefficient_invariants_finrank (E : Type) [Field E]
    (V : FDRep (PadicAlgCl 2) (M.originGroup E)) :
    Module.finrank ℂ (Representation.invariants ((coefficientFunctor C M E).obj V).ρ) =
      Module.finrank (PadicAlgCl 2) (Representation.invariants V.ρ) :=
  invariants_finrank_eq TwoAdicComplexEmbedding.complexEquiv (M.originGroup E) V

omit [∀ X, Abelian (C X)] in
theorem coefficient_trivialAction (E : Type) [Field E]
    (V : FDRep (PadicAlgCl 2) (M.originGroup E)) :
    (∀ g, ((coefficientFunctor C M E).obj V).ρ g = 1) ↔ (∀ g, V.ρ g = 1) :=
  trivialAction_iff TwoAdicComplexEmbedding.complexEquiv (M.originGroup E) V

def coefficientDualIso (E : Type) [Field E]
    (V : FDRep (PadicAlgCl 2) (M.originGroup E)) :
    (coefficientFunctor C M E).obj
      (FiniteRepresentationCoefficientMonoidal.dualObject (M.originGroup E) V) ≅
    FiniteRepresentationCoefficientMonoidal.dualObject (M.originGroup E)
      ((coefficientFunctor C M E).obj V) :=
  FiniteRepresentationCoefficientMonoidal.dualIso
    TwoAdicComplexEmbedding.complexEquiv (M.originGroup E) V

section Tensor
variable [∀ X, MonoidalCategory (C X)]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  [∀ (E : Type) [Field E], (M.origin E).Monoidal]

instance nearbyOriginMonoidal (E : Type) [Field E] : (nearbyOrigin C M E).Monoidal :=
  inferInstanceAs (M.origin E ⋙
    (coefficientEquivalence TwoAdicComplexEmbedding.complexEquiv (M.originGroup E)).functor).Monoidal

instance genericZeroMonoidal (K : Type) [Field K] : (genericZero C U M K).Monoidal :=
  inferInstanceAs (U.pull (genericFractionMorphism K) ⋙
    nearbyOrigin C M (ParameterFractionField K)).Monoidal

instance primitiveZeroMonoidal (K : Type) [Field K] : (primitiveZero C U M K).Monoidal :=
  inferInstanceAs (U.pull (ArithmeticSourceMaps.localInputMorphism K (ParameterFractionField K)) ⋙
    nearbyOrigin C M (ParameterFractionField K)).Monoidal

def genericZeroTensorIso (K : Type) [Field K]
    (A B : C (GenericSourceSpecialization.genericScheme K)) :
    (genericZero C U M K).obj (A ⊗ B) ≅
      (genericZero C U M K).obj A ⊗ (genericZero C U M K).obj B :=
  (Functor.Monoidal.μIso (genericZero C U M K) A B).symm

def genericZeroUnitIso (K : Type) [Field K] :
    (genericZero C U M K).obj (𝟙_ (C (GenericSourceSpecialization.genericScheme K))) ≅
      𝟙_ (FDRep ℂ (M.originGroup (ParameterFractionField K))) :=
  (Functor.Monoidal.εIso (genericZero C U M K)).symm
end Tensor

variable (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)
  (L : ∀ X : Scheme, ObjectProperty (C X))
  (O : QSTPrimitiveBridgesFromCommonKatzConstruction.Constructions C)
  (tame : ∀ (E : Type) [Field E], M.originGroup E →* Multiplicative ℂ)
  (zeroRestriction : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0),
    O.zero K h2 ⋙ U.pull (ArithmeticSourceMaps.localInputMorphism K K) ≅ 𝟭 _)
  (rawKatzBaseBasis : ∀ (K E : Type) [Field K] [Fintype K] [Field E] [Algebra K E]
    (hK : (2 : K) ≠ 0) (_hE : (2 : E) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n),
    HasRegularTameBasis ((U.pull (ScalarLocalPropagationFromFilteredTraits.baseGmMorphism K E) ⋙
      nearbyOrigin C M E).obj (O.katz K hK (kloostermanIndex ψ hψ n hn 0))).ρ (tame E) n)
  (lineTateBaseNearby : ∀ (K E : Type) [Field K] [Field E] [Algebra K E]
    (hK : (2 : K) ≠ 0) (_hE : (2 : E) ≠ 0) (n : ℤ),
    O.lineTate K hK n ⋙ baseOriginFunctor C U (fun F => M.originGroup F)
      (nearbyOrigin C M) K E ≅
    baseOriginFunctor C U (fun F => M.originGroup F) (nearbyOrigin C M) K E)
  (smoothBaseOriginAction : ∀ (K E : Type) [Field K] [Field E] [Algebra K E]
    (_hK : (2 : K) ≠ 0) (_hE : (2 : E) ≠ 0)
    (A : C (StartingSourceMaps.affineLine K)), L (StartingSourceMaps.affineLine K) A →
    ∀ g, ((baseOriginFunctor C U (fun F => M.originGroup F) (nearbyOrigin C M) K E).obj A).ρ g = 1)
  (lisseBaseNearbyGenericDimension : ∀ (K E : Type) [Field K] [Field E] [Algebra K E]
    (_hK : (2 : K) ≠ 0) (_hE : (2 : E) ≠ 0)
    (A : C (ArithmeticSourceMaps.fiberScheme K)), L (ArithmeticSourceMaps.fiberScheme K) A →
    Module.finrank ℂ ((U.pull (ScalarLocalPropagationFromFilteredTraits.baseGmMorphism K E) ⋙
      nearbyOrigin C M E).obj A) =
    Module.finrank ℂ ((QSTGenericFiberFromActualGenericPoint.rawGenericFiber K C U G).obj
      ((QSTCompactBridgeFromCompactifiedDerivedPushforward.boundedDegreeZero C _).obj A)))

section PrimitiveRules
variable [∀ X, MonoidalCategory (C X)]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  [∀ X, (L X).IsClosedUnderIsomorphisms]
  (standardASLisse : ∀ (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)), ψ ≠ 1 →
      L (StartingSourceMaps.affineLine K) (O.artinSchreier K hK ψ))
  (p : ℕ) [Fact p.Prime] (hK : (2 : ZMod p) ≠ 0)
  (R : RationalPointStalks.Data (CanonicalPrimeFramework.primeSource C U p))

include zeroRestriction rawKatzBaseBasis lineTateBaseNearby smoothBaseOriginAction
  lisseBaseNearbyGenericDimension standardASLisse in
def originRules (E : Type) [Field E] [Algebra (ZMod p) E] (hE : (2 : E) ≠ 0) :
    PublishedLocalOrigin.Rules
      (RationalPointStalks.PrimitiveOperations.primitive R (primitiveOperations C O p hK))
      (LinePurityFromStalks.geometry R
        (GloballyLisseLineRamificationFromKatz.canonicalObservables C U L M G (ZMod p)))
      (fun A => (baseOriginFunctor C U (fun F => M.originGroup F) (nearbyOrigin C M)
        (ZMod p) E).obj A) (tame E) :=
  PrimitiveOriginRulesFromConstantFieldExtension.originRules C U G L O
    (fun F => M.originGroup F) (nearbyOrigin C M) tame zeroRestriction rawKatzBaseBasis
    lineTateBaseNearby smoothBaseOriginAction lisseBaseNearbyGenericDimension M
    standardASLisse p hK R E hE

omit [∀ X, MonoidalCategory (C X)]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal] in
theorem primitiveZero_same_baseOrigin (A : C (StartingSourceMaps.affineLine (ZMod p))) :
    (primitiveZero C U M (ZMod p)).obj A =
    (baseOriginFunctor C U (fun F => M.originGroup F) (nearbyOrigin C M)
      (ZMod p) (ParameterFractionField (ZMod p))).obj A := rfl
end PrimitiveRules

theorem fraction_two_ne_zero (K : Type) [Field K] (hK : (2 : K) ≠ 0) :
    (2 : ParameterFractionField K) ≠ 0 := by
  have h := (algebraMap K (ParameterFractionField K)).injective.ne hK
  simpa only [map_ofNat, map_zero] using h

section ScalarComparison
variable [∀ X, MonoidalCategory (C X)]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  [∀ X, (L X).IsClosedUnderIsomorphisms]
  (lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y), L Y A → L X ((U.pull f).obj A))
  (scalarOriginAutomorphism : ∀ (F : Type) [Field F], (2 : F) ≠ 0 →
    Fˣ → M.originGroup F ≃* M.originGroup F)
  (scalarOriginComparison : ∀ (F : Type) [Field F] (hF : (2 : F) ≠ 0) (a : Fˣ),
    (L (ArithmeticSourceMaps.fiberScheme F)).ι ⋙
      U.pull (ArithmeticSourceMaps.scalarMorphism F F a) ⋙ M.origin F ≅
    (L (ArithmeticSourceMaps.fiberScheme F)).ι ⋙ M.origin F ⋙
      Action.res (FGModuleCat (PadicAlgCl 2)) (scalarOriginAutomorphism F hF a).toMonoidHom)
  (scalarOriginTameQuotient : ∀ (F : Type) [Field F] (hF : (2 : F) ≠ 0)
    (a : Fˣ) (g : M.originGroup F), ∃ w : M.wildOrigin F,
      scalarOriginAutomorphism F hF a g = g * w.val)
  (baseOriginHom : ∀ (F B : Type) [Field F] [Field B] [Algebra F B],
    (2 : F) ≠ 0 → (2 : B) ≠ 0 → M.originGroup B →* M.originGroup F)
  (baseOriginWild : ∀ (F B : Type) [Field F] [Field B] [Algebra F B]
    (hF : (2 : F) ≠ 0) (hB : (2 : B) ≠ 0) (g : M.wildOrigin B),
    baseOriginHom F B hF hB g.val ∈ M.wildOrigin F)
  (baseOriginComparison : ∀ (F B : Type) [Field F] [Field B] [Algebra F B]
    (hF : (2 : F) ≠ 0) (hB : (2 : B) ≠ 0),
    (L (ArithmeticSourceMaps.fiberScheme F)).ι ⋙
      U.pull (ScalarLocalPropagationFromFilteredTraits.baseGmMorphism F B) ⋙ M.origin B ≅
    (L (ArithmeticSourceMaps.fiberScheme F)).ι ⋙ M.origin F ⋙
      Action.res (FGModuleCat (PadicAlgCl 2)) (baseOriginHom F B hF hB))
  (p : ℕ) [Fact p.Prime] (hK : (2 : ZMod p) ≠ 0)
  (R : RationalPointStalks.Data (CanonicalPrimeFramework.primeSource C U p))

include lissePull scalarOriginComparison scalarOriginTameQuotient baseOriginWild baseOriginComparison in
def originPullback : GeometricOriginFromScalar.PullbackData (ZMod p)
    (fun f => U.pull f) (fun A => (genericZero C U M (ZMod p)).obj A)
    (LinePurityFromStalks.geometry R
      (GloballyLisseLineRamificationFromKatz.canonicalObservables C U L M G (ZMod p))) :=
  TameScalarNearbyFromQuotientAction.originPullbackData C U L M (coefficientFunctor C M)
    scalarOriginAutomorphism scalarOriginComparison scalarOriginTameQuotient lissePull
    baseOriginHom baseOriginWild baseOriginComparison G p hK R

include lissePull scalarOriginComparison scalarOriginTameQuotient baseOriginWild baseOriginComparison in
theorem originPullback_primitiveZero :
    (originPullback C U M G L lissePull scalarOriginAutomorphism scalarOriginComparison
      scalarOriginTameQuotient baseOriginHom baseOriginWild baseOriginComparison p hK R).primitiveZero =
    fun A => (primitiveZero C U M (ZMod p)).obj A := rfl
end ScalarComparison
end PrimeGap182.TypeIII.OriginModelsFromSameComputedCoefficients
