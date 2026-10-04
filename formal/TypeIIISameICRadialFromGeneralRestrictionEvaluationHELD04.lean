import TypeIIIRadialDualTateFromEvaluation
import TypeIIICanonicalOrdinaryDualEvaluation
import TypeIIIOriginModelsFromSameComputedCoefficients
import TypeIIIPhysicalTensorComparison
import TypeIIIGenericPhysicalEntry
import TypeIIICoherentSourceGlobalCohomologyFromGuardedLaurent04

/-!
The standard plane operations are declared once before p: actual
total j_{!*}(^pH0(A[2])), its SAME whole arithmetic Weil lift, and ordinary H^{-2}
of SAME ray pull. For lisse A on the smooth dimension-two torus,
^pH0(A[2]) is A[2]. No exactness of normalization is asserted.
Their interpretation is an explicit external obligation.
The general restriction theorem ranges over ALL lisse ordinary torus
objects; no physical-family comparison is supplied.

The geometric observer is literal nearbyOrigin at PhaseField K. Parameter
dual/Tate is the actual ordinary internal dual followed by Tate(-1).
Canonical evaluation is curried, and finite-lisse perfection makes that
computed map bijective. Its equivariance follows from evaluation, without
a supplied contragredient action equation or selected dual isomorphism.

GENERAL clauses require ONE genuinely interpreted finite-Q2/adic theory,
with the fixed coefficient embedding. Arbitrary abstract dictionaries do
not establish them. Geometric Tate triviality does not assert arithmetic
Frobenius is trivial. No adic foundations or native-model existence claim.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory TensorProduct

namespace PrimeGap182.TypeIII.SameICRadialFromGeneralRestrictionEvaluationHELD04
open ExactInverseImagesToDerived UniversalOrdinaryInverseImages CanonicalPrimeFramework
open QSTDualityBridgesFromSmoothLisseVerdier PublishedPhysicalConstruction
open PublishedSupportRules PublishedStalkCertificate PublishedPhaseApplication
open GenericCurvePullback CanonicalOrdinaryDualEvaluation

universe mu group plane

/-- Rank and trivial action construct the line normalization; no basis is an input. -/
def trivialRankOneIso {G : Type group} [Group G] (V : FDRep ℂ G)
    (trivial : Representation.IsTrivial V.ρ) (rank : Module.finrank ℂ V = 1) :
    V ≅ 𝟙_ (FDRep ℂ G) := by
  letI := trivial
  let e : V ≃ₗ[ℂ] ℂ := Classical.choice
    (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (by simpa using rank))
  refine Action.mkIso e.toFGModuleCatIso (fun g => ?_)
  apply FGModuleCat.hom_ext
  ext v
  change e (V.ρ g v) = e v
  rw [Representation.isTrivial_def V.ρ g]
  rfl

section Evaluation
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)]
  [∀ X, MonoidalCategory (C X)] [∀ X, MonoidalClosed (C X)]
  [∀ X, BraidedCategory (C X)]

/-- SAME closed evaluation, with the evaluation line and unit comparisons. -/
def canonicalPairing (X : Scheme) {G : Type group} [Group G]
    (F : C X ⥤ FDRep ℂ G) [F.Monoidal]
    (line : C X) (normalization : F.obj line ≅ F.obj (𝟙_ (C X))) (V : C X) :
    F.obj V ⊗ F.obj (line ⊗ (ordinaryDual C X).obj (op V)) ⟶
      𝟙_ (FDRep ℂ G) :=
  (Functor.Monoidal.μIso F _ _).hom ≫
    F.map (evaluateLine C X line V) ≫
      normalization.hom ≫ (Functor.Monoidal.εIso F).inv

/-- Actual curried evaluation; GENERAL perfection concerns this map. -/
def canonicalDualTateMap (X : Scheme) {G : Type group} [Group G]
    (F : C X ⥤ FDRep ℂ G) [F.Monoidal]
    (line : C X) (normalization : F.obj line ≅ F.obj (𝟙_ (C X))) (V : C X) :
    F.obj (line ⊗ (ordinaryDual C X).obj (op V)) →ₗ[ℂ]
      Module.Dual ℂ (F.obj V) :=
  TensorProduct.curry ((canonicalPairing C X F line normalization V).hom.hom.hom ∘ₗ
    (TensorProduct.comm ℂ _ _).toLinearMap)
end Evaluation

variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)]
  [∀ X, Abelian (C X)] [∀ X, MonoidalCategory (C X)]
  [∀ X, MonoidalClosed (C X)] [∀ X, BraidedCategory (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (M : PrimitiveRamificationFromGeneralKatzTheory.LocalRealization C)
  [∀ (E : Type) [Field E], (M.origin E).Monoidal]
  (DO : QSTDualityBridgesFromSmoothLisseVerdier.Operations C)

/-- The group's meaning is full geometric inertia at the SAME positive trait. -/
abbrev nearby (K : Type) [Field K] :
    C (GenericCurvePullback.parameterScheme K) ⥤
      FDRep ℂ (M.originGroup (PublishedPhaseApplication.PhaseField K)) :=
  OriginModelsFromSameComputedCoefficients.nearbyOrigin C M
    (PublishedPhaseApplication.PhaseField K)

abbrev actedPull (K : Type) [Field K]
    (f : GenericCurvePullback.parameterScheme K ⟶ PhysicalTorusMorphism.torusScheme K) :
    C (PhysicalTorusMorphism.torusScheme K) ⥤
      FDRep ℂ (M.originGroup (PublishedPhaseApplication.PhaseField K)) :=
  U.pull f ⋙ nearby C M K

/-- ALL fields with 2 invertible, ALL actual maps, ALL integer Tate lines,
ALL finite-rank lisse objects. No output dual equivalence/action is a field. -/
structure GeneralGeometricEvaluation : Prop where
  tensorHom : ∀ (K : Type) [Field K] (_h2 : (2 : K) ≠ 0) (n : ℤ)
    (V : C (PhysicalTorusMorphism.torusScheme K)),
    DO.globalLisse _ V → IsIso (tensorHomComparison C _ (DO.line _ n) V)
  lineTrivial : ∀ (K : Type) [Field K] (_h2 : (2 : K) ≠ 0)
    (f : GenericCurvePullback.parameterScheme K ⟶ PhysicalTorusMorphism.torusScheme K)
    (n : ℤ), Representation.IsTrivial ((actedPull C U M K f).obj (DO.line _ n)).ρ
  lineRank : ∀ (K : Type) [Field K] (_h2 : (2 : K) ≠ 0)
    (f : GenericCurvePullback.parameterScheme K ⟶ PhysicalTorusMorphism.torusScheme K)
    (n : ℤ), Module.finrank ℂ ((actedPull C U M K f).obj (DO.line _ n)) = 1
  perfect : ∀ (K : Type) [Field K] (_h2 : (2 : K) ≠ 0)
    (f : GenericCurvePullback.parameterScheme K ⟶ PhysicalTorusMorphism.torusScheme K)
    (n : ℤ)
    (normalization : (actedPull C U M K f).obj (DO.line _ n) ≅
      (actedPull C U M K f).obj (𝟙_ (C (PhysicalTorusMorphism.torusScheme K))))
    (V : C (PhysicalTorusMorphism.torusScheme K)), DO.globalLisse _ V →
    Function.Bijective (canonicalDualTateMap C _ (actedPull C U M K f)
      (DO.line _ n) normalization V)

def lineNormalization (laws : GeneralGeometricEvaluation C U M DO)
    (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    (f : GenericCurvePullback.parameterScheme K ⟶ PhysicalTorusMorphism.torusScheme K)
    (n : ℤ) : (actedPull C U M K f).obj (DO.line _ n) ≅
      (actedPull C U M K f).obj (𝟙_ (C (PhysicalTorusMorphism.torusScheme K))) :=
  trivialRankOneIso _ (laws.lineTrivial K h2 f n) (laws.lineRank K h2 f n) ≪≫
    Functor.Monoidal.εIso (actedPull C U M K f)

set_option maxRecDepth 2048 in
def evaluationComparison (laws : GeneralGeometricEvaluation C U M DO)
    (K : Type) [Field K] (h2 : (2 : K) ≠ 0) (n : ℤ) :
    RadialDualTateFromEvaluation.Comparison (actedPull C U M K)
      (ordinaryDual C _ ⋙ ordinaryTate C DO _ n) (DO.globalLisse _)
      (CanonicalOrdinaryDualEvaluation.evaluation C _ (DO.line _ n) (DO.globalLisse _)
        (fun V hV => laws.tensorHom K h2 n V hV)) where
  monoidal _ := inferInstance
  line f := lineNormalization C U M DO laws K h2 f n
  equiv f V hV := LinearEquiv.ofBijective
    (canonicalDualTateMap C _ (actedPull C U M K f) (DO.line _ n)
      (lineNormalization C U M DO laws K h2 f n) V)
    (laws.perfect K h2 f n _ V hV)
  evaluation f V hV u v := by
    change (canonicalDualTateMap C _ _ _ _ V) v u = _
    simp only [canonicalDualTateMap, TensorProduct.curry_apply, LinearMap.comp_apply]
    rfl

variable (signed : ∀ (p : ℕ) [Fact p.Prime],
  C (PhysicalTorusMorphism.torusScheme (ZMod p)) ⥤
    C (PhysicalTorusMorphism.torusScheme (ZMod p)))

/-- The parameter dual operation is constructed literally; no equality guard. -/
def parameterOperations :
    CoherentSourceGlobalCohomologyFromGuardedLaurent04.ParameterOperations C where
  dualTateMinusOne X := ordinaryDual C X ⋙ ordinaryTate C DO X (-1)
  signed := signed

variable (RF : ∀ (p : ℕ) [Fact p.Prime],
  RationalPointStalks.Data (CanonicalPrimeFramework.primeSource C U p))

def nativeParameter (p : ℕ) [Fact p.Prime] :
    ParameterData (C (PhysicalTorusMorphism.torusScheme (ZMod p))) :=
  CoherentSourceGlobalCohomologyFromGuardedLaurent04.nativeParameter C U
    DO.globalLisse (parameterOperations C DO signed) p (RF p)

variable (PlaneObj : ℕ → Type plane)
  (surface : ∀ (p : ℕ) [Fact p.Prime],
    SurfaceData (AlgebraicClosure (ZMod p)) (PlaneObj p))
  (realization : ∀ (p : ℕ) [Fact p.Prime], RationalStalkRealization p (surface p))

/-- DATA for total j!*(pH0(A[2])) and ordinary degree -2 pull;
the ledger fixes their semantic interpretation, not arbitrary matching maps. -/
structure PlaneOperations where
  middle : ∀ (p : ℕ) [Fact p.Prime],
    C (PhysicalTorusMorphism.torusScheme (ZMod p)) → PlaneObj p
  wholeWeil : ∀ (p : ℕ) [Fact p.Prime] A,
    (realization p).WeilLift (middle p A)
  ordinaryRadial : ∀ (p : ℕ) [Fact p.Prime],
    PlaneObj p → C (GenericCurvePullback.parameterScheme (ZMod p))

def intermediateExtension
    (ops : PlaneOperations C PlaneObj surface realization) (p : ℕ) [Fact p.Prime] :
    IntermediateExtensionData (realization p)
      (C (PhysicalTorusMorphism.torusScheme (ZMod p))) where
  geometric := ops.middle p
  weil := ops.wholeWeil p

def nativeRadial (ops : PlaneOperations C PlaneObj surface realization)
    (p : ℕ) [Fact p.Prime] (Q : PlaneObj p) :
    FDRep ℂ (M.originGroup (PublishedPhaseApplication.PhaseField (ZMod p))) :=
  (nearby C M (ZMod p)).obj (ops.ordinaryRadial p Q)

/-- The same j!* restriction on ALL lisse objects, before choosing p.
Only existence of the ordinary restriction iso is stated, not a finished IR. -/
structure GeneralPlaneRestriction
    (ops : PlaneOperations C PlaneObj surface realization) : Prop where
  restriction : ∀ (p : ℕ) [Fact p.Prime] (_h2 : (2 : ZMod p) ≠ 0)
    (A : C (PhysicalTorusMorphism.torusScheme (ZMod p))), DO.globalLisse _ A →
    Nonempty (ops.ordinaryRadial p (ops.middle p A) ≅
      (U.pull (GenericPhysicalEntry.genericRadialMorphism (ZMod p))).obj A)

def inertiaCompatibility
    (ops : PlaneOperations C PlaneObj surface realization)
    (restriction : GeneralPlaneRestriction C U DO PlaneObj surface realization ops)
    (evaluation : GeneralGeometricEvaluation C U M DO)
    (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) :
    PhysicalTensorComparison.InertiaCompatibility
      (actedPull C U M (ZMod p) (GenericPhysicalEntry.genericRadialMorphism (ZMod p)))
      (intermediateExtension C PlaneObj surface realization ops p)
      (nativeRadial C M PlaneObj surface realization ops p)
      (nativeParameter C U DO signed RF p) where
  restriction A hA := TensorListRepresentation.equivOfIso
    ((nearby C M (ZMod p)).mapIso (Classical.choice (restriction.restriction p h2 A hA)))
  dualTate A hA := RadialDualTateFromEvaluation.dualTateEquiv
    (evaluationComparison C U M DO evaluation (ZMod p) h2 (-1))
    (GenericPhysicalEntry.genericRadialMorphism (ZMod p)) A hA

variable (fourier : ∀ (p : ℕ) [Fact p.Prime], PlaneObj p → PlaneObj p)
  (W : ∀ (p : ℕ) [Fact p.Prime],
    TraceWeightRules p (surface p) (realization p) (fourier p))
  (Z : ∀ (p : ℕ) [Fact p.Prime], PublishedCovarianceRules.TraceData p (realization p))

/-- Published ALL-lisse/pure middle-extension laws on these same operators.
Weight uses the same whole-Weil lift; support is geometric; trace is every
finite extension with its exact original Algebra and rational stalk system. -/
structure GeneralMiddleExtensionTheorems
    (ops : PlaneOperations C PlaneObj surface realization) : Prop where
  pure : ∀ (p : ℕ) [Fact p.Prime] (_h2 : (2 : ZMod p) ≠ 0) A a,
    (nativeParameter C U DO signed RF p).Lisse A →
    (nativeParameter C U DO signed RF p).Pure A a →
    (W p).PureOfWeight (ops.wholeWeil p A) (a + 2)
  fullSupport : ∀ (p : ℕ) [Fact p.Prime] (_h2 : (2 : ZMod p) ≠ 0) A a,
    (nativeParameter C U DO signed RF p).Lisse A →
    (nativeParameter C U DO signed RF p).Pure A a →
    (surface p).NoProperConstituents (ops.middle p A)
  semisimpleTorusIC : ∀ (p : ℕ) [Fact p.Prime] (_h2 : (2 : ZMod p) ≠ 0) A a,
    (nativeParameter C U DO signed RF p).Lisse A →
    (nativeParameter C U DO signed RF p).Pure A a → (Z p).TorusIC (ops.middle p A)
  trace : ∀ (p : ℕ) [Fact p.Prime] (_h2 : (2 : ZMod p) ≠ 0) A,
    (nativeParameter C U DO signed RF p).Lisse A →
    ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ x y : Eˣ,
    (Z p).trace E (ops.wholeWeil p A) (x : E) (y : E) =
      (RationalPointStalks.Data.torusArithmetic (RF p)).trace E A x y

omit [∀ X : Scheme, BraidedCategory (C X)] in
theorem intermediateExtensionRules
    (ops : PlaneOperations C PlaneObj surface realization)
    (laws : GeneralMiddleExtensionTheorems C U DO signed RF PlaneObj surface realization
      fourier W Z ops) (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) :
    IntermediateExtensionRules (W p) (Z p) (nativeParameter C U DO signed RF p)
      (RationalPointStalks.Data.torusArithmetic (RF p))
      (intermediateExtension C PlaneObj surface realization ops p) where
  pure := laws.pure p h2
  full := laws.fullSupport p h2
  torusIC := laws.semisimpleTorusIC p h2
  trace := laws.trace p h2

end PrimeGap182.TypeIII.SameICRadialFromGeneralRestrictionEvaluationHELD04

#print axioms PrimeGap182.TypeIII.SameICRadialFromGeneralRestrictionEvaluationHELD04.trivialRankOneIso
#print axioms PrimeGap182.TypeIII.SameICRadialFromGeneralRestrictionEvaluationHELD04.evaluationComparison
#print axioms PrimeGap182.TypeIII.SameICRadialFromGeneralRestrictionEvaluationHELD04.inertiaCompatibility
#print axioms PrimeGap182.TypeIII.SameICRadialFromGeneralRestrictionEvaluationHELD04.intermediateExtensionRules
