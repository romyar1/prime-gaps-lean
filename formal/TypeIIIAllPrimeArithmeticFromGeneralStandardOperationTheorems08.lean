import TypeIIIArithmeticRealizationFromPublishedPrimitiveAndBoundary05
import TypeIIICoherentSourceGlobalCohomologyFromGuardedLaurent04

/-!
# All-prime arithmetic realization computed from general standard operation laws

The standard category and operations, generic geometric fibers, genuine
lissity/duality, source compactification recipe, sign, origins and primitive
GENERAL theorems are fixed before the prime. The prime dictionaries are
computed from these operators and the SAME rational-point Frobenius.

The remaining theorem-family fields quantify ALL eligible ordinary source
objects, ALL finite extensions and ALL parameters. They contain no finished
AM/Inputs/primitive eligibility/corrected trace/Application family. Both
primitive guards and every origin/boundary/cohomological realization are
computed inside the output method. Numerical hypotheses are unaffected.

Genuine compatible continuous-adic interpretation, native trait and standard
construction calibration remain explicit external published premises. This
is the arithmetic half of the uniform endpoint factory, not a Lean check or
completed uniform TypeIII endpoint.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.AllPrimeArithmeticFromGeneralStandardOperationTheorems08
open ExactInverseImagesToDerived RationalPointStalksFromUniversalFiber
open QSTPrimitiveBridgesFromCommonKatzConstruction CanonicalPrimeFramework
open StandardGmTraceFromFaithfulArithmeticOperations StandardP1BoundaryPrimitives
open PublishedPhysicalConstruction CanonicalCurveInput
open OriginInputsFromSharedStandardOperationsHELD04
open AllPrimeOriginInputsFromGeneralOperationFamilies05
open ArithmeticRealizationFromComputedStandardBoundary13

universe nu g pt ps h gi
variable (C : Scheme → Type) [∀ X, Category.{0} (C X)]
  [∀ X, Abelian (C X)] [∀ X, MonoidalCategory (C X)]
  [∀ X, MonoidalClosed (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (F : ArithmeticFibers C)
  [∀ (E : Type) [Field E] [Fintype E], (F.fiber E).Additive]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteLimits (F.fiber E)]
  [∀ (E : Type) [Field E] [Fintype E], PreservesFiniteColimits (F.fiber E)]
  (O : Constructions C)
  (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)
  (Mgeo : PrimitiveRamificationFromGeneralKatzTheory.LocalRealization C)
  (DO : QSTDualityBridgesFromSmoothLisseVerdier.Operations C)
  [∀ X, ObjectProperty.IsClosedUnderIsomorphisms (DO.globalLisse X)]
  (Z : UniformSourceLocalObservablesFromParameterFibers.OriginProfiles C Mgeo)
  (nativeCompact : ∀ (E : Type) [Field E] [Fintype E] (_h2 : (2 : E) ≠ 0),
    Fin 3 → C (ArithmeticSourceMaps.fiberScheme E) ⥤ C (Spec (.of E)))
  {S : StandardGmPrimitives.{nu}} (B : Primitives.{nu,0,0} S)
  (AR : FaithfulArithmeticOperations C U F nativeCompact S)
  (originTrait : NativeCommonArithmeticTraitWeilCone.OriginTraitDictionary S B)
  (originGeneral : GeneralSharedOriginTheory.{0,nu,g,ps,pt} (C := C) (U := U) (F := F) (O := O)
    (geometricFiber := G) (lisse := DO.globalLisse) (nativeCompact := nativeCompact)
    (B := B) (D := AR) (originTrait := originTrait) (geometricM := Mgeo))
  [realizationMonoidal : ∀ (E : Type) [Field E] [Fintype E] (h2E : (2 : E) ≠ 0),
    letI := B.curveMonoidal E h2E; (AR.curveRealization E h2E).Monoidal]


variable
  (compactOps : QSTCompactBridgeFromCompactifiedDerivedPushforward.Operations C)
  (sourceCompactification : ∀ (K : Type) [Field K],
    QSTCompactBridgeFromCompactifiedDerivedPushforward.Compactification
      (SourceProjectionForQST.projection K))
  (signed : ∀ (p : ℕ) [Fact p.Prime],
    C (PhysicalTorusMorphism.torusScheme (ZMod p)) ⥤
      C (PhysicalTorusMorphism.torusScheme (ZMod p)))
  (InfinityGroup : ℕ → Type gi) [∀ p, Group (InfinityGroup p)]
  (coefficients : PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.CoefficientFibers C F)
  (primitiveGeneral : CanonicalPrimitiveEligibilityFromGeneralPublishedLaws05.GeneralPrimitiveLaws
    C U F O coefficients G DO.globalLisse Mgeo)

/-- The literal ordinary dual/Tate(-1) and the same fixed sign recipe. -/
def parameterOperations :
    CoherentSourceGlobalCohomologyFromGuardedLaurent04.ParameterOperations C where
  dualTateMinusOne X := QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C X ⋙
    QSTDualityBridgesFromSmoothLisseVerdier.ordinaryTate C DO X (-1)
  signed := signed

/-- The exact source observables, with actual all-field local profiles,
intrinsic generic rank and the SAME rational-point Frobenius purity. -/
def sourceObservations (p : ℕ) [Fact p.Prime] :=
  SourcePurityFromStalks.geometry (pointStalks C U F p)
    (UniformSourceLocalObservablesFromParameterFibers.sourceObservables (ZMod p)
      C U G DO.globalLisse Mgeo Z)

abbrev sourceDual (p : ℕ) [Fact p.Prime] :=
  QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C (StartingSourceMaps.sourceScheme (ZMod p))

def sourceCohomology (p : ℕ) [Fact p.Prime] :=
  CoherentSourceGlobalCohomologyFromGuardedLaurent04.nativeCohomology
    C compactOps (ZMod p) (sourceCompactification (ZMod p))

def sourceParameter (p : ℕ) [Fact p.Prime] :=
  CoherentSourceGlobalCohomologyFromGuardedLaurent04.nativeParameter
    C U DO.globalLisse (parameterOperations C DO signed) p (pointStalks C U F p)

/-- The prime numerical guard is proved, not a theorem-family input. -/
theorem primeGuard (p : ℕ) [Fact p.Prime] (hp : 3 < p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hdvd
  omega

/-- Precisely ALL-object published projections on these literal operators.
The data and this record are chosen before p. Selected TypeIII input/model,
AM, trace correction, profile, Fourier bound or Application are not fields. -/
structure GeneralArithmeticOperationTheorems where
  boundary : ∀ (p : ℕ) [Fact p.Prime] (hp : 3 < p),
    GeneralArithmeticBoundaryClauses
      (C := C) (U := U) (F := F) (nativeCompact := nativeCompact) (B := B) (AR := AR) (originTrait := originTrait)
      (realizationMonoidal := realizationMonoidal) (H := sourceCohomology C compactOps sourceCompactification p)
      (Ginf := InfinityGroup p) (h2p := primeGuard p hp)
      (Obs := sourceObservations C U F G Mgeo DO Z p) (dualInput := sourceDual C p)
  cohomology : ∀ (p : ℕ) [Fact p.Prime] (hp : 3 < p),
    GeneralArithmeticCohomologyClauses
      (C := C) (U := U) (F := F) (O := O) (G := G) (L := DO.globalLisse) (Mgeo := Mgeo)
      (nativeCompact := nativeCompact) (B := B) (AR := AR) (originTrait := originTrait) (originGeneral := originGeneral)
      (realizationMonoidal := realizationMonoidal) (H := sourceCohomology C compactOps sourceCompactification p)
      (PP := sourceParameter C U F DO signed p) (Ginf := InfinityGroup p) (h2p := primeGuard p hp)
      (Obs := sourceObservations C U F G Mgeo DO Z p) (dualInput := sourceDual C p)
      (boundaryGeneral := boundary p hp)
  scalar : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p),
    ScalarPullbackRules
      (FourierSourcePullbacks.originalPullbackData (ZMod p)
        (SourceInverseImageSystem.System.geometricPullbacks (primeSource C U p)))
      (computedPrimitiveLine C U F G DO.globalLisse Mgeo p)
      ((sourceObservations C U F G Mgeo DO Z p).curveData (sourceDual C p))
  curve : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p),
    CurveRules ((sourceObservations C U F G Mgeo DO Z p).curveData (sourceDual C p))
  tateTrace : ∀ (p : ℕ) [Fact p.Prime] (hp : 3 < p) (n : ℤ)
      (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
      (A : C (StartingSourceMaps.affineLine (ZMod p))) z,
    (pointStalks C U F p).lineTrace (E := E)
      ((O.lineTate (ZMod p) (primeGuard p hp) n).obj A) z =
      (Fintype.card E : ℂ)^(-n) * (pointStalks C U F p).lineTrace (E := E) A z
  tameNonzero : ∀ (p : ℕ) [Fact p.Prime] (_hp : 3 < p),
    ∃ z, (originGeneral.tame (ZMod p) z).toAdd ≠ 0

variable (general : GeneralArithmeticOperationTheorems
  (C := C) (U := U) (F := F) (O := O) (G := G) (Mgeo := Mgeo) (DO := DO) (Z := Z)
  (nativeCompact := nativeCompact) (B := B) (AR := AR) (originTrait := originTrait) (originGeneral := originGeneral)
  (realizationMonoidal := realizationMonoidal) (compactOps := compactOps) (sourceCompactification := sourceCompactification)
  (signed := signed) (InfinityGroup := InfinityGroup))

include C U F O G Mgeo DO Z nativeCompact B AR originTrait originGeneral realizationMonoidal
  compactOps sourceCompactification signed InfinityGroup coefficients primitiveGeneral general

/-- Uniform arithmetic output: no forall-prime finished AM provider is
accepted. Each AM is constructed from literal operators and GENERAL clauses. -/
def computedCohomologicalRealization (p : ℕ) [Fact p.Prime] (hp : 3 < p) :=
  ArithmeticRealizationFromPublishedPrimitiveAndBoundary05.computedCohomologicalRealization
    (C := C) (U := U) (F := F) (O := O) (G := G) (L := DO.globalLisse) (Mgeo := Mgeo)
    (nativeCompact := nativeCompact) (B := B) (AR := AR) (originTrait := originTrait)
    (originGeneral := originGeneral) (realizationMonoidal := realizationMonoidal)
    (h2p := primeGuard p hp) (hp := hp)
    (Obs := sourceObservations C U F G Mgeo DO Z p) (dualInput := sourceDual C p)
    (H := sourceCohomology C compactOps sourceCompactification p)
    (PP := sourceParameter C U F DO signed p) (Ginf := InfinityGroup p)
    (boundaryGeneral := general.boundary p hp) (cohomologyGeneral := general.cohomology p hp)
    (coefficients := coefficients) (primitiveGeneral := primitiveGeneral)
    (tateTrace := by
      intro E _ _ _ A z
      simpa using general.tateTrace p hp 1 E A z)
    (SR := general.scalar p hp) (CR := general.curve p hp) (htame := general.tameNonzero p hp)

end PrimeGap182.TypeIII.AllPrimeArithmeticFromGeneralStandardOperationTheorems08

#print axioms PrimeGap182.TypeIII.AllPrimeArithmeticFromGeneralStandardOperationTheorems08.primeGuard
#print axioms PrimeGap182.TypeIII.AllPrimeArithmeticFromGeneralStandardOperationTheorems08.computedCohomologicalRealization
