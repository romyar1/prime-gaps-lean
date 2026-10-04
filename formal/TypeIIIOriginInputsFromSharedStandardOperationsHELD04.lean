import TypeIIICommonOriginStalkDataFromStandardOperations04
import TypeIIIOriginRulesFromStandardPrimitiveAndFiniteConstant04
import TypeIIIPrimitiveOriginRulesFromConstantFieldExtension

/-!
# HELD seven-field origin application on one shared standard theory

The native local functor is DEFINED from the same curve realization and
standard origin Weil action. Individual ordinary scalar/Tate operation
comparisons compute its StalkData. ALL-positive-rank geometric tame laws
compute the Kl3 model; smooth rank-one laws compute the AS model. The
independent finite-constant and prime-origin published packages compute
both invariant Frobenius actions at every finite extension.

There is no supplied OriginStalks, StalkData, scalar/Tate Rules, geometric
Kl3/AS model, origin-Frobenius Rules, seven-field Inputs or whole arithmetic
realization. The genuine continuous-adic interpretation of the shared
operations, the positive tame coordinate and their fixed coefficient
calibration remains external. No mathematical compilation has occurred.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped MonoidalCategory PrimeGap182.TypeIII.TwoAdicComplexEmbedding

namespace PrimeGap182.TypeIII.OriginInputsFromSharedStandardOperationsHELD04
open ExactInverseImagesToDerived RationalPointStalksFromUniversalFiber
open QSTPrimitiveBridgesFromCommonKatzConstruction CanonicalPrimeFramework
open StartingSourceMaps ArithmeticSourceMaps ArithmeticSourceTransport
open ArithmeticSourcesFromOrigin ArithmeticPrimitiveSources
open ArithmeticPrimitivesFromCommonKatzConstruction
open StandardGmTraceFromFaithfulArithmeticOperations StandardP1BoundaryPrimitives
open RegularTameBasisFromFiniteJordanExponential
open RankOneTrivialRepresentationFromActualAction TensorListRepresentation
open GenericOriginFractionFieldCoordinates

universe mu nu g pt ps
variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)]
  [∀ X, Abelian (C X)] [∀ X, MonoidalCategory (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (F : ArithmeticFibers C) (O : Constructions C)
  (geometricFiber : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)
  (lisse : ∀ X : Scheme, ObjectProperty (C X))
  (nativeCompact : ∀ (E : Type) [Field E] [Fintype E] (_h2 : (2 : E) ≠ 0),
    Fin 3 → C (fiberScheme E) ⥤ C (Spec (.of E)))
  {S : StandardGmPrimitives.{nu}} (B : Primitives.{nu,0,0} S)
  (D : FaithfulArithmeticOperations C U F nativeCompact S)
  (originTrait : NativeCommonArithmeticTraitWeilCone.OriginTraitDictionary S B)

local instance allLocalizations : ∀ X : Scheme, HasDerivedCategory.{mu} (C X) :=
  fun _ => HasDerivedCategory.standard _

/-- The common native inertia group is a computed positive-chart group. -/
abbrev CommonGroup (K : Type) [Field K] :=
  NativeCommonArithmeticTraitWeilCone.CommonOrigin.{g} K

/-- Exact fiber, with every shared operation parameter explicitly bound. -/
abbrev nativeNearby
    (C : Scheme → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
    (U : OrdinarySystem (fun X : Scheme => X) C) (F : ArithmeticFibers C)
    (nativeCompact : ∀ (E : Type) [Field E] [Fintype E] (_h2 : (2 : E) ≠ 0),
      Fin 3 → C (fiberScheme E) ⥤ C (Spec (.of E)))
    {S : StandardGmPrimitives.{nu}} (B : Primitives.{nu,0,0} S)
    (D : FaithfulArithmeticOperations C U F nativeCompact S)
    (originTrait : NativeCommonArithmeticTraitWeilCone.OriginTraitDictionary S B)
    (K E : Type) [Field K] [Field E] [Fintype E] [Algebra K E]
    (hE : (2 : E) ≠ 0) : C (fiberScheme E) ⥤ FDRep ℂ (CommonGroup.{g} K) :=
  NativeCommonArithmeticTraitWeilCone.fiber.{0,mu,nu,g} K E B originTrait hE
    (D.curveRealization E hE)

/-- The same literal base pull followed by that exact fiber. -/
abbrev nativeOrigin
    (C : Scheme → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
    (U : OrdinarySystem (fun X : Scheme => X) C) (F : ArithmeticFibers C)
    (nativeCompact : ∀ (E : Type) [Field E] [Fintype E] (_h2 : (2 : E) ≠ 0),
      Fin 3 → C (fiberScheme E) ⥤ C (Spec (.of E)))
    {S : StandardGmPrimitives.{nu}} (B : Primitives.{nu,0,0} S)
    (D : FaithfulArithmeticOperations C U F nativeCompact S)
    (originTrait : NativeCommonArithmeticTraitWeilCone.OriginTraitDictionary S B)
    (K E : Type) [Field K] [Field E] [Fintype E] [Algebra K E]
    (hE : (2 : E) ≠ 0) :=
  U.pull (localInputMorphism K E) ⋙ nativeNearby C U F nativeCompact B D originTrait K E hE

/- These theorem families are fixed before the selected prime. Their
published interpretation requires exactly the same C/U/O/geometricFiber,
standard action, positive tame coordinate and coefficient embedding. -/
variable
  (tame : ∀ (K : Type) [Field K] [Fintype K], CommonGroup.{g} K →* Multiplicative ℂ)
  (zeroRestriction : ∀ (K : Type) [Field K] (hK : (2 : K) ≠ 0),
    O.zero K hK ⋙ U.pull (localInputMorphism K K) ≅ 𝟭 _)
  (rawKatzBaseBasis : ∀ (K E : Type) [Field K] [Fintype K] [Field E] [Fintype E]
    [Algebra K E] (hK : (2 : K) ≠ 0) (hE : (2 : E) ≠ 0)
    (psi : AddChar K (PadicAlgCl 2)) (_hpsi : psi ≠ 1) (n : ℕ) (_hn : 0 < n),
    HasRegularTameBasis
      ((U.pull (ScalarLocalPropagationFromFilteredTraits.baseGmMorphism K E) ⋙
        nativeNearby C U F nativeCompact B D originTrait K E hE).obj
        (O.katz K hK (kloostermanIndex psi _hpsi n _hn 0))).ρ (tame K) n)
  (lineTateBaseNearby : ∀ (K E : Type) [Field K] [Fintype K] [Field E] [Fintype E]
    [Algebra K E] (hK : (2 : K) ≠ 0) (hE : (2 : E) ≠ 0) (n : ℤ),
    O.lineTate K hK n ⋙ nativeOrigin C U F nativeCompact B D originTrait K E hE ≅
      nativeOrigin C U F nativeCompact B D originTrait K E hE)
  (smoothBaseOriginAction : ∀ (K E : Type) [Field K] [Fintype K] [Field E] [Fintype E]
    [Algebra K E] (_hK : (2 : K) ≠ 0) (hE : (2 : E) ≠ 0)
    (A : C (affineLine K)), lisse (affineLine K) A →
      ∀ z, ((nativeOrigin C U F nativeCompact B D originTrait K E hE).obj A).ρ z = 1)
  (lisseBaseNearbyGenericDimension : ∀ (K E : Type) [Field K] [Fintype K]
    [Field E] [Fintype E] [Algebra K E] (_hK : (2 : K) ≠ 0) (hE : (2 : E) ≠ 0)
    (A : C (fiberScheme K)), lisse (fiberScheme K) A →
      Module.finrank ℂ ((U.pull (ScalarLocalPropagationFromFilteredTraits.baseGmMorphism K E) ⋙
        nativeNearby.{mu,nu,g} C U F nativeCompact B D originTrait K E hE).obj A) =
      Module.finrank ℂ ((QSTGenericFiberFromActualGenericPoint.rawGenericFiber
        K C U geometricFiber).obj ((QSTCompactBridgeFromCompactifiedDerivedPushforward.boundedDegreeZero
          C _).obj A)))
  (lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y), lisse Y A → lisse X ((U.pull f).obj A))
  (standardASLisse : ∀ (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
    (psi : AddChar K (PadicAlgCl 2)), psi ≠ 1 → lisse (affineLine K) (O.artinSchreier K hK psi))
  (standardASGenericRank : ∀ (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
    (psi : AddChar K (PadicAlgCl 2)), psi ≠ 1 →
      PrimitiveRanksFromComputedGenericLineRank.canonicalLineRank C U geometricFiber K
        (O.artinSchreier K hK psi) = 1)

/-- Specialize the ALL-rank full-inertia basis law and actual zero pullback. -/
def rawGeometricModel (K E : Type) [Field K] [Fintype K] [Field E] [Fintype E]
    [Algebra K E] (hK : (2 : K) ≠ 0) (hE : (2 : E) ≠ 0)
    (psi : AddChar K (PadicAlgCl 2)) (hpsi : psi ≠ 1) :
    Representation.Equiv
      ((nativeOrigin C U F nativeCompact B D originTrait K E hE).obj
        (rawKloosterman3 C O K hK psi hpsi)).ρ
      (RegularUnipotentRepresentation.tameRepresentation (tame K)) :=
  (equivOfIso
    ((nativeNearby C U F nativeCompact B D originTrait K E hE).mapIso
      (ScalarLocalPropagationFromFilteredTraits.localInputBaseIso K E C U
        (rawKloosterman3 C O K hK psi hpsi)) ≪≫
    (nativeNearby C U F nativeCompact B D originTrait K E hE).mapIso
      ((U.pull (ScalarLocalPropagationFromFilteredTraits.baseGmMorphism K E)).mapIso ((zeroRestriction K hK).app
        (O.katz K hK (kloostermanIndex psi hpsi 3 (by decide) 0)))))).trans
    (HasRegularTameBasis.threeEquiv _ _ (rawKatzBaseBasis K E hK hE psi hpsi 3 (by decide)))

/-- Smooth ALL-character AS lissity plus actual generic rank gives the full trivial representation. -/
def asGeometricModel (K E : Type) [Field K] [Fintype K] [Field E] [Fintype E]
    [Algebra K E] (hK : (2 : K) ≠ 0) (hE : (2 : E) ≠ 0)
    (psi : AddChar K (PadicAlgCl 2)) (hpsi : psi ≠ 1) :
    Representation.Equiv
      ((nativeOrigin.{mu,nu,g} C U F nativeCompact B D originTrait K E hE).obj
        (O.artinSchreier K hK psi)).ρ
      (Representation.trivial ℂ (CommonGroup.{g} K) ℂ) :=
  rankOneTrivialEquiv _ (smoothBaseOriginAction K E hK hE _ (standardASLisse K hK psi hpsi))
    ((LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv
      ((nativeNearby.{mu,nu,g} C U F nativeCompact B D originTrait K E hE).mapIso
        (ScalarLocalPropagationFromFilteredTraits.localInputBaseIso K E C U
          (O.artinSchreier K hK psi))))).trans
    ((lisseBaseNearbyGenericDimension K E hK hE _
      (lissePull (localInputMorphism K K) _ (standardASLisse K hK psi hpsi))).trans
      (standardASGenericRank K hK psi hpsi)))

/- Independent standard GENERAL packages and individual object/curve
recognitions; no native completed rule record is a parameter. -/
variable (Pstd : StandardKloostermanLangOrigin.Operations S B)
  {primitiveInterpretation : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,0,0} S),
    StandardKloostermanLangOrigin.Operations S B → Prop}
  (primitiveTheorems : StandardKloostermanLangOrigin.PublishedTheorems primitiveInterpretation)
  (primitiveModel : primitiveInterpretation S B Pstd)
  (X : StandardFiniteConstantOrigin.Operations S B)
  {constantInterpretation : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,0,0} S),
    StandardFiniteConstantOrigin.Operations S B → Prop}
  (constantTheorems : StandardFiniteConstantOrigin.PublishedTheorems constantInterpretation)
  (constantModel : constantInterpretation S B X)
  (curveComparison : ∀ (K E : Type) [Field K] [Fintype K] [Field E] [Fintype E] [Algebra K E]
    (hK : (2 : K) ≠ 0) (hE : (2 : E) ≠ 0),
    U.pull (OriginFiniteConstantInvariantFrobeniusTransport.constantExtensionMorphism K E) ⋙
      D.curveRealization E hE ≅ D.curveRealization K hK ⋙ X.curvePull K E hK hE)
  (rawObjectRecognition : ∀ (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
    (n : ℕ) (hn : 0 < n) (psi : AddChar K (PadicAlgCl 2)) (hpsi : psi ≠ 1),
    (D.curveRealization K hK).obj ((U.pull (localInputMorphism K K)).obj
      ((O.zero K hK).obj (O.katz K hK (kloostermanIndex psi hpsi n hn 0)))) ≅
      Pstd.rawKloosterman K hK n psi)
  (asObjectRecognition : ∀ (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
    (psi : AddChar K (PadicAlgCl 2)) (_hpsi : psi ≠ 1),
    (D.curveRealization K hK).obj ((U.pull (localInputMorphism K K)).obj
      (O.artinSchreier K hK psi)) ≅ (Pstd.restriction K hK).obj (Pstd.langAS K hK psi))

variable (p : ℕ) [Fact p.Prime] (h2p : (2 : ZMod p) ≠ 0)
abbrev extensionGuard (E : Type) [Field E] [Algebra (ZMod p) E] : (2 : E) ≠ 0 :=
  OriginRulesFromStandardPrimitiveAndFiniteConstant.extension_two_ne_zero p h2p E

/-- ALL finite-extension invariant actions computed from genuine independent standard theorems. -/
def computedFrobeniusRules : PublishedOriginFrobenius.Rules (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p))
    (OriginRulesFromStandardPrimitiveAndFiniteConstant.commonOriginFamily.{nu,mu,g}
      C U F nativeCompact B D originTrait p (fun E _ _ _ => extensionGuard p h2p E)) :=
  OriginRulesFromStandardPrimitiveAndFiniteConstant.commonOriginRules.{nu,mu,g}
    C U F nativeCompact B D Pstd primitiveTheorems primitiveModel X constantTheorems
    constantModel originTrait p (fun E _ _ _ => extensionGuard p h2p E)
    (fun E _ _ _ => curveComparison (ZMod p) E h2p (extensionGuard p h2p E)) (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p))
    (fun psi hpsi => by
      change (D.curveRealization (ZMod p) h2p).obj
        ((U.pull (localInputMorphism (ZMod p) (ZMod p))).obj
          ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p).kloosterman3 psi)) ≅ _
      rw [primitiveOperations_kloosterman3_nontrivial C O p h2p psi hpsi]
      exact rawObjectRecognition (ZMod p) h2p 3 (by decide) psi hpsi)
    (fun psi hpsi => by
      change (D.curveRealization (ZMod p) h2p).obj
        ((U.pull (localInputMorphism (ZMod p) (ZMod p))).obj
          (O.artinSchreier (ZMod p) h2p psi)) ≅ _
      exact asObjectRecognition (ZMod p) h2p psi hpsi)

section OneFiniteExtension
variable (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]

/- The following are individual ordinary/Tate operations and ALL-object
squares on this same E; a uniform caller supplies their transparent
ALL-prime/ALL-E families. They are not a StalkData/Inputs provider. -/
variable {Point : Type pt} [Category.{ps} Point]
  (ordinaryOrigin : S.Curve E (extensionGuard p h2p E) ⥤ Point) (pointFiber : Point ⥤ ModuleCat ℂ)
  (pointFr : ∀ A, pointFiber.obj A ≃ₗ[ℂ] pointFiber.obj A)
  (pointNatural : ∀ {A A'} (f : A ≅ A') x,
    (pointFiber.mapIso f).toLinearEquiv (pointFr A x) =
      pointFr A' ((pointFiber.mapIso f).toLinearEquiv x))
  (jstarComparison : (Primitives.origin B E (extensionGuard p h2p E)) ⋙ forget₂ (FDRep ℂ (B.OriginGroup E (extensionGuard p h2p E)))
    (Rep ℂ (B.OriginGroup E (extensionGuard p h2p E))) ⋙ Rep.invariantsFunctor ℂ (B.OriginGroup E (extensionGuard p h2p E)) ≅
      ordinaryOrigin ⋙ pointFiber)
  (jstarOperator : ∀ A x, (jstarComparison.app A).toLinearEquiv
    (ArithmeticBoundaryFromInvariantFunctors.invariantAction ((Primitives.origin B E (extensionGuard p h2p E)).obj A)
      ((Primitives.originWeil B E (extensionGuard p h2p E)).localFrobenius.action A) (Primitives.originConjugation B E (extensionGuard p h2p E)) ((Primitives.originWeil B E (extensionGuard p h2p E)).covariance A) x) =
      pointFr (ordinaryOrigin.obj A) ((jstarComparison.app A).toLinearEquiv x))
  (standardScalar : Eˣ → S.Curve E (extensionGuard p h2p E) ⥤ S.Curve E (extensionGuard p h2p E))
  (fixedOrigin : ∀ a, standardScalar a ⋙ ordinaryOrigin ≅ ordinaryOrigin)
  (scalarOperation : ∀ a, (SourceInverseImageSystem.System.arithmeticPullbacks (primeSource C U p) E).localEnd (scalarMorphism (ZMod p) E a) ⋙ (FaithfulArithmeticOperations.curveRealization D E (extensionGuard p h2p E)) ≅ (FaithfulArithmeticOperations.curveRealization D E (extensionGuard p h2p E)) ⋙ standardScalar a)
  (T : S.Curve E (extensionGuard p h2p E)) (basis : ((Primitives.origin B E (extensionGuard p h2p E)).obj T).V ≃ₗ[ℂ] ℂ)
  (inertiaTrivial : ∀ z x, basis (((Primitives.origin B E (extensionGuard p h2p E)).obj T).ρ z x) = basis x)
  (twistOperation : letI := B.curveMonoidal E (extensionGuard p h2p E); ∀ A, ((SourceInverseImageSystem.System.arithmeticPullbacks (primeSource C U p) E).specialized (localInputMorphism (ZMod p) E) ⋙ (FaithfulArithmeticOperations.curveRealization D E (extensionGuard p h2p E))).obj ((PublishedPrimitiveSources.Data.twistOne (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p))) A) ≅
    ((SourceInverseImageSystem.System.arithmeticPullbacks (primeSource C U p) E).specialized (localInputMorphism (ZMod p) E) ⋙ (FaithfulArithmeticOperations.curveRealization D E (extensionGuard p h2p E))).obj A ⊗ T)
  (tensorRule : letI := B.curveMonoidal E (extensionGuard p h2p E); ArithmeticTensorFromWeil.TensorRules (Primitives.originWeil B E (extensionGuard p h2p E)))
  (lineOperator : ∀ x, basis ((Primitives.originWeil B E (extensionGuard p h2p E)).localFrobenius.action T x) = (Fintype.card E : ℂ)⁻¹ * basis x)
  (LG : CanonicalCurveInput.LineGeometry (C (affineLine (ZMod p))))
  (standardLisse standardTame : S.Curve E (extensionGuard p h2p E) → Prop)
  (lisseRecognition : ∀ A, LG.LisseOnUnits A → standardLisse (((SourceInverseImageSystem.System.arithmeticPullbacks (primeSource C U p) E).specialized (localInputMorphism (ZMod p) E) ⋙ (FaithfulArithmeticOperations.curveRealization D E (extensionGuard p h2p E))).obj A))
  (tameRecognition : ∀ A, LG.TameZero A → standardTame (((SourceInverseImageSystem.System.arithmeticPullbacks (primeSource C U p) E).specialized (localInputMorphism (ZMod p) E) ⋙ (FaithfulArithmeticOperations.curveRealization D E (extensionGuard p h2p E))).obj A))
  (standardScalarRestriction : ∀ (a : Eˣ) A, standardLisse A → standardTame A →
    Representation.Equiv ((Primitives.origin B E (extensionGuard p h2p E)).obj ((standardScalar a).obj A)).ρ ((Primitives.origin B E (extensionGuard p h2p E)).obj A).ρ)

/-- Compute the first three fields and guarded scalar restriction from individual operations. -/
def computedStalkData : ArithmeticOriginFromScalar.StalkData (ZMod p) E (SourceInverseImageSystem.System.arithmeticPullbacks (primeSource C U p) E) (nativeNearby C U F nativeCompact B D originTrait (ZMod p) E (extensionGuard p h2p E)) (LocalWeilAction.Data.localFrobenius (NativeCommonArithmeticTraitWeilCone.weilData.{0,mu,nu,g}
  (ZMod p) E B originTrait (extensionGuard p h2p E) (FaithfulArithmeticOperations.curveRealization D E (extensionGuard p h2p E)))) LG (PublishedPrimitiveSources.Data.twistOne (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p))) := by
  letI := B.curveMonoidal E (extensionGuard p h2p E)
  exact CommonOriginStalkDataFromStandardOperations.stalkData
    (K := ZMod p) (E := E) (P := (SourceInverseImageSystem.System.arithmeticPullbacks (primeSource C U p) E)) (R := (FaithfulArithmeticOperations.curveRealization D E (extensionGuard p h2p E))) (standardJ := (Primitives.origin B E (extensionGuard p h2p E)))
    (standardPhi := (Primitives.originConjugation B E (extensionGuard p h2p E))) (standardW := (Primitives.originWeil B E (extensionGuard p h2p E))) (groupDictionary := (NativeCommonArithmeticTraitWeilCone.originEquiv.{nu,g}
  (ZMod p) E B originTrait (extensionGuard p h2p E)))
    (weilDictionary := (NativeCommonArithmeticTraitWeilCone.weilEquiv.{nu,g} E B (extensionGuard p h2p E))) (ordinaryOrigin := ordinaryOrigin) (pointFiber := pointFiber)
    (pointFr := pointFr) (pointNatural := pointNatural) (jstarComparison := jstarComparison)
    (jstarOperator := jstarOperator) (standardScalar := standardScalar) (fixedOrigin := fixedOrigin)
    (scalarOperation := scalarOperation) (twistOne := (PublishedPrimitiveSources.Data.twistOne (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p)))) (T := T) (basis := basis)
    (inertiaTrivial := inertiaTrivial) (twistOperation := twistOperation) (tensorRule := tensorRule)
    (lineOperator := lineOperator) (LG := LG) (standardLisse := standardLisse)
    (standardTame := standardTame) (lisseRecognition := lisseRecognition)
    (tameRecognition := tameRecognition) (standardScalarRestriction := standardScalarRestriction)

/-- All seven original fields assembled; no specialized origin package is a premise. -/
def computedOriginInputs (hp : 3 < p)
    (hkl : CanonicalCurveInput.Kl3Properties LG ((PublishedPrimitiveSources.Data.twistOne (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p))) (PublishedPrimitiveSources.Data.rawKl (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p)))))
    (has : CanonicalCurveInput.ASProperties LG (PublishedPrimitiveSources.Data.as (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p)))) :
    ArithmeticSourcesFromOrigin.Inputs (ZMod p) E (SourceInverseImageSystem.System.arithmeticPullbacks (primeSource C U p) E) (nativeNearby C U F nativeCompact B D originTrait (ZMod p) E (extensionGuard p h2p E)) (LocalWeilAction.Data.localFrobenius (NativeCommonArithmeticTraitWeilCone.weilData.{0,mu,nu,g}
  (ZMod p) E B originTrait (extensionGuard p h2p E) (FaithfulArithmeticOperations.curveRealization D E (extensionGuard p h2p E)))) (PublishedPrimitiveSources.Data.twistOne (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p))) (PublishedPrimitiveSources.Data.rawKl (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p))) (PublishedPrimitiveSources.Data.as (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p))) (tame (ZMod p)) := by
  letI := B.curveMonoidal E (extensionGuard p h2p E)
  let SD := computedStalkData C U F O nativeCompact B D originTrait p h2p E
    ordinaryOrigin pointFiber pointFr pointNatural jstarComparison jstarOperator standardScalar
    fixedOrigin scalarOperation T basis inertiaTrivial twistOperation tensorRule lineOperator
    LG standardLisse standardTame lisseRecognition tameRecognition standardScalarRestriction
  let FR := computedFrobeniusRules C U F O nativeCompact B D originTrait Pstd primitiveTheorems
    primitiveModel X constantTheorems constantModel curveComparison rawObjectRecognition
    asObjectRecognition p h2p
  let I : ArithmeticOriginFromScalar.Inputs (ZMod p) E (SourceInverseImageSystem.System.arithmeticPullbacks (primeSource C U p) E) (nativeNearby C U F nativeCompact B D originTrait (ZMod p) E (extensionGuard p h2p E)) (LocalWeilAction.Data.localFrobenius (NativeCommonArithmeticTraitWeilCone.weilData.{0,mu,nu,g}
  (ZMod p) E B originTrait (extensionGuard p h2p E) (FaithfulArithmeticOperations.curveRealization D E (extensionGuard p h2p E)))) LG (PublishedPrimitiveSources.Data.twistOne (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p))) (PublishedPrimitiveSources.Data.rawKl (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p))) (PublishedPrimitiveSources.Data.as (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p))) (tame (ZMod p)) := {
    toGeometry := {
      toStalkData := SD
      klModel := by
        change Representation.Equiv
          ((nativeOrigin C U F nativeCompact B D originTrait (ZMod p) E (extensionGuard p h2p E)).obj
            ((O.lineTate (ZMod p) h2p 1).obj (PublishedPrimitiveSources.Data.rawKl (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p))))).ρ _
        refine (equivOfIso ((lineTateBaseNearby (ZMod p) E h2p (extensionGuard p h2p E) 1).app (PublishedPrimitiveSources.Data.rawKl (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p))))).trans ?_
        rw [ArithmeticPrimitivesFromCommonKatzConstruction.canonical_rawKl
          (C := C) (O := O) (p := p) (h2 := h2p) (U := U) (R := (pointStalks C U F p))]
        exact rawGeometricModel C U F O nativeCompact B D originTrait tame zeroRestriction
          rawKatzBaseBasis (ZMod p) E h2p (extensionGuard p h2p E) _ (CanonicalSourceCharacter.prime_ne_one p)
      asModel := by
        change Representation.Equiv
          ((nativeOrigin C U F nativeCompact B D originTrait (ZMod p) E (extensionGuard p h2p E)).obj
            (O.artinSchreier (ZMod p) h2p (CanonicalSourceCharacter.prime p))).ρ _
        exact asGeometricModel.{mu,nu,g} C U F O geometricFiber lisse nativeCompact B D originTrait
          smoothBaseOriginAction lisseBaseNearbyGenericDimension lissePull standardASLisse
          standardASGenericRank (ZMod p) E h2p (extensionGuard p h2p E) _ (CanonicalSourceCharacter.prime_ne_one p) }
    rawAction := by
      intro v
      change (OriginRulesFromStandardPrimitiveAndFiniteConstant.commonOriginFamily.{nu,mu,g}
        C U F nativeCompact B D originTrait p (fun E _ _ _ => extensionGuard p h2p E) E).frobenius (PublishedPrimitiveSources.Data.rawKl (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p))) v = v
      exact FR.canonical_rawAction hp E v
    asAction := by
      intro v
      change (OriginRulesFromStandardPrimitiveAndFiniteConstant.commonOriginFamily.{nu,mu,g}
        C U F nativeCompact B D originTrait p (fun E _ _ _ => extensionGuard p h2p E) E).frobenius (PublishedPrimitiveSources.Data.as (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p))) v = v
      exact FR.canonical_asAction hp E v }
  exact I.toOriginInputs hkl has
end OneFiniteExtension
end PrimeGap182.TypeIII.OriginInputsFromSharedStandardOperationsHELD04
