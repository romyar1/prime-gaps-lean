import TypeIIIOriginInputsFromSharedStandardOperationsHELD04
import TypeIIIGloballyLisseLineRamificationFromKatz

/-!
# ALL-prime arithmetic origin Inputs computed from general operations

This is the arithmetic component of the coherent endpoint factory. One
ordinary all-schemes category, inverse-image, finite-point and standard
Katz/AS/Tate theory is fixed before p. The theorem record retains ALL-rank,
ALL-character and ALL-object primitive/finite-constant statements. Its
ordinary operation families are quantified over ALL primes and ALL finite
extensions, with scalar/j-star/Tate laws on ALL eligible ordinary objects.

No OriginStalks, StalkData, geometric model, origin Frobenius Rules,
seven-field Inputs, scalar q^-1, complete AM or Application provider is a
record field. They are computed by the surviving seven-field constructor.
The arithmetic CommonGroup Fp is kept separate from the nonfinite geometric
origin group used by the generic Fourier component.

Genuine compatible standard adic/operator/trait interpretation, positive
tame calibration and published theorem matching remain external. Primitive
hkl/has are guarded inputs to this component, to be obtained from the
GENERAL Katz/AS application in the full factory. No Lean execution or
complete endpoint is claimed.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped MonoidalCategory PrimeGap182.TypeIII.TwoAdicComplexEmbedding

namespace PrimeGap182.TypeIII.AllPrimeOriginInputsFromGeneralOperationFamilies05
open ExactInverseImagesToDerived RationalPointStalksFromUniversalFiber
open QSTPrimitiveBridgesFromCommonKatzConstruction CanonicalPrimeFramework
open StartingSourceMaps ArithmeticSourceMaps ArithmeticSourceTransport
open ArithmeticSourcesFromOrigin ArithmeticPrimitiveSources
open ArithmeticPrimitivesFromCommonKatzConstruction
open StandardGmTraceFromFaithfulArithmeticOperations StandardP1BoundaryPrimitives
open RegularTameBasisFromFiniteJordanExponential GenericOriginFractionFieldCoordinates
open OriginInputsFromSharedStandardOperationsHELD04

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

  (geometricM : PrimitiveRamificationFromGeneralKatzTheory.LocalRealization C)

local instance allLocalizations : ∀ X : Scheme, HasDerivedCategory.{mu} (C X) :=
  fun _ => HasDerivedCategory.standard _

/-- SAME original rational stalks and SAME actual global geometric line. -/
def computedPrimitiveLine (p : ℕ) [Fact p.Prime] :=
  LinePurityFromStalks.geometry (pointStalks C U F p)
    (GloballyLisseLineRamificationFromKatz.canonicalObservables C U lisse geometricM geometricFiber (ZMod p))

/-- Standard ordinary zero/scalar/Tate operators and ALL-object laws.
The genuine standard theory supplies these for every prime and finite E.
Nothing in this record mentions a finished Kloosterman correlation.
-/
structure OrdinaryOriginOperationKit (p : ℕ) [Fact p.Prime]
    (h2p : (2 : ZMod p) ≠ 0) (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] where
  Point : Type pt
  [pointCategory : Category.{ps} Point]
  ordinaryOrigin : S.Curve E (extensionGuard p h2p E) ⥤ Point
  pointFiber : Point ⥤ ModuleCat ℂ
  pointFr : ∀ A, pointFiber.obj A ≃ₗ[ℂ] pointFiber.obj A
  pointNatural : ∀ {A A'} (f : A ≅ A') x,
    (pointFiber.mapIso f).toLinearEquiv (pointFr A x) =
      pointFr A' ((pointFiber.mapIso f).toLinearEquiv x)
  jstarComparison : (Primitives.origin B E (extensionGuard p h2p E)) ⋙ forget₂ (FDRep ℂ (B.OriginGroup E (extensionGuard p h2p E)))
    (Rep ℂ (B.OriginGroup E (extensionGuard p h2p E))) ⋙ Rep.invariantsFunctor ℂ (B.OriginGroup E (extensionGuard p h2p E)) ≅
      ordinaryOrigin ⋙ pointFiber
  jstarOperator : ∀ A x, (jstarComparison.app A).toLinearEquiv
    (ArithmeticBoundaryFromInvariantFunctors.invariantAction ((Primitives.origin B E (extensionGuard p h2p E)).obj A)
      ((Primitives.originWeil B E (extensionGuard p h2p E)).localFrobenius.action A) (Primitives.originConjugation B E (extensionGuard p h2p E)) ((Primitives.originWeil B E (extensionGuard p h2p E)).covariance A) x) =
      pointFr (ordinaryOrigin.obj A) ((jstarComparison.app A).toLinearEquiv x)
  standardScalar : Eˣ → S.Curve E (extensionGuard p h2p E) ⥤ S.Curve E (extensionGuard p h2p E)
  fixedOrigin : ∀ a, standardScalar a ⋙ ordinaryOrigin ≅ ordinaryOrigin
  scalarOperation : ∀ a, (SourceInverseImageSystem.System.arithmeticPullbacks (primeSource C U p) E).localEnd (scalarMorphism (ZMod p) E a) ⋙ (FaithfulArithmeticOperations.curveRealization D E (extensionGuard p h2p E)) ≅ (FaithfulArithmeticOperations.curveRealization D E (extensionGuard p h2p E)) ⋙ standardScalar a
  T : S.Curve E (extensionGuard p h2p E)
  basis : ((Primitives.origin B E (extensionGuard p h2p E)).obj T).V ≃ₗ[ℂ] ℂ
  inertiaTrivial : ∀ z x, basis (((Primitives.origin B E (extensionGuard p h2p E)).obj T).ρ z x) = basis x
  twistOperation : letI := B.curveMonoidal E (extensionGuard p h2p E); ∀ A, ((SourceInverseImageSystem.System.arithmeticPullbacks (primeSource C U p) E).specialized (localInputMorphism (ZMod p) E) ⋙ (FaithfulArithmeticOperations.curveRealization D E (extensionGuard p h2p E))).obj ((PublishedPrimitiveSources.Data.twistOne (RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
  (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2p))) A) ≅
    ((SourceInverseImageSystem.System.arithmeticPullbacks (primeSource C U p) E).specialized (localInputMorphism (ZMod p) E) ⋙ (FaithfulArithmeticOperations.curveRealization D E (extensionGuard p h2p E))).obj A ⊗ T
  tensorRule : letI := B.curveMonoidal E (extensionGuard p h2p E); ArithmeticTensorFromWeil.TensorRules (Primitives.originWeil B E (extensionGuard p h2p E))
  lineOperator : ∀ x, basis ((Primitives.originWeil B E (extensionGuard p h2p E)).localFrobenius.action T x) = (Fintype.card E : ℂ)⁻¹ * basis x
  standardLisse : S.Curve E (extensionGuard p h2p E) → Prop
  standardTame : S.Curve E (extensionGuard p h2p E) → Prop
  lisseRecognition : ∀ A, (computedPrimitiveLine C U F geometricFiber lisse geometricM p).LisseOnUnits A → standardLisse (((SourceInverseImageSystem.System.arithmeticPullbacks (primeSource C U p) E).specialized (localInputMorphism (ZMod p) E) ⋙ (FaithfulArithmeticOperations.curveRealization D E (extensionGuard p h2p E))).obj A)
  tameRecognition : ∀ A, (computedPrimitiveLine C U F geometricFiber lisse geometricM p).TameZero A → standardTame (((SourceInverseImageSystem.System.arithmeticPullbacks (primeSource C U p) E).specialized (localInputMorphism (ZMod p) E) ⋙ (FaithfulArithmeticOperations.curveRealization D E (extensionGuard p h2p E))).obj A)
  standardScalarRestriction : ∀ (a : Eˣ) A, standardLisse A → standardTame A →
    Representation.Equiv ((Primitives.origin B E (extensionGuard p h2p E)).obj ((standardScalar a).obj A)).ρ ((Primitives.origin B E (extensionGuard p h2p E)).obj A).ρ

/-- One precise GENERAL origin-theory boundary, before p. The standard
interpretation fields refer to independently standard ALL-object packages;
this does not prove that an arbitrary supplied native category realizes them.
-/
structure GeneralSharedOriginTheory where
  tame : ∀ (K : Type) [Field K] [Fintype K], CommonGroup.{g} K →* Multiplicative ℂ
  zeroRestriction : ∀ (K : Type) [Field K] (hK : (2 : K) ≠ 0),
    O.zero K hK ⋙ U.pull (localInputMorphism K K) ≅ 𝟭 _
  rawKatzBaseBasis : ∀ (K E : Type) [Field K] [Fintype K] [Field E] [Fintype E]
    [Algebra K E] (hK : (2 : K) ≠ 0) (hE : (2 : E) ≠ 0)
    (psi : AddChar K (PadicAlgCl 2)) (_hpsi : psi ≠ 1) (n : ℕ) (_hn : 0 < n),
    HasRegularTameBasis
      ((U.pull (ScalarLocalPropagationFromFilteredTraits.baseGmMorphism K E) ⋙
        nativeNearby.{mu,nu,g} C U F nativeCompact B D originTrait K E hE).obj
        (O.katz K hK (kloostermanIndex psi _hpsi n _hn 0))).ρ (tame K) n
  lineTateBaseNearby : ∀ (K E : Type) [Field K] [Fintype K] [Field E] [Fintype E]
    [Algebra K E] (hK : (2 : K) ≠ 0) (hE : (2 : E) ≠ 0) (n : ℤ),
    O.lineTate K hK n ⋙ nativeOrigin.{mu,nu,g} C U F nativeCompact B D originTrait K E hE ≅
      nativeOrigin.{mu,nu,g} C U F nativeCompact B D originTrait K E hE
  smoothBaseOriginAction : ∀ (K E : Type) [Field K] [Fintype K] [Field E] [Fintype E]
    [Algebra K E] (_hK : (2 : K) ≠ 0) (hE : (2 : E) ≠ 0)
    (A : C (affineLine K)), lisse (affineLine K) A →
      ∀ z, ((nativeOrigin.{mu,nu,g} C U F nativeCompact B D originTrait K E hE).obj A).ρ z = 1
  lisseBaseNearbyGenericDimension : ∀ (K E : Type) [Field K] [Fintype K]
    [Field E] [Fintype E] [Algebra K E] (_hK : (2 : K) ≠ 0) (hE : (2 : E) ≠ 0)
    (A : C (fiberScheme K)), lisse (fiberScheme K) A →
      Module.finrank ℂ ((U.pull (ScalarLocalPropagationFromFilteredTraits.baseGmMorphism K E) ⋙
        nativeNearby.{mu,nu,g} C U F nativeCompact B D originTrait K E hE).obj A) =
      Module.finrank ℂ ((QSTGenericFiberFromActualGenericPoint.rawGenericFiber
        K C U geometricFiber).obj ((QSTCompactBridgeFromCompactifiedDerivedPushforward.boundedDegreeZero
          C _).obj A))
  lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y), lisse Y A → lisse X ((U.pull f).obj A)
  standardASLisse : ∀ (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
    (psi : AddChar K (PadicAlgCl 2)), psi ≠ 1 → lisse (affineLine K) (O.artinSchreier K hK psi)
  standardASGenericRank : ∀ (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
    (psi : AddChar K (PadicAlgCl 2)), psi ≠ 1 →
      PrimitiveRanksFromComputedGenericLineRank.canonicalLineRank C U geometricFiber K
        (O.artinSchreier K hK psi) = 1
  Pstd : StandardKloostermanLangOrigin.Operations S B
  primitiveInterpretation : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,0,0} S),
    StandardKloostermanLangOrigin.Operations S B → Prop
  primitiveTheorems : StandardKloostermanLangOrigin.PublishedTheorems primitiveInterpretation
  primitiveModel : primitiveInterpretation S B Pstd
  X : StandardFiniteConstantOrigin.Operations S B
  constantInterpretation : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,0,0} S),
    StandardFiniteConstantOrigin.Operations S B → Prop
  constantTheorems : StandardFiniteConstantOrigin.PublishedTheorems constantInterpretation
  constantModel : constantInterpretation S B X
  curveComparison : ∀ (K E : Type) [Field K] [Fintype K] [Field E] [Fintype E] [Algebra K E]
    (hK : (2 : K) ≠ 0) (hE : (2 : E) ≠ 0),
    U.pull (OriginFiniteConstantInvariantFrobeniusTransport.constantExtensionMorphism K E) ⋙
      D.curveRealization E hE ≅ D.curveRealization K hK ⋙ X.curvePull K E hK hE
  rawObjectRecognition : ∀ (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
    (n : ℕ) (hn : 0 < n) (psi : AddChar K (PadicAlgCl 2)) (hpsi : psi ≠ 1),
    (D.curveRealization K hK).obj ((U.pull (localInputMorphism K K)).obj
      ((O.zero K hK).obj (O.katz K hK (kloostermanIndex psi hpsi n hn 0)))) ≅
      Pstd.rawKloosterman K hK n psi
  asObjectRecognition : ∀ (K : Type) [Field K] [Fintype K] (hK : (2 : K) ≠ 0)
    (psi : AddChar K (PadicAlgCl 2)) (_hpsi : psi ≠ 1),
    (D.curveRealization K hK).obj ((U.pull (localInputMorphism K K)).obj
      (O.artinSchreier K hK psi)) ≅ (Pstd.restriction K hK).obj (Pstd.langAS K hK psi)
  ordinaryOperations : ∀ (p : ℕ) [Fact p.Prime] (h2p : (2 : ZMod p) ≠ 0)
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
      OrdinaryOriginOperationKit.{mu,nu,ps,pt} (C := C) (U := U) (F := F) (O := O)
        (geometricFiber := geometricFiber) (lisse := lisse)
        (nativeCompact := nativeCompact) (B := B) (D := D)
        (geometricM := geometricM) p h2p E

variable (general : GeneralSharedOriginTheory.{mu,nu,g,ps,pt} (C := C) (U := U) (F := F) (O := O)
  (geometricFiber := geometricFiber) (lisse := lisse) (nativeCompact := nativeCompact)
  (B := B) (D := D) (originTrait := originTrait) (geometricM := geometricM))

include C U F O geometricFiber lisse nativeCompact B D originTrait geometricM general

/-- Seven-field Inputs are OUTPUTS for every prime and finite extension.
All scalar and invariant Frobenius operations are on the same native J/LF.
No all-prime finished Inputs provider is accepted.
-/
def computedAllPrimeOriginInputs (p : ℕ) [Fact p.Prime]
    (h2p : (2 : ZMod p) ≠ 0) (hp : 3 < p)
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (hkl : CanonicalCurveInput.Kl3Properties (computedPrimitiveLine C U F geometricFiber lisse geometricM p)
      ((PublishedPrimitiveSources.Data.twistOne (RationalPointStalks.PrimitiveOperations.primitive
        (pointStalks C U F p) (primitiveOperations C O p h2p)))
        (PublishedPrimitiveSources.Data.rawKl (RationalPointStalks.PrimitiveOperations.primitive
          (pointStalks C U F p) (primitiveOperations C O p h2p)))))
    (has : CanonicalCurveInput.ASProperties (computedPrimitiveLine C U F geometricFiber lisse geometricM p)
      (PublishedPrimitiveSources.Data.as (RationalPointStalks.PrimitiveOperations.primitive
        (pointStalks C U F p) (primitiveOperations C O p h2p)))) := by
  let kit := general.ordinaryOperations p h2p E
  letI := kit.pointCategory
  exact OriginInputsFromSharedStandardOperationsHELD04.computedOriginInputs
    (C := C) (U := U) (F := F) (O := O) (geometricFiber := geometricFiber) (lisse := lisse)
    (nativeCompact := nativeCompact) (B := B) (D := D) (originTrait := originTrait)
    (tame := general.tame) (zeroRestriction := general.zeroRestriction)
    (rawKatzBaseBasis := general.rawKatzBaseBasis) (lineTateBaseNearby := general.lineTateBaseNearby)
    (smoothBaseOriginAction := general.smoothBaseOriginAction)
    (lisseBaseNearbyGenericDimension := general.lisseBaseNearbyGenericDimension)
    (lissePull := general.lissePull) (standardASLisse := general.standardASLisse)
    (standardASGenericRank := general.standardASGenericRank)
    (Pstd := general.Pstd) (primitiveTheorems := general.primitiveTheorems)
    (primitiveModel := general.primitiveModel) (X := general.X)
    (constantTheorems := general.constantTheorems) (constantModel := general.constantModel)
    (curveComparison := general.curveComparison) (rawObjectRecognition := general.rawObjectRecognition)
    (asObjectRecognition := general.asObjectRecognition) (p := p) (h2p := h2p) (E := E)
    (ordinaryOrigin := kit.ordinaryOrigin) (pointFiber := kit.pointFiber)
    (pointFr := kit.pointFr) (pointNatural := kit.pointNatural)
    (jstarComparison := kit.jstarComparison) (jstarOperator := kit.jstarOperator)
    (standardScalar := kit.standardScalar) (fixedOrigin := kit.fixedOrigin)
    (scalarOperation := kit.scalarOperation) (T := kit.T) (basis := kit.basis)
    (inertiaTrivial := kit.inertiaTrivial) (twistOperation := kit.twistOperation)
    (tensorRule := kit.tensorRule) (lineOperator := kit.lineOperator)
    (LG := computedPrimitiveLine C U F geometricFiber lisse geometricM p)
    (standardLisse := kit.standardLisse) (standardTame := kit.standardTame)
    (lisseRecognition := kit.lisseRecognition) (tameRecognition := kit.tameRecognition)
    (standardScalarRestriction := kit.standardScalarRestriction) hp hkl has

end PrimeGap182.TypeIII.AllPrimeOriginInputsFromGeneralOperationFamilies05

#print axioms PrimeGap182.TypeIII.AllPrimeOriginInputsFromGeneralOperationFamilies05.computedAllPrimeOriginInputs
