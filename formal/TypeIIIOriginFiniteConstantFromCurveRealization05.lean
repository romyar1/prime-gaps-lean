import TypeIIIStandardFiniteConstantOriginTheorems01

/-! One individual ordinary curve-realization/pull comparison is enough to
apply the GENERAL standard finite-constant origin theorem to every native
affine-line object. The source map and compositor are computed. The extra
coefficient Frobenius square is derived from SAME standard Weil naturality;
it is never a second selected recognition/provider assumption. -/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace PrimeGap182.TypeIII.OriginFiniteConstantFromCurveRealization
open ArithmeticSourcesFromOrigin ArithmeticSourceMaps StartingSourceMaps
open StandardGmTraceFromFaithfulArithmeticOperations StandardP1BoundaryPrimitives
open ExactInverseImagesToDerived RationalPointStalksFromUniversalFiber
open OriginStalksFromStandardWeilInvariants StandardFiniteConstantOrigin
universe nu mu g
variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C) (F : ArithmeticFibers C)
  (nativeCompact : ∀ (E : Type) [Field E] [Fintype E] (_h2 : (2 : E) ≠ 0),
    Fin 3 → C (fiberScheme E) ⥤ C (Spec (.of E)))
  {S : StandardGmPrimitives.{nu}} (B : Primitives.{nu,0,0} S)
  (D : FaithfulArithmeticOperations C U F nativeCompact S)
  (X : StandardFiniteConstantOrigin.Operations S B)
  {interpretation : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,0,0} S),
    StandardFiniteConstantOrigin.Operations S B → Prop}
  (published : StandardFiniteConstantOrigin.PublishedTheorems interpretation)
  (model : interpretation S B X)
  (K E : Type) [Field K] [Field E] [Fintype K] [Fintype E] [Algebra K E]
  (h2K : (2 : K) ≠ 0) (h2E : (2 : E) ≠ 0)
  (curvePullComparison : U.pull (OriginFiniteConstantInvariantFrobeniusTransport.constantExtensionMorphism K E) ⋙
    D.curveRealization E h2E ≅ D.curveRealization K h2K ⋙ X.curvePull K E h2K h2E)

/-- Exact source realization, with positive-T scheme identity and SAME U. -/
def sourceRealizationIso : U.pull (localInputMorphism K E) ⋙ D.curveRealization E h2E ≅
    (U.pull (localInputMorphism K K) ⋙ D.curveRealization K h2K) ⋙ X.curvePull K E h2K h2E :=
  Functor.isoWhiskerRight (OriginFiniteConstantInvariantFrobeniusTransport.sourceConstantPullIso K E C U).symm
    (D.curveRealization E h2E) ≪≫
  Functor.associator (U.pull (localInputMorphism K K))
    (U.pull (OriginFiniteConstantInvariantFrobeniusTransport.constantExtensionMorphism K E))
    (D.curveRealization E h2E) ≪≫
  Functor.isoWhiskerLeft (U.pull (localInputMorphism K K)) curvePullComparison ≪≫
  (Functor.associator (U.pull (localInputMorphism K K)) (D.curveRealization K h2K)
    (X.curvePull K E h2K h2E)).symm

/-- Map only the individual curve-operation isomorphism through origin. -/
def sourceCoefficientIso (A : C (affineLine K)) :
    (B.origin E h2E).obj ((D.curveRealization E h2E).obj ((U.pull (localInputMorphism K E)).obj A)) ≅
    (B.origin E h2E).obj ((X.curvePull K E h2K h2E).obj
      ((D.curveRealization K h2K).obj ((U.pull (localInputMorphism K K)).obj A))) :=
  (B.origin E h2E).mapIso (sourceRealizationIso C U F nativeCompact B D X K E h2K h2E
    curvePullComparison |>.app A)

def sourceInvariantIso (A : C (affineLine K)) :
    (OriginStalksFromStandardWeilInvariants.originStalks C U F nativeCompact B D K E h2E).fiber A ≃ₗ[ℂ]
    (invariantStalks (B.origin E h2E) (B.originConjugation E h2E) (B.originWeil E h2E)).fiber
      ((X.curvePull K E h2K h2E).obj
        ((D.curveRealization K h2K).obj ((U.pull (localInputMorphism K K)).obj A))) :=
  ((Rep.invariantsFunctor ℂ (B.OriginGroup E h2E)).mapIso
    ((forget₂ (FDRep ℂ (B.OriginGroup E h2E)) (Rep ℂ (B.OriginGroup E h2E))).mapIso
      (sourceCoefficientIso C U F nativeCompact B D X K E h2K h2E curvePullComparison A))).toLinearEquiv

@[simp] theorem sourceInvariantIso_val (A : C (affineLine K))
    (x : (OriginStalksFromStandardWeilInvariants.originStalks C U F nativeCompact B D K E h2E).fiber A) :
    (sourceInvariantIso C U F nativeCompact B D X K E h2K h2E curvePullComparison A x).val =
      ((sourceCoefficientIso C U F nativeCompact B D X K E h2K h2E curvePullComparison A).hom).hom.hom
        x.val := rfl

/-- The ALL-Weil source square follows from SAME standard naturality. -/
theorem sourceCoefficientIso_weil (A : C (affineLine K)) (w : (B.originWeil E h2E).Weil)
    (x : ((B.origin E h2E).obj
      ((D.curveRealization E h2E).obj ((U.pull (localInputMorphism K E)).obj A))).V) :
    (sourceCoefficientIso C U F nativeCompact B D X K E h2K h2E curvePullComparison A).hom.hom.hom
      ((B.originWeil E h2E).representation
        ((D.curveRealization E h2E).obj ((U.pull (localInputMorphism K E)).obj A)) w x) =
    (B.originWeil E h2E).representation ((X.curvePull K E h2K h2E).obj
      ((D.curveRealization K h2K).obj ((U.pull (localInputMorphism K K)).obj A))) w
      ((sourceCoefficientIso C U F nativeCompact B D X K E h2K h2E curvePullComparison A).hom.hom.hom x) :=
  (B.originWeil E h2E).natural
    ((sourceRealizationIso C U F nativeCompact B D X K E h2K h2E curvePullComparison).hom.app A) w x

theorem sourceInvariantIso_frobenius (A : C (affineLine K))
    (x : (OriginStalksFromStandardWeilInvariants.originStalks C U F nativeCompact B D K E h2E).fiber A) :
    sourceInvariantIso C U F nativeCompact B D X K E h2K h2E curvePullComparison A
      ((OriginStalksFromStandardWeilInvariants.originStalks C U F nativeCompact B D K E h2E).frobenius A x) =
    (invariantStalks (B.origin E h2E) (B.originConjugation E h2E) (B.originWeil E h2E)).frobenius
      ((X.curvePull K E h2K h2E).obj
        ((D.curveRealization K h2K).obj ((U.pull (localInputMorphism K K)).obj A)))
      (sourceInvariantIso C U F nativeCompact B D X K E h2K h2E curvePullComparison A x) := by
  apply Subtype.ext
  exact sourceCoefficientIso_weil C U F nativeCompact B D X K E h2K h2E curvePullComparison A
    (B.originWeil E h2E).frobenius x.val

/-- Output comparison for the exact computed original OriginStalks32. -/
def sourceInvariantComparison (A : C (affineLine K)) :
    (OriginStalksFromStandardWeilInvariants.originStalks C U F nativeCompact B D K E h2E).fiber A ≃ₗ[ℂ]
    (OriginStalksFromStandardWeilInvariants.originStalks C U F nativeCompact B D K K h2K).fiber A :=
  (sourceInvariantIso C U F nativeCompact B D X K E h2K h2E curvePullComparison A).trans
    (StandardFiniteConstantOrigin.invariantComparison published B X model K E h2K h2E
      ((D.curveRealization K h2K).obj ((U.pull (localInputMorphism K K)).obj A)))

/-- ALL affine-line ordinary objects, SAME E/K Algebra, no selected Fr law. -/
theorem source_frobenius_square (A : C (affineLine K))
    (x : (OriginStalksFromStandardWeilInvariants.originStalks C U F nativeCompact B D K E h2E).fiber A) :
    sourceInvariantComparison C U F nativeCompact B D X published model K E h2K h2E curvePullComparison A
      ((OriginStalksFromStandardWeilInvariants.originStalks C U F nativeCompact B D K E h2E).frobenius A x) =
    ((OriginStalksFromStandardWeilInvariants.originStalks C U F nativeCompact B D K K h2K).frobenius A ^
      Module.finrank K E)
      (sourceInvariantComparison C U F nativeCompact B D X published model K E h2K h2E curvePullComparison A x) := by
  change StandardFiniteConstantOrigin.invariantComparison published B X model K E h2K h2E
    ((D.curveRealization K h2K).obj ((U.pull (localInputMorphism K K)).obj A))
    (sourceInvariantIso C U F nativeCompact B D X K E h2K h2E curvePullComparison A
      ((OriginStalksFromStandardWeilInvariants.originStalks C U F nativeCompact B D K E h2E).frobenius A x)) = _
  rw [sourceInvariantIso_frobenius]
  exact StandardFiniteConstantOrigin.invariant_frobenius_square published B X model K E h2K h2E
    ((D.curveRealization K h2K).obj ((U.pull (localInputMorphism K K)).obj A))
    (sourceInvariantIso C U F nativeCompact B D X K E h2K h2E curvePullComparison A x)

/-- Change native common-group labels on both sides using the gated SAME-E
bridge. No identification of arbitrary retained groups or model is asserted. -/
def commonSourceComparison
    (originTrait : NativeCommonArithmeticTraitWeilCone.OriginTraitDictionary S B)
    (A : C (affineLine K)) :
    (OriginInvariantsSameFieldCommonConeBridge.commonOriginStalks.{g,nu,mu}
      C U F nativeCompact B D originTrait K E h2E).fiber A ≃ₗ[ℂ]
    (OriginInvariantsSameFieldCommonConeBridge.commonOriginStalks.{g,nu,mu}
      C U F nativeCompact B D originTrait K K h2K).fiber A :=
  (OriginInvariantsSameFieldCommonConeBridge.commonInvariantComparison.{g,nu,mu}
    C U F nativeCompact B D originTrait K E h2E A).trans
    ((sourceInvariantComparison C U F nativeCompact B D X published model K E h2K h2E
      curvePullComparison A).trans
      (OriginInvariantsSameFieldCommonConeBridge.commonInvariantComparison.{g,nu,mu}
        C U F nativeCompact B D originTrait K K h2K A).symm)

/-- Derived finite-extension power on exact computed native-common invariants.
Only the individual curve-operation MODEL and standard GENERAL inputs remain. -/
theorem commonSource_frobenius_square
    (originTrait : NativeCommonArithmeticTraitWeilCone.OriginTraitDictionary S B)
    (A : C (affineLine K))
    (x : (OriginInvariantsSameFieldCommonConeBridge.commonOriginStalks.{g,nu,mu}
      C U F nativeCompact B D originTrait K E h2E).fiber A) :
    commonSourceComparison C U F nativeCompact B D X published model K E h2K h2E
      curvePullComparison originTrait A
      ((OriginInvariantsSameFieldCommonConeBridge.commonOriginStalks
        C U F nativeCompact B D originTrait K E h2E).frobenius A x) =
    ((OriginInvariantsSameFieldCommonConeBridge.commonOriginStalks
      C U F nativeCompact B D originTrait K K h2K).frobenius A ^ Module.finrank K E)
      (commonSourceComparison C U F nativeCompact B D X published model K E h2K h2E
        curvePullComparison originTrait A x) := by
  let eK := OriginInvariantsSameFieldCommonConeBridge.commonInvariantComparison.{g,nu,mu}
    C U F nativeCompact B D originTrait K K h2K A
  have hpow (n : ℕ)
      (y : (OriginInvariantsSameFieldCommonConeBridge.commonOriginStalks.{g,nu,mu}
        C U F nativeCompact B D originTrait K K h2K).fiber A) :
      eK (((OriginInvariantsSameFieldCommonConeBridge.commonOriginStalks
        C U F nativeCompact B D originTrait K K h2K).frobenius A ^ n) y) =
      ((OriginStalksFromStandardWeilInvariants.originStalks
        C U F nativeCompact B D K K h2K).frobenius A ^ n) (eK y) := by
    induction n generalizing y with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ, pow_succ]
        change eK (((OriginInvariantsSameFieldCommonConeBridge.commonOriginStalks
          C U F nativeCompact B D originTrait K K h2K).frobenius A ^ n)
          ((OriginInvariantsSameFieldCommonConeBridge.commonOriginStalks
            C U F nativeCompact B D originTrait K K h2K).frobenius A y)) = _
        rw [ih, OriginInvariantsSameFieldCommonConeBridge.common_frobenius_square]
        rfl
  apply eK.injective
  simp only [commonSourceComparison, LinearEquiv.trans_apply]
  rw [hpow, LinearEquiv.apply_symm_apply]
  rw [OriginInvariantsSameFieldCommonConeBridge.common_frobenius_square]
  exact source_frobenius_square C U F nativeCompact B D X published model K E h2K h2E
    curvePullComparison A
    (OriginInvariantsSameFieldCommonConeBridge.commonInvariantComparison.{g,nu,mu}
      C U F nativeCompact B D originTrait K E h2E A x)
/-- The individual native operation MODEL family can be fixed before any
prime/source parameter: ALL finite K/E, SAME Algebra K E, and both original
h2 guards. Its data identify only constant pull and curve realization. -/
def UniversalCurveConstantPullRecognition :=
  ∀ (K E : Type) [Field K] [Field E] [Fintype K] [Fintype E] [Algebra K E]
    (h2K : (2 : K) ≠ 0) (h2E : (2 : E) ≠ 0),
    U.pull (OriginFiniteConstantInvariantFrobeniusTransport.constantExtensionMorphism K E) ⋙
      D.curveRealization E h2E ≅ D.curveRealization K h2K ⋙ X.curvePull K E h2K h2E

end PrimeGap182.TypeIII.OriginFiniteConstantFromCurveRealization
