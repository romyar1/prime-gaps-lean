import TypeIIICoherentNormalizedFourierCompactInfinity03
import TypeIIIGeneralFuPrimitiveInfinityApplication03
import TypeIIIMiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology

/-!
# Normalized infinity uses the literal ordinary open restriction

Fix ONE ordinary inverse-image system, actual ordinary open adjoints and
local realization before any prime or selected primitive. Generic infinity
is the SAME local functor and fixed coefficient transport as the GENERAL
Fu primitive application. The ordinary affine infinity role is DEFINED as
actual Gm restriction followed by that functor.

The open comparison is COMPUTED from the actual adjoint triple and the
open restriction-unit isomorphism. No ALL-object open-comparison callback,
selected j-star recognition, finished correlation comparison, or independent
infinity observer is an input. GENERAL derived generic-degree-minus-one and
punctual quotient laws construct the normalized fiber rules; their meaning
is on ONE genuine smooth-curve theory. Neither normalization nor j-star nor
intermediate extension is asserted exact. No Lean execution or TypeIII
completion is claimed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.NormalizedInfinityFromLiteralOpenAdjunction01
open ExactInverseImagesToDerived PrimitiveRamificationFromGeneralKatzTheory
open PublishedLocalConstruction PublishedPhaseApplication CanonicalLocalCorrelation
open CoherentNormalizedFourierCompactInfinity03

universe mu pv ph dv dh
variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)]
  [∀ X, Abelian (C X)] [∀ X, MonoidalCategory (C X)]
  [∀ X, MonoidalClosed (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (F : OrdinaryOpenExtensionsFromAdjunctions.OrdinaryOpenFamily C U)
  (M : LocalRealization C)
  [∀ (E : Type) [Field E], (M.infinity E).Monoidal]
  (K : Type) [Field K] (h2 : (2 : PhaseField K) ≠ 0)

/-- SAME generic infinity as the all-rank Fu primitive construction. -/
def actualInfinity : C (ArithmeticSourceMaps.fiberScheme (PhaseField K)) ⥤
    FDRep ℂ (M.infinityGroup (PhaseField K)) :=
  GeneralFuPrimitiveInfinityApplication03.infinityObserver (C := C) (M := M) (PhaseField K)

instance actualInfinityMonoidal : (actualInfinity C M K).Monoidal :=
  inferInstanceAs (M.infinity (PhaseField K) ⋙
    (FiniteRepresentationCoefficientTransport.coefficientEquivalence
      TwoAdicComplexEmbedding.complexEquiv (M.infinityGroup (PhaseField K))).functor).Monoidal

/-- Actual ordinary j-star, given by the SAME right adjoint to U.pull. -/
def actualJStar : C (FourierSourceMaps.localScheme K) ⥤
    C (StartingSourceMaps.affineLine (PhaseField K)) :=
  F.push (PhaseField K) h2
    (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.gmPresentation (PhaseField K))
    (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.linePresentation (PhaseField K))
    (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K)) rfl

/-- The ordinary affine infinity role is literal open inverse image. -/
def actualOrdinaryInfinity : C (StartingSourceMaps.affineLine (PhaseField K)) ⥤
    FDRep ℂ (M.infinityGroup (PhaseField K)) :=
  U.pull (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K)) ⋙
    actualInfinity C M K

include F h2 in
/-- Restriction of actual ordinary j-star follows from the adjoint triple,
then the SAME generic infinity functor is applied. This is a whole natural
comparison on ALL ordinary inputs, not a selected correlation isomorphism. -/
def actualJStarInfinityIso :
    actualJStar C U F K h2 ⋙ actualOrdinaryInfinity C U M K ≅ actualInfinity C M K :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.pushRestrictionIso
        C U F (PhaseField K) h2
        (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.gmPresentation (PhaseField K))
        (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.linePresentation (PhaseField K))
        (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K)) rfl)
      (actualInfinity C M K) ≪≫ Functor.leftUnitor _

/-- Scalar and dual are actual ordinary operations; the middle role is
literal ordinary j-star. Its subsequent perverse normalization is separate. -/
def actualLocalOperations : SheafOperations (PhaseField K)
    (C (FourierSourceMaps.localScheme K))
    (C (StartingSourceMaps.affineLine (PhaseField K))) where
  scalar lambda := U.pull (FourierSourceMaps.scalarMorphism K lambda)
  scalar_one := eqToIso (congrArg (fun f => U.pull f) (FourierSourceMaps.scalarMorphism_one K)) ≪≫
    U.identity (FourierSourceMaps.localScheme K)
  dual A := (QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C
    (FourierSourceMaps.localScheme K)).obj (Opposite.op A)
  middleExtension := actualJStar C U F K h2

variable {Perv : Type pv} [Category.{ph} Perv]
  {Derived : Type dv} [Category.{dh} Derived]
  {LF : LocalFourierData K ℂ (M.infinityGroup (PhaseField K)) (M.originGroup (PhaseField K))}
  (underlying : Perv ⥤ Derived)
  (N : CurveNormalizationOperations (Ord := C (StartingSourceMaps.affineLine (PhaseField K))) underlying)
  (S : StandardFiniteOriginOperations (LF := LF) underlying)

/-- GENERAL derived Fourier fiber and punctual-torsion clauses on the
literal ordinary infinity operation. Every clause concerns ALL ordinary
inputs; the compact functor is the SAME degree-one Fourier-kernel recipe
when interpreted in the genuine theory. No correlation rank/profile or
Fourier bound is asserted. -/
structure GeneralLiteralFiberClauses where
  compactDegreeOne : (s : PhaseField K) → s ≠ 0 →
    C (StartingSourceMaps.affineLine (PhaseField K)) ⥤ FDRep ℂ (M.originGroup (PhaseField K))
  fourierFiber : ∀ (s : PhaseField K) (hs : s ≠ 0),
    (N.shiftOne ⋙ S.radialFourier s hs) ⋙ S.originGenericMinusOne ≅ compactDegreeOne s hs
  compactQuotientIsIso : ∀ (s : PhaseField K) (hs : s ≠ 0) A,
    IsIso ((compactDegreeOne s hs).map (N.quotientMap.app A))
  infinityFiber : N.shiftOne ⋙ S.infinityGenericMinusOne ≅ actualOrdinaryInfinity C U M K
  infinityQuotientIsIso : ∀ A,
    IsIso ((actualOrdinaryInfinity C U M K).map (N.quotientMap.app A))

variable (laws : GeneralLiteralFiberClauses C U M K underlying N S)

/-- The original normalized rules are constructed with literal infinity. -/
def computedFiberRules : GeneralCurveFiberRules N S where
  compactDegreeOne := laws.compactDegreeOne
  ordinaryInfinity := actualOrdinaryInfinity C U M K
  fourierFiber := laws.fourierFiber
  compactQuotientIsIso := laws.compactQuotientIsIso
  infinityFiber := laws.infinityFiber
  infinityQuotientIsIso := laws.infinityQuotientIsIso

variable (dualGenericInfinity : ∀ A : C (FourierSourceMaps.localScheme K),
  Representation.Equiv
    ((actualInfinity C M K).obj
      ((QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C
        (FourierSourceMaps.localScheme K)).obj (Opposite.op A))).ρ
    (dualRepresentation ((actualInfinity C M K).obj A)).ρ)

include F h2 dualGenericInfinity in
/-- IRinf is now derived from computed normalization and literal open
restriction. The remaining dual clause is the GENERAL finite generic
stalk/internal-dual law, uniformly on ALL ordinary constructible inputs. -/
def computedInfinityCompatibility :
    InfinityCompatibility (actualLocalOperations C U F K h2) (actualInfinity C M K)
      (normalizedData N S) :=
  normalizedInfinityCompatibility N S (computedFiberRules C U M K underlying N S laws)
    (actualLocalOperations C U F K h2) (actualInfinity C M K) dualGenericInfinity
    (fun A => (actualJStarInfinityIso C U F M K h2).app A)

end PrimeGap182.TypeIII.NormalizedInfinityFromLiteralOpenAdjunction01
#print axioms PrimeGap182.TypeIII.NormalizedInfinityFromLiteralOpenAdjunction01.actualJStarInfinityIso
#print axioms PrimeGap182.TypeIII.NormalizedInfinityFromLiteralOpenAdjunction01.computedFiberRules
#print axioms PrimeGap182.TypeIII.NormalizedInfinityFromLiteralOpenAdjunction01.computedInfinityCompatibility
