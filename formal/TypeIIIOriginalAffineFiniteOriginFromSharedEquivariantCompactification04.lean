import TypeIIIOriginalAffineKernelFromPublishedOpenCompact03
import TypeIIIEquivariantCompactification
import TypeIIICurveDataFromOperations

/-!
# Literal affine diagram and derived finite-origin inertia comparison

Define the relative affine object by the computed ordinary j-star compact
recipe. General projective/localization maps construct the old M on that
literal object. Its RM and RI are derived from the same FDRep-valued maps.
The normalized original-coordinate iso supplies BC and BI automatically.
No independent M, FC, RM, RI, BI or completed family comparison is supplied.

The same genuine curve observations, boundary Z, projective operations,
guarded localization clauses, standard normalized Fourier laws and adic
interpretation remain external. No model existence or Type III endpoint
completion is asserted. This source has not been executed in Lean.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.OriginalAffineFiniteOriginFromSharedEquivariantCompactification04

open PublishedPhaseApplication GenericSourceSpecialization FourierSourceMaps
open GenericRelativeAffineLineCoordinates RelativeAffineFourierKernelFromActualCoordinates
open OrdinaryOpenExtensionsFromAdjunctions QSTCompactBridgeFromCompactifiedDerivedPushforward
open OrdinaryFourierKernelExtensionFromGeneralSmoothBaseChange
open CoherentGeneralOpenCompactKernelApplication01
open CoherentNormalizedFourierCompactInfinity03 OriginalAffineKernelFromPublishedOpenCompact03
open PublishedPhysicalConstruction BoundaryFromSourceModels MiddleFromLocalization
open FourierStalkFromSources FourierStalkInertia CanonicalLocalCorrelation

universe mu u v w z a b d e
variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)]
  [∀ X, Abelian (C X)] [∀ X, MonoidalCategory (C X)]
  (U : ExactInverseImagesToDerived.OrdinarySystem (fun X : Scheme => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (O : Operations C) (F : OrdinaryOpenFamily C U)
  (lisse : ∀ X : Scheme, ObjectProperty (C X))
  (smoothOpen : UniversalSmoothOpenBaseChange C U F)
  (lisseProjection : UniversalLisseOpenProjection C U F lisse)
  (lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y),
    lisse Y A → lisse X ((U.pull f).obj A))
  (compactBaseChange : UniversalCompactBaseChange C U O)

variable (K : Type) [Field K] (h2 : (2 : PhaseField K) ≠ 0)
  (c : Compactification (relativeProjection K))
  {Point : Type u} (Obs : CurveDataFromOperations.Observables (C (genericScheme K)) Point)
  (dualGeneric : (C (genericScheme K))ᵒᵖ ⥤ C (genericScheme K))
  {Outer : Type mu} [Group Outer]
  {H : CohomologyData (C (genericScheme K)) (C (GenericCurvePullback.parameterScheme K))}
  (observer : C (GenericCurvePullback.parameterScheme K) ⥤ FDRep ℂ Outer)
  {BS : BoundarySequence (Obs.curveData dualGeneric) H (observer ⋙ forgetInertia Outer)}
  {G0 : Type d} [Group G0] {Ginf : Type e} [Group Ginf]
  (Z : RestrictionData (G0 := G0) (Ginf := Ginf)
    (Obs.curveData dualGeneric) H (observer ⋙ forgetInertia Outer) BS)

/- These are the SAME projective cohomology and individual ALL-object
canonical maps. Their genuine standard-operation interpretation is
explicit; no independently selected affine cohomology is accepted. -/
variable
  (projective : C (genericScheme K) ⥤ FDRep ℂ Outer)
  (fromCompact : ∀ A, observer.obj (H.compact A) ⟶
    (observedAffineFunctor C U O F K h2 c observer).obj A)
  (toProjective : observedAffineFunctor C U O F K h2 c observer ⟶ projective)
  (leray : ∀ A, projective.obj A ⟶ observer.obj (H.ordinary A))
  (fromInfinity : ∀ A, invariantModule (Z.infinity A) ⟶
    (observedAffineFunctor C U O F K h2 c observer ⋙ forgetInertia Outer).obj A)

include projective fromCompact toProjective leray fromInfinity

/-- The affine role is literally the computed ordinary j-star compact
recipe. Every comparison map is retained before forgetting inertia. -/
def sharedDiagram : EquivariantCompactification.Data observer Z where
  affine := observedAffineFunctor C U O F K h2 c observer
  projective := projective
  fromCompact := fromCompact
  toProjective := toProjective
  leray := leray
  fromInfinity := fromInfinity

/-- Construct M, rather than supply an independently chosen M.affine. -/
def computedCompactification : CompactificationData Z :=
  (sharedDiagram C U O F K h2 c Obs dualGeneric observer Z
    projective fromCompact toProjective leray fromInfinity).compactification

/-- Construct RM from the SAME affine representation-valued functor. -/
def computedAffineInertia : FunctorInertia
    (computedCompactification C U O F K h2 c Obs dualGeneric observer Z
      projective fromCompact toProjective leray fromInfinity).affine Outer :=
  (sharedDiagram C U O F K h2 c Obs dualGeneric observer Z
    projective fromCompact toProjective leray fromInfinity).inertia

omit [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal] in
/-- The old RI is equivariance of the original morphism of FDRep objects. -/
theorem computedLocalizationInertia : LocalizationInertia Z
    (computedCompactification C U O F K h2 c Obs dualGeneric observer Z
      projective fromCompact toProjective leray fromInfinity)
    (FunctorInertia.ofFDRepFunctor observer)
    (computedAffineInertia C U O F K h2 c Obs dualGeneric observer Z
      projective fromCompact toProjective leray fromInfinity) :=
  (sharedDiagram C U O F K h2 c Obs dualGeneric observer Z
    projective fromCompact toProjective leray fromInfinity).localizationInertia

section GeneralLocalization

variable
  (comparison : ∀ A, Obs.Lisse A →
    (forgetInertia Outer).map (fromCompact A) ≫
      (forgetInertia Outer).map (toProjective.app A) ≫
      (forgetInertia Outer).map (leray A) =
        (observer ⋙ forgetInertia Outer).map (H.comparison A))
  (zeroLocalization : ∀ A, Obs.Lisse A →
    LinearMap.range ((forgetInertia Outer).map (fromCompact A)).hom = ⊤)
  (infinityLocalization : ∀ A, Obs.Lisse A →
    LinearMap.range (fromInfinity A).hom =
      LinearMap.ker ((forgetInertia Outer).map (toProjective.app A)).hom)
  (lerayInjective : ∀ A, Obs.Lisse A →
    Function.Injective ((forgetInertia Outer).map (leray A)).hom)

include comparison zeroLocalization infinityLocalization lerayInjective

omit [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal] in
/-- Apply GENERAL localization/Leray on those SAME canonical maps.
The outgoing geometric-point H1 map is already zero by its definition. -/
theorem computedCompactificationRules : CompactificationRules Z
    (computedCompactification C U O F K h2 c Obs dualGeneric observer Z
      projective fromCompact toProjective leray fromInfinity) where
  comparison A hA := comparison A hA
  zero_exact A hA := by
    change LinearMap.range ((forgetInertia Outer).map (fromCompact A)).hom =
      LinearMap.ker (0 : _ →ₗ[ℂ] _)
    rw [LinearMap.ker_zero]
    exact zeroLocalization A hA
  infinity_exact A hA := infinityLocalization A hA
  leray_injective A hA := lerayInjective A hA

end GeneralLocalization

section LiteralLocalOperations
omit projective fromCompact toProjective leray fromInfinity

/-- The ordinary local operation record is defined from actual scalar
inverse images and actual ordinary j-star, before any Kl input is chosen. -/
def literalLocalOperations (dualLocal : C (localScheme K) → C (localScheme K)) :
    SheafOperations (PhaseField K) (C (localScheme K))
      (C (StartingSourceMaps.affineLine (PhaseField K))) where
  scalar lambda := U.pull (scalarMorphism K lambda)
  scalar_one := eqToIso (congrArg (fun f => U.pull f) (scalarMorphism_one K)) ≪≫
    U.identity (localScheme K)
  dual := dualLocal
  middleExtension := F.push (PhaseField K) h2
    (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.gmPresentation (PhaseField K))
    (MiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology.linePresentation (PhaseField K))
    (ArithmeticSourceMaps.localInputMorphism (PhaseField K) (PhaseField K)) rfl

end LiteralLocalOperations

section ComputedFourierComparison
omit projective fromCompact toProjective leray fromInfinity

variable {Perv : Type v} [Category.{w} Perv]
  {Derived : Type z} [Category.{a} Derived]
  {I : Type b} [Group I]
  {LF : PublishedLocalConstruction.LocalFourierData K ℂ I Outer}
  (underlying : Perv ⥤ Derived)
  (N : CurveNormalizationOperations
    (Ord := C (StartingSourceMaps.affineLine (PhaseField K))) underlying)
  (S : StandardFiniteOriginOperations (LF := LF) underlying)
  (as : C (StartingSourceMaps.affineLine K))
  (hAS : lisse (StartingSourceMaps.affineLine K) as)
  (R : ObservedFourierCurveRules C U O K c underlying N S as)
  (dualLocal : C (localScheme K) → C (localScheme K))
  {BS' : BoundarySequence (Obs.curveData dualGeneric) H
    (R.radialObserver ⋙ forgetInertia Outer)}
  (Z' : RestrictionData (G0 := G0) (Ginf := Ginf)
    (Obs.curveData dualGeneric) H (R.radialObserver ⋙ forgetInertia Outer) BS')
  (projective' : C (genericScheme K) ⥤ FDRep ℂ Outer)
  (fromCompact' : ∀ A, R.radialObserver.obj (H.compact A) ⟶
    (observedAffineFunctor C U O F K h2 c R.radialObserver).obj A)
  (toProjective' : observedAffineFunctor C U O F K h2 c R.radialObserver ⟶ projective')
  (leray' : ∀ A, projective'.obj A ⟶ R.radialObserver.obj (H.ordinary A))
  (fromInfinity' : ∀ A, invariantModule (Z'.infinity A) ⟶
    (observedAffineFunctor C U O F K h2 c R.radialObserver ⋙ forgetInertia Outer).obj A)

include smoothOpen lisseProjection lissePull compactBaseChange
  projective' fromCompact' toProjective' leray' fromInfinity'

/-- The old BC is an output of the normalized original-coordinate FDRep
comparison. Its additive object is the literal source map AS(T^2*x/s). -/
def computedFourierBaseChange : FourierBaseChange Z'
    (computedCompactification C U O F K h2 c Obs dualGeneric R.radialObserver Z'
      projective' fromCompact' toProjective' leray' fromInfinity')
    (literalLocalOperations C U F K h2 dualLocal)
    (U.pull (projectionMorphism K)) (normalizedData N S) where
  additive s hs := (U.pull (additiveMorphism K (Units.mk0 s hs))).obj as
  comparison s hs A :=
    (normalizedOriginToLiteralASAffineEquiv C U O F lisse smoothOpen lisseProjection lissePull
      compactBaseChange K h2 c underlying N S as hAS R s hs A).toLinearEquiv

/-- Inertia compatibility is derived from that SAME equivariant map,
instead of being supplied separately for the finished BC. -/
theorem computedFourierInertia : FourierInertia Z'
    (computedCompactification C U O F K h2 c Obs dualGeneric R.radialObserver Z'
      projective' fromCompact' toProjective' leray' fromInfinity')
    (computedAffineInertia C U O F K h2 c Obs dualGeneric R.radialObserver Z'
      projective' fromCompact' toProjective' leray' fromInfinity')
    (literalLocalOperations C U F K h2 dualLocal) (U.pull (projectionMorphism K))
    (normalizedData N S)
    (computedFourierBaseChange C U O F lisse smoothOpen lisseProjection lissePull
      compactBaseChange K h2 c Obs dualGeneric underlying N S as hAS R dualLocal Z'
      projective' fromCompact' toProjective' leray' fromInfinity') where
  natural s hs A t :=
    (normalizedOriginToLiteralASAffineEquiv C U O F lisse smoothOpen lisseProjection lissePull
      compactBaseChange K h2 c underlying N S as hAS R s hs A).isIntertwining' t

end ComputedFourierComparison


end PrimeGap182.TypeIII.OriginalAffineFiniteOriginFromSharedEquivariantCompactification04

#print axioms PrimeGap182.TypeIII.OriginalAffineFiniteOriginFromSharedEquivariantCompactification04.sharedDiagram
#print axioms PrimeGap182.TypeIII.OriginalAffineFiniteOriginFromSharedEquivariantCompactification04.computedCompactification
#print axioms PrimeGap182.TypeIII.OriginalAffineFiniteOriginFromSharedEquivariantCompactification04.computedAffineInertia
#print axioms PrimeGap182.TypeIII.OriginalAffineFiniteOriginFromSharedEquivariantCompactification04.computedLocalizationInertia
#print axioms PrimeGap182.TypeIII.OriginalAffineFiniteOriginFromSharedEquivariantCompactification04.computedCompactificationRules

#print axioms PrimeGap182.TypeIII.OriginalAffineFiniteOriginFromSharedEquivariantCompactification04.literalLocalOperations
#print axioms PrimeGap182.TypeIII.OriginalAffineFiniteOriginFromSharedEquivariantCompactification04.computedFourierBaseChange
#print axioms PrimeGap182.TypeIII.OriginalAffineFiniteOriginFromSharedEquivariantCompactification04.computedFourierInertia
