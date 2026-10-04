import TypeIIIPrimitiveRanksFromComputedGenericLineRank
import TypeIIISourceRanksFromCommonFinitePoint
import TypeIIIScalarSourcePointCoordinates

/-!
# Scalar pullback rank from the common finite point and generic line fiber

The existing ALL-lisse Gm generic/arithmetic-point rank comparison is
applied to the actual line restriction. SAME-U composition and the literal
native Gm point factorization transport its rank to the original line point.
No selected primitive rank or chosen rank observable is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.ScalarRankFromCommonFinitePoints
open ExactInverseImagesToDerived QSTCompactBridgeFromCompactifiedDerivedPushforward
open QSTGenericFiberFromActualGenericPoint PrimitiveRanksFromComputedGenericLineRank
open RationalPointStalksFromUniversalFiber PrimitiveTracesFromGeneralKatzArtinSchreierFormulas
open SourceRanksFromCommonFinitePoint
open ScalarSourcePointCoordinates

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (F : ArithmeticFibers C)
  (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)
  (L : ∀ X : Scheme, ObjectProperty (C X))
local instance allLocalizations : ∀ X : Scheme, HasDerivedCategory.{mu} (C X) :=
  fun _ => HasDerivedCategory.standard _

variable (lisseGenericPointRank : ∀ (K : Type) [Field K] [Fintype K]
    (A : C (ArithmeticSourceMaps.fiberScheme K)), L (ArithmeticSourceMaps.fiberScheme K) A →
    ∀ (E : Type) [Field E] [Fintype E] [Algebra K E] (x : Eˣ),
      Module.finrank ℂ ((rawGenericFiber K C U G).obj ((boundedDegreeZero C _).obj A)) =
      Module.finrank ℂ ((F.fiber E).obj ((U.pull (gmPoint K E x)).obj A)))

include lisseGenericPointRank in
/-- Every finite unit line point has the computed rank of a globally lisse Gm restriction. -/
theorem line_rank_at_point (K : Type) [Field K] [Fintype K]
    (A : C (StartingSourceMaps.affineLine K))
    (hA : SourceGlobalLissityFromKatzPullbacks.lineLisseOnUnits K C U L A)
    (E : Type) [Field E] [Fintype E] [Algebra K E] (u : Eˣ) :
    canonicalLineRank C U G K A = pointRank C U F E _
      (RationalPointStalks.linePoint (K := K) (u : E)) A := by
  let e := (U.composition (gmPoint K E u) (ArithmeticSourceMaps.localInputMorphism K K)).app A
  have hi := ((F.fiber E).mapIso e).toLinearEquiv.finrank_eq
  rw [gmPoint_comp] at hi
  exact (lisseGenericPointRank K _ hA E u).trans hi

include lisseGenericPointRank in
/-- Every actual scalar pullback of a globally lisse unit-line restriction
has the same computed source rank, for every finite field and parameter unit. -/
theorem scalar_rank (K : Type) [Field K] [Fintype K]
    (c : (PhysicalTorusMorphism.TorusRing K)ˣ)
    (A : C (StartingSourceMaps.affineLine K))
    (hA : SourceGlobalLissityFromKatzPullbacks.lineLisseOnUnits K C U L A) :
    canonicalSourceRank C U F K ((U.pull (CanonicalCurveInput.scalarMorphism K c)).obj A) =
      canonicalLineRank C U G K A := by
  let u : Kˣ :=
    Units.map (PhysicalTorusMorphism.evaluation (K := K) (1 : Kˣ) 1).toRingHom c
  let e := (U.composition (RationalPointStalks.curvePoint (K := K) (L := K) 1 1 1)
    (CanonicalCurveInput.scalarMorphism K c)).app A
  have hi := ((F.fiber K).mapIso e).toLinearEquiv.finrank_eq
  rw [curvePoint_one_scalarMorphism] at hi
  exact hi.trans (line_rank_at_point C U F G L lisseGenericPointRank K A hA K u).symm

end PrimeGap182.TypeIII.ScalarRankFromCommonFinitePoints
