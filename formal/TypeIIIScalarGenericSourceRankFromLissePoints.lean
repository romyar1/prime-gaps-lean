import TypeIIIGenericSourceRanksFromActualFractionPoint
import TypeIIIScalarRankFromCommonFinitePoints

/-!
# Scalar generic source rank from general lisse point-rank constancy

One universal general comparison identifies SAME-G geometric point rank
with SAME-F finite arithmetic point rank for globally finite-rank lisse
objects on every integral scheme. No comparison is asserted for arbitrary
constructible objects. Actual source integrality and the already proved
scalar lissity give the comparison at the original source unit point.
The prior literal scalar rank application then computes the generic rank.
The original ALL-lisse Gm generic/finite-point rank law and actual source
maps are reused without a selected scalar rank premise.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.ScalarGenericSourceRankFromLissePoints
open ExactInverseImagesToDerived RationalPointStalksFromUniversalFiber
open PrimitiveRanksFromComputedGenericLineRank SourceRanksFromCommonFinitePoint
open GenericSourceRanksFromActualFractionPoint SourceGlobalLissityFromKatzPullbacks

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (F : ArithmeticFibers C)
  (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)
  (L : ∀ X : Scheme, ObjectProperty (C X))
  (lisseGeometricArithmeticPointRank : ∀ (X : Scheme) [IsIntegral X]
    (A : C X), L X A → ∀ (Eg : Type) [Field Eg] (xg : Spec (.of Eg) ⟶ X)
      (Ea : Type) [Field Ea] [Fintype Ea] (xa : Spec (.of Ea) ⟶ X),
      geometricPointRank C U G Eg X xg A = pointRank C U F Ea X xa A)

include lisseGeometricArithmeticPointRank in
/-- The generic source rank equals every finite point rank for globally lisse source objects. -/
theorem source_generic_rank_at_finite_point (K : Type) [Field K] [Fintype K]
    (A : C (StartingSourceMaps.sourceScheme K))
    (hA : L (StartingSourceMaps.sourceScheme K) A)
    (E : Type) [Field E] [Fintype E]
    (x : Spec (.of E) ⟶ StartingSourceMaps.sourceScheme K) :
    canonicalGenericSourceRank K C U G A = pointRank C U F E _ x A :=
  lisseGeometricArithmeticPointRank (StartingSourceMaps.sourceScheme K) A hA
    (GenericSourceField K) (genericSourcePoint K) E x

include lisseGeometricArithmeticPointRank in
/-- In the globally lisse domain, the old computed unit-point rank equals generic source rank. -/
theorem source_generic_rank_at_unit (K : Type) [Field K] [Fintype K]
    (A : C (StartingSourceMaps.sourceScheme K))
    (hA : L (StartingSourceMaps.sourceScheme K) A) :
    canonicalGenericSourceRank K C U G A = canonicalSourceRank C U F K A :=
  source_generic_rank_at_finite_point C U F G L lisseGeometricArithmeticPointRank K A hA K
    (RationalPointStalks.curvePoint (K := K) (L := K) 1 1 1)

local instance allLocalizations : ∀ X : Scheme, HasDerivedCategory.{mu} (C X) :=
  fun _ => HasDerivedCategory.standard _

variable [∀ X, (L X).IsClosedUnderIsomorphisms]
  (lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y), L Y A → L X ((U.pull f).obj A))
  (lisseGenericPointRank : ∀ (K : Type) [Field K] [Fintype K]
    (A : C (ArithmeticSourceMaps.fiberScheme K)), L (ArithmeticSourceMaps.fiberScheme K) A →
    ∀ (E : Type) [Field E] [Fintype E] [Algebra K E] (x : Eˣ),
      Module.finrank ℂ ((QSTGenericFiberFromActualGenericPoint.rawGenericFiber K C U G).obj
        ((QSTCompactBridgeFromCompactifiedDerivedPushforward.boundedDegreeZero C _).obj A)) =
      Module.finrank ℂ ((F.fiber E).obj
        ((U.pull (PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.gmPoint K E x)).obj A)))

include lisseGeometricArithmeticPointRank lissePull lisseGenericPointRank in
/-- The actual scalar pullback has the computed generic line rank, under its original global lissity guard. -/
theorem scalar_rank (K : Type) [Field K] [Fintype K]
    (c : (PhysicalTorusMorphism.TorusRing K)ˣ)
    (A : C (StartingSourceMaps.affineLine K))
    (hA : lineLisseOnUnits K C U L A) :
    canonicalGenericSourceRank K C U G ((U.pull (CanonicalCurveInput.scalarMorphism K c)).obj A) =
      canonicalLineRank C U G K A := by
  exact (source_generic_rank_at_unit C U F G L lisseGeometricArithmeticPointRank K _
    (scalar_lisse K C U L lissePull c A hA)).trans
      (ScalarRankFromCommonFinitePoints.scalar_rank C U F G L lisseGenericPointRank K c A hA)

end PrimeGap182.TypeIII.ScalarGenericSourceRankFromLissePoints
