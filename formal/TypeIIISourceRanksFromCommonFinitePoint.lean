import TypeIIISourcePointDualityFromGeneralLisseDualStalks
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Source tensor and dual ranks from the common actual finite point

Source rank is DEFINED as the dimension of SAME U/F at the original source
unit point (1,1,1), over EVERY finite base field. For globally lisse objects
on the connected source torus this is the usual rank. No arbitrary source
rank, rank-recognition dictionary or selected tensor/dual rank is a premise.

Actual strong monoidal comparison and finite-dimensional tensor-product
dimension prove tensor rank at EVERY finite point of EVERY scheme. The
already general bijectivity theorem for the COMPUTED lisse dual map, and
actual finite-dimensional dual dimension, prove dual rank at every such
point. Both source laws are applications to the SAME chosen unit point.
No new published theorem or coefficient Frobenius law is introduced.
The actual continuous constructible interpretation of the coefficient
categories, fibers and lissity remains external general framework data.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory TensorProduct

namespace PrimeGap182.TypeIII.SourceRanksFromCommonFinitePoint
open ExactInverseImagesToDerived RationalPointStalksFromUniversalFiber
open QSTDualityBridgesFromSmoothLisseVerdier SourcePointDualityFromGeneralLisseDualStalks

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (F : ArithmeticFibers C)

/-- Dimension of the actual ordinary coefficient point fiber. -/
def pointRank (E : Type) [Field E] [Fintype E] (X : Scheme)
    (x : Spec (.of E) ⟶ X) (A : C X) : ℕ :=
  Module.finrank ℂ ((U.pull x ⋙ F.fiber E).obj A)

/-- Source rank is a computed dimension at the original unit source point. -/
def canonicalSourceRank (K : Type) [Field K] [Fintype K]
    (A : C (StartingSourceMaps.sourceScheme K)) : ℕ :=
  pointRank C U F K _ (RationalPointStalks.curvePoint (K := K) (L := K) 1 1 1) A

/-- Isomorphic ordinary objects have equal computed ranks at every point. -/
theorem pointRank_iso (E : Type) [Field E] [Fintype E] (X : Scheme)
    (x : Spec (.of E) ⟶ X) {A B : C X} (e : A ≅ B) :
    pointRank C U F E X x A = pointRank C U F E X x B :=
  ((U.pull x ⋙ F.fiber E).mapIso e).toLinearEquiv.finrank_eq

variable [∀ X, MonoidalCategory (C X)]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  [coefficientMonoidal : ∀ (E : Type) [Field E] [Fintype E], (F.fiber E).Monoidal]

/-- Every actual monoidal finite point has multiplicative tensor rank. -/
theorem pointRank_tensor (E : Type) [Field E] [Fintype E] (X : Scheme)
    (x : Spec (.of E) ⟶ X) (A B : C X) :
    pointRank C U F E X x (A ⊗ B) =
      pointRank C U F E X x A * pointRank C U F E X x B := by
  let : FiniteDimensional ℂ ((U.pull x ⋙ F.fiber E).obj A) := F.finite E ((U.pull x).obj A)
  let : FiniteDimensional ℂ ((U.pull x ⋙ F.fiber E).obj B) := F.finite E ((U.pull x).obj B)
  exact (Functor.Monoidal.μIso (U.pull x ⋙ F.fiber E) A B).toLinearEquiv.finrank_eq.symm.trans
    Module.finrank_tensorProduct

/-- The computed source rank satisfies the original tensor rank law. -/
theorem source_tensor_rank (K : Type) [Field K] [Fintype K]
    (A B : C (StartingSourceMaps.sourceScheme K)) :
    canonicalSourceRank C U F K (A ⊗ B) =
      canonicalSourceRank C U F K A * canonicalSourceRank C U F K B :=
  pointRank_tensor C U F K _ (RationalPointStalks.curvePoint (K := K) (L := K) 1 1 1) A B

variable [∀ X, MonoidalClosed (C X)] [∀ X, BraidedCategory (C X)]
  (L : ∀ X : Scheme, C X → Prop)
  (dualStalkBijective : ∀ (X : Scheme) (E : Type) [Field E] [Fintype E]
    (x : Spec (.of E) ⟶ X) (A : C X), L X A →
      Function.Bijective (canonicalDualMap C X (U.pull x ⋙ F.fiber E) A))

include dualStalkBijective in
/-- Every finite-rank lisse dual has the same actual point dimension. -/
theorem pointRank_dual (E : Type) [Field E] [Fintype E] (X : Scheme)
    (x : Spec (.of E) ⟶ X) (A : C X) (hA : L X A) :
    pointRank C U F E X x ((ordinaryDual C X).obj (Opposite.op A)) =
      pointRank C U F E X x A := by
  let : FiniteDimensional ℂ ((U.pull x ⋙ F.fiber E).obj A) := F.finite E ((U.pull x).obj A)
  exact (dualStalkEquiv C U F L dualStalkBijective X E x A hA).finrank_eq.trans
    Subspace.dual_finrank_eq

include dualStalkBijective in
/-- The original ordinary source dual preserves the computed source rank. -/
theorem source_dual_rank (K : Type) [Field K] [Fintype K]
    (A : C (StartingSourceMaps.sourceScheme K))
    (hA : L (StartingSourceMaps.sourceScheme K) A) :
    canonicalSourceRank C U F K
      ((ordinaryDual C (StartingSourceMaps.sourceScheme K)).obj (Opposite.op A)) =
      canonicalSourceRank C U F K A :=
  pointRank_dual C U F L dualStalkBijective K _
    (RationalPointStalks.curvePoint (K := K) (L := K) 1 1 1) A hA

end PrimeGap182.TypeIII.SourceRanksFromCommonFinitePoint
