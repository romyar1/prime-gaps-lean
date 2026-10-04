import TypeIIIPointTensorAndAutomorphismsFromUniversalWeilFibers
import TypeIIICanonicalOrdinaryDualEvaluation
import TypeIIIPointDualSpectrumFromEvaluation

/-!
# Source dual-stalk comparison from the general finite-lisse dual theorem

The linear comparison is COMPUTED by currying the actual monoidal stalk
image of the SAME closed source evaluation. The sole additional theorem is
bijectivity of this computed map for EVERY scheme, EVERY finite-field point
and EVERY globally lisse finite-rank coefficient object. This is the general
finite-locally-free internal-Hom/stalk theorem, not a selected source duality
record, Frobenius equation, spectral identity or purity premise.

Arithmetic/continuous-adic finite-rank lissity, internal-Hom and coefficient
realization remain explicit external model data. This application does not
construct them or the complete compatible Inputs family.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory TensorProduct
namespace PrimeGap182.TypeIII.SourcePointDualityFromGeneralLisseDualStalks
open ExactInverseImagesToDerived RationalPointStalksFromUniversalFiber
open CanonicalPrimeFramework CanonicalOrdinaryDualEvaluation
open QSTDualityBridgesFromSmoothLisseVerdier
open PointTensorAndAutomorphismsFromUniversalWeilFibers

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)]
  [∀ X, MonoidalCategory (C X)] [∀ X, MonoidalClosed (C X)] [∀ X, BraidedCategory (C X)]

/-- The actual closed evaluation, actual tensor comparison, and actual
unit comparison determine this linear map without a chosen dual equivalence. -/
def canonicalDualMap (X : Scheme) (T : C X ⥤ ModuleCat.{0} ℂ) [T.Monoidal] (A : C X) :
    T.obj ((ordinaryDual C X).obj (op A)) →ₗ[ℂ] Module.Dual ℂ (T.obj A) :=
  TensorProduct.curry ((Functor.Monoidal.εIso T).toLinearEquiv.symm.toLinearMap ∘ₗ
    (T.map (sourceEvaluate C X A)).hom ∘ₗ
    (Functor.Monoidal.μIso T ((ordinaryDual C X).obj (op A)) A).toLinearEquiv.toLinearMap)

variable [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (F : ArithmeticFibers C)
  [coefficientMonoidal : ∀ (E : Type) [Field E] [Fintype E], (F.fiber E).Monoidal]
  (L : ∀ X : Scheme, C X → Prop)
  (dualStalkBijective : ∀ (X : Scheme) (E : Type) [Field E] [Fintype E]
    (x : Spec (.of E) ⟶ X) (A : C X), L X A →
      Function.Bijective (canonicalDualMap C X (U.pull x ⋙ F.fiber E) A))

/-- The general finite-lisse theorem makes the computed comparison an equivalence. -/
def dualStalkEquiv (X : Scheme) (E : Type) [Field E] [Fintype E]
    (x : Spec (.of E) ⟶ X) (A : C X) (hA : L X A) :
    (U.pull x ⋙ F.fiber E).obj ((ordinaryDual C X).obj (op A)) ≃ₗ[ℂ]
      Module.Dual ℂ ((U.pull x ⋙ F.fiber E).obj A) :=
  LinearEquiv.ofBijective (canonicalDualMap C X (U.pull x ⋙ F.fiber E) A)
    (dualStalkBijective X E x A hA)

/-- Its pairing is definitionally the image of the exact original evaluation. -/
theorem dualStalkEquiv_evaluation (X : Scheme) (E : Type) [Field E] [Fintype E]
    (x : Spec (.of E) ⟶ X) (A : C X) (hA : L X A) u v :
    dualStalkEquiv C U F L dualStalkBijective X E x A hA u v =
      (Functor.Monoidal.εIso (U.pull x ⋙ F.fiber E)).toLinearEquiv.symm
        (((U.pull x ⋙ F.fiber E).map (sourceEvaluate C X A)).hom
          ((Functor.Monoidal.μIso (U.pull x ⋙ F.fiber E)
            ((ordinaryDual C X).obj (op A)) A).toLinearEquiv (u ⊗ₜ[ℂ] v))) := rfl

variable [coefficientFrobeniusMonoidal : ∀ (E : Type) [Field E] [Fintype E],
  NatTrans.IsMonoidal (F.frobenius E)]

/-- Exact original sourcePointDuality: no arithmetic or spectral comparison
is supplied; both fields come from the universal computed dual comparison. -/
def sourcePointDuality (p : ℕ) [Fact p.Prime] :
    PointDualSpectrumFromEvaluation.Comparison (pointStalks C U F p) (pointTensor C U F p)
      .source (sourceDualFunctor C U p) (sourceEvaluation C U p)
      (L (StartingSourceMaps.sourceScheme (ZMod p))) where
  equiv E _ _ _ x A hA := dualStalkEquiv C U F L dualStalkBijective _ E x A hA
  evaluation E _ _ _ x A hA u v :=
    dualStalkEquiv_evaluation C U F L dualStalkBijective _ E x A hA u v

end PrimeGap182.TypeIII.SourcePointDualityFromGeneralLisseDualStalks
