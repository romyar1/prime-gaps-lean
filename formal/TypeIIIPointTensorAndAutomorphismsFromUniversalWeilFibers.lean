import TypeIIIRationalPointStalksFromUniversalFiber
import TypeIIIPointTraceFromTensor
import TypeIIIImageWeightsFromCompact
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Point tensor and Frobenius invertibility from SAME universal Weil fibers

Only universal coefficient-fiber monoidality, monoidality of its actual
Frobenius transformation and invertibility of that transformation are
parameters before a prime. SAME actual ordinary inverse images compute
point fibers, so monoidal whiskering and actual component invertibility
construct the two original point fields. No finished ALLpoint law/Inputs
record, new mathematical axiom, purity theorem or trace formula is supplied.
The continuous-adic/Weil interpretation remains explicit external data.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory TensorProduct
namespace PrimeGap182.TypeIII.PointTensorAndAutomorphismsFromUniversalWeilFibers
open ExactInverseImagesToDerived RationalPointStalksFromUniversalFiber

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  [∀ X, MonoidalCategory (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (F : ArithmeticFibers C)
  [coefficientMonoidal : ∀ (E : Type) [Field E] [Fintype E], (F.fiber E).Monoidal]
  [coefficientFrobeniusMonoidal : ∀ (E : Type) [Field E] [Fintype E],
    NatTrans.IsMonoidal (F.frobenius E)]
  [coefficientFrobeniusIso : ∀ (E : Type) [Field E] [Fintype E], IsIso (F.frobenius E)]

/-- Actual SAME-U point fibers are monoidal and their SAME-F Frobenius
preserves the tensor/unit structure by natural monoidal whiskering. -/
def pointTensor (p : ℕ) [Fact p.Prime] : PointTraceFromTensor.Laws (pointStalks C U F p) where
  monoidal E _ _ _ X x := by
    change (U.pull x ⋙ F.fiber E).Monoidal
    infer_instance
  tensor E _ _ _ X x A B v := by
    let τ := (U.pull x).whiskerLeft (F.frobenius E)
    have h := NatTrans.IsMonoidal.tensor (τ := τ) A B
    exact (congrArg (fun m => m.hom v) h).symm
  unit E _ _ _ X x z := by
    let τ := (U.pull x).whiskerLeft (F.frobenius E)
    have h := NatTrans.IsMonoidal.unit (τ := τ)
    exact congrArg (fun m => m.hom z) h

omit coefficientMonoidal coefficientFrobeniusMonoidal in
/-- The SAME coefficient Frobenius automorphism gives every original
point component's invertibility, with no selected component premise. -/
theorem pointAutomorphisms (p : ℕ) [Fact p.Prime] :
    ImageWeightsFromCompact.Automorphisms (pointStalks C U F p) := by
  refine ⟨?_⟩
  intro E _ _ _ X x A
  change IsIso ((F.frobenius E).app ((U.pull x).obj A))
  infer_instance


end PrimeGap182.TypeIII.PointTensorAndAutomorphismsFromUniversalWeilFibers
