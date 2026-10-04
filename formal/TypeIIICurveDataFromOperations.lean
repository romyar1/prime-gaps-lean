import TypeIIIFourierStalkFromSources

/-!
# Curve data from the existing tensor and dual operations

The relative curve recipe uses the monoidal product of its category and
its selected contravariant dual functor. Only the geometric observables
remain separate data. Tensor and dual comparison maps are identities;
no additional mathematical law or choice of curve operation is assumed.
The general curve laws and compatibility of duality with specialization
remain explicit published inputs in the application.
-/

noncomputable section
open CategoryTheory Opposite
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.CurveDataFromOperations
open PublishedPhysicalConstruction

universe u v w

/-- Geometric predicates and numerical observables, without independently
chosen tensor or dual operations. The published curve laws constrain these
observables on the actual categorical operations. -/
structure Observables (C : Type u) (Point : Type v) where
  Lisse : C → Prop
  Pure : C → ℝ → Prop
  rank : C → ℕ
  TameZero : C → Prop
  BreaksLE : C → ℚ → Prop
  Isoclinic : C → ℚ → Prop
  swanZero : C → Point → ℕ
  swanInfinity : C → Point → ℕ

variable {C : Type u} {Point : Type v} [Category.{w} C] [MonoidalCategory C]
  (S : Observables C Point) (dual : Cᵒᵖ ⥤ C)

/-- Use the already selected category tensor and contravariant dual. -/
def Observables.curveData : CurveData C Point where
  tensor A B := A ⊗ B
  dual A := dual.obj (op A)
  Lisse := S.Lisse
  Pure := S.Pure
  rank := S.rank
  TameZero := S.TameZero
  BreaksLE := S.BreaksLE
  Isoclinic := S.Isoclinic
  swanZero := S.swanZero
  swanInfinity := S.swanInfinity

/-- The recipe tensor is the categorical tensor itself. -/
def Observables.tensorComparison (A B : C) :
    (S.curveData dual).tensor A B ≅ A ⊗ B := Iso.refl _

/-- The recipe dual is the chosen dual functor itself. -/
def Observables.dualComparison (A : C) :
    (S.curveData dual).dual A ≅ dual.obj (op A) := Iso.refl _

end PrimeGap182.TypeIII.CurveDataFromOperations

#print axioms PrimeGap182.TypeIII.CurveDataFromOperations.Observables.curveData
#print axioms PrimeGap182.TypeIII.CurveDataFromOperations.Observables.tensorComparison
#print axioms PrimeGap182.TypeIII.CurveDataFromOperations.Observables.dualComparison
