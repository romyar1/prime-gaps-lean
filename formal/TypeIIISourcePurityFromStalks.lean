import TypeIIITensorPurityFromStalks
import TypeIIICurveDataFromOperations

/-!
# Source-curve purity from the common arithmetic stalks

The source lies over the finite prime field. Its purity is the same
fixed-embedding condition on original Frobenius roots as parameter
purity. Tensor purity reuses the existing spectral theorem; ordinary
dual purity uses the existing lisse dual spectrum at twist zero.
Generic geometric-curve purity is not redefined using finite points.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.SourcePurityFromStalks
open SourceInverseImageSystem PublishedPhysicalConstruction ParameterPurityFromStalks

universe mu v w

/-- The unchanged geometric observables, without a separate purity predicate. -/
structure Observables (C : Type v) (Point : Type w) where
  Lisse : C → Prop
  rank : C → ℕ
  TameZero : C → Prop
  BreaksLE : C → ℚ → Prop
  Isoclinic : C → ℚ → Prop
  swanZero : C → Point → ℕ
  swanInfinity : C → Point → ℕ

variable {p : ℕ} [Fact p.Prime] {B : System.{0,mu} (ZMod p)}
  (R : RationalPointStalks.Data B) {Point : Type w}
  (O : Observables (B.Obj .source) Point)

/-- Read source purity from all actual finite-extension source points. -/
def geometry : CurveDataFromOperations.Observables (B.Obj .source) Point where
  Lisse := O.Lisse
  Pure := pointwisePure R .source
  rank := O.rank
  TameZero := O.TameZero
  BreaksLE := O.BreaksLE
  Isoclinic := O.Isoclinic
  swanZero := O.swanZero
  swanInfinity := O.swanInfinity

theorem weights : PureDualTrace.Weights R .source (geometry R O).Pure :=
  ParameterPurityFromStalks.weights R .source

variable {R} {X : Space (ZMod p)} {Lisse : B.Obj X → Prop}
  {dual : (B.Obj X)ᵒᵖ ⥤ B.Obj X}

/-- Ordinary duality inverts every original eigenvalue, retaining
algebraic multiplicities and the original lissity guard. -/
theorem dual_pure (DS : PureDualTrace.DualSpectrum R X dual Lisse 0)
    (A : B.Obj X) (a : ℝ) (hl : Lisse A) (hp : pointwisePure R X A a) :
    pointwisePure R X (dual.obj (Opposite.op A)) (-a) := by
  intro E _ _ _ x z hz
  rw [DS.roots E x A hl] at hz
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hz
  have hq : (0 : ℝ) < (Fintype.card E : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [pow_zero, Complex.normSq_div, hp E x t ht, Real.rpow_neg (le_of_lt hq)]
  simp

/-- The twelve retained geometric rules, excluding tensor and dual purity.
They concern the same curve operations as the former complete interface. -/
structure GeometricRules {Input : Type v} {Point : Type w}
    (D : CurveData Input Point) : Prop where
  tensor_lisse : ∀ A B, D.Lisse A → D.Lisse B → D.Lisse (D.tensor A B)
  tensor_rank : ∀ A B, D.Lisse A → D.Lisse B →
    D.rank (D.tensor A B) = D.rank A * D.rank B
  dual_lisse : ∀ A, D.Lisse A → D.Lisse (D.dual A)
  dual_rank : ∀ A, D.Lisse A → D.rank (D.dual A) = D.rank A
  tensor_tame : ∀ A B, D.TameZero A → D.TameZero B → D.TameZero (D.tensor A B)
  dual_tame : ∀ A, D.TameZero A → D.TameZero (D.dual A)
  tensor_breaks : ∀ A B r, D.BreaksLE A r → D.BreaksLE B r →
    D.BreaksLE (D.tensor A B) r
  dual_breaks : ∀ A r, D.BreaksLE A r → D.BreaksLE (D.dual A) r
  tensor_unequal_breaks : ∀ A B r s, r < s → D.BreaksLE A r →
    D.Isoclinic B s → D.Isoclinic (D.tensor A B) s
  dual_isoclinic : ∀ A r, D.Isoclinic A r → D.Isoclinic (D.dual A) r
  tame_swan : ∀ A, D.TameZero A → ∀ t, D.swanZero A t = 0
  slope_one_swan : ∀ A, D.Isoclinic A 1 → ∀ t, D.swanInfinity A t = D.rank A

variable (R) (T : PointTraceFromTensor.Laws R) (dual : (B.Obj .source)ᵒᵖ ⥤ B.Obj .source)

include T in
/-- Supply both purity clauses from the original point spectra, retaining
all twelve geometric clauses verbatim. -/
theorem curveRules (DS : PureDualTrace.DualSpectrum R .source dual O.Lisse 0)
    (G : GeometricRules ((geometry R O).curveData dual)) :
    CurveRules ((geometry R O).curveData dual) where
  tensor_lisse := G.tensor_lisse
  tensor_rank := G.tensor_rank
  tensor_pure := TensorPurityFromStalks.tensor_pure R T .source
  dual_lisse := G.dual_lisse
  dual_rank := G.dual_rank
  dual_pure := dual_pure DS
  tensor_tame := G.tensor_tame
  dual_tame := G.dual_tame
  tensor_breaks := G.tensor_breaks
  dual_breaks := G.dual_breaks
  tensor_unequal_breaks := G.tensor_unequal_breaks
  dual_isoclinic := G.dual_isoclinic
  tame_swan := G.tame_swan
  slope_one_swan := G.slope_one_swan

end PrimeGap182.TypeIII.SourcePurityFromStalks

#print axioms PrimeGap182.TypeIII.SourcePurityFromStalks.geometry
#print axioms PrimeGap182.TypeIII.SourcePurityFromStalks.weights
#print axioms PrimeGap182.TypeIII.SourcePurityFromStalks.dual_pure
#print axioms PrimeGap182.TypeIII.SourcePurityFromStalks.curveRules
