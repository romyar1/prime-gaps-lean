import TypeIIIRationalPointStalks
import TypeIIISignStalkFromTensor
import TypeIIICurveDataFromOperations

/-!
# Tensor and unit traces on the common rational-point stalks

Use the actual monoidal stalk maps and the same geometric Frobenius.
Their equivariance gives the tensor trace product and constant-unit trace,
as in Laumon (1.1.1.0) and (1.1.1.2). The same comparison also supplies
the sign calculation. General cohomology and pure-dual laws remain explicit.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open scoped MonoidalCategory TensorProduct Classical

namespace PrimeGap182.TypeIII.PointTraceFromTensor
open SourceInverseImageSystem RationalPointStalks PublishedPhysicalConstruction

universe mu h
variable {p : ℕ} [Fact p.Prime] {B : System.{0,mu} (ZMod p)} (R : Data B)

/-- General monoidality and Frobenius laws at every rational point.
The operators and structural maps are those of the original stalk system. -/
structure Laws where
  [monoidal : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] X x,
    (R.fiber E X x).Monoidal]
  tensor : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] X x A C v,
    (Functor.Monoidal.μIso (R.fiber E X x) A C).toLinearEquiv
      (TensorProduct.map ((R.frobenius E X x).app A).hom
        ((R.frobenius E X x).app C).hom v) =
      ((R.frobenius E X x).app (A ⊗ C)).hom
        ((Functor.Monoidal.μIso (R.fiber E X x) A C).toLinearEquiv v)
  unit : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] X x (z : ℂ),
    ((R.frobenius E X x).app (𝟙_ (B.Obj X))).hom
      ((Functor.Monoidal.εIso (R.fiber E X x)).toLinearEquiv z) =
      (Functor.Monoidal.εIso (R.fiber E X x)).toLinearEquiv z

variable {R} (S : Laws R)
  (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
  (X : Space (ZMod p)) (x : Spec (.of E) ⟶ scheme (ZMod p) X)

/-- The sign calculation uses the inverse of the same monoidal stalk map. -/
def Laws.tensorRules : SignStalkFromTensor.TensorFiberRules (R.fiber E X x) (R.frobenius E X x) := by
  letI stalkMonoidal := S.monoidal E X x
  exact {
    comparison A C := (Functor.Monoidal.μIso (R.fiber E X x) A C).toLinearEquiv.symm
    frobenius A C v := by
      let e := (Functor.Monoidal.μIso (R.fiber E X x) A C).toLinearEquiv
      apply e.injective
      change e (e.symm _) = _
      rw [e.apply_symm_apply, S.tensor E X x A C]
      change ((R.frobenius E X x).app (A ⊗ C)).hom v =
        ((R.frobenius E X x).app (A ⊗ C)).hom (e (e.symm v))
      rw [e.apply_symm_apply]
  }

include S in
/-- Trace is multiplicative for all ordinary stalk objects, using finite
dimensionality of both factors from the shared point system. -/
theorem Laws.tensor_trace (A C : B.Obj X) :
    R.trace E x (A ⊗ C) = R.trace E x A * R.trace E x C := by
  let := R.finite E X x A
  let := R.finite E X x C
  let T := S.tensorRules E X x
  let e := T.comparison A C
  have hc : e.conj ((R.frobenius E X x).app (A ⊗ C)).hom =
      TensorProduct.map ((R.frobenius E X x).app A).hom
        ((R.frobenius E X x).app C).hom := by
    apply LinearMap.ext
    intro v
    change e (((R.frobenius E X x).app (A ⊗ C)).hom (e.symm v)) = _
    rw [T.frobenius, e.apply_symm_apply]
  change LinearMap.trace ℂ _ _ = _
  rw [← LinearMap.trace_conj' _ e, hc, LinearMap.trace_tensorProduct']
  rfl

include S in
/-- The original tensor unit has identity Frobenius on its one-dimensional stalk. -/
theorem Laws.unit_trace : R.trace E x (𝟙_ (B.Obj X)) = 1 := by
  let stalkMonoidal := S.monoidal E X x
  let e := (Functor.Monoidal.εIso (R.fiber E X x)).toLinearEquiv.symm
  have hc : e.conj ((R.frobenius E X x).app (𝟙_ (B.Obj X))).hom = LinearMap.id := by
    apply LinearMap.ext
    intro z
    change e (((R.frobenius E X x).app (𝟙_ (B.Obj X))).hom (e.symm z)) = z
    have hz := congrArg e (S.unit E X x z)
    simpa only [e, stalkMonoidal, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply] using hz
  change LinearMap.trace ℂ _ _ = _
  rw [← LinearMap.trace_conj' _ e, hc, LinearMap.trace_id]
  change (Module.finrank ℂ ℂ : ℂ) = 1
  rw [Module.finrank_self]
  norm_num

/-- Retained torus geometry and pure dual/Tate trace. Unit and product
traces are derived from the common point system instead of supplied here. -/
structure TorusGeometryRules (R : Data B) (P : ParameterData (B.Obj .torus)) : Prop where
  pullback_lisse : ∀ f A, P.Lisse A → P.Lisse ((B.torusOperations.pullback f).obj A)
  pullback_pure : ∀ f A a, P.Pure A a → P.Pure ((B.torusOperations.pullback f).obj A) a
  unit_lisse : P.Lisse (𝟙_ (B.Obj .torus))
  unit_pure : P.Pure (𝟙_ (B.Obj .torus)) 0
  tensor_lisse : ∀ A C, P.Lisse A → P.Lisse C → P.Lisse (A ⊗ C)
  tensor_pure : ∀ A C a b, P.Pure A a → P.Pure C b → P.Pure (A ⊗ C) (a + b)
  dualTate_trace : ∀ A, P.Lisse A → P.Pure A 1 →
    ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L], ∀ x y : Lˣ,
      R.torusArithmetic.trace L (P.dualTateMinusOne A) x y = star (R.torusArithmetic.trace L A x y)

variable {P : ParameterData (B.Obj .torus)}

include S in
/-- Supply both trace laws on the exact torus fibers used by the endpoint. -/
theorem Laws.torusOtherRules (T : TorusGeometryRules R P) : TorusOtherRules R P where
  pullback_lisse := T.pullback_lisse
  pullback_pure := T.pullback_pure
  unit_lisse := T.unit_lisse
  unit_pure := T.unit_pure
  tensor_lisse := T.tensor_lisse
  tensor_pure := T.tensor_pure
  unit_trace L _ _ _ x y := S.unit_trace L .torus (PhysicalTorusMorphism.schemePoint x y)
  tensor_trace A C _ _ L _ _ _ x y := S.tensor_trace L .torus (PhysicalTorusMorphism.schemePoint x y) A C
  dualTate_trace := T.dualTate_trace

variable {Point : Type h} (O : CurveDataFromOperations.Observables (B.Obj .source) Point)
  (dual : (B.Obj .source)ᵒᵖ ⥤ B.Obj .source)
  (H : CohomologyData (B.Obj .source) (B.Obj .torus))
  (point : Point) (lambda xi : Eˣ)

/-- The original cohomological trace, GOS and pure dual laws are retained
with precisely their original lissity and slope guards. -/
structure CurveOtherRules (R : Data B) : Prop where
  compact_finite : ∀ A, O.Lisse A →
    FiniteDimensional ℂ ((R.torusArithmetic.fiber E lambda xi).obj (H.compact A))
  compact_rank : ∀ A, O.Lisse A → O.Isoclinic A 1 → O.Isoclinic (dual.obj (op A)) 1 →
    Module.finrank ℂ ((R.torusArithmetic.fiber E lambda xi).obj (H.compact A)) =
      O.swanZero A point + O.swanInfinity A point
  compact_trace : ∀ A, O.Lisse A → O.Isoclinic A 1 → O.Isoclinic (dual.obj (op A)) 1 →
    LinearMap.trace ℂ ((R.torusArithmetic.fiber E lambda xi).obj (H.compact A))
      ((R.torusArithmetic.frobenius E lambda xi).app (H.compact A)).hom =
      -∑ z : Eˣ, R.trace E (X := .source) (curvePoint z lambda xi) A
  dual_weight_zero_trace : ∀ A, O.Lisse A → O.Pure A 0 → ∀ z : Eˣ,
    R.trace E (X := .source) (curvePoint z lambda xi) (dual.obj (op A)) =
      star (R.trace E (X := .source) (curvePoint z lambda xi) A)

include S in
/-- Curve and torus multiplication now use the same all-point tensor law. -/
theorem Laws.curveRules (T : CurveOtherRules E O dual H point lambda xi R) :
    CurveFiberRules (O.curveData dual) H (R.torusArithmetic.fiber E lambda xi)
      (R.torusArithmetic.frobenius E lambda xi) E
      (R.curveTraceData (O.curveData dual) point lambda xi) where
  compact_finite := T.compact_finite
  compact_rank := T.compact_rank
  compact_trace := T.compact_trace
  tensor_trace A C z := S.tensor_trace E .source (curvePoint z lambda xi) A C
  dual_weight_zero_trace := T.dual_weight_zero_trace

end PrimeGap182.TypeIII.PointTraceFromTensor

#print axioms PrimeGap182.TypeIII.PointTraceFromTensor.Laws.tensorRules
#print axioms PrimeGap182.TypeIII.PointTraceFromTensor.Laws.tensor_trace
#print axioms PrimeGap182.TypeIII.PointTraceFromTensor.Laws.unit_trace
#print axioms PrimeGap182.TypeIII.PointTraceFromTensor.Laws.torusOtherRules
#print axioms PrimeGap182.TypeIII.PointTraceFromTensor.Laws.curveRules
