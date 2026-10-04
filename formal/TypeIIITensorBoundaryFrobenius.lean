import TypeIIIBoundaryFrobeniusNormalization
import TypeIIIRegularUnipotentBoundary

/-!
# Frobenius on the actual tensor-invariant boundary model

Tensor-Hom naturality identifies the actual source tensor operator
F1 tensor dual(F2 inverse) with X |-> F1 X F2 inverse. The invariant
subspace is the full tensor-invariant space already identified with the
Jordan centralizer. Its Frobenius action and correction trace are derived
from the two single-source scaling and invariant-line laws.

The common geometric realization and the natural boundary-cohomology
comparison still need to carry this model to the physical boundary.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Classical TensorProduct

namespace PrimeGap182.TypeIII.TensorBoundaryFrobenius

open RegularUnipotentBoundary BoundaryFrobeniusNormalization

universe u v
variable {k : Type u} [Field k]

abbrev ModelSpace := Fin 3 → k
abbrev ModelTensor := ModelSpace (k := k) ⊗[k] Module.Dual k (ModelSpace (k := k))

def tensorHomEquiv : ModelTensor (k := k) ≃ₗ[k] Module.End k (ModelSpace (k := k)) :=
  (TensorProduct.comm k _ _).trans (dualTensorHomEquiv k _ _)

def tensorMatrixEquiv : ModelTensor (k := k) ≃ₗ[k] Matrix (Fin 3) (Fin 3) k :=
  tensorHomEquiv.trans LinearMap.toMatrix'

/-- The tensor-Hom comparison preserves arbitrary operators on both
source factors. The second acts by precomposition through its dual. -/
theorem tensorHomEquiv_natural (A B : Module.End k (ModelSpace (k := k)))
    (x : ModelTensor (k := k)) :
    tensorHomEquiv (TensorProduct.map A B.dualMap x) =
      (A.comp (tensorHomEquiv x)).comp B := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v phi =>
    apply LinearMap.ext
    intro w
    change phi (B w) • A v = A (phi (B w) • v)
    exact (A.map_smul (phi (B w)) v).symm
  | add x y hx hy =>
    simp only [map_add, hx, hy, LinearMap.comp_add, LinearMap.add_comp]

/-- The operator on matrices uses the same actual left and right source
operators; it is not an assumed boundary action. -/
theorem tensorMatrixEquiv_natural (A B : Matrix (Fin 3) (Fin 3) k)
    (x : ModelTensor (k := k)) :
    tensorMatrixEquiv (TensorProduct.map (Matrix.toLin' A) (Matrix.toLin' B).dualMap x) =
      A * tensorMatrixEquiv x * B := by
  change LinearMap.toMatrix' (tensorHomEquiv _) = _
  rw [tensorHomEquiv_natural, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_toLin']
  rfl

variable {G : Type v} [Group G] {rho : Representation k G (ModelSpace (k := k))}
  (M : RegularModel rho)

/-- The exact invariant subspace of the canonical model tensor. -/
def modelInvariantsEquiv :
    (rho.tprod rho.dual).invariants ≃ₗ[k] jordanThreeCentralizer k :=
  (invariantsEquiv ((Representation.TensorProduct.comm rho rho.dual).trans
    (Representation.Equiv.dualTensorHom rho rho))).trans (endomorphismInvariantsEquiv M)

theorem modelInvariantsEquiv_val (x : (rho.tprod rho.dual).invariants) :
    (modelInvariantsEquiv M x).val = tensorMatrixEquiv x.val := rfl

/-- The literal tensor of the first source operator and the dual inverse
of the second. No restriction to invariants is assumed at this stage. -/
def tensorFrobenius (F1 F2 : Matrix (Fin 3) (Fin 3) k) :
    ModelTensor (k := k) →ₗ[k] ModelTensor (k := k) :=
  TensorProduct.map (Matrix.toLin' F1) (Matrix.toLin' F2⁻¹).dualMap

/-- Construct the operator on the full invariant subspace. Its inclusion
agrees with the raw tensor operator by the next theorem. -/
def invariantFrobenius (q c : k) (F1 F2 : Matrix (Fin 3) (Fin 3) k) :
    (rho.tprod rho.dual).invariants →ₗ[k] (rho.tprod rho.dual).invariants :=
  (modelInvariantsEquiv M).symm.conj (relativeOperator q c F1 F2)

theorem invariantFrobenius_val (q c : k) (hq : q ≠ 0) (hc : c ≠ 0)
    (F1 F2 : Matrix (Fin 3) (Fin 3) k)
    (hN1 : F1 * jordanThree k = q⁻¹ • (jordanThree k * F1))
    (hN2 : F2 * jordanThree k = q⁻¹ • (jordanThree k * F2))
    (hl1 : F1 0 0 = c) (hl2 : F2 0 0 = c) (x : (rho.tprod rho.dual).invariants) :
    (invariantFrobenius M q c F1 F2 x).val = tensorFrobenius F1 F2 x.val := by
  apply tensorMatrixEquiv.injective
  rw [← modelInvariantsEquiv_val M, invariantFrobenius, LinearEquiv.conj_apply_apply,
    LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply,
    relativeOperator_val q c hq hc F1 F2 hN1 hN2 hl1 hl2, modelInvariantsEquiv_val,
    tensorFrobenius, tensorMatrixEquiv_natural]

/-- The correction trace for the actual tensor-invariant Frobenius,
with its raw source action proved in `invariantFrobenius_val`. -/
theorem invariantFrobenius_trace (q c : k) (F1 F2 : Matrix (Fin 3) (Fin 3) k) :
    LinearMap.trace k (rho.tprod rho.dual).invariants (invariantFrobenius M q c F1 F2) =
      1 + q⁻¹ + q⁻¹ ^ 2 := by
  unfold invariantFrobenius
  rw [LinearMap.trace_conj' (R := k) (M := jordanThreeCentralizer k)
    (N := (rho.tprod rho.dual).invariants)
    (relativeOperator q c F1 F2) (modelInvariantsEquiv M).symm]
  exact relativeOperator_trace q c F1 F2

variable (q c : k) (hq : q ≠ 0) (hc : c ≠ 0)
  (F1 F2 : Matrix (Fin 3) (Fin 3) k)
  (hN1 : F1 * jordanThree k = q⁻¹ • (jordanThree k * F1))
  (hN2 : F2 * jordanThree k = q⁻¹ • (jordanThree k * F2))
  (hl1 : F1 0 0 = c) (hl2 : F2 0 0 = c)

/-- Restrict the raw tensor Frobenius itself. Invariance is proved from
the source laws and the preceding equivariant coordinate calculation. -/
def actualInvariantFrobenius :
    (rho.tprod rho.dual).invariants →ₗ[k] (rho.tprod rho.dual).invariants where
  toFun x := ⟨tensorFrobenius F1 F2 x.val, by
    rw [← invariantFrobenius_val M q c hq hc F1 F2 hN1 hN2 hl1 hl2 x]
    exact (invariantFrobenius M q c F1 F2 x).property⟩
  map_add' x y := Subtype.ext ((tensorFrobenius F1 F2).map_add x.val y.val)
  map_smul' a x := Subtype.ext ((tensorFrobenius F1 F2).map_smul a x.val)

theorem actualInvariantFrobenius_eq :
    actualInvariantFrobenius M q c hq hc F1 F2 hN1 hN2 hl1 hl2 =
      invariantFrobenius M q c F1 F2 :=
  LinearMap.ext (fun x => Subtype.ext
    (invariantFrobenius_val M q c hq hc F1 F2 hN1 hN2 hl1 hl2 x).symm)

/-- The correction trace for the literal restricted tensor operator.
Its type retains both single-source normalization hypotheses. -/
theorem actualInvariantFrobenius_trace :
    LinearMap.trace k (rho.tprod rho.dual).invariants
      (actualInvariantFrobenius M q c hq hc F1 F2 hN1 hN2 hl1 hl2) =
        1 + q⁻¹ + q⁻¹ ^ 2 := by
  rw [actualInvariantFrobenius_eq, invariantFrobenius_trace]

end PrimeGap182.TypeIII.TensorBoundaryFrobenius

#print axioms PrimeGap182.TypeIII.TensorBoundaryFrobenius.tensorHomEquiv
#print axioms PrimeGap182.TypeIII.TensorBoundaryFrobenius.tensorMatrixEquiv
#print axioms PrimeGap182.TypeIII.TensorBoundaryFrobenius.tensorHomEquiv_natural
#print axioms PrimeGap182.TypeIII.TensorBoundaryFrobenius.tensorMatrixEquiv_natural
#print axioms PrimeGap182.TypeIII.TensorBoundaryFrobenius.modelInvariantsEquiv
#print axioms PrimeGap182.TypeIII.TensorBoundaryFrobenius.modelInvariantsEquiv_val
#print axioms PrimeGap182.TypeIII.TensorBoundaryFrobenius.tensorFrobenius
#print axioms PrimeGap182.TypeIII.TensorBoundaryFrobenius.invariantFrobenius
#print axioms PrimeGap182.TypeIII.TensorBoundaryFrobenius.invariantFrobenius_val
#print axioms PrimeGap182.TypeIII.TensorBoundaryFrobenius.invariantFrobenius_trace
#print axioms PrimeGap182.TypeIII.TensorBoundaryFrobenius.actualInvariantFrobenius
#print axioms PrimeGap182.TypeIII.TensorBoundaryFrobenius.actualInvariantFrobenius_eq
#print axioms PrimeGap182.TypeIII.TensorBoundaryFrobenius.actualInvariantFrobenius_trace
