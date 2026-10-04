import TypeIIIConstantSignInertia

/-!
# Arithmetic sign comparison from the same constant line

Stalks commute with tensor products and Frobenius acts on both factors.
The constant sign line has scalar (-1)^d over a degree-d extension.
These general inputs, together with the existing signed-object tensor
isomorphism, imply the full SignStalkComparison for every object.
No signed-core Frobenius comparison is an input. The geometric sign
removal and this arithmetic comparison use the same SignTensorData.line.
-/

noncomputable section
open CategoryTheory
open scoped MonoidalCategory TensorProduct

namespace PrimeGap182.TypeIII.SignStalkFromTensor

open PublishedPhysicalConstruction ConstantSignInertia

universe w z
variable {C : Type w} [Category.{z} C] [MonoidalCategory C]
  (F : C ⥤ ModuleCat.{w} ℂ) (Fr : F ⟶ F)

/-- General tensor/stalk compatibility for all pairs of objects. -/
structure TensorFiberRules where
  comparison : ∀ A B, F.obj (A ⊗ B) ≃ₗ[ℂ] (F.obj A ⊗[ℂ] F.obj B)
  frobenius : ∀ A B v, comparison A B ((Fr.app (A ⊗ B)).hom v) =
    TensorProduct.map (Fr.app A).hom (Fr.app B).hom (comparison A B v)

variable {P : ParameterData C} (S : SignTensorData P) (d : ℕ)

/-- Only the constant line's arithmetic scalar is source-specific.
The tensor law is independent of the signed operation. -/
structure Inputs where
  tensor : TensorFiberRules F Fr
  basis : F.obj S.line ≃ₗ[ℂ] ℂ
  line_frobenius : ∀ v, basis ((Fr.app S.line).hom v) = (-1 : ℂ) ^ d * basis v

namespace Inputs

variable {F Fr S d} (R : Inputs F Fr S d)

def lineContraction (A : C) : (F.obj S.line ⊗[ℂ] F.obj A) ≃ₗ[ℂ] F.obj A :=
  (TensorProduct.congr R.basis (LinearEquiv.refl ℂ (F.obj A))).trans
    (TensorProduct.lid ℂ (F.obj A))

/-- Tensor Frobenius contracts to the sign scalar times the original action. -/
theorem lineContraction_frobenius (A : C) (v : F.obj S.line ⊗[ℂ] F.obj A) :
    R.lineContraction A (TensorProduct.map (Fr.app S.line).hom (Fr.app A).hom v) =
      ((-1 : ℂ) ^ d) • (Fr.app A).hom (R.lineContraction A v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp [lineContraction, R.line_frobenius, mul_smul]
  | add a b ha hb => simp only [map_add, ha, hb, smul_add]

omit [MonoidalCategory C] in
/-- Naturality transports Frobenius across any object isomorphism. -/
theorem mapIso_frobenius {A B : C} (e : A ≅ B) (v : F.obj A) :
    (F.mapIso e).toLinearEquiv ((Fr.app A).hom v) =
      (Fr.app B).hom ((F.mapIso e).toLinearEquiv v) := by
  have h := congrArg (fun f : F.obj A ⟶ F.obj B => f.hom v) (Fr.naturality e.hom)
  exact h.symm

/-- The comparison is constructed from the actual signed tensor isomorphism. -/
def stalkEquiv (A : C) : F.obj (P.signed A) ≃ₗ[ℂ] F.obj A :=
  (F.mapIso (S.tensorIso A)).toLinearEquiv.trans
    ((R.tensor.comparison S.line A).trans (R.lineContraction A))

theorem stalkEquiv_frobenius (A : C) (v : F.obj (P.signed A)) :
    R.stalkEquiv A ((Fr.app (P.signed A)).hom v) =
      ((-1 : ℂ) ^ d) • (Fr.app A).hom (R.stalkEquiv A v) := by
  change R.lineContraction A (R.tensor.comparison S.line A
    ((F.mapIso (S.tensorIso A)).toLinearEquiv ((Fr.app (P.signed A)).hom v))) = _
  rw [mapIso_frobenius, R.tensor.frobenius, R.lineContraction_frobenius]
  rfl

/-- The former full sign comparison is now a consequence of general laws
and the constant line's degree-d action. -/
def signStalkComparison : SignStalkComparison P F Fr d where
  comparison := R.stalkEquiv
  frobenius A := by
    ext v
    change R.stalkEquiv A ((Fr.app (P.signed A)).hom ((R.stalkEquiv A).symm v)) = _
    rw [R.stalkEquiv_frobenius, LinearEquiv.apply_symm_apply]
    rfl

end Inputs

end PrimeGap182.TypeIII.SignStalkFromTensor

#print axioms PrimeGap182.TypeIII.SignStalkFromTensor.Inputs.lineContraction_frobenius
#print axioms PrimeGap182.TypeIII.SignStalkFromTensor.Inputs.mapIso_frobenius
#print axioms PrimeGap182.TypeIII.SignStalkFromTensor.Inputs.stalkEquiv_frobenius
#print axioms PrimeGap182.TypeIII.SignStalkFromTensor.Inputs.signStalkComparison
