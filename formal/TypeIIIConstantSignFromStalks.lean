import TypeIIISignStalkFromTensor
import TypeIIISharedCohomology

/-!
# The same constant sign line in arithmetic and geometric stalks

For sheaves pulled back from the constant field, finite-extension
Frobenius is the degree-th power of prime-field Frobenius and geometric
inertia acts trivially. These general published representation/pullback
laws remain explicit. A single constant line with prime-field scalar -1
supplies every extension sign and geometric sign model. Signing itself
is tensoring with that same line.

Milne, Lectures on Etale Cohomology, section 30, review of notation,
printed p.176, identifies the constant-field quotient and degree powers.
Stacks 59.65.1 gives the finite locally constant representation formalism;
its adic interpretation remains part of the shared background.
-/

noncomputable section
open CategoryTheory
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.ConstantSignFromStalks
open PublishedPhysicalConstruction ConstantSignInertia

universe u v g i
variable {C : Type u} [Category.{v} C] {G : Type g} [Group G]
  {Index : Type i} {p : ℕ} [Fact p.Prime]
  (TA : TorusArithmeticData p C) (geom : Index → C ⥤ FDRep ℂ G)

/-- General stalk laws for objects pulled back from the constant field.
They do not mention the sign, the correlation, or a Type III estimate. -/
structure Rules where
  Constant : C → Prop
  arithmetic : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (x y : Eˣ) (A : C), Constant A →
    (TA.fiber E x y).obj A ≃ₗ[ℂ] (TA.fiber (ZMod p) 1 1).obj A
  arithmetic_frobenius : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (x y : Eˣ) (A : C) (hA : Constant A) (v : (TA.fiber E x y).obj A),
    arithmetic E x y A hA (((TA.frobenius E x y).app A).hom v) =
      (fun w => ((TA.frobenius (ZMod p) 1 1).app A).hom w)^[Module.finrank (ZMod p) E]
        (arithmetic E x y A hA v)
  geometric : ∀ (f : Index) (A : C), Constant A →
    (geom f).obj A ≃ₗ[ℂ] (TA.fiber (ZMod p) 1 1).obj A
  geometric_action : ∀ (f : Index) (A : C) (hA : Constant A) (g : G)
    (v : (geom f).obj A), geometric f A hA (((geom f).obj A).ρ g v) = geometric f A hA v

variable {TA geom} (R : Rules TA geom)

/-- One primitive constant line with prime-field Frobenius -1.
No extension-dependent action or geometric sign comparison is supplied. -/
structure LineData where
  line : C
  constant : R.Constant line
  basis : (TA.fiber (ZMod p) 1 1).obj line ≃ₗ[ℂ] ℂ
  frobenius : ∀ v, basis (((TA.frobenius (ZMod p) 1 1).app line).hom v) = (-1 : ℂ) * basis v

/-- A scalar action iterates to the corresponding scalar power. -/
theorem iterate_scalar {V : Type u} [AddCommGroup V] [Module ℂ V]
    (T : V → V) (e : V ≃ₗ[ℂ] ℂ) (a : ℂ) (h : ∀ v, e (T v) = a * e v)
    (n : ℕ) (v : V) : e (T^[n] v) = a ^ n * e v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply, ih, h, pow_succ, mul_assoc]

variable {R} (L : LineData R)

/-- Use one prime-field basis for every finite-extension stalk. -/
def LineData.arithmeticBasis (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (x y : Eˣ) : (TA.fiber E x y).obj L.line ≃ₗ[ℂ] ℂ :=
  (R.arithmetic E x y L.line L.constant).trans L.basis

/-- All finite-extension signs follow from the single prime-field action. -/
theorem LineData.arithmetic_action (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (x y : Eˣ) (v : (TA.fiber E x y).obj L.line) :
    L.arithmeticBasis E x y (((TA.frobenius E x y).app L.line).hom v) =
      (-1 : ℂ) ^ Module.finrank (ZMod p) E * L.arithmeticBasis E x y v := by
  change L.basis (R.arithmetic E x y L.line L.constant _) = _
  rw [R.arithmetic_frobenius]
  exact iterate_scalar _ L.basis (-1) L.frobenius _ _

variable {W : Type v} [Group W] (degree : W →* Multiplicative ℤ)
  (inertia : G →* W) (geometric : ∀ g, degree (inertia g) = 1)

/-- The geometric model is derived from constancy of the same line. -/
def LineData.geometricModel (f : Index) :
    SignLineModel degree inertia ((geom f).obj L.line) where
  basis := (R.geometric f L.line L.constant).trans L.basis
  action g v := by
    change L.basis (R.geometric f L.line L.constant _) = _
    rw [R.geometric_action, geometric_sign_scalar degree inertia geometric, one_mul]
    rfl

/-- Parameter observables without an independently chosen signed operation. -/
structure ParameterGeometry (C : Type u) where
  Lisse : C → Prop
  Pure : C → ℝ → Prop

variable [MonoidalCategory C]

def ParameterGeometry.withLine (O : ParameterGeometry C) (line : C) :
    SharedCohomology.ParameterObservables C where
  Lisse := O.Lisse
  Pure := O.Pure
  signed A := line ⊗ A

def ParameterGeometry.signTensor (O : ParameterGeometry C) (DT : Cᵒᵖ ⥤ C) (line : C) :
    SignTensorData ((O.withLine line).data DT) where
  line := line
  tensorIso _ := Iso.refl _

/-- Construct the existing arithmetic sign input on the selected line. -/
def LineData.signInputs (O : ParameterGeometry C) (DT : Cᵒᵖ ⥤ C)
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (x y : Eˣ)
    (tensor : SignStalkFromTensor.TensorFiberRules (TA.fiber E x y) (TA.frobenius E x y)) :
    SignStalkFromTensor.Inputs (TA.fiber E x y) (TA.frobenius E x y)
      (O.signTensor DT L.line) (Module.finrank (ZMod p) E) where
  tensor := tensor
  basis := L.arithmeticBasis E x y
  line_frobenius := L.arithmetic_action E x y

end PrimeGap182.TypeIII.ConstantSignFromStalks

#print axioms PrimeGap182.TypeIII.ConstantSignFromStalks.iterate_scalar
#print axioms PrimeGap182.TypeIII.ConstantSignFromStalks.LineData.arithmetic_action
#print axioms PrimeGap182.TypeIII.ConstantSignFromStalks.LineData.geometricModel
#print axioms PrimeGap182.TypeIII.ConstantSignFromStalks.ParameterGeometry.withLine
#print axioms PrimeGap182.TypeIII.ConstantSignFromStalks.ParameterGeometry.signTensor
#print axioms PrimeGap182.TypeIII.ConstantSignFromStalks.LineData.signInputs
