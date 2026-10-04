import TypeIIITensorListRepresentation

/-!
# The constant arithmetic sign on geometric inertia

The constant Weil line acts by (-1) to the arithmetic degree. On
geometric inertia that degree is zero. Its line model therefore gives
an equivariant trivialization, and a strong monoidal functor transports
this to tensor with the sign on every object. No signed-core equivalence
is supplied. No assertion that the arithmetic Frobenius sign is trivial
is made.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.ConstantSignInertia

open PublishedPhysicalConstruction TensorListRepresentation

universe u v w z a b
variable {E : Type u} [Field E] {G : Type v} [Group G]
  {W : Type w} [Group W] (degree : W →* Multiplicative ℤ) (inertia : G →* W)

/-- The scalar-action description of a constant sign line. This is a
one-dimensional source model, independent of any Type III core. -/
structure SignLineModel (V : FDRep E G) where
  basis : V ≃ₗ[E] E
  action : ∀ g v, basis (V.ρ g v) =
    (-1 : E) ^ (degree (inertia g)).toAdd * basis v

variable (geometric : ∀ g, degree (inertia g) = 1)

include geometric in
/-- The arithmetic degree vanishes on geometric inertia. -/
theorem geometric_sign_scalar (g : G) :
    (-1 : E) ^ (degree (inertia g)).toAdd = 1 := by
  rw [geometric g]
  simp

variable {V : FDRep E G} (R : SignLineModel degree inertia V)

include geometric R in
/-- The original line action, not only its character, is trivial. -/
theorem signLine_action (g : G) (v : V) : V.ρ g v = v := by
  apply R.basis.injective
  rw [R.action, geometric_sign_scalar degree inertia geometric, one_mul]

/-- Identify the actual line representation with the tensor unit. -/
def signLineUnitEquiv : Representation.Equiv V.ρ (𝟙_ (FDRep E G)).ρ where
  toLinearEquiv := R.basis
  isIntertwining' g := by
    ext v
    change R.basis (V.ρ g v) = R.basis v
    rw [signLine_action degree inertia geometric R]

variable {C : Type z} [Category.{a} C] [MonoidalCategory C]
  (P : ParameterData C)

/-- The original signed operation is tensor with its fixed constant line.
This law quantifies over every parameter object. -/
structure SignTensorData where
  line : C
  tensorIso : ∀ A, P.signed A ≅ line ⊗ A

variable (S : SignTensorData P) (J : C ⥤ FDRep E G) [J.Monoidal]
  (RS : SignLineModel degree inertia (J.obj S.line))

/-- Derive sign removal on geometric inertia from the line model,
monoidality and the tensor unit; no completed-family map is an input. -/
def signedInertiaEquiv (A : C) :
    Representation.Equiv (J.obj (P.signed A)).ρ (J.obj A).ρ :=
  (equivOfIso (J.mapIso (S.tensorIso A) ≪≫
    (Functor.Monoidal.μIso J S.line A).symm)).trans
      ((PublishedMackey.tensorEquiv (signLineUnitEquiv degree inertia geometric RS)
        (Representation.Equiv.refl (J.obj A).ρ)).trans
          (equivOfIso (λ_ (J.obj A))))

end PrimeGap182.TypeIII.ConstantSignInertia

#print axioms PrimeGap182.TypeIII.ConstantSignInertia.geometric_sign_scalar
#print axioms PrimeGap182.TypeIII.ConstantSignInertia.signLine_action
#print axioms PrimeGap182.TypeIII.ConstantSignInertia.signLineUnitEquiv
#print axioms PrimeGap182.TypeIII.ConstantSignInertia.signedInertiaEquiv
