import TypeIIIRegularUnipotentBoundary

/-! Pure tensor and invariant contraction for ONE inertia-trivial coefficient
line. Its single-line Frobenius scalar transfers through the literal tensor
operator and an ordinary twist comparison. No all-object Tate scalar rule,
origin stalk provider, finite-field model or Type III hypothesis is assumed. -/
noncomputable section
open scoped TensorProduct
namespace PrimeGap182.TypeIII.TateLineInvariantContraction
open RegularUnipotentBoundary
universe u v w z
variable {k : Type u} [Field k] {G : Type v} [Group G]
  {V : Type w} [AddCommGroup V] [Module k V]
  {L : Type z} [AddCommGroup L] [Module k L]

/-- Contract the coefficient line using its ONE chosen basis. -/
def contraction (e : L ≃ₗ[k] k) : V ⊗[k] L ≃ₗ[k] V :=
  (TensorProduct.congr (LinearEquiv.refl k V) e).trans (TensorProduct.rid k V)

@[simp] theorem contraction_tmul (e : L ≃ₗ[k] k) (x : V) (l : L) :
    contraction (V := V) e (x ⊗ₜ[k] l) = e l • x := rfl

/-- Inertia-triviality of the coefficient line makes contraction equivariant. -/
def representationContraction (rho : Representation k G V)
    (sigma : Representation k G L) (e : L ≃ₗ[k] k)
    (he : ∀ g l, e (sigma g l) = e l) :
    Representation.Equiv (rho.tprod sigma) rho :=
  Representation.Equiv.mk (contraction e) (by
    intro g
    ext x l
    change contraction e ((rho.tprod sigma) g (x ⊗ₜ[k] l)) =
      rho g (contraction e (x ⊗ₜ[k] l))
    rw [Representation.tprod_apply, TensorProduct.map_tmul,
      contraction_tmul, contraction_tmul, map_smul, he])

/-- Restriction to invariants uses the computed representation equivalence. -/
def invariantContraction (rho : Representation k G V)
    (sigma : Representation k G L) (e : L ≃ₗ[k] k)
    (he : ∀ g l, e (sigma g l) = e l) :
    (rho.tprod sigma).invariants ≃ₗ[k] rho.invariants :=
  invariantsEquiv (representationContraction rho sigma e he)

@[simp] theorem invariantContraction_val (rho : Representation k G V)
    (sigma : Representation k G L) (e : L ≃ₗ[k] k)
    (he : ∀ g l, e (sigma g l) = e l)
    (x : (rho.tprod sigma).invariants) :
    ((invariantContraction rho sigma e he) x).val = contraction e x.val := rfl

/-- The ONE coefficient-line scalar derives the entire tensor action. -/
theorem contraction_tensor_operator (e : L ≃ₗ[k] k)
    (F : V →ₗ[k] V) (T : L →ₗ[k] L) (s : k)
    (hT : ∀ l, e (T l) = s * e l) (x : V ⊗[k] L) :
    contraction e (TensorProduct.map F T x) = s • F (contraction e x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x l =>
    simp only [TensorProduct.map_tmul, contraction_tmul]
    rw [hT, map_smul, smul_smul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-- Transfer from an actual object via its ordinary tensor comparison. -/
theorem contraction_twist_operator
    {U : Type*} [AddCommGroup U] [Module k U]
    (a : U ≃ₗ[k] V ⊗[k] L) (e : L ≃ₗ[k] k)
    (FU : U →ₗ[k] U) (F : V →ₗ[k] V) (T : L →ₗ[k] L) (s : k)
    (hT : ∀ l, e (T l) = s * e l)
    (ha : ∀ x, a (FU x) = TensorProduct.map F T (a x)) (x : U) :
    (a.trans (contraction e)) (FU x) = s • F ((a.trans (contraction e)) x) := by
  change contraction e (a (FU x)) = s • F (contraction e (a x))
  rw [ha]
  exact contraction_tensor_operator e F T s hT (a x)
end PrimeGap182.TypeIII.TateLineInvariantContraction
