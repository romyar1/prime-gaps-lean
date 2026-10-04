import TypeIIIRegularUnipotentRepresentation

/-!
# Applying an ALL-rank regular-unipotent tame-basis theorem at rank three

The universal published input may specify an actual basis and finite Jordan
exponential action for every positive raw Kloosterman rank (GKM4.1.1(3)).
Its application at rank three is derived here on arbitrary actual
representations: the finite exponential is the existing literal tame model.
No general exponential representation laws or inertia foundations are rebuilt.
-/
noncomputable section
open scoped Classical Matrix BigOperators

namespace PrimeGap182.TypeIII.RegularTameBasisFromFiniteJordanExponential
open RegularUnipotentRepresentation

universe u v w
variable {k : Type u} [Field k]

/-- The literal nilpotent one-block matrix in every finite dimension. -/
def jordanBlock (n : ℕ) : Matrix (Fin n) (Fin n) k :=
  fun i j => if j.val = i.val + 1 then 1 else 0

/-- The finite nilpotent exponential, with no infinite series or topology. -/
def finiteJordanExponential (n : ℕ) (t : k) : Matrix (Fin n) (Fin n) k :=
  ∑ j : Fin n, (t ^ j.val / (j.val.factorial : k)) • (jordanBlock n) ^ j.val

/-- At rank three the ALL-rank formula is precisely the existing model. -/
theorem finiteJordanExponential_three (t : k) :
    finiteJordanExponential 3 t = exponentialMatrix t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteJordanExponential, jordanBlock, exponentialMatrix,
      RegularUnipotentBoundary.regularMatrix, jordanThreeCoordinates,
      Fin.sum_univ_succ, Matrix.mul_apply, pow_succ]

variable {H : Type v} [Group H] {V : Type w} [AddCommGroup V] [Module k V]
  (rho : Representation k H V) (tame : H →* Multiplicative k)

/-- Exact ALL-rank regular-unipotent tame-basis property. The supplied basis
is a linear equivalence of the actual coefficient module, and specifies
ALL actual inertia operators in the universal finite Jordan formula. -/
def HasRegularTameBasis (n : ℕ) : Prop :=
  ∃ e : V ≃ₗ[k] (Fin n → k), ∀ g : H,
    e.conj (rho g) = Matrix.toLin' (finiteJordanExponential n (tame g).toAdd)

/-- The actual finite basis computes dimension without a chosen rank dictionary. -/
theorem HasRegularTameBasis.rank (n : ℕ) (h : HasRegularTameBasis rho tame n) :
    Module.finrank k V = n := by
  obtain ⟨e, _⟩ := h
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using e.finrank_eq

variable [CharZero k]

/-- Specialization of the universal basis theorem yields the full original
rank-three representation equivalence, not merely its invariants or rank. -/
def HasRegularTameBasis.threeEquiv (h : HasRegularTameBasis rho tame 3) :
    Representation.Equiv rho (tameRepresentation tame) := by
  let e := Classical.choose h
  have he : ∀ g : H, e.conj (rho g) =
      Matrix.toLin' (finiteJordanExponential 3 (tame g).toAdd) := Classical.choose_spec h
  refine Representation.Equiv.mk e ?_
  intro g
  apply LinearMap.ext
  intro x
  have ht := congrArg (fun f : (Fin 3 → k) →ₗ[k] (Fin 3 → k) => f (e x)) (he g)
  rw [finiteJordanExponential_three] at ht
  change e (rho g x) = Matrix.toLin' (exponentialMatrix (tame g).toAdd) (e x)
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply] at ht
  change e (rho g (e.symm (e x))) = Matrix.toLin' (exponentialMatrix (tame g).toAdd) (e x) at ht
  simpa only [LinearEquiv.symm_apply_apply] using ht

end PrimeGap182.TypeIII.RegularTameBasisFromFiniteJordanExponential
