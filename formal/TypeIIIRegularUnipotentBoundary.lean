import TypeIIITensorListRepresentation
import TypeIIIJordanCorrection
import Mathlib.RepresentationTheory.Invariants

/-!
# Tensor invariants of the regular unipotent rank-three model

An actual representation in a common regular-unipotent basis has matrices
1 + a(g)N + b(g)N^2, with a(g) nonzero for some inertia element.
Its endomorphism invariants are exactly the already computed centralizer
of N. Equivariant tensor-Hom and change-of-basis maps then identify the
invariants of two such source factors, one dualized, with that centralizer.
The calculation also includes the trivial additive factor at zero.

The two single-source regular-unipotent models remain published geometric
inputs (Katz, GKM, Theorem 7.4.3). No invariant-space identification or
dimension-three assertion for their tensor is an input here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Classical Matrix TensorProduct

namespace PrimeGap182.TypeIII.RegularUnipotentBoundary

open PublishedMackey PublishedPhaseApplication

universe u v w z
variable {k : Type u} [Field k]

def regularMatrix (a b : k) : Matrix (Fin 3) (Fin 3) k :=
  jordanThreeCoordinates ![1, a, b]

/-- Commuting with one regular unipotent matrix forces the full Jordan
centralizer. The quadratic coefficient need not have a prescribed value. -/
theorem regularMatrix_commutes_iff (a b : k) (ha : a ≠ 0)
    (X : Matrix (Fin 3) (Fin 3) k) :
    regularMatrix a b * X = X * regularMatrix a b ↔ X ∈ jordanThreeCentralizer k := by
  constructor
  · intro h
    have h10 := congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M 1 0) h
    have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M 0 0) h
    have h22 := congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M 2 2) h
    have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M 0 1) h
    have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M 1 2) h
    have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M 0 2) h
    simp [regularMatrix, jordanThreeCoordinates, Matrix.mul_apply, Fin.sum_univ_succ]
      at h10 h00 h22 h01 h12 h02
    have e20 : X 2 0 = 0 := h10.resolve_left ha
    have e10 : X 1 0 = 0 := (mul_eq_zero.mp
      (by simpa only [e20, mul_zero, add_zero] using h00 : a * X 1 0 = 0)).resolve_left ha
    have e21 : X 2 1 = 0 := (mul_eq_zero.mp
      (by linear_combination -h22 - b * e20 : a * X 2 1 = 0)).resolve_left ha
    have e11 : X 1 1 = X 0 0 := by
      apply (mul_left_cancel₀ ha)
      linear_combination h01 - b * e21
    have e22 : X 2 2 = X 0 0 := by
      apply (mul_left_cancel₀ ha)
      linear_combination h12 + b * e10 + a * e11
    have e12 : X 1 2 = X 0 1 := by
      apply (mul_left_cancel₀ ha)
      linear_combination h02 - b * e22
    have hx : X = jordanThreeCoordinates ![X 0 0, X 0 1, X 0 2] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [jordanThreeCoordinates, e20, e10, e21, e11, e22, e12]
    rw [hx]
    exact jordanThreeCoordinates_mem _
  · intro hx
    rw [jordanThreeCentralizer_eq_coordinates X hx]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [regularMatrix, jordanThreeCoordinates, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

variable {G : Type v} [Group G]

/-- A model for one rank-three inertia representation. The hypotheses
specify its operators, not an invariant space of a tensor representation. -/
structure RegularModel (rho : Representation k G (Fin 3 → k)) where
  linearCoefficient : G → k
  quadraticCoefficient : G → k
  action : ∀ g, LinearMap.toMatrix' (rho g) =
    regularMatrix (linearCoefficient g) (quadraticCoefficient g)
  regular : ∃ g, linearCoefficient g ≠ 0

variable {rho : Representation k G (Fin 3 → k)} (M : RegularModel rho)

include M in
theorem endomorphism_invariants_iff (f : (Fin 3 → k) →ₗ[k] (Fin 3 → k)) :
    f ∈ (Representation.linHom rho rho).invariants ↔
      LinearMap.toMatrix' f ∈ jordanThreeCentralizer k := by
  simp only [Representation.mem_invariants, Representation.linHom_apply,
    Representation.mem_linHom_invariants_iff_isIntertwining]
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := M.regular
    apply (regularMatrix_commutes_iff _ _ hg _).mp
    have he : (rho g).comp f = f.comp (rho g) :=
      LinearMap.ext (fun x => (hf.isIntertwining g x).symm)
    have h := congrArg LinearMap.toMatrix' he
    simpa only [LinearMap.toMatrix'_comp, M.action] using h
  · intro hf
    refine ⟨fun g x => ?_⟩
    have hc : regularMatrix (M.linearCoefficient g) (M.quadraticCoefficient g) *
        LinearMap.toMatrix' f = LinearMap.toMatrix' f *
          regularMatrix (M.linearCoefficient g) (M.quadraticCoefficient g) := by
      rw [jordanThreeCentralizer_eq_coordinates _ hf]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [regularMatrix, jordanThreeCoordinates, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
    have he : f.comp (rho g) = (rho g).comp f :=
      LinearMap.toMatrix'.injective (by simpa only [LinearMap.toMatrix'_comp, M.action] using hc.symm)
    exact congrArg (fun l => l x) he

/-- Explicit matrix coordinates on the endomorphism-invariant subspace. -/
def endomorphismInvariantsEquiv :
    (Representation.linHom rho rho).invariants ≃ₗ[k] jordanThreeCentralizer k where
  toFun f := ⟨LinearMap.toMatrix' f.val, (endomorphism_invariants_iff M f.val).mp f.property⟩
  invFun X := ⟨Matrix.toLin' X.val, (endomorphism_invariants_iff M _).mpr (by
    rw [LinearMap.toMatrix'_toLin']; exact X.property)⟩
  left_inv f := Subtype.ext (Matrix.toLin'_toMatrix' f.val)
  right_inv X := Subtype.ext (LinearMap.toMatrix'_toLin' X.val)
  map_add' f g := Subtype.ext (map_add LinearMap.toMatrix' f.val g.val)
  map_smul' a f := Subtype.ext (map_smul LinearMap.toMatrix' a f.val)

section Transport

variable {V : Type w} [AddCommGroup V] [Module k V]
  {W : Type z} [AddCommGroup W] [Module k W]
  {sigma : Representation k G V} {tau : Representation k G W}

/-- Restrict an actual equivariant equivalence to its invariant subspaces. -/
def invariantsEquiv (e : Representation.Equiv sigma tau) : sigma.invariants ≃ₗ[k] tau.invariants where
  toFun x := ⟨e x, fun g =>
    (congrArg (fun f => f x.val) (e.isIntertwining' g)).symm.trans
      (congrArg e (x.property g))⟩
  invFun y := ⟨e.symm y, fun g =>
    (congrArg (fun f => f y.val) (e.symm.isIntertwining' g)).symm.trans
      (congrArg e.symm (y.property g))⟩
  left_inv x := Subtype.ext (e.toLinearEquiv.symm_apply_apply x)
  right_inv y := Subtype.ext (e.toLinearEquiv.apply_symm_apply y)
  map_add' x y := Subtype.ext (e.toLinearEquiv.map_add x y)
  map_smul' a x := Subtype.ext (e.toLinearEquiv.map_smul a x)

end Transport

/-- The tensor of two individual regular-unipotent source models has
the computed invariant space; one source is dualized exactly as in the input. -/
def tensorDualInvariantsEquiv (A B : FDRep k G)
    (hA : Representation.Equiv A.ρ rho) (hB : Representation.Equiv B.ρ rho) :
    Representation.invariants (tensor A (dualRepresentation B)).ρ ≃ₗ[k] jordanThreeCentralizer k :=
  (invariantsEquiv ((tensorEquiv (B := FDRep.of rho) hA
    (dualEquiv (B := FDRep.of rho) hB)).trans
    ((Representation.TensorProduct.comm rho rho.dual).trans
      (Representation.Equiv.dualTensorHom rho rho)))).trans (endomorphismInvariantsEquiv M)

/-- Include the original additive factor, which is trivial at zero. -/
def inputInvariantsEquiv (A B L : FDRep k G)
    (hA : Representation.Equiv A.ρ rho) (hB : Representation.Equiv B.ρ rho)
    (hL : Representation.Equiv L.ρ (Representation.trivial k G k)) :
    Representation.invariants (tensor (tensor A (dualRepresentation B)) L).ρ ≃ₗ[k] jordanThreeCentralizer k :=
  (invariantsEquiv ((tensorEquiv (A := tensor A (dualRepresentation B))
    (B := tensor A (dualRepresentation B)) (D := FDRep.of (Representation.trivial k G k))
    (Representation.Equiv.refl _) hL).trans
    (Representation.TensorProduct.rid k (tensor A (dualRepresentation B)).ρ))).trans
      (tensorDualInvariantsEquiv M A B hA hB)

include M in
theorem input_invariants_finrank (A B L : FDRep k G)
    (hA : Representation.Equiv A.ρ rho) (hB : Representation.Equiv B.ρ rho)
    (hL : Representation.Equiv L.ρ (Representation.trivial k G k)) :
    Module.finrank k (Representation.invariants (tensor (tensor A (dualRepresentation B)) L).ρ) = 3 := by
  rw [(inputInvariantsEquiv M A B L hA hB hL).finrank_eq, jordanThreeCentralizer_finrank]

end PrimeGap182.TypeIII.RegularUnipotentBoundary

#print axioms PrimeGap182.TypeIII.RegularUnipotentBoundary.regularMatrix_commutes_iff
#print axioms PrimeGap182.TypeIII.RegularUnipotentBoundary.endomorphism_invariants_iff
#print axioms PrimeGap182.TypeIII.RegularUnipotentBoundary.endomorphismInvariantsEquiv
#print axioms PrimeGap182.TypeIII.RegularUnipotentBoundary.invariantsEquiv
#print axioms PrimeGap182.TypeIII.RegularUnipotentBoundary.tensorDualInvariantsEquiv
#print axioms PrimeGap182.TypeIII.RegularUnipotentBoundary.inputInvariantsEquiv
#print axioms PrimeGap182.TypeIII.RegularUnipotentBoundary.input_invariants_finrank
