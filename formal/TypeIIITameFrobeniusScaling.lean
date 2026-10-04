import TypeIIIRegularUnipotentRepresentation
import TypeIIIRestrictionFrobenius

/-!
# Nilpotent Frobenius scaling from the actual inertia action

Compare the finite exponential at a nonzero tame value and twice that
value. This derives the Jordan-monodromy scaling from Frobenius/inertia
covariance. The transported source Frobenius is constructed from the
original operator and the individual-source inertia equivalence.
-/

noncomputable section
open scoped Matrix

namespace PrimeGap182.TypeIII.TameFrobeniusScaling

open RegularUnipotentRepresentation RegularUnipotentBoundary
open PublishedPhaseApplication

universe u v w
variable {k : Type u} [Field k] [CharZero k]

omit [CharZero k] in
/-- The literal regular action is the degree-two nilpotent exponential. -/
theorem exponentialMatrix_polynomial (t : k) :
    exponentialMatrix t = 1 + t • jordanThree k + (t ^ 2 / 2) • (jordanThree k) ^ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exponentialMatrix, regularMatrix, jordanThreeCoordinates, jordanThree,
      pow_two]

/-- Two exponential intertwining identities force the linear monodromy
identity. No matrix normal form or source scaling is assumed. -/
theorem scaling_of_exponentials (F : Matrix (Fin 3) (Fin 3) k) (r t : k) (ht : t ≠ 0)
    (h : F * exponentialMatrix t = exponentialMatrix (r * t) * F)
    (hdouble : F * exponentialMatrix (2 * t) = exponentialMatrix (r * (2 * t)) * F) :
    F * jordanThree k = r • (jordanThree k * F) := by
  simp only [exponentialMatrix_polynomial, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul] at h hdouble
  ext i j
  have h1 := congrArg (fun A : Matrix (Fin 3) (Fin 3) k => A i j) h
  have h2 := congrArg (fun A : Matrix (Fin 3) (Fin 3) k => A i j) hdouble
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h1 h2 ⊢
  apply mul_left_cancel₀ ht
  linear_combination 2 * h1 - (1 / 2 : k) * h2

variable {G : Type v} [Group G] (tame : G →* Multiplicative k)
  (htame : ∃ g, (tame g).toAdd ≠ 0)

include htame in
/-- The identities at g and g*g provide the two nonzero tame samples. -/
theorem scaling_of_tame_covariance (F : (Fin 3 → k) ≃ₗ[k] (Fin 3 → k))
    (phi : G →* G) (r : k)
    (htau : ∀ g, (tame (phi g)).toAdd = r * (tame g).toAdd)
    (hcov : ∀ g, F.toLinearMap.comp (tameRepresentation tame g) =
      (tameRepresentation tame (phi g)).comp F.toLinearMap) :
    LinearMap.toMatrix' F.toLinearMap * jordanThree k =
      r • (jordanThree k * LinearMap.toMatrix' F.toLinearMap) := by
  obtain ⟨g, hg⟩ := htame
  have he (g : G) : LinearMap.toMatrix' F.toLinearMap * exponentialMatrix (tame g).toAdd =
      exponentialMatrix (r * (tame g).toAdd) * LinearMap.toMatrix' F.toLinearMap := by
    have hc := hcov g
    change F.toLinearMap.comp (Matrix.toLin' (exponentialMatrix (tame g).toAdd)) =
      (Matrix.toLin' (exponentialMatrix (tame (phi g)).toAdd)).comp F.toLinearMap at hc
    have hh := congrArg LinearMap.toMatrix' hc
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', htau] using hh
  apply scaling_of_exponentials _ r _ hg (he g)
  have htgg : (tame (g * g)).toAdd = 2 * (tame g).toAdd := by
    rw [map_mul]
    change (tame g).toAdd + (tame g).toAdd = 2 * (tame g).toAdd
    ring
  simpa only [htgg] using he (g * g)

variable (V : FDRep k G)
  (e : Representation.Equiv V.ρ (tameRepresentation tame)) (Fr : V.V ≃ₗ[k] V.V)

/-- Transport the actual source Frobenius; it is not a separately
supplied matrix or a chosen operator with prescribed eigenvalues. -/
def sourceFrobenius : (Fin 3 → k) ≃ₗ[k] (Fin 3 → k) :=
  (e.toLinearEquiv.symm.trans Fr).trans e.toLinearEquiv

/-- Compatibility with the original source operator holds by construction. -/
theorem sourceFrobenius_natural (x : V.V) :
    e (Fr x) = sourceFrobenius tame V e Fr (e x) := by
  change e.toLinearEquiv (Fr x) =
    e.toLinearEquiv (Fr (e.toLinearEquiv.symm (e.toLinearEquiv x)))
  rw [e.toLinearEquiv.symm_apply_apply]


/-- Transport the general inertia/Frobenius square along the source
inertia equivalence; no second operator comparison is assumed. -/
theorem sourceFrobenius_covariance (phi : G →* G)
    (hcov : ∀ g x, Fr (V.ρ g x) = V.ρ (phi g) (Fr x)) (g : G) :
    (sourceFrobenius tame V e Fr).toLinearMap.comp (tameRepresentation tame g) =
      (tameRepresentation tame (phi g)).comp (sourceFrobenius tame V e Fr).toLinearMap := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := e.toLinearEquiv.surjective x
  have he (g : G) (y : V.V) : e (V.ρ g y) = tameRepresentation tame g (e y) :=
    LinearMap.congr_fun (e.isIntertwining' g) y
  change sourceFrobenius tame V e Fr (tameRepresentation tame g (e y)) =
    tameRepresentation tame (phi g) (sourceFrobenius tame V e Fr (e y))
  rw [← he g y, ← sourceFrobenius_natural, hcov g y, he,
    ← sourceFrobenius_natural]

include htame in
/-- The exact scaling required by the arithmetic boundary construction,
now derived from general covariance and the tame character law. -/
theorem sourceFrobenius_scaling (phi : G →* G) (r : k)
    (htau : ∀ g, (tame (phi g)).toAdd = r * (tame g).toAdd)
    (hcov : ∀ g x, Fr (V.ρ g x) = V.ρ (phi g) (Fr x)) :
    LinearMap.toMatrix' (sourceFrobenius tame V e Fr).toLinearMap * jordanThree k =
      r • (jordanThree k * LinearMap.toMatrix' (sourceFrobenius tame V e Fr).toLinearMap) :=
  scaling_of_tame_covariance tame htame (sourceFrobenius tame V e Fr) phi r htau
    (sourceFrobenius_covariance tame V e Fr phi hcov)

/-- The leading matrix coefficient follows from the eigenvalue on the
actual source invariant vector; no matrix-entry law is required. -/
theorem sourceFrobenius_leading (c : k)
    (hline : Fr (e.toLinearEquiv.symm (Pi.single 0 1)) =
      c • e.toLinearEquiv.symm (Pi.single 0 1)) :
    LinearMap.toMatrix' (sourceFrobenius tame V e Fr).toLinearMap 0 0 = c := by
  have h := congrArg e.toLinearEquiv hline
  simp only [map_smul, LinearEquiv.apply_symm_apply] at h
  have h0 := congrArg (fun x : Fin 3 → k => x 0) h
  simpa [LinearMap.toMatrix'_apply, sourceFrobenius] using h0

end PrimeGap182.TypeIII.TameFrobeniusScaling

#print axioms PrimeGap182.TypeIII.TameFrobeniusScaling.exponentialMatrix_polynomial
#print axioms PrimeGap182.TypeIII.TameFrobeniusScaling.scaling_of_exponentials
#print axioms PrimeGap182.TypeIII.TameFrobeniusScaling.scaling_of_tame_covariance
#print axioms PrimeGap182.TypeIII.TameFrobeniusScaling.sourceFrobenius
#print axioms PrimeGap182.TypeIII.TameFrobeniusScaling.sourceFrobenius_natural

#print axioms PrimeGap182.TypeIII.TameFrobeniusScaling.sourceFrobenius_covariance
#print axioms PrimeGap182.TypeIII.TameFrobeniusScaling.sourceFrobenius_scaling

#print axioms PrimeGap182.TypeIII.TameFrobeniusScaling.sourceFrobenius_leading
