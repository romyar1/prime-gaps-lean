import Mathlib

/-!
# The rank-three Jordan-model correction trace

This file computes an actual matrix centralizer and the trace of actual
conjugation on it. It does not identify Kloosterman inertia or Frobenius with
this linear-algebra model.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open scoped Matrix BigOperators

set_option maxHeartbeats 1000000

variable {k : Type*} [Field k]

/-- The nilpotent Jordan block with ones on the superdiagonal. -/
def jordanThree (k : Type*) [Field k] : Matrix (Fin 3) (Fin 3) k :=
  !![0, 1, 0; 0, 0, 1; 0, 0, 0]

/-- The actual centralizer as a submodule of the nine-dimensional matrix space. -/
def jordanThreeCentralizer (k : Type*) [Field k] : Submodule k (Matrix (Fin 3) (Fin 3) k) :=
  (Subalgebra.centralizer k {jordanThree k}).toSubmodule

theorem mem_jordanThreeCentralizer (A : Matrix (Fin 3) (Fin 3) k) :
    A ∈ jordanThreeCentralizer k ↔ jordanThree k * A = A * jordanThree k := by
  simp only [jordanThreeCentralizer, Subalgebra.mem_toSubmodule,
    Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]

/-- The three coordinates of an upper triangular Toeplitz matrix. -/
def jordanThreeCoordinates (a : Fin 3 → k) : Matrix (Fin 3) (Fin 3) k :=
  !![a 0, a 1, a 2; 0, a 0, a 1; 0, 0, a 0]

theorem jordanThree_sq : jordanThree k ^ 2 = !![0, 0, 1; 0, 0, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanThree, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]

theorem jordanThree_cube : jordanThree k ^ 3 = 0 := by
  rw [pow_succ, jordanThree_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanThree, Matrix.mul_apply, Fin.sum_univ_succ]

theorem jordanThreeCoordinates_eq_powers (a : Fin 3 → k) :
    jordanThreeCoordinates a = a 0 • (1 : Matrix (Fin 3) (Fin 3) k) +
      a 1 • jordanThree k + a 2 • jordanThree k ^ 2 := by
  rw [jordanThree_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanThreeCoordinates, jordanThree]

theorem jordanThreeCoordinates_mem (a : Fin 3 → k) :
    jordanThreeCoordinates a ∈ jordanThreeCentralizer k := by
  rw [mem_jordanThreeCentralizer]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanThreeCoordinates, jordanThree, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Solving the actual commutation equations determines every matrix entry. -/
theorem jordanThreeCentralizer_eq_coordinates (A : Matrix (Fin 3) (Fin 3) k)
    (hA : A ∈ jordanThreeCentralizer k) :
    A = jordanThreeCoordinates ![A 0 0, A 0 1, A 0 2] := by
  have h := (mem_jordanThreeCentralizer A).mp hA
  have h10 := congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M 0 0) h
  have h11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M 0 1) h
  have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M 0 2) h
  have h20 := congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M 1 0) h
  have h21 := congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M 2 2) h
  have h22 := congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M 1 2) h
  simp [jordanThree, Matrix.mul_apply, Fin.sum_univ_succ] at h10 h11 h12 h20 h21 h22
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanThreeCoordinates, h10, h11, h12, h20, h21.symm, h22]

/-- An actual linear equivalence, so the centralizer has exactly three
independent coordinates. -/
def jordanThreeCentralizerEquiv : (Fin 3 → k) ≃ₗ[k] jordanThreeCentralizer k where
  toFun a := ⟨jordanThreeCoordinates a, jordanThreeCoordinates_mem a⟩
  invFun A := ![A.val 0 0, A.val 0 1, A.val 0 2]
  left_inv a := by ext i; fin_cases i <;> rfl
  right_inv A := Subtype.ext (jordanThreeCentralizer_eq_coordinates A.val A.property).symm
  map_add' a b := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [jordanThreeCoordinates]
  map_smul' c a := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [jordanThreeCoordinates]

@[simp] theorem jordanThreeCentralizerEquiv_val (a : Fin 3 → k) :
    (jordanThreeCentralizerEquiv a).val = jordanThreeCoordinates a := rfl

theorem jordanThreeCentralizer_eq_span : jordanThreeCentralizer k =
    Submodule.span k {(1 : Matrix (Fin 3) (Fin 3) k), jordanThree k, jordanThree k ^ 2} := by
  apply le_antisymm
  · intro A hA
    rw [jordanThreeCentralizer_eq_coordinates A hA, jordanThreeCoordinates_eq_powers]
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · apply Submodule.span_le.mpr
    intro A hA
    apply (mem_jordanThreeCentralizer A).mpr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl | rfl
    all_goals simp [pow_two, Matrix.mul_assoc]

theorem jordanThreeCentralizer_finrank : Module.finrank k (jordanThreeCentralizer k) = 3 := by
  rw [← (jordanThreeCentralizerEquiv (k := k)).finrank_eq]
  simp

/-- The diagonal operator in the stated Jordan model. -/
def jordanThreeFrobenius (q : k) : Matrix (Fin 3) (Fin 3) k :=
  Matrix.diagonal ![1, q, q ^ 2]

theorem jordanThreeFrobenius_mul_inverse (q : k) (hq : q ≠ 0) :
    jordanThreeFrobenius q * jordanThreeFrobenius q⁻¹ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanThreeFrobenius, Matrix.mul_apply, Fin.sum_univ_succ, hq]

theorem jordanThreeFrobenius_inv (q : k) (hq : q ≠ 0) :
    (jordanThreeFrobenius q)⁻¹ = jordanThreeFrobenius q⁻¹ :=
  Matrix.inv_eq_right_inv (jordanThreeFrobenius_mul_inverse q hq)

/-- Conjugation by the actual matrix, using its actual matrix inverse. -/
def jordanThreeConjugation (q : k) :
    Matrix (Fin 3) (Fin 3) k →ₗ[k] Matrix (Fin 3) (Fin 3) k where
  toFun A := jordanThreeFrobenius q * A * (jordanThreeFrobenius q)⁻¹
  map_add' A B := by simp [mul_add, add_mul]
  map_smul' c A := by simp

@[simp] theorem jordanThreeConjugation_apply (q : k) (A : Matrix (Fin 3) (Fin 3) k) :
    jordanThreeConjugation q A =
      jordanThreeFrobenius q * A * (jordanThreeFrobenius q)⁻¹ := rfl

theorem jordanThreeConjugation_coordinates (q : k) (hq : q ≠ 0) (a : Fin 3 → k) :
    jordanThreeConjugation q (jordanThreeCoordinates a) =
      jordanThreeCoordinates ![a 0, q⁻¹ * a 1, q⁻¹ ^ 2 * a 2] := by
  rw [jordanThreeConjugation_apply, jordanThreeFrobenius_inv q hq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanThreeFrobenius, jordanThreeCoordinates,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
  all_goals field_simp [hq]

theorem jordanThreeConjugation_mem (q : k) (hq : q ≠ 0)
    (A : Matrix (Fin 3) (Fin 3) k) (hA : A ∈ jordanThreeCentralizer k) :
    jordanThreeConjugation q A ∈ jordanThreeCentralizer k := by
  rw [jordanThreeCentralizer_eq_coordinates A hA,
    jordanThreeConjugation_coordinates q hq]
  exact jordanThreeCoordinates_mem _

/-- The restriction of actual matrix conjugation to the actual centralizer. -/
def jordanThreeCentralizerConjugation (q : k) (hq : q ≠ 0) :
    jordanThreeCentralizer k →ₗ[k] jordanThreeCentralizer k where
  toFun A := ⟨jordanThreeConjugation q A.val,
    jordanThreeConjugation_mem q hq A.val A.property⟩
  map_add' A B := Subtype.ext ((jordanThreeConjugation q).map_add A.val B.val)
  map_smul' c A := Subtype.ext ((jordanThreeConjugation q).map_smul c A.val)

@[simp] theorem jordanThreeCentralizerConjugation_val (q : k) (hq : q ≠ 0)
    (A : jordanThreeCentralizer k) :
    (jordanThreeCentralizerConjugation q hq A).val =
      jordanThreeConjugation q A.val := rfl

theorem jordanThreeCentralizerConjugation_coordinates (q : k) (hq : q ≠ 0)
    (a : Fin 3 → k) :
    jordanThreeCentralizerConjugation q hq (jordanThreeCentralizerEquiv a) =
      jordanThreeCentralizerEquiv ![a 0, q⁻¹ * a 1, q⁻¹ ^ 2 * a 2] := by
  apply Subtype.ext
  exact jordanThreeConjugation_coordinates q hq a

/-- The restricted map is conjugate to the computed diagonal matrix. This is
proved from the matrix action; it is not the definition of the restricted map. -/
theorem jordanThreeCentralizerConjugation_eq_conj (q : k) (hq : q ≠ 0) :
    jordanThreeCentralizerConjugation q hq =
      jordanThreeCentralizerEquiv.conj
        (Matrix.toLin' (Matrix.diagonal ![1, q⁻¹, q⁻¹ ^ 2])) := by
  apply LinearMap.ext
  intro A
  obtain ⟨a, rfl⟩ := (jordanThreeCentralizerEquiv (k := k)).surjective A
  rw [jordanThreeCentralizerConjugation_coordinates q hq,
    LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  congr 1
  ext i
  fin_cases i <;> simp [Matrix.toLin'_apply, Matrix.mulVec_diagonal]

/-- The eigenvalue of conjugation on the nilpotent generator. -/
theorem jordanThreeConjugation_jordan (q : k) (hq : q ≠ 0) :
    jordanThreeConjugation q (jordanThree k) = q⁻¹ • jordanThree k := by
  have h := jordanThreeConjugation_coordinates q hq ![0, 1, 0]
  simpa [jordanThreeCoordinates, jordanThree] using h

theorem jordanThreeConjugation_jordan_sq (q : k) (hq : q ≠ 0) :
    jordanThreeConjugation q (jordanThree k ^ 2) = q⁻¹ ^ 2 • jordanThree k ^ 2 := by
  have h := jordanThreeConjugation_coordinates q hq ![0, 0, 1]
  simpa [jordanThreeCoordinates, jordanThree_sq] using h

/-- The actual linear trace is exactly the origin correction in the rank-three
Jordan model. -/
theorem jordanThreeCentralizerConjugation_trace (q : k) (hq : q ≠ 0) :
    LinearMap.trace k (jordanThreeCentralizer k)
      (jordanThreeCentralizerConjugation q hq) = 1 + q⁻¹ + q⁻¹ ^ 2 := by
  rw [jordanThreeCentralizerConjugation_eq_conj q hq, LinearMap.trace_conj',
    Matrix.trace_toLin'_eq]
  simp [Matrix.trace_diagonal, Fin.sum_univ_succ, add_assoc]

/-- Specialization to a positive rational-prime parameter in a characteristic
zero coefficient field; primality is not needed for this linear algebra. -/
theorem jordanThreeCentralizerConjugation_trace_nat [CharZero k] (p : ℕ) (hp : 0 < p) :
    LinearMap.trace k (jordanThreeCentralizer k)
      (jordanThreeCentralizerConjugation (p : k) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp))) =
        1 + (p : k)⁻¹ + (p : k)⁻¹ ^ 2 :=
  jordanThreeCentralizerConjugation_trace (p : k) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp))

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.jordanThreeCentralizer_eq_span
#print axioms PrimeGap182.TypeIII.jordanThreeCentralizer_finrank
#print axioms PrimeGap182.TypeIII.jordanThreeConjugation_coordinates
#print axioms PrimeGap182.TypeIII.jordanThreeConjugation_jordan
#print axioms PrimeGap182.TypeIII.jordanThreeConjugation_jordan_sq
#print axioms PrimeGap182.TypeIII.jordanThreeCentralizerConjugation_eq_conj
#print axioms PrimeGap182.TypeIII.jordanThreeCentralizerConjugation_trace
#print axioms PrimeGap182.TypeIII.jordanThreeCentralizerConjugation_trace_nat
