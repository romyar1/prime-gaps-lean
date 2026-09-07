import Mathlib
import TypeIIICurvePolynomial

/-! From actual zero-locus equations to the polynomial tangent obstruction.

This uses Mathlib's Nullstellensatz. It does not assert that a Fourier support
curve has the tangent property or prove any local Fourier estimate.
-/

noncomputable section
open scoped Classical
open MvPolynomial

namespace PrimeGap182.TypeIII.CurvePolynomial

variable {k σ : Type*} [Field k] [IsAlgClosed k] [Fintype σ]

/-- A polynomial vanishing at every actual zero of an irreducible polynomial
is divisible by it, over the algebraically closed coefficient field. -/
theorem irreducible_dvd_of_zeroLocus_vanishing
    {f g : MvPolynomial σ k} (hf : Irreducible f)
    (hvan : ∀ x : σ → k, eval x f = 0 → eval x g = 0) : f ∣ g := by
  let I : Ideal (MvPolynomial σ k) := Ideal.span {f}
  let : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hf.prime
  have hmem : g ∈ vanishingIdeal k (zeroLocus k I) := by
    intro x hx
    have hfx := hx f (Ideal.mem_span_singleton_self f)
    change eval x f = 0 at hfx
    change eval x g = 0
    exact hvan x hfx
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hmem
  exact Ideal.mem_span_singleton.mp hmem

/-- The all-tangents-through-zero condition written at actual plane points
forces a line, with the characteristic restriction retained. -/
theorem irreducible_zeroLocus_radial_tangents_eq_linear_charP
    (p : ℕ) [CharP k p] {f : MvPolynomial (Fin 2) k}
    (hf : Irreducible f) (hp : f.totalDegree < p)
    (hvan : ∀ x : Fin 2 → k, eval x f = 0 →
      x 0 * eval x (pderiv 0 f) + x 1 * eval x (pderiv 1 f) = 0) :
    ∃ a b : k, (a ≠ 0 ∨ b ≠ 0) ∧ f = C a * X 0 + C b * X 1 := by
  apply irreducible_bivariate_dvd_euler_eq_linear_charP p hf hp
  apply irreducible_dvd_of_zeroLocus_vanishing hf
  intro x hx
  simpa only [eval_add, eval_mul, eval_X] using hvan x hx

theorem irreducible_zeroLocus_radial_tangents_eq_linear_charZero
    [CharZero k] {f : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (hvan : ∀ x : Fin 2 → k, eval x f = 0 →
      x 0 * eval x (pderiv 0 f) + x 1 * eval x (pderiv 1 f) = 0) :
    ∃ a b : k, (a ≠ 0 ∨ b ≠ 0) ∧ f = C a * X 0 + C b * X 1 := by
  apply irreducible_bivariate_dvd_euler_eq_linear_charZero hf
  apply irreducible_dvd_of_zeroLocus_vanishing hf
  intro x hx
  simpa only [eval_add, eval_mul, eval_X] using hvan x hx

/-- Thus a nonlinear irreducible bounded-degree curve has an actual regular
point whose tangent does not pass through the origin. -/
theorem exists_nonradial_regular_point_charP
    (p : ℕ) [CharP k p] {f : MvPolynomial (Fin 2) k}
    (hf : Irreducible f) (hp : f.totalDegree < p) (hd : 1 < f.totalDegree) :
    ∃ x : Fin 2 → k, eval x f = 0 ∧
      (x 0 * eval x (pderiv 0 f) + x 1 * eval x (pderiv 1 f) ≠ 0) ∧
      (eval x (pderiv 0 f) ≠ 0 ∨ eval x (pderiv 1 f) ≠ 0) := by
  have hn : ¬∀ x : Fin 2 → k, eval x f = 0 →
      x 0 * eval x (pderiv 0 f) + x 1 * eval x (pderiv 1 f) = 0 := by
    intro h
    obtain ⟨a, b, _, he⟩ := irreducible_zeroLocus_radial_tangents_eq_linear_charP p hf hp h
    have hdeg : f.totalDegree ≤ 1 := by
      rw [he]
      exact (totalDegree_add _ _).trans
        (max_le (by simpa only [totalDegree_C, totalDegree_X, zero_add] using
            totalDegree_mul (C a) (X (0 : Fin 2)))
          (by simpa only [totalDegree_C, totalDegree_X, zero_add] using
            totalDegree_mul (C b) (X (1 : Fin 2))))
    exact (not_le_of_gt hd) hdeg
  push Not at hn
  obtain ⟨x, hx, hE⟩ := hn
  refine ⟨x, hx, hE, ?_⟩
  by_contra h
  push Not at h
  exact hE (by rw [h.1, h.2, mul_zero, mul_zero, add_zero])

#print axioms irreducible_dvd_of_zeroLocus_vanishing
#print axioms irreducible_zeroLocus_radial_tangents_eq_linear_charP
#print axioms irreducible_zeroLocus_radial_tangents_eq_linear_charZero
#print axioms exists_nonradial_regular_point_charP

end PrimeGap182.TypeIII.CurvePolynomial
