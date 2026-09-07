import TypeIIICurveTangents
import TypeIIICurveDirection
import TypeIIICurveGauss

/-! Actual polynomial open sets on irreducible nonlinear plane curves.

These isolated statements use the actual zero locus, finite sets of points,
polynomial evaluation, and divisibility. They do not supply a sheaf lisse
locus, a projection, or a ramification theorem.
-/

noncomputable section
open scoped BigOperators
open MvPolynomial

namespace PrimeGap182.TypeIII.CurveOpen

open PrimeGap182.TypeIII.CurvePolynomial

set_option maxHeartbeats 600000

variable {k : Type*} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- A nonlinear polynomial cannot divide a vertical affine line equation. -/
theorem nonlinear_not_dvd_vertical {f : MvPolynomial (Fin 2) k}
    (hd : 1 < f.totalDegree) (c : k) : ¬f ∣ X 0 - C c := by
  have hl : (X (0 : Fin 2) - C c : MvPolynomial (Fin 2) k) ≠ 0 := by
    intro hl
    have h := congrArg (pderiv (0 : Fin 2)) hl
    simp at h
  intro hdiv
  have hfdeg := totalDegree_le_of_dvd_of_isDomain hdiv hl
  have hldeg : (X (0 : Fin 2) - C c : MvPolynomial (Fin 2) k).totalDegree ≤ 1 := by
    simpa only [totalDegree_X] using totalDegree_sub_C_le (X (0 : Fin 2)) c
  exact (not_le_of_gt hd) (hfdeg.trans hldeg)

/-- Every principal polynomial open subset of a nonlinear irreducible curve
has an actual point outside any specified finite set. -/
theorem exists_zeroLocus_nonzero_outside_finset
    {f g : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (hd : 1 < f.totalDegree) (hg : ¬f ∣ g) (S : Finset (Fin 2 → k)) :
    ∃ x : Fin 2 → k, x ∉ S ∧ eval x f = 0 ∧ eval x g ≠ 0 := by
  classical
  have hprime : Prime f := hf.prime
  let B : MvPolynomial (Fin 2) k := ∏ z ∈ S, (X 0 - C (z 0))
  have hB : ¬f ∣ B := hprime.not_dvd_finsetProd
    (fun z _ => nonlinear_not_dvd_vertical hd (z 0))
  have hprod : ¬f ∣ g * B := hprime.not_dvd_mul hg hB
  have hvan : ¬∀ x : Fin 2 → k, eval x f = 0 → eval x (g * B) = 0 := by
    intro hvan
    exact hprod (irreducible_dvd_of_zeroLocus_vanishing hf hvan)
  push Not at hvan
  obtain ⟨x, hxf, hx⟩ := hvan
  rw [map_mul, mul_ne_zero_iff] at hx
  refine ⟨x, ?_, hxf, hx.1⟩
  intro hxS
  apply hx.2
  dsimp [B]
  rw [map_prod]
  exact Finset.prod_eq_zero hxS (by simp)

/-- Removing finitely many points preserves polynomial density on the
actual curve: vanishing there still implies divisibility by its equation. -/
theorem irreducible_dvd_of_zeroLocus_vanishing_outside_finset
    {f g : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (hd : 1 < f.totalDegree) (S : Finset (Fin 2 → k))
    (hvan : ∀ x : Fin 2 → k, eval x f = 0 → x ∉ S → eval x g = 0) : f ∣ g := by
  by_contra hg
  obtain ⟨x, hxS, hxf, hxg⟩ := exists_zeroLocus_nonzero_outside_finset hf hd hg S
  exact hxg (hvan x hxf hxS)

theorem exists_zeroLocus_nonzero_outside_finite
    {f g : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (hd : 1 < f.totalDegree) (hg : ¬f ∣ g)
    (S : Set (Fin 2 → k)) (hS : S.Finite) :
    ∃ x : Fin 2 → k, x ∉ S ∧ eval x f = 0 ∧ eval x g ≠ 0 := by
  simpa only [Set.Finite.mem_toFinset] using
    exists_zeroLocus_nonzero_outside_finset hf hd hg hS.toFinset

/-- Finitely many nonempty polynomial open conditions can be imposed
simultaneously, still avoiding any specified finite point set. -/
theorem exists_zeroLocus_all_nonzero_outside_finset
    {ι : Type*} {f : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (hd : 1 < f.totalDegree) (S : Finset (Fin 2 → k))
    (I : Finset ι) (g : ι → MvPolynomial (Fin 2) k)
    (hg : ∀ i ∈ I, ¬f ∣ g i) :
    ∃ x : Fin 2 → k, x ∉ S ∧ eval x f = 0 ∧ ∀ i ∈ I, eval x (g i) ≠ 0 := by
  have hprime : Prime f := hf.prime
  have hprod : ¬f ∣ ∏ i ∈ I, g i := hprime.not_dvd_finsetProd hg
  obtain ⟨x, hxS, hxf, hxg⟩ := exists_zeroLocus_nonzero_outside_finset hf hd hprod S
  refine ⟨x, hxS, hxf, ?_⟩
  rw [map_prod, Finset.prod_ne_zero_iff] at hxg
  exact hxg

theorem nonlinear_not_dvd_euler_charZero [CharZero k]
    {f : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (hd : 1 < f.totalDegree) : ¬f ∣ eulerOperator f := by
  intro hdiv
  have hdiv' : f ∣ X 0 * pderiv 0 f + X 1 * pderiv 1 f := by
    simpa only [eulerOperator, Fin.sum_univ_two] using hdiv
  obtain ⟨a, b, _, hlin⟩ := irreducible_bivariate_dvd_euler_eq_linear_charZero hf hdiv'
  have hh : f.IsHomogeneous 1 := by
    rw [hlin]
    exact ((isHomogeneous_X k 0).C_mul a).add ((isHomogeneous_X k 1).C_mul b)
  exact (ne_of_gt hd) (hh.totalDegree hf.ne_zero)

theorem nonlinear_not_dvd_euler_charP (p : ℕ) [CharP k p]
    {f : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (hp : f.totalDegree < p) (hd : 1 < f.totalDegree) : ¬f ∣ eulerOperator f := by
  intro hdiv
  have hdiv' : f ∣ X 0 * pderiv 0 f + X 1 * pderiv 1 f := by
    simpa only [eulerOperator, Fin.sum_univ_two] using hdiv
  obtain ⟨a, b, _, hlin⟩ := irreducible_bivariate_dvd_euler_eq_linear_charP p hf hp hdiv'
  have hh : f.IsHomogeneous 1 := by
    rw [hlin]
    exact ((isHomogeneous_X k 0).C_mul a).add ((isHomogeneous_X k 1).C_mul b)
  exact (ne_of_gt hd) (hh.totalDegree hf.ne_zero)

private theorem exists_nonradial_regular_point_outside_of_not_dvd_euler
    {f : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (hd : 1 < f.totalDegree) (hE : ¬f ∣ eulerOperator f)
    (S : Finset (Fin 2 → k)) :
    ∃ x : Fin 2 → k, x ∉ S ∧ eval x f = 0 ∧
      x 0 * eval x (pderiv 0 f) + x 1 * eval x (pderiv 1 f) ≠ 0 ∧
      (eval x (pderiv 0 f) ≠ 0 ∨ eval x (pderiv 1 f) ≠ 0) := by
  obtain ⟨x, hxS, hxf, hxE⟩ := exists_zeroLocus_nonzero_outside_finset hf hd hE S
  have hxE' : x 0 * eval x (pderiv 0 f) + x 1 * eval x (pderiv 1 f) ≠ 0 := by
    simpa only [eulerOperator, Fin.sum_univ_two, map_add, map_mul, eval_X] using hxE
  refine ⟨x, hxS, hxf, hxE', ?_⟩
  by_contra h
  push Not at h
  exact hxE' (by rw [h.1, h.2, mul_zero, mul_zero, add_zero])

theorem exists_nonradial_regular_point_outside_finset_charZero [CharZero k]
    {f : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (hd : 1 < f.totalDegree) (S : Finset (Fin 2 → k)) :
    ∃ x : Fin 2 → k, x ∉ S ∧ eval x f = 0 ∧
      x 0 * eval x (pderiv 0 f) + x 1 * eval x (pderiv 1 f) ≠ 0 ∧
      (eval x (pderiv 0 f) ≠ 0 ∨ eval x (pderiv 1 f) ≠ 0) :=
  exists_nonradial_regular_point_outside_of_not_dvd_euler hf hd
    (nonlinear_not_dvd_euler_charZero hf hd) S

theorem exists_nonradial_regular_point_outside_finset_charP (p : ℕ) [CharP k p]
    {f : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (hp : f.totalDegree < p) (hd : 1 < f.totalDegree) (S : Finset (Fin 2 → k)) :
    ∃ x : Fin 2 → k, x ∉ S ∧ eval x f = 0 ∧
      x 0 * eval x (pderiv 0 f) + x 1 * eval x (pderiv 1 f) ≠ 0 ∧
      (eval x (pderiv 0 f) ≠ 0 ∨ eval x (pderiv 1 f) ≠ 0) :=
  exists_nonradial_regular_point_outside_of_not_dvd_euler hf hd
    (nonlinear_not_dvd_euler_charP p hf hp hd) S

private theorem exists_nonradial_regular_point_avoiding_of_not_dvd
    {ι : Type*} {f : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (hd : 1 < f.totalDegree) (hE : ¬f ∣ eulerOperator f)
    (S : Finset (Fin 2 → k)) (I : Finset ι) (a b : ι → k)
    (hD : ∀ i ∈ I, ¬f ∣ C (a i) * pderiv 0 f + C (b i) * pderiv 1 f) :
    ∃ x : Fin 2 → k, x ∉ S ∧ eval x f = 0 ∧
      x 0 * eval x (pderiv 0 f) + x 1 * eval x (pderiv 1 f) ≠ 0 ∧
      (eval x (pderiv 0 f) ≠ 0 ∨ eval x (pderiv 1 f) ≠ 0) ∧
      ∀ i ∈ I, a i * eval x (pderiv 0 f) + b i * eval x (pderiv 1 f) ≠ 0 := by
  have hprime : Prime f := hf.prime
  let P : MvPolynomial (Fin 2) k :=
    ∏ i ∈ I, (C (a i) * pderiv 0 f + C (b i) * pderiv 1 f)
  have hP : ¬f ∣ P := hprime.not_dvd_finsetProd hD
  obtain ⟨x, hxS, hxf, hx⟩ := exists_zeroLocus_nonzero_outside_finset hf hd
    (hprime.not_dvd_mul hE hP) S
  rw [map_mul, mul_ne_zero_iff] at hx
  have hxE : x 0 * eval x (pderiv 0 f) + x 1 * eval x (pderiv 1 f) ≠ 0 := by
    simpa only [eulerOperator, Fin.sum_univ_two, map_add, map_mul, eval_X] using hx.1
  refine ⟨x, hxS, hxf, hxE, ?_, ?_⟩
  · by_contra h
    push Not at h
    exact hxE (by rw [h.1, h.2, mul_zero, mul_zero, add_zero])
  · have hprod : (∏ i ∈ I,
        (a i * eval x (pderiv 0 f) + b i * eval x (pderiv 1 f))) ≠ 0 := by
      simpa only [P, map_prod, map_add, map_mul, eval_C] using hx.2
    exact Finset.prod_ne_zero_iff.mp hprod

/-- A nonradial regular point can avoid a finite set of points and all
specified nonzero tangent directions simultaneously, in characteristic zero. -/
theorem exists_nonradial_regular_point_avoiding_charZero [CharZero k]
    {ι : Type*} {f : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (hd : 1 < f.totalDegree) (S : Finset (Fin 2 → k))
    (I : Finset ι) (a b : ι → k) (hab : ∀ i ∈ I, a i ≠ 0 ∨ b i ≠ 0) :
    ∃ x : Fin 2 → k, x ∉ S ∧ eval x f = 0 ∧
      x 0 * eval x (pderiv 0 f) + x 1 * eval x (pderiv 1 f) ≠ 0 ∧
      (eval x (pderiv 0 f) ≠ 0 ∨ eval x (pderiv 1 f) ≠ 0) ∧
      ∀ i ∈ I, a i * eval x (pderiv 0 f) + b i * eval x (pderiv 1 f) ≠ 0 := by
  apply exists_nonradial_regular_point_avoiding_of_not_dvd hf hd
    (nonlinear_not_dvd_euler_charZero hf hd) S I a b
  intro i hi
  exact direction_not_dvd_of_nonlinear_charZero hf hd (a i) (b i) (hab i hi)

/-- The actual finite-open point assertion below the positive characteristic. -/
theorem exists_nonradial_regular_point_avoiding_charP
    (p : ℕ) [CharP k p] {ι : Type*} {f : MvPolynomial (Fin 2) k}
    (hf : Irreducible f) (hp : f.totalDegree < p) (hd : 1 < f.totalDegree)
    (S : Finset (Fin 2 → k)) (I : Finset ι) (a b : ι → k)
    (hab : ∀ i ∈ I, a i ≠ 0 ∨ b i ≠ 0) :
    ∃ x : Fin 2 → k, x ∉ S ∧ eval x f = 0 ∧
      x 0 * eval x (pderiv 0 f) + x 1 * eval x (pderiv 1 f) ≠ 0 ∧
      (eval x (pderiv 0 f) ≠ 0 ∨ eval x (pderiv 1 f) ≠ 0) ∧
      ∀ i ∈ I, a i * eval x (pderiv 0 f) + b i * eval x (pderiv 1 f) ≠ 0 := by
  apply exists_nonradial_regular_point_avoiding_of_not_dvd hf hd
    (nonlinear_not_dvd_euler_charP p hf hp hd) S I a b
  intro i hi
  exact direction_not_dvd_of_nonlinear_charP p hf hp hd (a i) (b i) (hab i hi)

theorem exists_nonradial_regular_point_avoiding_finite_charZero [CharZero k]
    {ι : Type*} {f : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (hd : 1 < f.totalDegree) (S : Set (Fin 2 → k)) (hS : S.Finite)
    (I : Finset ι) (a b : ι → k) (hab : ∀ i ∈ I, a i ≠ 0 ∨ b i ≠ 0) :
    ∃ x : Fin 2 → k, x ∉ S ∧ eval x f = 0 ∧
      x 0 * eval x (pderiv 0 f) + x 1 * eval x (pderiv 1 f) ≠ 0 ∧
      (eval x (pderiv 0 f) ≠ 0 ∨ eval x (pderiv 1 f) ≠ 0) ∧
      ∀ i ∈ I, a i * eval x (pderiv 0 f) + b i * eval x (pderiv 1 f) ≠ 0 := by
  simpa only [Set.Finite.mem_toFinset] using
    exists_nonradial_regular_point_avoiding_charZero hf hd hS.toFinset I a b hab

theorem exists_nonradial_regular_point_avoiding_finite_charP
    (p : ℕ) [CharP k p] {ι : Type*} {f : MvPolynomial (Fin 2) k}
    (hf : Irreducible f) (hp : f.totalDegree < p) (hd : 1 < f.totalDegree)
    (S : Set (Fin 2 → k)) (hS : S.Finite) (I : Finset ι) (a b : ι → k)
    (hab : ∀ i ∈ I, a i ≠ 0 ∨ b i ≠ 0) :
    ∃ x : Fin 2 → k, x ∉ S ∧ eval x f = 0 ∧
      x 0 * eval x (pderiv 0 f) + x 1 * eval x (pderiv 1 f) ≠ 0 ∧
      (eval x (pderiv 0 f) ≠ 0 ∨ eval x (pderiv 1 f) ≠ 0) ∧
      ∀ i ∈ I, a i * eval x (pderiv 0 f) + b i * eval x (pderiv 1 f) ≠ 0 := by
  simpa only [Set.Finite.mem_toFinset] using
    exists_nonradial_regular_point_avoiding_charP p hf hp hd hS.toFinset I a b hab

#print axioms nonlinear_not_dvd_vertical
#print axioms exists_zeroLocus_nonzero_outside_finset
#print axioms irreducible_dvd_of_zeroLocus_vanishing_outside_finset
#print axioms exists_zeroLocus_nonzero_outside_finite
#print axioms exists_zeroLocus_all_nonzero_outside_finset
#print axioms nonlinear_not_dvd_euler_charZero
#print axioms nonlinear_not_dvd_euler_charP
#print axioms exists_nonradial_regular_point_outside_finset_charZero
#print axioms exists_nonradial_regular_point_outside_finset_charP
#print axioms exists_nonradial_regular_point_avoiding_charZero
#print axioms exists_nonradial_regular_point_avoiding_charP
#print axioms exists_nonradial_regular_point_avoiding_finite_charZero
#print axioms exists_nonradial_regular_point_avoiding_finite_charP

end PrimeGap182.TypeIII.CurveOpen
