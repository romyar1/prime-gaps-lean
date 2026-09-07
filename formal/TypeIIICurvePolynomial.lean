import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! Elementary polynomial geometry for the Type III curve argument.

This isolated module is not part of the frozen analytic final closure. It
proves the converse Euler identity below the characteristic using the actual
`MvPolynomial.pderiv`, support, total degree, and `IsHomogeneous` predicate.
It introduces no sheaf or Fourier-support hypothesis and proves no local
Fourier bound. The source statement is `finite_exceptional_type_iii.tex`,
lines 320--325.
-/

noncomputable section

open scoped BigOperators
open MvPolynomial

namespace PrimeGap182.TypeIII.CurvePolynomial

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

variable {k σ : Type*} [Field k] [Fintype σ]

/-- The actual Euler differential operator on a finite variable set. -/
def eulerOperator (f : MvPolynomial σ k) : MvPolynomial σ k :=
  ∑ i : σ, X i * pderiv i f

/-- Euler differentiation multiplies each monomial by its actual degree. -/
theorem coeff_eulerOperator (f : MvPolynomial σ k) (d : σ →₀ ℕ) :
    coeff d (eulerOperator f) = (d.degree : k) * coeff d f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg =>
      simp [eulerOperator, map_add, mul_add, Finset.sum_add_distrib,
        coeff_add] at hf hg ⊢
      rw [hf, hg]
  | monomial m a =>
      rw [eulerOperator, (isHomogeneous_monomial a rfl).sum_X_mul_pderiv,
        coeff_smul, nsmul_eq_mul]
      by_cases h : d = m
      · subst d
        rfl
      · simp [coeff_monomial, Ne.symm h]

/-- Any nonzero coefficient in an Euler eigenvector has the eigenvalue's
degree in the coefficient field. -/
theorem degree_cast_of_euler_eigen {f : MvPolynomial σ k} {c : k}
    (hE : eulerOperator f = C c * f) {d : σ →₀ ℕ}
    (hd : coeff d f ≠ 0) : (d.degree : k) = c := by
  have h := congrArg (coeff d) hE
  rw [coeff_eulerOperator, coeff_C_mul] at h
  exact mul_right_cancel₀ hd h

theorem totalDegree_eulerOperator_le (f : MvPolynomial σ k) :
    (eulerOperator f).totalDegree ≤ f.totalDegree := by
  apply totalDegree_le_of_support_subset
  intro d hd
  rw [mem_support_iff, coeff_eulerOperator] at hd
  exact mem_support_iff.mpr (mul_ne_zero_iff.mp hd).2

/-- Divisibility by the polynomial already forces an Euler eigenrelation;
the quotient is proved constant from its actual total degree. -/
theorem euler_eigen_of_dvd {f : MvPolynomial σ k} (hf : f ≠ 0)
    (hdiv : f ∣ eulerOperator f) : ∃ c : k, eulerOperator f = C c * f := by
  by_cases hzero : eulerOperator f = 0
  · exact ⟨0, by simp [hzero]⟩
  obtain ⟨g, hg⟩ := hdiv
  have hg0 : g ≠ 0 := by
    intro h
    apply hzero
    rw [hg, h, mul_zero]
  have hd := totalDegree_eulerOperator_le f
  rw [hg, totalDegree_mul_of_isDomain hf hg0] at hd
  have hgd : g.totalDegree = 0 := by omega
  refine ⟨coeff 0 g, ?_⟩
  calc
    eulerOperator f = f * g := hg
    _ = f * C (coeff 0 g) := congrArg (fun q => f * q)
      (totalDegree_eq_zero_iff_eq_C.mp hgd)
    _ = C (coeff 0 g) * f := mul_comm _ _

private theorem homogeneous_of_euler_eigen_of_cast_inj
    {f : MvPolynomial σ k} {c : k} (hf : f ≠ 0)
    (hE : eulerOperator f = C c * f)
    (hinj : Set.InjOn (fun n : ℕ => (n : k)) (Set.Iic f.totalDegree)) :
    f.IsHomogeneous f.totalDegree ∧ c = (f.totalDegree : k) := by
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hf
  have hmdeg : m.degree ≤ f.totalDegree :=
    le_totalDegree (mem_support_iff.mpr hm)
  have hhom : f.IsHomogeneous m.degree := by
    intro d hd
    change Finsupp.weight (fun _ : σ => 1) d = m.degree
    rw [← Finsupp.degree_eq_weight_one]
    apply hinj (le_totalDegree (mem_support_iff.mpr hd)) hmdeg
    exact (degree_cast_of_euler_eigen hE hd).trans
      (degree_cast_of_euler_eigen hE hm).symm
  have hn := hhom.totalDegree hf
  exact ⟨hn ▸ hhom, by rw [hn]; exact (degree_cast_of_euler_eigen hE hm).symm⟩

/-- Converse Euler identity in characteristic zero, with no supplied degree. -/
theorem euler_eigen_isHomogeneous_charZero [CharZero k]
    {f : MvPolynomial σ k} {c : k} (hf : f ≠ 0)
    (hE : eulerOperator f = C c * f) :
    f.IsHomogeneous f.totalDegree ∧ c = (f.totalDegree : k) :=
  homogeneous_of_euler_eigen_of_cast_inj hf hE Nat.cast_injective.injOn

/-- Converse Euler identity in characteristic `p` strictly larger than the
actual total degree. The degree cutoff rules out Frobenius counterexamples. -/
theorem euler_eigen_isHomogeneous_charP (p : ℕ) [CharP k p]
    {f : MvPolynomial σ k} {c : k} (hf : f ≠ 0)
    (hp : f.totalDegree < p) (hE : eulerOperator f = C c * f) :
    f.IsHomogeneous f.totalDegree ∧ c = (f.totalDegree : k) := by
  apply homogeneous_of_euler_eigen_of_cast_inj hf hE
  intro a ha b hb hab
  exact CharP.natCast_injOn_Iio k p (ha.trans_lt hp) (hb.trans_lt hp) hab

/-- Literal two-variable form of the manuscript's Euler relation. -/
theorem bivariate_euler_isHomogeneous_charP (p : ℕ) [CharP k p]
    {f : MvPolynomial (Fin 2) k} {c : k} (hf : f ≠ 0)
    (hp : f.totalDegree < p)
    (hE : X 0 * pderiv 0 f + X 1 * pderiv 1 f = C c * f) :
    f.IsHomogeneous f.totalDegree ∧ c = (f.totalDegree : k) := by
  apply euler_eigen_isHomogeneous_charP p hf hp
  simpa only [eulerOperator, Fin.sum_univ_two] using hE

theorem bivariate_euler_isHomogeneous_charZero [CharZero k]
    {f : MvPolynomial (Fin 2) k} {c : k} (hf : f ≠ 0)
    (hE : X 0 * pderiv 0 f + X 1 * pderiv 1 f = C c * f) :
    f.IsHomogeneous f.totalDegree ∧ c = (f.totalDegree : k) := by
  apply euler_eigen_isHomogeneous_charZero hf
  simpa only [eulerOperator, Fin.sum_univ_two] using hE

/-- Specializing the second coordinate to one does not increase degree. -/
theorem dehomogenize_natDegree_le (f : MvPolynomial (Fin 2) k) :
    (MvPolynomial.aeval ![(Polynomial.X : Polynomial k), 1] f).natDegree ≤ f.totalDegree := by
  classical
  conv_lhs => rw [← f.support_sum_monomial_coeff, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  have hddeg : d 0 + d 1 ≤ f.totalDegree := by
    simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using le_totalDegree hd
  rw [MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_pow, mul_one]
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
    ((Nat.le_add_right _ _).trans hddeg)

/-- A nonzero homogeneous binary polynomial of positive degree over an
algebraically closed field has an actual nonzero linear homogeneous divisor. -/
theorem homogeneous_binary_has_linear_factor [IsAlgClosed k]
    {f : MvPolynomial (Fin 2) k} {n : ℕ} (hf : f ≠ 0)
    (hh : f.IsHomogeneous n) (hn : 0 < n) :
    ∃ l : MvPolynomial (Fin 2) k, l.IsHomogeneous 1 ∧ l ≠ 0 ∧ l ∣ f := by
  classical
  let p : Polynomial k := MvPolynomial.aeval ![Polynomial.X, 1] f
  have hpdegree : p.natDegree ≤ n :=
    (dehomogenize_natDegree_le f).trans hh.totalDegree_le
  have hpf : p.homogenize n = f :=
    Polynomial.homogenize_eq_of_isHomogeneous hh rfl
  have hp : p ≠ 0 := by
    intro hp0
    apply hf
    rw [← hpf, hp0, Polynomial.homogenize_zero]
  by_cases hpconstant : p.natDegree = 0
  · refine ⟨X 1, isHomogeneous_X k 1, X_ne_zero 1, ?_⟩
    rw [← hpf, Polynomial.eq_C_of_natDegree_eq_zero hpconstant,
      Polynomial.homogenize_C]
    refine ⟨C (p.coeff 0) * X 1 ^ (n - 1), ?_⟩
    have hpow : (X (1 : Fin 2) : MvPolynomial (Fin 2) k) ^ n =
        X 1 ^ (n - 1) * X 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hn]
    rw [hpow]
    ring
  · have hpdeg : p.degree ≠ 0 := by
      intro hpdeg
      exact hpconstant (Polynomial.natDegree_eq_of_degree_eq_some hpdeg)
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p hpdeg
    obtain ⟨q, hpq⟩ := (Polynomial.dvd_iff_isRoot.mpr ha)
    have hq : q ≠ 0 := by
      intro hq0
      apply hp
      rw [hpq, hq0, mul_zero]
    have hqd : q.natDegree ≤ n - 1 := by
      rw [hpq, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero a) hq,
        Polynomial.natDegree_X_sub_C] at hpdegree
      omega
    let l : MvPolynomial (Fin 2) k := X 0 - C a * X 1
    have hlh : l.IsHomogeneous 1 :=
      (isHomogeneous_X k 0).sub ((isHomogeneous_X k 1).C_mul a)
    have hl : l ≠ 0 := by
      intro hl0
      have he := congrArg (MvPolynomial.eval ![1, 0]) hl0
      simp [l] at he
    refine ⟨l, hlh, hl, q.homogenize (n - 1), ?_⟩
    calc
      f = p.homogenize n := hpf.symm
      _ = ((Polynomial.X - Polynomial.C a) * q).homogenize (1 + (n - 1)) := by
        rw [← hpq, Nat.add_sub_of_le hn]
      _ = (Polynomial.X - Polynomial.C a).homogenize 1 * q.homogenize (n - 1) :=
        Polynomial.homogenize_mul _ _ (by simp) hqd
      _ = l * q.homogenize (n - 1) := by simp [l]

/-- An irreducible homogeneous binary polynomial over an algebraically
closed field has degree one; this does not assume a supplied factorization. -/
theorem irreducible_homogeneous_binary_degree_one [IsAlgClosed k]
    {f : MvPolynomial (Fin 2) k} {n : ℕ} (hf : Irreducible f)
    (hh : f.IsHomogeneous n) : n = 1 := by
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    have hd0 : f.totalDegree = 0 := (hh.totalDegree hf.ne_zero).trans hn0
    have hconst := totalDegree_eq_zero_iff_eq_C.mp hd0
    have hc : coeff 0 f ≠ 0 := by
      intro hc
      apply hf.ne_zero
      rw [hconst, hc, map_zero]
    apply hf.not_isUnit
    rw [hconst]
    exact (isUnit_iff_ne_zero.mpr hc).map C
  obtain ⟨l, hlh, hl, hlf⟩ := homogeneous_binary_has_linear_factor hf.ne_zero hh hn
  have hld : l.totalDegree = 1 := hlh.totalDegree hl
  have hlnu : ¬IsUnit l := by
    intro hlu
    have := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hlu).2
    omega
  have hfl : f ∣ l := ((hf.dvd_iff.mp hlf).resolve_left hlnu).dvd
  have hdegree := totalDegree_le_of_dvd_of_isDomain hfl hl
  rw [hh.totalDegree hf.ne_zero, hld] at hdegree
  omega

/-- Actual coefficient representation of any homogeneous linear binary form. -/
theorem homogeneous_binary_degree_one_eq_linear
    {f : MvPolynomial (Fin 2) k} (hh : f.IsHomogeneous 1) :
    ∃ a b : k, f = C a * X 0 + C b * X 1 := by
  have hspan : f ∈ Submodule.span k (Set.range (X : Fin 2 → MvPolynomial (Fin 2) k)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact hh
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hspan
  refine ⟨c 0, c 1, ?_⟩
  simpa only [Fin.sum_univ_two, ← C_mul'] using hc.symm

/-- The geometric-irreducibility conclusion in actual polynomial terms. -/
theorem irreducible_homogeneous_binary_eq_linear [IsAlgClosed k]
    {f : MvPolynomial (Fin 2) k} {n : ℕ} (hf : Irreducible f)
    (hh : f.IsHomogeneous n) :
    ∃ a b : k, (a ≠ 0 ∨ b ≠ 0) ∧ f = C a * X 0 + C b * X 1 := by
  obtain rfl := irreducible_homogeneous_binary_degree_one hf hh
  obtain ⟨a, b, hab⟩ := homogeneous_binary_degree_one_eq_linear hh
  refine ⟨a, b, ?_, hab⟩
  by_contra h
  push Not at h
  apply hf.ne_zero
  simp [hab, h.1, h.2]

/-- The full polynomial consequence of the Euler eigenrelation in large
characteristic: a geometrically irreducible binary polynomial is a line. -/
theorem irreducible_bivariate_euler_eq_linear_charP [IsAlgClosed k]
    (p : ℕ) [CharP k p] {f : MvPolynomial (Fin 2) k} {c : k}
    (hf : Irreducible f) (hp : f.totalDegree < p)
    (hE : X 0 * pderiv 0 f + X 1 * pderiv 1 f = C c * f) :
    ∃ a b : k, (a ≠ 0 ∨ b ≠ 0) ∧ f = C a * X 0 + C b * X 1 :=
  irreducible_homogeneous_binary_eq_linear hf
    (bivariate_euler_isHomogeneous_charP p hf.ne_zero hp hE).1

theorem irreducible_bivariate_euler_eq_linear_charZero [IsAlgClosed k] [CharZero k]
    {f : MvPolynomial (Fin 2) k} {c : k} (hf : Irreducible f)
    (hE : X 0 * pderiv 0 f + X 1 * pderiv 1 f = C c * f) :
    ∃ a b : k, (a ≠ 0 ∨ b ≠ 0) ∧ f = C a * X 0 + C b * X 1 :=
  irreducible_homogeneous_binary_eq_linear hf
    (bivariate_euler_isHomogeneous_charZero hf.ne_zero hE).1

/-- Literal polynomial core of the all-tangents-through-zero deduction. -/
theorem irreducible_bivariate_dvd_euler_eq_linear_charP [IsAlgClosed k]
    (p : ℕ) [CharP k p] {f : MvPolynomial (Fin 2) k}
    (hf : Irreducible f) (hp : f.totalDegree < p)
    (hdiv : f ∣ X 0 * pderiv 0 f + X 1 * pderiv 1 f) :
    ∃ a b : k, (a ≠ 0 ∨ b ≠ 0) ∧ f = C a * X 0 + C b * X 1 := by
  obtain ⟨c, hc⟩ := euler_eigen_of_dvd hf.ne_zero
    (by simpa only [eulerOperator, Fin.sum_univ_two] using hdiv)
  apply irreducible_bivariate_euler_eq_linear_charP p hf hp
  simpa only [eulerOperator, Fin.sum_univ_two] using hc

theorem irreducible_bivariate_dvd_euler_eq_linear_charZero [IsAlgClosed k] [CharZero k]
    {f : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (hdiv : f ∣ X 0 * pderiv 0 f + X 1 * pderiv 1 f) :
    ∃ a b : k, (a ≠ 0 ∨ b ≠ 0) ∧ f = C a * X 0 + C b * X 1 := by
  obtain ⟨c, hc⟩ := euler_eigen_of_dvd hf.ne_zero
    (by simpa only [eulerOperator, Fin.sum_univ_two] using hdiv)
  apply irreducible_bivariate_euler_eq_linear_charZero hf
  simpa only [eulerOperator, Fin.sum_univ_two] using hc

#print axioms coeff_eulerOperator
#print axioms degree_cast_of_euler_eigen
#print axioms totalDegree_eulerOperator_le
#print axioms euler_eigen_of_dvd
#print axioms euler_eigen_isHomogeneous_charZero
#print axioms euler_eigen_isHomogeneous_charP
#print axioms bivariate_euler_isHomogeneous_charP
#print axioms bivariate_euler_isHomogeneous_charZero
#print axioms dehomogenize_natDegree_le
#print axioms homogeneous_binary_has_linear_factor
#print axioms irreducible_homogeneous_binary_degree_one
#print axioms homogeneous_binary_degree_one_eq_linear
#print axioms irreducible_homogeneous_binary_eq_linear
#print axioms irreducible_bivariate_euler_eq_linear_charP
#print axioms irreducible_bivariate_euler_eq_linear_charZero
#print axioms irreducible_bivariate_dvd_euler_eq_linear_charP
#print axioms irreducible_bivariate_dvd_euler_eq_linear_charZero

end PrimeGap182.TypeIII.CurvePolynomial
