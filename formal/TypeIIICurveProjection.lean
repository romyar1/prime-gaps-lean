import TypeIIICurvePolynomial
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.FieldDivision

/-! Actual generic linear projection polynomial and its degree.

This isolated module constructs `f(s-z*T,T)` over actual rational-function
fields. Polynomial degree is not a substitute for a geometric finiteness or
ramification theorem; no such theorem is asserted here.
-/

noncomputable section
open scoped BigOperators
open MvPolynomial

namespace PrimeGap182.TypeIII.CurveProjection

set_option maxHeartbeats 600000

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The literal projection polynomial `f(s-z*T,T)` after coefficient extension. -/
def projectionPolynomial (f : MvPolynomial (Fin 2) k) (z s : K) : Polynomial K :=
  MvPolynomial.aeval ![Polynomial.C s - Polynomial.C z * Polynomial.X, Polynomial.X] f

theorem eval_projectionPolynomial (f : MvPolynomial (Fin 2) k) (z s t : K) :
    Polynomial.eval t (projectionPolynomial f z s) =
      MvPolynomial.aeval ![s - z * t, t] f := by
  change ((Polynomial.aeval t : Polynomial K →ₐ[K] K).restrictScalars k)
    (MvPolynomial.aeval _ f) = _
  rw [MvPolynomial.comp_aeval_apply]
  apply congrArg (fun v : Fin 2 → K => MvPolynomial.aeval v f)
  funext i
  fin_cases i <;> simp

private theorem affine_natDegree_le (z s : K) :
    (Polynomial.C s - Polynomial.C z * Polynomial.X).natDegree ≤ 1 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  exact max_le (by simp)
    ((Polynomial.natDegree_C_mul_le z Polynomial.X).trans Polynomial.natDegree_X_le)

theorem projectionPolynomial_monomial (d : Fin 2 →₀ ℕ) (c : k) (z s : K) :
    projectionPolynomial (monomial d c) z s =
      Polynomial.C (algebraMap k K c) *
        (Polynomial.C s - Polynomial.C z * Polynomial.X) ^ d 0 * Polynomial.X ^ d 1 := by
  rw [projectionPolynomial, MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Polynomial.algebraMap_apply, mul_assoc]

private theorem natDegree_monomial_projection_le (u v : ℕ) (c z s : K) :
    (Polynomial.C c * (Polynomial.C s - Polynomial.C z * Polynomial.X) ^ u *
      Polynomial.X ^ v).natDegree ≤ u + v := by
  apply Polynomial.natDegree_mul_le_of_le _ (by simp)
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    (by simpa using Polynomial.natDegree_pow_le_of_le u (affine_natDegree_le z s))

/-- The degree bound holds for every slope and intercept, generic or not. -/
theorem natDegree_projectionPolynomial_le (f : MvPolynomial (Fin 2) k) (z s : K) :
    (projectionPolynomial f z s).natDegree ≤ f.totalDegree := by
  classical
  unfold projectionPolynomial
  conv_lhs => rw [← f.support_sum_monomial_coeff, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  change (projectionPolynomial (monomial d (coeff d f)) z s).natDegree ≤ _
  rw [projectionPolynomial_monomial]
  apply (natDegree_monomial_projection_le _ _ _ z s).trans
  simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using le_totalDegree hd

private theorem coeff_monomial_projection (u v N : ℕ) (c z s : K)
    (hN : u + v ≤ N) :
    (Polynomial.C c * (Polynomial.C s - Polynomial.C z * Polynomial.X) ^ u *
      Polynomial.X ^ v).coeff N = if u + v = N then c * (-z) ^ u else 0 := by
  by_cases h : u + v = N
  · subst N
    rw [ite_eq_left rfl, Polynomial.coeff_mul_add_eq_of_natDegree_le
      ((Polynomial.natDegree_C_mul_le _ _).trans
        (by simpa using Polynomial.natDegree_pow_le_of_le u (affine_natDegree_le z s)))
      (by simp), Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one]
    have hp := Polynomial.coeff_pow_of_natDegree_le (m := u) (affine_natDegree_le z s)
    simpa using congrArg (fun t : K => c * t) hp
  · rw [ite_eq_right h]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      ((natDegree_monomial_projection_le u v c z s).trans_lt (lt_of_le_of_ne hN h))

/-- The top bounded-degree coefficient is the actual homogeneous part
evaluated at the direction `(-z,1)`; it is independent of the intercept. -/
theorem coeff_projectionPolynomial_of_totalDegree_le
    (f : MvPolynomial (Fin 2) k) (z s : K) (N : ℕ) (hN : f.totalDegree ≤ N) :
    (projectionPolynomial f z s).coeff N =
      MvPolynomial.aeval ![-z, (1 : K)] (homogeneousComponent N f) := by
  classical
  unfold projectionPolynomial
  conv_lhs => rw [← f.support_sum_monomial_coeff, map_sum, Polynomial.finsetSum_coeff]
  rw [homogeneousComponent_apply, map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  have hdN : d 0 + d 1 ≤ N := by
    apply le_trans _ hN
    simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using le_totalDegree hd
  change (projectionPolynomial (monomial d (coeff d f)) z s).coeff N = _
  rw [projectionPolynomial_monomial, coeff_monomial_projection _ _ _ _ z s hdN]
  have hddeg : d.degree = d 0 + d 1 := by
    simp only [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  rw [hddeg]
  split_ifs with he
  · rw [MvPolynomial.aeval_monomial,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp
  · rfl

/-- A nonzero polynomial has a nonzero homogeneous component at its actual
total degree. -/
theorem topHomogeneousComponent_ne_zero {f : MvPolynomial (Fin 2) k} (hf : f ≠ 0) :
    homogeneousComponent f.totalDegree f ≠ 0 := by
  classical
  obtain ⟨d, hd, hdegree⟩ := f.support.exists_mem_eq_sup
    (by simpa using hf) (fun d => d.degree)
  have hddegree : d.degree = f.totalDegree := by
    change d.sum (fun _ e => e) = f.support.sup (fun e => e.sum (fun _ n => n))
    exact hdegree.symm
  intro hzero
  have h := congrArg (MvPolynomial.coeff d) hzero
  rw [coeff_homogeneousComponent, ite_eq_left hddegree, coeff_zero] at h
  exact (mem_support_iff.mp hd) h

/-- The genuine univariate dehomogenization of the top homogeneous part. -/
def topDirectionPolynomial (f : MvPolynomial (Fin 2) k) : Polynomial k :=
  MvPolynomial.aeval ![Polynomial.X, 1] (homogeneousComponent f.totalDegree f)

theorem topDirectionPolynomial_ne_zero {f : MvPolynomial (Fin 2) k} (hf : f ≠ 0) :
    topDirectionPolynomial f ≠ 0 := by
  have hhom := homogeneousComponent_isHomogeneous f.totalDegree f
  have hrec : (topDirectionPolynomial f).homogenize f.totalDegree =
      homogeneousComponent f.totalDegree f :=
    Polynomial.homogenize_eq_of_isHomogeneous hhom rfl
  intro hzero
  apply topHomogeneousComponent_ne_zero hf
  rw [← hrec, hzero, Polynomial.homogenize_zero]

theorem aeval_topDirectionPolynomial (f : MvPolynomial (Fin 2) k) (z : K) :
    Polynomial.aeval (-z) (topDirectionPolynomial f) =
      MvPolynomial.aeval ![-z, (1 : K)] (homogeneousComponent f.totalDegree f) := by
  unfold topDirectionPolynomial
  rw [MvPolynomial.comp_aeval_apply]
  apply congrArg (fun v : Fin 2 → K => MvPolynomial.aeval v (homogeneousComponent f.totalDegree f))
  funext i
  fin_cases i <;> simp

private theorem transcendental_neg {z : K} (hz : Transcendental k z) :
    Transcendental k (-z) := by
  rw [transcendental_iff] at hz ⊢
  intro q hq
  have hcomp : Polynomial.aeval z (q.comp (-Polynomial.X)) = 0 := by
    rw [Polynomial.aeval_comp]
    simpa using hq
  have hzero := hz _ hcomp
  have h := congrArg (fun p : Polynomial k => p.comp (-Polynomial.X)) hzero
  simpa only [Polynomial.comp_neg_X_comp_neg_X, Polynomial.zero_comp] using h

theorem topCoefficient_projectionPolynomial_ne_zero
    {f : MvPolynomial (Fin 2) k} (hf : f ≠ 0) {z : K}
    (hz : Transcendental k z) (s : K) :
    (projectionPolynomial f z s).coeff f.totalDegree ≠ 0 := by
  rw [coeff_projectionPolynomial_of_totalDegree_le f z s f.totalDegree le_rfl,
    ← aeval_topDirectionPolynomial]
  intro hzero
  exact topDirectionPolynomial_ne_zero hf
    ((transcendental_iff.mp (transcendental_neg hz)) _ hzero)

/-- Exact degree for a transcendental slope and any intercept. -/
theorem natDegree_projectionPolynomial_eq
    {f : MvPolynomial (Fin 2) k} (hf : f ≠ 0) {z : K}
    (hz : Transcendental k z) (s : K) :
    (projectionPolynomial f z s).natDegree = f.totalDegree :=
  Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (natDegree_projectionPolynomial_le f z s)
    (topCoefficient_projectionPolynomial_ne_zero hf hz s)

theorem projectionPolynomial_ne_zero
    {f : MvPolynomial (Fin 2) k} (hf : f ≠ 0) {z : K}
    (hz : Transcendental k z) (s : K) : projectionPolynomial f z s ≠ 0 := by
  intro hzero
  have h := topCoefficient_projectionPolynomial_ne_zero hf hz s
  simp [hzero] at h

theorem leadingCoeff_projectionPolynomial
    {f : MvPolynomial (Fin 2) k} (hf : f ≠ 0) {z : K}
    (hz : Transcendental k z) (s : K) :
    (projectionPolynomial f z s).leadingCoeff =
      Polynomial.aeval (-z) (topDirectionPolynomial f) := by
  rw [Polynomial.leadingCoeff, natDegree_projectionPolynomial_eq hf hz s,
    coeff_projectionPolynomial_of_totalDegree_le f z s f.totalDegree le_rfl,
    aeval_topDirectionPolynomial]

/-- Monic rescaling of the actual projection polynomial. -/
def monicProjectionPolynomial (f : MvPolynomial (Fin 2) k) (z s : K) : Polynomial K :=
  Polynomial.C (projectionPolynomial f z s).leadingCoeff⁻¹ * projectionPolynomial f z s

theorem monic_monicProjectionPolynomial
    {f : MvPolynomial (Fin 2) k} (hf : f ≠ 0) {z : K}
    (hz : Transcendental k z) (s : K) : (monicProjectionPolynomial f z s).Monic := by
  apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
  exact inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr (projectionPolynomial_ne_zero hf hz s))

theorem natDegree_monicProjectionPolynomial_eq
    {f : MvPolynomial (Fin 2) k} (hf : f ≠ 0) {z : K}
    (hz : Transcendental k z) (s : K) :
    (monicProjectionPolynomial f z s).natDegree = f.totalDegree := by
  rw [monicProjectionPolynomial, Polynomial.natDegree_C_mul
    (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr (projectionPolynomial_ne_zero hf hz s)))]
  exact natDegree_projectionPolynomial_eq hf hz s

theorem eval_monicProjectionPolynomial_eq_zero_iff
    {f : MvPolynomial (Fin 2) k} (hf : f ≠ 0) {z : K}
    (hz : Transcendental k z) (s t : K) :
    Polynomial.eval t (monicProjectionPolynomial f z s) = 0 ↔
      Polynomial.eval t (projectionPolynomial f z s) = 0 := by
  rw [monicProjectionPolynomial, Polynomial.eval_mul, Polynomial.eval_C]
  exact mul_eq_zero_iff_left
    (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr (projectionPolynomial_ne_zero hf hz s)))

section ActualGenericField

variable (k) in
/-- The concrete field `k(z)(s)` of two independent rational-function variables. -/
abbrev ProjectionField := RatFunc (RatFunc k)

variable (k) in
def genericSlope : ProjectionField k := RatFunc.C (RatFunc.X : RatFunc k)

variable (k) in
def genericIntercept : ProjectionField k := RatFunc.X

theorem genericSlope_transcendental : Transcendental k (genericSlope k) := by
  change Transcendental k
    (algebraMap (RatFunc k) (ProjectionField k) (RatFunc.X : RatFunc k))
  rw [transcendental_algebraMap_iff (algebraMap (RatFunc k) (ProjectionField k)).injective]
  exact RatFunc.transcendental_X

/-- The outer variable is transcendental even over the full inner rational-function field. -/
theorem genericIntercept_transcendental :
    Transcendental (RatFunc k) (genericIntercept k) := RatFunc.transcendental_X

def genericProjectionPolynomial (f : MvPolynomial (Fin 2) k) : Polynomial (ProjectionField k) :=
  projectionPolynomial f (genericSlope k) (genericIntercept k)

theorem genericProjectionPolynomial_ne_zero
    {f : MvPolynomial (Fin 2) k} (hf : f ≠ 0) : genericProjectionPolynomial f ≠ 0 :=
  projectionPolynomial_ne_zero hf genericSlope_transcendental (genericIntercept k)

/-- No algebraic independence or unspecified coefficient polynomial is an
input: both rational-function variables and the substitution are explicit. -/
theorem natDegree_genericProjectionPolynomial
    {f : MvPolynomial (Fin 2) k} (hf : f ≠ 0) :
    (genericProjectionPolynomial f).natDegree = f.totalDegree :=
  natDegree_projectionPolynomial_eq hf genericSlope_transcendental (genericIntercept k)

theorem degree_genericProjectionPolynomial
    {f : MvPolynomial (Fin 2) k} (hf : f ≠ 0) :
    (genericProjectionPolynomial f).degree = (f.totalDegree : WithBot ℕ) := by
  rw [Polynomial.degree_eq_natDegree (genericProjectionPolynomial_ne_zero hf),
    natDegree_genericProjectionPolynomial hf]

theorem leadingCoeff_genericProjectionPolynomial
    {f : MvPolynomial (Fin 2) k} (hf : f ≠ 0) :
    (genericProjectionPolynomial f).leadingCoeff =
      Polynomial.aeval (-genericSlope k) (topDirectionPolynomial f) :=
  leadingCoeff_projectionPolynomial hf genericSlope_transcendental (genericIntercept k)

theorem genericProjection_monic_rescaling
    {f : MvPolynomial (Fin 2) k} (hf : f ≠ 0) :
    (monicProjectionPolynomial f (genericSlope k) (genericIntercept k)).Monic ∧
      (monicProjectionPolynomial f (genericSlope k) (genericIntercept k)).natDegree =
        f.totalDegree :=
  ⟨monic_monicProjectionPolynomial hf genericSlope_transcendental (genericIntercept k),
    natDegree_monicProjectionPolynomial_eq hf genericSlope_transcendental (genericIntercept k)⟩

end ActualGenericField

#print axioms eval_projectionPolynomial
#print axioms projectionPolynomial_monomial
#print axioms natDegree_projectionPolynomial_le
#print axioms coeff_projectionPolynomial_of_totalDegree_le
#print axioms topHomogeneousComponent_ne_zero
#print axioms topDirectionPolynomial_ne_zero
#print axioms aeval_topDirectionPolynomial
#print axioms topCoefficient_projectionPolynomial_ne_zero
#print axioms natDegree_projectionPolynomial_eq
#print axioms projectionPolynomial_ne_zero
#print axioms leadingCoeff_projectionPolynomial
#print axioms monic_monicProjectionPolynomial
#print axioms natDegree_monicProjectionPolynomial_eq
#print axioms eval_monicProjectionPolynomial_eq_zero_iff
#print axioms genericSlope_transcendental
#print axioms genericIntercept_transcendental
#print axioms genericProjectionPolynomial_ne_zero
#print axioms natDegree_genericProjectionPolynomial
#print axioms degree_genericProjectionPolynomial
#print axioms leadingCoeff_genericProjectionPolynomial
#print axioms genericProjection_monic_rescaling

end PrimeGap182.TypeIII.CurveProjection
