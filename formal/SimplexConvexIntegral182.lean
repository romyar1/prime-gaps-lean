import PrimeGaps186
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Exact barycentric first moments and the convex upper integral bound on a
four-dimensional simplex. These are analytic theorems, not numerical leaves. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Matrix

namespace PrimeGap182Analytic.Simplex

def standardFour : Set (Fin 4 → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

theorem standardFour_compact : IsCompact standardFour := by
  have hn : IsClosed {x : Fin 4 → ℝ | ∀ i, 0 ≤ x i} := by
    simpa only [Set.ofPred_forall] using
      (isClosed_iInter fun i : Fin 4 => isClosed_le continuous_const (continuous_apply i))
  have hc : IsClosed standardFour :=
    hn.inter (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
  apply isCompact_Icc.of_isClosed_subset hc
  intro x hx
  refine ⟨hx.1, fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2

theorem standardFour_measurable : MeasurableSet standardFour :=
  standardFour_compact.measurableSet

theorem standardFour_integral_one : (∫ _x in standardFour, (1 : ℝ)) = 1 / 24 := by
  simp only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, mul_one,
    Measure.real, standardFour, PrimeGap186.standardFourSimplex_volume]
  norm_num

/-- Change of variables for an actual nonsingular affine matrix in dimension four. -/
theorem setIntegral_affine_matrix (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (b : Fin 4 → ℝ) (S : Set (Fin 4 → ℝ)) (hS : MeasurableSet S)
    (f : (Fin 4 → ℝ) → ℝ) :
    (∫ y in (fun x => b + M *ᵥ x) '' S, f y) =
      |M.det| * ∫ x in S, f (b + M *ᵥ x) := by
  let L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) := (Matrix.toLin' M).toContinuousLinearMap
  have hderiv (x : Fin 4 → ℝ) (_hx : x ∈ S) :
      HasFDerivWithinAt (fun x => b + M *ᵥ x) L S x :=
    (L.hasFDerivAt.const_add b).hasFDerivWithinAt
  have hinj : Set.InjOn (fun x => b + M *ᵥ x) S := by
    intro x _ y _ hxy
    exact Matrix.mulVec_injective_of_det_ne_zero hM (add_left_cancel hxy)
  have hh := integral_image_eq_integral_abs_det_fderiv_smul
    (volume : Measure (Fin 4 → ℝ)) hS hderiv hinj f
  have hd : L.det = M.det := by
    change LinearMap.det (Matrix.toLin' M) = M.det
    exact LinearMap.det_toLin' M
  simpa only [hd, smul_eq_mul, integral_const_mul] using hh

def barycentricSwap (i : Fin 4) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun j => if j = i then 1 - ∑ k, x k else x j

def barycentricSwapMatrix (i : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun r c => if r = i then -1 else if r = c then 1 else 0

theorem barycentricSwap_eq_affine (i : Fin 4) (x : Fin 4 → ℝ) :
    barycentricSwap i x = Pi.single i 1 + barycentricSwapMatrix i *ᵥ x := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [barycentricSwap, barycentricSwapMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four] <;> ring

theorem barycentricSwapMatrix_det (i : Fin 4) : (barycentricSwapMatrix i).det = -1 := by
  rw [Matrix.det_succ_row (barycentricSwapMatrix i) 0]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply]
  fin_cases i <;> norm_num [barycentricSwapMatrix, Fin.succAbove, Fin.lt_def,
    Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE]

theorem barycentricSwap_sum (i : Fin 4) (x : Fin 4 → ℝ) :
    (∑ j, barycentricSwap i x j) = 1 - x i := by
  fin_cases i <;> simp [barycentricSwap, Fin.sum_univ_four] <;> ring

theorem barycentricSwap_self (i : Fin 4) (x : Fin 4 → ℝ) :
    barycentricSwap i x i = 1 - ∑ j, x j := by
  simp only [barycentricSwap, ite_true]

theorem barycentricSwap_involutive (i : Fin 4) : Function.Involutive (barycentricSwap i) := by
  intro x
  ext j
  by_cases hji : j = i
  · subst j
    rw [barycentricSwap_self, barycentricSwap_sum]
    ring
  · simp only [barycentricSwap, hji, ite_false]

theorem barycentricSwap_mem (i : Fin 4) (x : Fin 4 → ℝ) (hx : x ∈ standardFour) :
    barycentricSwap i x ∈ standardFour := by
  refine ⟨fun j => ?_, ?_⟩
  · by_cases hji : j = i
    · subst j
      simpa only [barycentricSwap, ite_true] using sub_nonneg.mpr hx.2
    · simpa only [barycentricSwap, hji, ite_false] using hx.1 j
  · rw [barycentricSwap_sum]
    linarith only [hx.1 i]

theorem barycentricSwap_image (i : Fin 4) : barycentricSwap i '' standardFour = standardFour := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact barycentricSwap_mem i x hx
  · intro x hx
    exact ⟨barycentricSwap i x, barycentricSwap_mem i x hx, barycentricSwap_involutive i x⟩

theorem standardFour_coordinate_eq_complement (i : Fin 4) :
    (∫ x in standardFour, x i) = ∫ x in standardFour, 1 - ∑ j, x j := by
  have hdet := barycentricSwapMatrix_det i
  have hh := setIntegral_affine_matrix (barycentricSwapMatrix i) (by rw [hdet]; norm_num)
    (Pi.single i 1) standardFour standardFour_measurable (fun x => x i)
  have hfun : (fun x => Pi.single i 1 + barycentricSwapMatrix i *ᵥ x) = barycentricSwap i :=
    funext fun x => (barycentricSwap_eq_affine i x).symm
  rw [hfun, barycentricSwap_image, hdet] at hh
  simpa only [← barycentricSwap_eq_affine, abs_neg, abs_one, one_mul,
    barycentricSwap, ite_true] using hh

theorem standardFour_barycentric_integral (i : Fin 5) :
    (∫ x in standardFour, (Fin.cons (1 - ∑ j, x j) x : Fin 5 → ℝ) i) = 1 / 120 := by
  have hcoord (j : Fin 4) : IntegrableOn (fun x : Fin 4 → ℝ => x j) standardFour :=
    (continuous_apply j).continuousOn.integrableOn_compact standardFour_compact
  have hsum : IntegrableOn (fun x : Fin 4 → ℝ => ∑ j, x j) standardFour :=
    (continuous_finsetSum _ fun j _ => continuous_apply j).continuousOn.integrableOn_compact
      standardFour_compact
  have hconst : IntegrableOn (fun _x : Fin 4 → ℝ => (1 : ℝ)) standardFour :=
    continuous_const.continuousOn.integrableOn_compact standardFour_compact
  have hcomp : (∫ x in standardFour, 1 - ∑ j, x j) = 1 / 120 := by
    have heq : (∫ x in standardFour, 1 - ∑ j, x j) =
        1 / 24 - ∑ j : Fin 4, ∫ x in standardFour, x j := by
      rw [integral_sub hconst hsum, standardFour_integral_one,
        integral_finsetSum _ (fun j _ => hcoord j)]
    simp_rw [standardFour_coordinate_eq_complement] at heq
    norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at heq
    linarith only [heq]
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using hcomp
  · simpa only [Fin.cons_succ] using (standardFour_coordinate_eq_complement j).trans hcomp

theorem barycentric_affine (v : Fin 5 → (Fin 4 → ℝ)) (x : Fin 4 → ℝ) :
    (∑ i : Fin 5, (Fin.cons (1 - ∑ j, x j) x : Fin 5 → ℝ) i • v i) =
      v 0 + (fun r c : Fin 4 => v c.succ r - v 0 r) *ᵥ x := by
  ext r
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

/-- The integral of a convex continuous function on a nondegenerate simplex
is at most its volume times the average of its five vertex values. -/
theorem convex_simplex_integral_upper (v : Fin 5 → (Fin 4 → ℝ))
    (hd : Matrix.det (fun r c : Fin 4 => v c.succ r - v 0 r) ≠ 0)
    (f : (Fin 4 → ℝ) → ℝ)
    (hf : ConvexOn ℝ (convexHull ℝ (Set.range v)) f)
    (hfc : ContinuousOn f (convexHull ℝ (Set.range v))) :
    (∫ x in convexHull ℝ (Set.range v), f x) ≤
      |Matrix.det (fun r c : Fin 4 => v c.succ r - v 0 r)| / 120 * ∑ i : Fin 5, f (v i) := by
  let M : Matrix (Fin 4) (Fin 4) ℝ := fun r c => v c.succ r - v 0 r
  let A : (Fin 4 → ℝ) → (Fin 4 → ℝ) := fun x => v 0 + M *ᵥ x
  let W (x : Fin 4 → ℝ) (i : Fin 5) : ℝ := (Fin.cons (1 - ∑ j, x j) x : Fin 5 → ℝ) i
  have hA : Set.MapsTo A standardFour (convexHull ℝ (Set.range v)) := by
    intro x hx
    rw [PrimeGap186.convexHull_five_eq_affine_image]
    exact ⟨x, hx, rfl⟩
  have hAc : Continuous A := by dsimp only [A]; fun_prop
  have hleft : IntegrableOn (fun x => f (A x)) standardFour :=
    (hfc.comp hAc.continuousOn hA).integrableOn_compact standardFour_compact
  have hwc (i : Fin 5) : Continuous (fun x => W x i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change Continuous (fun x : Fin 4 → ℝ => 1 - ∑ j, x j)
      fun_prop
    · change Continuous (fun x : Fin 4 → ℝ => x j)
      exact continuous_apply j
  have hright : IntegrableOn (fun x => ∑ i : Fin 5, W x i * f (v i)) standardFour :=
    (continuous_finsetSum _ fun i _ => (hwc i).mul continuous_const).continuousOn.integrableOn_compact
      standardFour_compact
  have hpoint (x : Fin 4 → ℝ) (hx : x ∈ standardFour) :
      f (A x) ≤ ∑ i : Fin 5, W x i * f (v i) := by
    have hp := hf.map_sum_le (t := Finset.univ) (w := W x) (p := v)
      (fun i _ => Fin.cases (sub_nonneg.mpr hx.2) (fun j => hx.1 j) i)
      (by simp [W])
      (fun i _ => subset_convexHull ℝ (Set.range v) (Set.mem_range_self i))
    simpa only [W, barycentric_affine, smul_eq_mul] using hp
  have hint := setIntegral_mono_on hleft hright standardFour_measurable hpoint
  have heval : (∫ x in standardFour, ∑ i : Fin 5, W x i * f (v i)) =
      (1 / 120 : ℝ) * ∑ i : Fin 5, f (v i) := by
    rw [integral_finsetSum Finset.univ (f := fun i x => W x i * f (v i)) (fun i _ =>
      ((hwc i).mul_const (f (v i))).continuousOn.integrableOn_compact standardFour_compact)]
    simp only [integral_mul_const, W, standardFour_barycentric_integral, Finset.mul_sum]
  rw [heval] at hint
  rw [PrimeGap186.convexHull_five_eq_affine_image]
  change (∫ x in (fun x => v 0 + M *ᵥ x) '' standardFour, f x) ≤ _
  rw [setIntegral_affine_matrix M hd (v 0) standardFour standardFour_measurable]
  have hh := mul_le_mul_of_nonneg_left hint (abs_nonneg M.det)
  simpa only [A, M, div_eq_mul_inv, mul_assoc, one_mul] using hh

#print axioms setIntegral_affine_matrix
#print axioms standardFour_barycentric_integral
#print axioms convex_simplex_integral_upper

end PrimeGap182Analytic.Simplex
