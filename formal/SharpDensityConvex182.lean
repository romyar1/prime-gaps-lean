import SharpIntegralGeometry182
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Convexity and positivity of the actual normalized sharp-deficit density. -/

noncomputable section
open Set PrimeGap186
open scoped BigOperators

namespace PrimeGap182Analytic.SharpMean

def positiveFive : Set (Fin 5 → ℝ) := {x | ∀ i, 0 < x i}

def reciprocalFiveProduct (x : Fin 5 → ℝ) : ℝ := (∏ i, x i)⁻¹

theorem positiveFive_convex : Convex ℝ positiveFive := by
  intro x hx y hy a b ha hb hab i
  exact convex_Ioi (0 : ℝ) (hx i) (hy i) ha hb hab

theorem reciprocalFiveProduct_exp (x : Fin 5 → ℝ) (hx : x ∈ positiveFive) :
    reciprocalFiveProduct x = Real.exp (-(∑ i, Real.log (x i))) := by
  rw [Real.exp_neg, Real.exp_sum]
  unfold reciprocalFiveProduct
  congr 1
  exact Finset.prod_congr rfl (fun i _ => (Real.exp_log (hx i)).symm)

theorem reciprocalFiveProduct_convex : ConvexOn ℝ positiveFive reciprocalFiveProduct := by
  refine ⟨positiveFive_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : a • x + b • y ∈ positiveFive := positiveFive_convex hx hy ha hb hab
  rw [reciprocalFiveProduct_exp _ hxy, reciprocalFiveProduct_exp _ hx,
    reciprocalFiveProduct_exp _ hy]
  have hlog : (∑ i : Fin 5, (a * Real.log (x i) + b * Real.log (y i))) ≤
      ∑ i : Fin 5, Real.log (a * x i + b * y i) := by
    apply Finset.sum_le_sum
    intro i _
    exact strictConcaveOn_log_Ioi.concaveOn.2 (hx i) (hy i) ha hb hab
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hlog
  change Real.exp (-(∑ i : Fin 5, Real.log (a * x i + b * y i))) ≤
    a * Real.exp (-(∑ i, Real.log (x i))) + b * Real.exp (-(∑ i, Real.log (y i)))
  calc
    _ ≤ Real.exp (a * (-(∑ i, Real.log (x i))) + b * (-(∑ i, Real.log (y i)))) :=
      Real.exp_le_exp.mpr (by linarith only [hlog])
    _ ≤ _ := convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

def normalizedFiveLinear : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ) where
  toFun z := Fin.snoc z (-(∑ i, z i))
  map_add' x y := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, Pi.add_apply, Finset.sum_add_distrib]
      ring
    · simp only [Fin.snoc_castSucc, Pi.add_apply]
  map_smul' a x := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        ← Finset.mul_sum]
      ring
    · simp only [Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

def normalizedFiveAffine : (Fin 4 → ℝ) →ᵃ[ℝ] (Fin 5 → ℝ) :=
  AffineMap.const ℝ (Fin 4 → ℝ) (fun _ => (1 / 5 : ℝ)) +
    (((1361 / 100000 : ℝ) • normalizedFiveLinear).toAffineMap)

theorem normalizedFiveAffine_apply (z : Fin 4 → ℝ) (i : Fin 5) :
    normalizedFiveAffine z i = (1 : ℝ) / 5 + (1361 : ℝ) / 100000 *
      (Fin.snoc z (-(∑ j, z j)) : Fin 5 → ℝ) i := rfl

def sharpNormalizedDensity (z : Fin 4 → ℝ) : ℝ :=
  reciprocalFiveProduct (normalizedFiveAffine z)

theorem sharpNormalizedDensity_eq (z : Fin 4 → ℝ) :
    sharpNormalizedDensity z =
      (∏ i : Fin 5, ((1 : ℝ) / 5 + (1361 : ℝ) / 100000 *
        (Fin.snoc z (-(∑ j, z j)) : Fin 5 → ℝ) i))⁻¹ := rfl

theorem sharpNormalizedDensity_convex :
    ConvexOn ℝ (normalizedFiveAffine ⁻¹' positiveFive) sharpNormalizedDensity :=
  reciprocalFiveProduct_convex.comp_affineMap normalizedFiveAffine

theorem continuous_normalizedFiveAffine_coordinate (i : Fin 5) :
    Continuous (fun z => normalizedFiveAffine z i) := by
  simp_rw [normalizedFiveAffine_apply]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    fun_prop
  · simp only [Fin.snoc_castSucc]
    fun_prop

theorem sharpNormalizedDensity_continuousOn :
    ContinuousOn sharpNormalizedDensity (normalizedFiveAffine ⁻¹' positiveFive) := by
  intro z hz
  have hp : ContinuousAt (fun z => ∏ i : Fin 5, normalizedFiveAffine z i) z :=
    (continuous_finsetProd _ fun i _ => continuous_normalizedFiveAffine_coordinate i).continuousAt
  exact (hp.inv₀ (Finset.prod_ne_zero_iff.mpr (fun i _ => (hz i).ne'))).continuousWithinAt

theorem normalizedFiveAffine_vertex_pos (j : Fin 7) (i : Fin 5) :
    0 < normalizedFiveAffine (minorantVertices1 j) i := by
  rw [normalizedFiveAffine_apply]
  fin_cases j <;> fin_cases i <;>
    norm_num [minorantVertices1, Fin.snoc, Fin.lastCases, Fin.sum_univ_four,
      Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Fin.castPred, Fin.castLT]

def sharpSimplex (j : Fin 3) : Set (Fin 4 → ℝ) :=
  convexHull ℝ (Set.range fun i : Fin 5 => minorantVertices1 (minorantSimplexIndices1 j i))

theorem sharpSimplex_subset_positive (j : Fin 3) :
    sharpSimplex j ⊆ normalizedFiveAffine ⁻¹' positiveFive := by
  apply convexHull_min
  · rintro z ⟨i, rfl⟩ k
    exact normalizedFiveAffine_vertex_pos _ k
  · exact positiveFive_convex.affine_preimage normalizedFiveAffine

theorem sharpNormalizedDensity_convex_simplex (j : Fin 3) :
    ConvexOn ℝ (sharpSimplex j) sharpNormalizedDensity :=
  sharpNormalizedDensity_convex.subset (sharpSimplex_subset_positive j) (convex_convexHull _ _)

theorem sharpNormalizedDensity_continuousOn_simplex (j : Fin 3) :
    ContinuousOn sharpNormalizedDensity (sharpSimplex j) :=
  sharpNormalizedDensity_continuousOn.mono (sharpSimplex_subset_positive j)

theorem sharpNormalizedDensity_pos (z : Fin 4 → ℝ)
    (hz : z ∈ normalizedFiveAffine ⁻¹' positiveFive) : 0 < sharpNormalizedDensity z :=
  inv_pos.mpr (Finset.prod_pos (fun i _ => hz i))

#print axioms reciprocalFiveProduct_convex
#print axioms sharpNormalizedDensity_convex_simplex
#print axioms sharpNormalizedDensity_continuousOn_simplex

end PrimeGap182Analytic.SharpMean
