import SimplexConvexIntegral182
import SharpDensityValues182
import SharpDeficitMargin182

/-! A proved upper bound for the actual sharp-minorant deficit. The exact
three-simplex integral is bounded using convexity and rational vertex values.
No numerical integral hypothesis is used for this bound.
-/

noncomputable section
open MeasureTheory Set PrimeGap186
open scoped BigOperators

namespace PrimeGap182Analytic.SharpMean

theorem sharpSimplex_compact (j : Fin 3) : IsCompact (sharpSimplex j) :=
  (Set.finite_range _).isCompact_convexHull ℝ

theorem sharpNormalizedDensity_integrable_simplex (j : Fin 3) :
    IntegrableOn sharpNormalizedDensity (sharpSimplex j) :=
  (sharpNormalizedDensity_continuousOn_simplex j).integrableOn_compact (sharpSimplex_compact j)

theorem sharpNormalizedDensity_integral_sum :
    (∫ z in sharpNormalizedRegion, sharpNormalizedDensity z) =
      ∑ j : Fin 3, ∫ z in sharpSimplex j, sharpNormalizedDensity z := by
  have hf := integrableOn_iUnion_of_summable_integral_norm
    sharpNormalizedDensity_integrable_simplex (hasSum_fintype _).summable
  rw [sharpNormalizedRegion_eq_simplices]
  change (∫ z in ⋃ j : Fin 3, sharpSimplex j, sharpNormalizedDensity z) = _
  rw [integral_iUnion_ae
    (fun j => (sharpSimplex_compact j).measurableSet.nullMeasurableSet)
    minorant_simplex1_pairwise_aedisjoint hf, tsum_fintype]

def sharpSimplexConvexUpper (j : Fin 3) : ℝ :=
  |(![-125 / 216, 625 / 864, -625 / 288] : Fin 3 → ℝ) j| / 120 *
    ∑ i : Fin 5, sharpNormalizedDensity (minorantVertices1 (minorantSimplexIndices1 j i))

theorem sharpSimplex_integral_le (j : Fin 3) :
    (∫ z in sharpSimplex j, sharpNormalizedDensity z) ≤ sharpSimplexConvexUpper j := by
  let v : Fin 5 → (Fin 4 → ℝ) := fun i => minorantVertices1 (minorantSimplexIndices1 j i)
  have hd := minorantSimplex1_edge_det j
  change Matrix.det (fun r c : Fin 4 => v c.succ r - v 0 r) =
    (![-125 / 216, 625 / 864, -625 / 288] : Fin 3 → ℝ) j at hd
  have hd0 : Matrix.det (fun r c : Fin 4 => v c.succ r - v 0 r) ≠ 0 := by
    rw [hd]
    fin_cases j <;> norm_num
  have hh := Simplex.convex_simplex_integral_upper v hd0 sharpNormalizedDensity
    (sharpNormalizedDensity_convex_simplex j) (sharpNormalizedDensity_continuousOn_simplex j)
  rw [hd] at hh
  simpa only [sharpSimplexConvexUpper, sharpSimplex, v] using hh

theorem sharpSimplex_rational_upper :
    6 * ((1361 : ℝ) / 100000) ^ 4 * (∑ j : Fin 3, sharpSimplexConvexUpper j) <
      (PrimeGap182.trialConvexKappaBound : ℝ) := by
  simp only [sharpSimplexConvexUpper, sharpNormalizedDensity_vertex_value,
    Fin.sum_univ_three, Fin.sum_univ_five]
  norm_num [sharpVertexDensity, minorantSimplexIndices1,
    Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    PrimeGap182.trialConvexKappaBound]

/-- The actual deficit in the proved sharp-minorant mean is below 0.000093568.
This theorem has no finite-field, distribution, or numerical-integral premise. -/
theorem sharpMass_lt_convexKappaBound : sharpMass < (PrimeGap182.trialConvexKappaBound : ℝ) := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
    (fun j _ => sharpSimplex_integral_le j)
  rw [← sharpNormalizedDensity_integral_sum] at hsum
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (by positivity : (0 : ℝ) ≤ 6 * ((1361 : ℝ) / 100000) ^ 4)
  have hmass : sharpMass =
      6 * ((1361 : ℝ) / 100000) ^ 4 * ∫ z in sharpNormalizedRegion, sharpNormalizedDensity z := by
    simpa only [sharpNormalizedDensity_eq] using sharpMass_eq_normalized_integral
  rw [← hmass] at hscaled
  exact hscaled.trans_lt sharpSimplex_rational_upper

#print axioms sharpNormalizedDensity_integral_sum
#print axioms sharpSimplex_rational_upper
#print axioms sharpMass_lt_convexKappaBound

end PrimeGap182Analytic.SharpMean
