import SharpDensityConvex182

/-! Kernel-checked rational values of the actual density at the seven vertices. -/

noncomputable section
open PrimeGap186
open scoped BigOperators

namespace PrimeGap182Analytic.SharpMean

theorem sharpNormalizedDensity_eq_sharpDensity (z : Fin 4 → ℝ) :
    sharpNormalizedDensity z = sharpDensity (sharpAffine z) := by
  have hf : normalizedFiveAffine z =
      fun i : Fin 5 => (1 : ℝ) / 5 + (1361 : ℝ) / 100000 *
        (Fin.snoc z (-(∑ j, z j)) : Fin 5 → ℝ) i :=
    funext (normalizedFiveAffine_apply z)
  unfold sharpNormalizedDensity reciprocalFiveProduct
  rw [hf, ← sharpAffine_snoc]
  rfl

theorem sharpNormalizedDensity_four (z : Fin 4 → ℝ) :
    sharpNormalizedDensity z =
      (1 - ∑ i : Fin 4, sharpAffine z i)⁻¹ * (∏ i : Fin 4, sharpAffine z i)⁻¹ := by
  rw [sharpNormalizedDensity_eq_sharpDensity, sharpDensity_eq]

def sharpVertexDensity (j : Fin 7) : ℝ :=
  if j.val = 0 then 607500000000000000000000000 / 193444357493631107237801
  else if j.val = 1 then 3125
  else if j.val = 2 then 1280000000000000000000000000 / 407803704452263447765209
  else if j.val = 3 then 120000000000000000000000000 / 38326504988594779181911
  else if j.val = 4 then 80000000000000000000000000 / 25282941235271252387199
  else if j.val = 5 then 1280000000000000000000000000 / 407803704452263447765209
  else 607500000000000000000000000 / 193444357493631107237801

theorem sharpNormalizedDensity_vertex_value (j : Fin 7) :
    sharpNormalizedDensity (minorantVertices1 j) = sharpVertexDensity j := by
  rw [sharpNormalizedDensity_four]
  fin_cases j <;>
    norm_num [sharpVertexDensity, sharpAffine, minorantVertices1,
      Fin.sum_univ_four, Fin.prod_univ_four, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

#print axioms sharpNormalizedDensity_vertex_value

end PrimeGap182Analytic.SharpMean
