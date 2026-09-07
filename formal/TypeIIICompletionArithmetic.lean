import TypeIIIFrequencyMasks

/-!
# Scalar bounds after positive squarefree completion

These estimates apply to each actual rectangle in the expanded local Fourier envelope.
The four local weight inequalities are multiplied first; the completed rectangle is then
expanded into its four nonnegative terms.  The result keeps explicit logarithmic factors
and interval lengths, without asymptotic notation.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

theorem product_completion_weight_bounds
    {ι : Type*} [Fintype ι] (S G Qh Qk W : ι → ℝ)
    (hW : ∀ i, 0 ≤ W i)
    (h : ∀ i, (W i) ^ 2 ≤ S i * G i ∧
      (W i) ^ 2 ≤ (Qh i) ^ 2 * G i ∧
      (W i) ^ 2 ≤ (Qk i) ^ 2 * G i ∧ W i ≤ Qh i * Qk i) :
    (∏ i, W i) ^ 2 ≤ (∏ i, S i) * (∏ i, G i) ∧
    (∏ i, W i) ^ 2 ≤ (∏ i, Qh i) ^ 2 * (∏ i, G i) ∧
    (∏ i, W i) ^ 2 ≤ (∏ i, Qk i) ^ 2 * (∏ i, G i) ∧
    (∏ i, W i) ≤ (∏ i, Qh i) * (∏ i, Qk i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hh := Finset.prod_le_prod (s := Finset.univ)
      (fun i _ => sq_nonneg (W i)) (fun i _ => (h i).1)
    simpa only [Finset.prod_mul_distrib, ← Finset.prod_pow] using hh
  · have hh := Finset.prod_le_prod (s := Finset.univ)
      (fun i _ => sq_nonneg (W i)) (fun i _ => (h i).2.1)
    simpa only [Finset.prod_mul_distrib, ← Finset.prod_pow] using hh
  · have hh := Finset.prod_le_prod (s := Finset.univ)
      (fun i _ => sq_nonneg (W i)) (fun i _ => (h i).2.2.1)
    simpa only [Finset.prod_mul_distrib, ← Finset.prod_pow] using hh
  · have hh := Finset.prod_le_prod (s := Finset.univ) (fun i _ => hW i)
      (fun i _ => (h i).2.2.2)
    simpa only [Finset.prod_mul_distrib] using hh

/-- The four expanded completed-rectangle terms admit this explicit common bound. -/
theorem completed_rectangle_scalar_bound
    {S G Qh Qk W Nh Nk L : ℝ}
    (hS : 0 ≤ S) (hG : 0 ≤ G) (hQh : 0 < Qh) (hQk : 0 < Qk)
    (hW : 0 ≤ W) (hNh : 0 ≤ Nh) (hNk : 0 ≤ Nk) (hL : 0 ≤ L)
    (hWS : W ^ 2 ≤ S * G) (hWh : W ^ 2 ≤ Qh ^ 2 * G)
    (hWk : W ^ 2 ≤ Qk ^ 2 * G) (hWhk : W ≤ Qh * Qk) :
    S * W * (2 * Nh + S / Qh * L) * (2 * Nk + S / Qk * L) ≤
      S ^ 3 * L ^ 2 + 2 * (Nh + Nk) * S ^ 2 * L * Real.sqrt G +
        4 * Nh * Nk * S * Real.sqrt (S * G) := by
  have hWS' : W ≤ Real.sqrt (S * G) := Real.le_sqrt_of_sq_le hWS
  have hWh' : W / Qh ≤ Real.sqrt G := by
    apply (div_le_iff₀ hQh).mpr
    have hsq : W ^ 2 ≤ (Real.sqrt G * Qh) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hG]
      simpa only [mul_comm] using hWh
    exact (sq_le_sq₀ hW (mul_nonneg (Real.sqrt_nonneg _) hQh.le)).mp hsq
  have hWk' : W / Qk ≤ Real.sqrt G := by
    apply (div_le_iff₀ hQk).mpr
    have hsq : W ^ 2 ≤ (Real.sqrt G * Qk) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hG]
      simpa only [mul_comm] using hWk
    exact (sq_le_sq₀ hW (mul_nonneg (Real.sqrt_nonneg _) hQk.le)).mp hsq
  have hWhk' : W / (Qh * Qk) ≤ 1 := by
    apply (div_le_iff₀ (mul_pos hQh hQk)).mpr
    simpa only [one_mul] using hWhk
  calc
    _ = S ^ 3 * L ^ 2 * (W / (Qh * Qk)) +
        2 * Nh * S ^ 2 * L * (W / Qk) + 2 * Nk * S ^ 2 * L * (W / Qh) +
        4 * Nh * Nk * S * W := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ S ^ 3 * L ^ 2 * 1 + 2 * Nh * S ^ 2 * L * Real.sqrt G +
        2 * Nk * S ^ 2 * L * Real.sqrt G + 4 * Nh * Nk * S * Real.sqrt (S * G) := by
      gcongr
    _ = _ := by ring

/-- An explicit form of the squarefree incomplete-cycle bound, before absorbing logarithms. -/
def squarefreeCompletionShape (S G : ℝ) (Nh Nk : ℕ) : ℝ :=
  S ^ 3 * (1 + Real.log S) ^ 2 +
    2 * ((Nh : ℝ) + Nk) * S ^ 2 * (1 + Real.log S) * Real.sqrt G +
      4 * Nh * Nk * S * Real.sqrt (S * G)

theorem squarefreeCompletionShape_nonneg {S G : ℝ}
    (hS : 1 ≤ S) (Nh Nk : ℕ) :
    0 ≤ squarefreeCompletionShape S G Nh Nk := by
  have hs0 : 0 ≤ S := zero_le_one.trans hS
  have hL : 0 ≤ 1 + Real.log S := add_nonneg zero_le_one (Real.log_nonneg hS)
  unfold squarefreeCompletionShape
  positivity

/-- The preceding scalar lemma specialized to the proved interval Fourier majorants. -/
theorem intervalMass_completed_scalar_bound
    (s qh qk : ℕ) [NeZero s] [NeZero qh] [NeZero qk]
    (G W : ℝ) (hG : 0 ≤ G) (hW : 0 ≤ W) (Nh Nk : ℕ)
    (hWS : W ^ 2 ≤ s * G) (hWh : W ^ 2 ≤ (qh : ℝ) ^ 2 * G)
    (hWk : W ^ 2 ≤ (qk : ℝ) ^ 2 * G) (hWhk : W ≤ (qh : ℝ) * qk) :
    (s : ℝ) * W * intervalMassBound s qh Nh * intervalMassBound s qk Nk ≤
      squarefreeCompletionShape s G Nh Nk := by
  have hs : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s from NeZero.one_le)
  have hqh : (0 : ℝ) < qh := by exact_mod_cast (NeZero.pos qh)
  have hqk : (0 : ℝ) < qk := by exact_mod_cast (NeZero.pos qk)
  exact completed_rectangle_scalar_bound (Nat.cast_nonneg _) hG hqh hqk hW
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (add_nonneg zero_le_one (Real.log_nonneg hs)) hWS hWh hWk hWhk

#print axioms product_completion_weight_bounds
#print axioms completed_rectangle_scalar_bound
#print axioms intervalMass_completed_scalar_bound

end

end PrimeGap182.TypeIII
