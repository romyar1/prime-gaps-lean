import TypeIIIFrequencyMasks

/-!
# Exact two-dimensional interval completion

The transform is the actual unnormalized positive-phase transform from `TypeIIILocal`.
The interval transforms use the negative phase. Thus their product is the exact Fourier
inversion pairing, with the factor `s⁻²` retained explicitly.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

/-- The actual sum of a residue function over two integer intervals. -/
def intervalRectangleSum (s : ℕ) [NeZero s] (Ah Ak : ℤ) (Nh Nk : ℕ)
    (f : ZMod s → ZMod s → ℂ) : ℂ :=
  ∑ u ∈ Finset.range Nh, ∑ v ∈ Finset.range Nk,
    f ((Ah + u : ℤ) : ZMod s) ((Ak + v : ℤ) : ZMod s)

/-- Exact completion, before taking norms or enlarging any set of frequencies. -/
theorem intervalRectangleSum_fourier
    (s : ℕ) [NeZero s] (Ah Ak : ℤ) (Nh Nk : ℕ)
    (f : ZMod s → ZMod s → ℂ) :
    intervalRectangleSum s Ah Ak Nh Nk f =
      ((s : ℂ)⁻¹) ^ 2 * ∑ h : ZMod s, ∑ k : ZMod s,
        intervalFourier s Ah Nh h * intervalFourier s Ak Nk k * fourier₂ s f h k := by
  let wh := PrimeGap186.integerIntervalResidueWeight s Ah Nh (fun _ => 1)
  let wk := PrimeGap186.integerIntervalResidueWeight s Ak Nk (fun _ => 1)
  have hphysical : (∑ h : ZMod s, ∑ k : ZMod s, wh h * wk k * f h k) =
      intervalRectangleSum s Ah Ak Nh Nk f := by
    calc
      _ = ∑ h : ZMod s, wh h * (∑ k : ZMod s, wk k * f h k) := by
        simp only [Finset.mul_sum, mul_assoc]
      _ = ∑ u ∈ Finset.range Nh, (∑ k : ZMod s,
          wk k * f ((Ah + u : ℤ) : ZMod s) k) := by
        simpa only [one_mul] using
          (PrimeGap186.integerIntervalResidueWeight_spec s Ah Nh (fun _ => 1)).1
            (fun h => ∑ k : ZMod s, wk k * f h k)
      _ = _ := by
        unfold intervalRectangleSum
        apply Finset.sum_congr rfl
        intro u hu
        simpa only [one_mul] using
          (PrimeGap186.integerIntervalResidueWeight_spec s Ak Nk (fun _ => 1)).1
            (f ((Ah + u : ℤ) : ZMod s))
  have hhat (h k : ZMod s) :
      (∑ x : ZMod s, ∑ y : ZMod s,
        f x y * ZMod.stdAddChar (-(x * (-h) + y * (-k)))) = fourier₂ s f h k := by
    simp only [fourier₂, mul_neg, neg_add, neg_neg, mul_comm]
  have hh := (PrimeGap186.weighted_double_sum_fourier_completion s wh wk (fun k h => f h k)).1
  dsimp only at hh
  rw [hphysical] at hh
  simp_rw [hhat] at hh
  simpa only [wh, wk, ← intervalFourier_eq_dft] using hh

/-- Norm completion preserves every frequency and its individual Fourier coefficient. -/
theorem intervalRectangleSum_norm_le
    (s : ℕ) [NeZero s] (Ah Ak : ℤ) (Nh Nk : ℕ)
    (f : ZMod s → ZMod s → ℂ) :
    ‖intervalRectangleSum s Ah Ak Nh Nk f‖ ≤
      ((s : ℝ)⁻¹) ^ 2 * ∑ h : ZMod s, ∑ k : ZMod s,
        ‖fourier₂ s f h k‖ * ‖intervalFourier s Ah Nh h‖ * ‖intervalFourier s Ak Nk k‖ := by
  rw [intervalRectangleSum_fourier, norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply norm_sum_le_of_le
  intro h hh
  apply norm_sum_le_of_le
  intro k hk
  simp only [norm_mul]
  exact le_of_eq (by ring)

/-- A pointwise majorant for the actual transform gives the weighted completion bound. -/
theorem intervalRectangleSum_norm_le_majorant
    (s : ℕ) [NeZero s] (Ah Ak : ℤ) (Nh Nk : ℕ)
    (f : ZMod s → ZMod s → ℂ) (U : ZMod s → ZMod s → ℝ)
    (hU : ∀ h k, ‖fourier₂ s f h k‖ ≤ U h k) :
    ‖intervalRectangleSum s Ah Ak Nh Nk f‖ ≤
      ((s : ℝ)⁻¹) ^ 2 * ∑ h : ZMod s, ∑ k : ZMod s,
        U h k * ‖intervalFourier s Ah Nh h‖ * ‖intervalFourier s Ak Nk k‖ := by
  apply (intervalRectangleSum_norm_le s Ah Ak Nh Nk f).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro h hh
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hU h k) (norm_nonneg _)) (norm_nonneg _)

private theorem weighted_two_indicators
    (s : ℕ) [NeZero s] (Ah Ak : ℤ) (Nh Nk : ℕ)
    (Z E : Finset (ZMod s × ZMod s)) (c bZ bE : ℝ) :
    (∑ h : ZMod s, ∑ k : ZMod s,
      (c * (1 + bZ * (if (h, k) ∈ Z then 1 else 0) +
        bE * (if (h, k) ∈ E then 1 else 0))) *
          ‖intervalFourier s Ah Nh h‖ * ‖intervalFourier s Ak Nk k‖) =
      c * ((∑ h : ZMod s, ‖intervalFourier s Ah Nh h‖) *
        (∑ k : ZMod s, ‖intervalFourier s Ak Nk k‖) +
          bZ * frequencyMass s Ah Ak Nh Nk Z + bE * frequencyMass s Ah Ak Nh Nk E) := by
  classical
  calc
    _ = ∑ h : ZMod s, ∑ k : ZMod s,
        (c * (‖intervalFourier s Ah Nh h‖ * ‖intervalFourier s Ak Nk k‖) +
          c * bZ * (if (h, k) ∈ Z then
            ‖intervalFourier s Ah Nh h‖ * ‖intervalFourier s Ak Nk k‖ else 0) +
          c * bE * (if (h, k) ∈ E then
            ‖intervalFourier s Ah Nh h‖ * ‖intervalFourier s Ak Nk k‖ else 0)) := by
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro k hk
      split_ifs <;> ring
    _ = _ := by
      rw [frequencyMass_eq_double, frequencyMass_eq_double]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- Completion for an actual transform satisfying a base bound and two explicit exceptional
set contributions. The exceptional contributions remain their positive weighted masses. -/
theorem intervalRectangleSum_norm_le_two_indicators
    (s : ℕ) [NeZero s] (Ah Ak : ℤ) (Nh Nk : ℕ)
    (f : ZMod s → ZMod s → ℂ) (Z E : Finset (ZMod s × ZMod s)) (c bZ bE : ℝ)
    (hF : ∀ h k, ‖fourier₂ s f h k‖ ≤
      c * (1 + bZ * (if (h, k) ∈ Z then 1 else 0) +
        bE * (if (h, k) ∈ E then 1 else 0))) :
    ‖intervalRectangleSum s Ah Ak Nh Nk f‖ ≤
      ((s : ℝ)⁻¹) ^ 2 * c *
        ((∑ h : ZMod s, ‖intervalFourier s Ah Nh h‖) *
          (∑ k : ZMod s, ‖intervalFourier s Ak Nk k‖) +
            bZ * frequencyMass s Ah Ak Nh Nk Z + bE * frequencyMass s Ah Ak Nh Nk E) := by
  have hh := intervalRectangleSum_norm_le_majorant s Ah Ak Nh Nk f _ hF
  rw [weighted_two_indicators, ← mul_assoc] at hh
  exact hh

#print axioms intervalRectangleSum_fourier
#print axioms intervalRectangleSum_norm_le
#print axioms intervalRectangleSum_norm_le_two_indicators

end

end PrimeGap182.TypeIII
