import TypeIIISharedCRT
import TypeIIIFrequencyDecay

/-!
# Exact smooth Poisson completion at a common integer frequency

This uses the public, proved compact-profile Poisson theorem but retains each integer
frequency. No maximum over local Fourier coefficients or entrywise triangle inequality
is taken. The periodic function can be an entire signed matrix coefficient sum.
-/

open scoped BigOperators Classical FourierTransform ContDiff

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- The positive-sign, unnormalized transform evaluated at an actual integer frequency. -/
def periodicFourier (m : ℕ) [NeZero m] (F : ZMod m → ℂ) (c : ℤ) : ℂ :=
  ZMod.dft F (-(c : ZMod m))

theorem periodicFourier_eq_sum (m : ℕ) [NeZero m] (F : ZMod m → ℂ) (c : ℤ) :
    periodicFourier m F c =
      ∑ x : ZMod m, F x * ZMod.stdAddChar ((c : ZMod m) * x) := by
  simp [periodicFourier, ZMod.dft_apply, smul_eq_mul, mul_comm]

/-- Exact grid reindexing with an arbitrary periodic coefficient, including summability. -/
theorem poisson_grid_reindex_weighted (m : ℕ) [NeZero m] (F : ℝ → ℂ)
    (J : ZMod m → ℂ)
    (hs : Summable (fun c : ℤ => ‖F ((c : ℝ) / (m : ℝ))‖)) :
    Summable (fun c : ℤ => F ((c : ℝ) / (m : ℝ)) * J (c : ZMod m)) ∧
      (∑ ξ : ZMod m, (∑' k : ℤ, F ((k : ℝ) + (ξ.val : ℝ) / (m : ℝ))) * J ξ) =
        ∑' c : ℤ, F ((c : ℝ) / (m : ℝ)) * J (c : ZMod m) := by
  have hJ (ξ : ZMod m) : ‖J ξ‖ ≤ ∑ η : ZMod m, ‖J η‖ :=
    Finset.single_le_sum (fun η _ => norm_nonneg (J η)) (Finset.mem_univ ξ)
  have hsum : Summable (fun c : ℤ => F ((c : ℝ) / (m : ℝ)) * J (c : ZMod m)) :=
    (hs.mul_right (∑ η : ZMod m, ‖J η‖)).of_norm_bounded (fun c => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hJ _) (norm_nonneg _))
  refine ⟨hsum, ?_⟩
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m =>
    have hm : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hpoint (p : ℤ × Fin (m + 1)) :
        (((Int.divModEquiv (m + 1)).symm p : ℤ) : ℝ) / ((m + 1 : ℕ) : ℝ) =
          (p.1 : ℝ) + (p.2.val : ℝ) / ((m + 1 : ℕ) : ℝ) := by
      rw [Int.divModEquiv_symm_apply]
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
      rw [add_div, mul_div_cancel_right₀ _ hm]
    have hres (p : ℤ × Fin (m + 1)) :
        (((Int.divModEquiv (m + 1)).symm p : ℤ) : ZMod (m + 1)) = p.2 := by
      rw [Int.divModEquiv_symm_apply]
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
        mul_zero, zero_add]
      exact ZMod.natCast_zmod_val (n := m + 1) p.2
    have he : Summable (fun p : ℤ × Fin (m + 1) =>
        F ((((Int.divModEquiv (m + 1)).symm p : ℤ) : ℝ) / ((m + 1 : ℕ) : ℝ)) *
          J (((Int.divModEquiv (m + 1)).symm p : ℤ) : ZMod (m + 1))) :=
      ((Int.divModEquiv (m + 1)).symm.summable_iff
        (f := fun c : ℤ => F ((c : ℝ) / ((m + 1 : ℕ) : ℝ)) *
          J (c : ZMod (m + 1)))).mpr hsum
    have hp : Summable (fun p : ℤ × Fin (m + 1) =>
        F ((p.1 : ℝ) + (p.2.val : ℝ) / ((m + 1 : ℕ) : ℝ)) * J p.2) := by
      simpa only [hpoint, hres] using he
    calc
      _ = ∑ ξ : Fin (m + 1), ∑' k : ℤ,
          F ((k : ℝ) + (ξ.val : ℝ) / ((m + 1 : ℕ) : ℝ)) * J ξ := by
        simp only [tsum_mul_right]
        rfl
      _ = ∑' p : ℤ × Fin (m + 1),
          F ((p.1 : ℝ) + (p.2.val : ℝ) / ((m + 1 : ℕ) : ℝ)) * J p.2 := by
        simpa only [tsum_fintype] using
          (hp.tsum_comm (f := fun (k : ℤ) (ξ : Fin (m + 1)) =>
            F ((k : ℝ) + (ξ.val : ℝ) / ((m + 1 : ℕ) : ℝ)) * J ξ)).trans
              hp.tsum_prod.symm
      _ = _ := by
        simpa only [hpoint, hres] using (Int.divModEquiv (m + 1)).symm.tsum_eq
          (fun c : ℤ => F ((c : ℝ) / ((m + 1 : ℕ) : ℝ)) * J (c : ZMod (m + 1)))

/-- Exact Poisson completion of the actual finite, compactly supported physical sum. -/
theorem compactProfile_periodic_poisson
    (m : ℕ) [NeZero m] (T N t₀ : ℝ) (hT : 0 ≤ T) (hN : 0 < N)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hsupport : Function.support ψ ⊆ Set.Icc (-T) T) (F : ZMod m → ℂ) :
    let w : ℝ → ℂ := fun t => ψ ((t - t₀) / N)
    Summable (fun c : ℤ => 𝓕 w ((c : ℝ) / (m : ℝ)) * periodicFourier m F c) ∧
      (∑ ℓ ∈ Finset.Icc ⌈t₀ - T * N⌉ ⌊t₀ + T * N⌋, w (ℓ : ℝ) * F (ℓ : ZMod m)) =
        (m : ℂ)⁻¹ * ∑' c : ℤ, 𝓕 w ((c : ℝ) / (m : ℝ)) * periodicFourier m F c := by
  intro w
  let A : ℤ := ⌈t₀ - T * N⌉
  let B : ℤ := ⌊t₀ + T * N⌋
  let K : ℕ := (B + 1 - A).toNat
  let W : ZMod m → ℂ := PrimeGap186.integerIntervalResidueWeight m A K
    (fun j => w ((A : ℝ) + (j : ℝ)))
  obtain ⟨hgrid, halias, _⟩ :=
    PrimeGap186.compactProfile_poisson_completion m T N t₀ hT hN ψ hψ hsupport
  have hreindex := poisson_grid_reindex_weighted m (𝓕 w) (fun ξ => ZMod.dft F (-ξ)) hgrid
  refine ⟨hreindex.1, ?_⟩
  have hperiod : (∑ x : ZMod m, W x * F x) =
      ∑ ℓ ∈ Finset.Icc A B, w (ℓ : ℝ) * F (ℓ : ZMod m) := by
    rw [(PrimeGap186.integerIntervalResidueWeight_spec m A K _).1 F,
      Int.Icc_eq_finset_map, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply, Int.cast_add, Int.cast_natCast]
  change (∑ ℓ ∈ Finset.Icc A B, w (ℓ : ℝ) * F (ℓ : ZMod m)) = _
  rw [← hperiod, PrimeGap186.full_weighted_sum_dft]
  congr 1
  calc
    _ = ∑ ξ : ZMod m, (∑' k : ℤ,
        𝓕 w ((k : ℝ) + (ξ.val : ℝ) / (m : ℝ))) * ZMod.dft F (-ξ) := by
      apply Finset.sum_congr rfl
      intro ξ _
      rw [← (halias ξ).tsum_eq]
    _ = _ := hreindex.2

#print axioms poisson_grid_reindex_weighted
#print axioms compactProfile_periodic_poisson

end

end PrimeGap182.TypeIII
