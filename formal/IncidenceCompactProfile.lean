import IncidenceSmoothWindow

/-!
# Actual scaled compact profiles and their Fourier bounds

The Fourier envelope used by smooth-window completion is discharged by the
baseline's proved twice-integration-by-parts estimate. No Fourier decay
assumption is introduced for these profiles.
-/

noncomputable section

namespace PrimeGap182Audit

open scoped BigOperators FourierTransform SchwartzMap

def incidenceScaleEquiv (N : ℝ) (hN : N ≠ 0) : ℝ ≃L[ℝ] ℝ :=
  (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 N hN)).symm

def incidenceScaledSchwartz (f : 𝓢(ℝ, ℂ)) (N t₀ : ℝ) (hN : N ≠ 0) : 𝓢(ℝ, ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (incidenceScaleEquiv N hN) f).compSubConstCLM ℂ t₀

theorem incidenceScaledSchwartz_apply (f : 𝓢(ℝ, ℂ)) (N t₀ : ℝ) (hN : N ≠ 0) (x : ℝ) :
    incidenceScaledSchwartz f N t₀ hN x = f ((x - t₀) / N) := by
  simp [incidenceScaledSchwartz, incidenceScaleEquiv, div_eq_mul_inv]

/-- The required scale-sensitive Fourier estimate for each actual compact profile. -/
theorem incidenceScaledSchwartz_fourier_bound (f : 𝓢(ℝ, ℂ)) (T L N t₀ : ℝ)
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hN : 0 < N)
    (hsupport : Function.support f ⊆ Set.Icc (-T) T)
    (hbound : ∀ x : ℝ,
      ‖f x‖ ≤ L ∧ ‖deriv f x‖ ≤ L ∧ ‖deriv (deriv f) x‖ ≤ L) :
    ∀ ξ : ℝ, ‖𝓕 (incidenceScaledSchwartz f N t₀ hN.ne') ξ‖ ≤
      (8 * T * L * N) * incidenceDecay N ξ := by
  intro ξ
  have hb := PrimeGap186.compactProfile_fourier_decay_bound T L N t₀ hT hL hN
    f (f.smooth 2) hsupport hbound ξ
  have heq : (incidenceScaledSchwartz f N t₀ hN.ne' : ℝ → ℂ) =
      (fun x => f ((x - t₀) / N)) := funext (incidenceScaledSchwartz_apply f N t₀ hN.ne')
  change ‖𝓕 (fun x => incidenceScaledSchwartz f N t₀ hN.ne' x) ξ‖ ≤ _
  rw [heq]
  simpa only [incidenceDecay, div_eq_mul_inv, inv_pow] using hb

/-- A genuine scaled Schwartz profile also has the needed spatial envelope. -/
theorem incidenceScaledSchwartz_spatial_bound (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N t₀ : ℝ, ∀ hN : 0 < N, ∀ x : ℝ,
      ‖incidenceScaledSchwartz f N t₀ hN.ne' x‖ ≤ C * incidenceDecay (1 / N) (x - t₀) := by
  obtain ⟨C, hC, hb⟩ := incidenceSchwartz_decay_bound f
  refine ⟨C, hC, ?_⟩
  intro N t₀ hN x
  rw [incidenceScaledSchwartz_apply]
  simpa only [incidenceDecay_div _ _ _ hN] using hb ((x - t₀) / N)

#print axioms incidenceScaledSchwartz_apply
#print axioms incidenceScaledSchwartz_fourier_bound
#print axioms incidenceScaledSchwartz_spatial_bound

end PrimeGap182Audit
