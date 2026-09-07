import IncidencePeriodization
import IncidenceAliasBound

/-!
# A completed incidence bound for an actual sheared smooth weight

The intermediate Fourier-envelope assumptions refer to the transforms of
the specified Schwartz profiles. Every lattice sum and matrix in the
conclusion is actual, and the zero-mode coefficient is the unrestricted
lattice mass. The compact-profile specialization discharges the envelopes.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators FourierTransform SchwartzMap ComplexOrder Matrix.Norms.L2Operator

variable {q : ℕ} [NeZero q]

/-- A real lattice weight represented by a sheared product of Schwartz profiles is summable. -/
theorem incidenceSchwartzWeight_summable (u v : 𝓢(ℝ, ℂ)) (τ : ℝ)
    (w : ℤ × ℤ → ℝ)
    (hw : ∀ z, (w z : ℂ) = u (z.1 : ℝ) * v ((z.2 : ℝ) - τ * (z.1 : ℝ))) :
    Summable w := by
  apply Complex.summable_ofReal.mp
  have hs := incidenceShearedPhysical_summable u v τ 0 0
  apply hs.congr
  intro z
  simp only [incidenceShearedPhysical, neg_zero, zero_mul, sub_zero,
    incidenceRealChar_zero, mul_one]
  exact (hw z).symm

set_option maxHeartbeats 800000 in
/-- The actual incidence energy is controlled by its exact mass and the
proved gcd-weighted Fourier error. Only the local scalar rank-four bound
supplies finite-field cancellation. -/
theorem incidenceSchwartzWindow_energy_le (hK4 : AllIncidenceRankFourBounds)
    (hq : Squarefree q) (A : ZMod q) (hA : IsUnit A)
    (u v : 𝓢(ℝ, ℂ)) (τ C₁ C₂ E₁ E₂ : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hE₁ : 0 < E₁) (hE₂ : 0 < E₂)
    (hu : ∀ t, ‖𝓕 u t‖ ≤ C₁ * incidenceDecay E₁ t)
    (hv : ∀ t, ‖𝓕 v t‖ ≤ C₂ * incidenceDecay E₂ t)
    (w : ℤ × ℤ → ℝ) (hw0 : ∀ z, 0 ≤ w z)
    (hw : ∀ z, (w z : ℂ) = u (z.1 : ℝ) * v ((z.2 : ℝ) - τ * (z.1 : ℝ)))
    (c : ZMod q → ℂ) :
    (∑' z : ℤ × ℤ, w z *
      ‖(incidenceMatrixMod A *ᵥ c) (incidenceIntegerResidue q z)‖ ^ 2) ≤
      ((∑' z, w z) + ((q : ℝ) ^ 2)⁻¹ *
        ((8 : ℝ) ^ q.primeFactors.card * (q : ℝ) * Real.sqrt (q : ℝ)) *
        (C₁ * C₂) * (q.divisors.card : ℝ) *
        (8 / ((E₁ / q) * (E₂ / q)) + 4 / (E₂ / q) + 2 / (E₁ / q))) *
          incidenceVectorEnergy c := by
  have hws := incidenceSchwartzWeight_summable u v τ w hw
  have hbase := incidenceLatticeEnergy_squarefree_le hK4 hq A hA w hws hw0 c
  have hd (ξ : ZMod q × ZMod q) :
      (∑' z : ℤ × ℤ, (w z : ℂ) * incidenceJointChar ξ (-incidenceIntegerResidue q z)) =
        ∑' z : ℤ × ℤ, incidenceShearedFourier u v τ
          ((ξ.1.val : ℝ) / q) ((ξ.2.val : ℝ) / q) z := by
    rw [← incidencePoisson_sheared]
    apply tsum_congr
    intro z
    simp only [hw, incidenceJointChar_integer, incidenceShearedPhysical]
  simp only [hd] at hbase
  let P : ℝ := (8 : ℝ) ^ q.primeFactors.card * (q : ℝ) * Real.sqrt (q : ℝ)
  let H (ξ : ZMod q × ZMod q) : ℝ :=
    ‖∑' z : ℤ × ℤ, incidenceShearedFourier u v τ
      ((ξ.1.val : ℝ) / q) ((ξ.2.val : ℝ) / q) z‖ *
        Real.sqrt (incidenceFrequencyGCD ξ : ℝ)
  have hfactor :
      (∑ ξ ∈ (Finset.univ : Finset (ZMod q × ZMod q)).erase 0,
        ‖∑' z : ℤ × ℤ, incidenceShearedFourier u v τ
          ((ξ.1.val : ℝ) / q) ((ξ.2.val : ℝ) / q) z‖ *
          (P * Real.sqrt (incidenceFrequencyGCD ξ : ℝ))) =
        P * ∑ ξ ∈ Finset.univ.erase 0, H ξ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ξ _
    dsimp [H]
    ring
  change _ ≤ ((∑' z, w z) + ((q : ℝ) ^ 2)⁻¹ *
    ∑ ξ ∈ Finset.univ.erase 0,
      ‖∑' z : ℤ × ℤ, incidenceShearedFourier u v τ
        ((ξ.1.val : ℝ) / q) ((ξ.2.val : ℝ) / q) z‖ *
          (P * Real.sqrt (incidenceFrequencyGCD ξ : ℝ))) * incidenceVectorEnergy c at hbase
  rw [hfactor] at hbase
  have hbound := incidenceShearedAliases_gcd_bound (q := q) u v τ C₁ C₂ E₁ E₂
    hC₁ hC₂ hE₁ hE₂ hu hv
  calc
    _ ≤ ((∑' z, w z) + ((q : ℝ) ^ 2)⁻¹ *
        (P * ∑ ξ ∈ Finset.univ.erase 0, H ξ)) * incidenceVectorEnergy c := hbase
    _ ≤ ((∑' z, w z) + ((q : ℝ) ^ 2)⁻¹ *
        (P * ((C₁ * C₂) * (q.divisors.card : ℝ) *
          (8 / ((E₁ / q) * (E₂ / q)) + 4 / (E₂ / q) + 2 / (E₁ / q))))) *
            incidenceVectorEnergy c := by
      apply mul_le_mul_of_nonneg_right _ (incidenceVectorEnergy_nonneg c)
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hbound (by dsimp [P]; positivity)
    _ = _ := by simp only [P, mul_assoc]

#print axioms incidenceSchwartzWeight_summable
#print axioms incidenceSchwartzWindow_energy_le

end PrimeGap182Audit
