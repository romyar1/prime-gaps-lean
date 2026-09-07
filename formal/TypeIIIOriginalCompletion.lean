import TypeIIISeparatedCoefficients
import TypeIIIPoissonEnvelope

/-!
# Exact completion of the original signed coefficient sums

The periodic function is the whole original matrix coefficient sum. Its transform is
proved equal to `sharedOriginalCoefficientSum` before any norm is applied.
-/

open scoped BigOperators Classical FourierTransform ContDiff

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

def sharedInverseFunction (u v w : ℕ) [NeZero u] [NeZero v] [NeZero w]
    (a m n : ℤ) : ZMod (u * (v * w)) → ℂ :=
  sharedPairFunction u v w
    (((a : ZMod (u * w)) * (m : ZMod (u * w))⁻¹).val : ℤ)
    (((a : ZMod (v * w)) * (n : ZMod (v * w))⁻¹).val : ℤ)

theorem sharedInverseFunction_int (u v w : ℕ) [NeZero u] [NeZero v] [NeZero w]
    (a m n ℓ : ℤ) :
    sharedInverseFunction u v w a m n (ℓ : ZMod (u * (v * w))) =
      if IsUnit (ℓ : ZMod (u * (v * w))) then
        PrimeGap186.normalizedKloosterman3Mod (u * w)
          (((a : ZMod (u * w)) * (m : ZMod (u * w))⁻¹) * (ℓ : ZMod (u * w))) *
        star (PrimeGap186.normalizedKloosterman3Mod (v * w)
          (((a : ZMod (v * w)) * (n : ZMod (v * w))⁻¹) * (ℓ : ZMod (v * w))))
      else 0 := by
  have hu : u * w ∣ u * (v * w) := by
    refine ⟨v, ?_⟩
    ring
  have hv : v * w ∣ u * (v * w) := dvd_mul_left _ _
  simp only [sharedInverseFunction, sharedPairFunction, ZMod.natCast_val,
    ZMod.intCast_zmod_cast, ZMod.cast_intCast hu, ZMod.cast_intCast hv]

theorem periodicFourier_sharedInverseFunction
    (u v w : ℕ) [NeZero u] [NeZero v] [NeZero w] (a m n c : ℤ) :
    periodicFourier (u * (v * w)) (sharedInverseFunction u v w a m n) c =
      sharedInverseFourier u v w a m n c := by
  rw [periodicFourier_eq_sum]
  exact (sharedPairFourier_eq_transform u v w _ _ c).symm

/-- The entire original periodic coefficient sum, retaining both row unit masks. -/
def sharedOriginalFunction (u v w : ℕ) [NeZero u] [NeZero v] [NeZero w]
    (a A B : ℤ) (N M : ℕ) (α : IntegerIntervalIndex A N → ℂ)
    (β : IntegerIntervalIndex B M → ℂ) (h : ZMod (u * (v * w))) : ℂ :=
  ∑ m : IntegerIntervalIndex A N, ∑ n : IntegerIntervalIndex B M,
    if IsUnit (m.1 : ZMod (u * w)) ∧ IsUnit (n.1 : ZMod (v * w)) then
      α m * sharedInverseFunction u v w a m.1 n.1 h * star (β n)
    else 0

theorem periodicFourier_sharedOriginalFunction
    (u v w : ℕ) [NeZero u] [NeZero v] [NeZero w]
    (a c A B : ℤ) (N M : ℕ) (α : IntegerIntervalIndex A N → ℂ)
    (β : IntegerIntervalIndex B M → ℂ) :
    periodicFourier (u * (v * w)) (sharedOriginalFunction u v w a A B N M α β) c =
      sharedOriginalCoefficientSum u v w a c A B N M α β := by
  rw [periodicFourier_eq_sum]
  simp only [sharedOriginalFunction, sharedOriginalCoefficientSum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : IsUnit (m.1 : ZMod (u * w)) ∧ IsUnit (n.1 : ZMod (v * w))
  · simp only [ite_eq_left h]
    rw [← periodicFourier_sharedInverseFunction, periodicFourier_eq_sum]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    ring
  · simp only [ite_eq_right h, zero_mul, Finset.sum_const_zero]

/-- The actual compactly supported physical correlation, with its signed matrix
coefficient sum formed before completion. -/
def sharedProfileCoefficientSum (u v w : ℕ) [NeZero u] [NeZero v] [NeZero w]
    (a A B : ℤ) (N M : ℕ) (α : IntegerIntervalIndex A N → ℂ)
    (β : IntegerIntervalIndex B M → ℂ) (T H t₀ : ℝ) (ψ : ℝ → ℂ) : ℂ :=
  ∑ ℓ ∈ Finset.Icc ⌈t₀ - T * H⌉ ⌊t₀ + T * H⌋,
    ψ (((ℓ : ℝ) - t₀) / H) *
      sharedOriginalFunction u v w a A B N M α β (ℓ : ZMod (u * (v * w)))

/-- The exact original correlation is an absolutely convergent integer-frequency sum. -/
theorem sharedProfileCoefficientSum_poisson
    (u v w : ℕ) [NeZero u] [NeZero v] [NeZero w]
    (a A B : ℤ) (N M : ℕ) (α : IntegerIntervalIndex A N → ℂ)
    (β : IntegerIntervalIndex B M → ℂ) (T H t₀ : ℝ) (hT : 0 ≤ T) (hH : 0 < H)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hsupport : Function.support ψ ⊆ Set.Icc (-T) T) :
    Summable (fun c : ℤ => normalizedProfileFourier (u * (v * w)) ψ H t₀ c *
      sharedOriginalCoefficientSum u v w a c A B N M α β) ∧
    sharedProfileCoefficientSum u v w a A B N M α β T H t₀ ψ =
      ∑' c : ℤ, normalizedProfileFourier (u * (v * w)) ψ H t₀ c *
        sharedOriginalCoefficientSum u v w a c A B N M α β := by
  have hp := compactProfile_periodic_poisson (u * (v * w)) T H t₀ hT hH ψ hψ hsupport
    (sharedOriginalFunction u v w a A B N M α β)
  simp only [periodicFourier_sharedOriginalFunction] at hp
  have hs := hp.1.mul_left ((u * (v * w) : ℕ) : ℂ)⁻¹
  refine ⟨?_, ?_⟩
  · simpa only [normalizedProfileFourier, mul_assoc] using hs
  · rw [sharedProfileCoefficientSum, hp.2]
    simpa only [normalizedProfileFourier, mul_assoc] using
      (hp.1.tsum_mul_left (((u * (v * w) : ℕ) : ℂ)⁻¹)).symm

#print axioms sharedInverseFunction_int
#print axioms periodicFourier_sharedOriginalFunction
#print axioms sharedProfileCoefficientSum_poisson

end

end PrimeGap182.TypeIII
