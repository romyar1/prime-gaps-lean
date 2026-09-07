import IncidenceSmoothSeparation

noncomputable section

namespace PrimeGap182Audit

open MeasureTheory WithLp
open scoped BigOperators FourierTransform SchwartzMap RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Positive row weights are retained inside the actual square-norm
estimate while the genuine joint Schwartz profile is separated. -/
theorem incidenceSchwartz_weighted_separation {ρ κ : Type*} [Fintype ρ] [Fintype κ]
    (w : ρ → ℝ) (hw : ∀ r, 0 ≤ w r) (Z : ρ → κ → ℂ)
    (x : ρ → V) (y : κ → V) (F : 𝓢(V, ℂ)) (K : ℝ) (hK : 0 ≤ K)
    (hresponse : ∀ u : κ → ℂ, (∀ k, ‖u k‖ ≤ 1) →
      (∑ r, w r * ‖∑ k, Z r k * u k‖ ^ 2) ≤ K) :
    (∑ r, w r * ‖∑ k, Z r k * F (x r + y k)‖ ^ 2) ≤
      (∫ ξ : V, ‖(𝓕 F : 𝓢(V, ℂ)) ξ‖) ^ 2 * K := by
  let Z' : ρ → κ → ℂ := fun r k => (Real.sqrt (w r) : ℂ) * Z r k
  have he (u : ρ → κ → ℂ) : incidenceVectorEnergy
      (fun r => ∑ k, Z' r k * u r k) =
        ∑ r, w r * ‖∑ k, Z r k * u r k‖ ^ 2 := by
    unfold incidenceVectorEnergy
    apply Finset.sum_congr rfl
    intro r _
    simp only [Z', mul_assoc, ← Finset.mul_sum, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (hw r)]
  have hb := incidenceSchwartz_separation_energy Z' x y F K hK
    (fun u hu => by rw [he (fun _ k => u k)]; exact hresponse u hu)
  rw [he (fun r k => F (x r + y k))] at hb
  exact hb

#print axioms incidenceSchwartz_weighted_separation

end PrimeGap182Audit
