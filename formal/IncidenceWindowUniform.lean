import IncidenceWindowMass
import IncidenceWindowArithmetic

/-!
# Uniform smooth-window bound for actual nonnegative compact product profiles

This proves the window's matrix-energy estimate, for every squarefree modulus,
all positive scales, arbitrary real centers, and arbitrary real shear. The
only finite-field input is the explicitly stated scalar rank-four estimate.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators SchwartzMap FourierTransform ComplexOrder Matrix.Norms.L2Operator

set_option maxHeartbeats 1000000 in
theorem incidenceCompactProductWindow_bound (hK4 : AllIncidenceRankFourBounds)
    (f g : 𝓢(ℝ, ℂ)) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (T₁ T₂ L₁ L₂ : ℝ) (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hsf : Function.support f ⊆ Set.Icc (-T₁) T₁)
    (hsg : Function.support g ⊆ Set.Icc (-T₂) T₂)
    (hbf : ∀ x : ℝ, ‖f x‖ ≤ L₁ ∧ ‖deriv f x‖ ≤ L₁ ∧ ‖deriv (deriv f) x‖ ≤ L₁)
    (hbg : ∀ x : ℝ, ‖g x‖ ≤ L₂ ∧ ‖deriv g x‖ ≤ L₂ ∧ ‖deriv (deriv g) x‖ ≤ L₂)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ [NeZero q], Squarefree q →
      ∀ A : ZMod q, IsUnit A → ∀ E₁ E₂ e₀ γ₀ τ : ℝ, 0 < E₁ → 0 < E₂ →
      ∀ c : ZMod q → ℂ,
        (∑' z : ℤ × ℤ, incidenceScaledProductWeight f g E₁ E₂ e₀ γ₀ τ z *
          ‖(incidenceMatrixMod A *ᵥ c) (incidenceIntegerResidue q z)‖ ^ 2) ≤
          C * incidenceWindowScale η q E₁ E₂ * incidenceVectorEnergy c := by
  obtain ⟨CM, hCM, hmass⟩ := incidenceScaledProductWeight_mass_bound f g hf hg
  obtain ⟨CS, hCS, hsub⟩ := incidence_prime_divisor_subpower η hη
  let K₁ : ℝ := 8 * T₁ * L₁
  let K₂ : ℝ := 8 * T₂ * L₂
  have hK₁ : 0 ≤ K₁ := by dsimp [K₁]; positivity
  have hK₂ : 0 ≤ K₂ := by dsimp [K₂]; positivity
  let CE : ℝ := 8 * K₁ * K₂ * CS
  have hCE : 0 ≤ CE := by dsimp [CE]; positivity
  refine ⟨16 * CM + CE, by positivity, ?_⟩
  intro q _ hq A hA E₁ E₂ e₀ γ₀ τ hE₁ hE₂ c
  let u := incidenceScaledSchwartz f E₁ e₀ hE₁.ne'
  let v := incidenceScaledSchwartz g E₂ γ₀ hE₂.ne'
  let w := incidenceScaledProductWeight f g E₁ E₂ e₀ γ₀ τ
  let err : ℝ := ((q : ℝ) ^ 2)⁻¹ *
    ((8 : ℝ) ^ q.primeFactors.card * (q : ℝ) * Real.sqrt (q : ℝ)) *
    ((K₁ * E₁) * (K₂ * E₂)) * (q.divisors.card : ℝ) *
    (8 / ((E₁ / q) * (E₂ / q)) + 4 / (E₂ / q) + 2 / (E₁ / q))
  have hu : ∀ t, ‖𝓕 u t‖ ≤ (K₁ * E₁) * incidenceDecay E₁ t :=
    incidenceScaledSchwartz_fourier_bound f T₁ L₁ E₁ e₀ hT₁ hL₁ hE₁ hsf hbf
  have hv : ∀ t, ‖𝓕 v t‖ ≤ (K₂ * E₂) * incidenceDecay E₂ t :=
    incidenceScaledSchwartz_fourier_bound g T₂ L₂ E₂ γ₀ hT₂ hL₂ hE₂ hsg hbg
  have hbase : (∑' z : ℤ × ℤ, w z *
      ‖(incidenceMatrixMod A *ᵥ c) (incidenceIntegerResidue q z)‖ ^ 2) ≤
      ((∑' z, w z) + err) * incidenceVectorEnergy c :=
    incidenceSchwartzWindow_energy_le hK4 hq A hA u v τ (K₁ * E₁) (K₂ * E₂) E₁ E₂
      (mul_nonneg hK₁ hE₁.le) (mul_nonneg hK₂ hE₂.le) hE₁ hE₂ hu hv w
      (incidenceScaledProductWeight_nonneg f g hf hg E₁ E₂ e₀ γ₀ τ)
      (incidenceScaledProductWeight_cast f g hf hg E₁ E₂ e₀ γ₀ τ hE₁.ne' hE₂.ne') c
  have he : err ≤ CE * incidenceWindowScale η q E₁ E₂ :=
    incidenceWindowScale_error η q (NeZero.ne q) CS K₁ K₂ E₁ E₂
      hCS.le hK₁ hK₂ hE₁ hE₂ (hsub q (NeZero.ne q))
  have hm : (∑' z : ℤ × ℤ, w z) ≤ 16 * CM * incidenceWindowScale η q E₁ E₂ := by
    calc
      _ ≤ CM * (2 + 4 * E₁) * (2 + 4 * E₂) := hmass E₁ E₂ e₀ γ₀ τ hE₁ hE₂
      _ = CM * ((2 + 4 * E₁) * (2 + 4 * E₂)) := by ring
      _ ≤ CM * (16 * incidenceWindowScale η q E₁ E₂) :=
        mul_le_mul_of_nonneg_left
          (incidenceWindowScale_mass η hη q (NeZero.ne q) E₁ E₂ hE₁.le hE₂.le) hCM.le
      _ = _ := by ring
  calc
    _ ≤ ((∑' z, w z) + err) * incidenceVectorEnergy c := hbase
    _ ≤ (16 * CM * incidenceWindowScale η q E₁ E₂ +
        CE * incidenceWindowScale η q E₁ E₂) * incidenceVectorEnergy c :=
      mul_le_mul_of_nonneg_right (add_le_add hm he) (incidenceVectorEnergy_nonneg c)
    _ = _ := by ring

#print axioms incidenceCompactProductWindow_bound

end PrimeGap182Audit
