import IncidenceSourceWindow
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Actual smooth separation by Fourier inversion

A genuine Schwartz profile of the sum of a row coordinate and an input
coordinate is separated by its actual Fourier transform. The resulting
quadratic estimate costs the square of its Fourier L¹ norm. This theorem
assumes only the displayed finite response estimate for bounded input
weights; that estimate is supplied by the proved incidence/Farey window.
-/

noncomputable section

namespace PrimeGap182Audit

open MeasureTheory WithLp
open scoped BigOperators FourierTransform SchwartzMap RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem incidenceInnerPhase_continuous (x : V) :
    Continuous (fun ξ : V => incidenceRealChar ⟪ξ, x⟫) := by
  change Continuous (fun ξ : V => Complex.exp ((2 * Real.pi * ⟪ξ, x⟫ : ℝ) * Complex.I))
  fun_prop

theorem incidenceSchwartz_inverse_split (F : 𝓢(V, ℂ)) (x y : V) :
    Integrable (fun ξ : V => (𝓕 F : 𝓢(V, ℂ)) ξ * incidenceRealChar ⟪ξ, x⟫ *
      incidenceRealChar ⟪ξ, y⟫) ∧
    (∫ ξ : V, (𝓕 F : 𝓢(V, ℂ)) ξ * incidenceRealChar ⟪ξ, x⟫ *
      incidenceRealChar ⟪ξ, y⟫) = F (x + y) := by
  have hc : Continuous (fun ξ : V => (𝓕 F : 𝓢(V, ℂ)) ξ * incidenceRealChar ⟪ξ, x⟫ *
      incidenceRealChar ⟪ξ, y⟫) :=
    ((𝓕 F : 𝓢(V, ℂ)).continuous.mul (incidenceInnerPhase_continuous x)).mul
      (incidenceInnerPhase_continuous y)
  have hi : Integrable (fun ξ : V => (𝓕 F : 𝓢(V, ℂ)) ξ * incidenceRealChar ⟪ξ, x⟫ *
      incidenceRealChar ⟪ξ, y⟫) :=
    (𝓕 F : 𝓢(V, ℂ)).integrable.norm.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall
      (fun ξ => by simp only [norm_mul, incidenceRealChar_norm, mul_one, le_refl]))
  refine ⟨hi, ?_⟩
  have hinv := congrArg (fun G : 𝓢(V, ℂ) => G (x + y))
    (FourierTransform.fourierInv_fourier_eq (F := 𝓢(V, ℂ)) F)
  change (𝓕⁻ (𝓕 F : 𝓢(V, ℂ))) (x + y) = F (x + y) at hinv
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq] at hinv
  rw [← hinv]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [inner_add_right, Circle.smul_def, smul_eq_mul]
  change (𝓕 F : 𝓢(V, ℂ)) ξ * incidenceRealChar ⟪ξ, x⟫ * incidenceRealChar ⟪ξ, y⟫ =
    incidenceRealChar (⟪ξ, x⟫ + ⟪ξ, y⟫) * (𝓕 F : 𝓢(V, ℂ)) ξ
  rw [incidenceRealChar_add]
  ring

set_option maxHeartbeats 800000 in
/-- Smooth joint row/input weights preserve the finite response bound,
with the fully explicit cost of the actual Fourier L¹ norm. -/
theorem incidenceSchwartz_separation_energy {ρ κ : Type*} [Fintype ρ] [Fintype κ]
    (Z : ρ → κ → ℂ) (x : ρ → V) (y : κ → V) (F : 𝓢(V, ℂ))
    (K : ℝ) (hK : 0 ≤ K)
    (hresponse : ∀ u : κ → ℂ, (∀ k, ‖u k‖ ≤ 1) →
      incidenceVectorEnergy (fun r => ∑ k, Z r k * u k) ≤ K) :
    incidenceVectorEnergy (fun r => ∑ k, Z r k * F (x r + y k)) ≤
      (∫ ξ : V, ‖(𝓕 F : 𝓢(V, ℂ)) ξ‖) ^ 2 * K := by
  classical
  let g : V → EuclideanSpace ℂ ρ := fun ξ => toLp 2 (fun r =>
    incidenceRealChar ⟪ξ, x r⟫ * ∑ k, Z r k * incidenceRealChar ⟪ξ, y k⟫)
  let f : V → EuclideanSpace ℂ ρ := fun ξ => (𝓕 F : 𝓢(V, ℂ)) ξ • g ξ
  have hgcont : Continuous g := by
    apply (PiLp.continuous_toLp 2 (fun _ : ρ => ℂ)).comp
    apply continuous_pi
    intro r
    apply (incidenceInnerPhase_continuous (x r)).mul
    exact continuous_finsetSum _ (fun k _ => continuous_const.mul
      (incidenceInnerPhase_continuous (y k)))
  have hg (ξ : V) : ‖g ξ‖ ≤ Real.sqrt K := by
    apply (Real.le_sqrt (norm_nonneg _) hK).mpr
    have he : ‖g ξ‖ ^ 2 =
        incidenceVectorEnergy (fun r => ∑ k, Z r k * incidenceRealChar ⟪ξ, y k⟫) := by
      simp only [g, PiLp.norm_sq_eq_of_L2, norm_mul,
        incidenceRealChar_norm, one_mul, incidenceVectorEnergy]
    rw [he]
    exact hresponse _ (fun k => le_of_eq (incidenceRealChar_norm _))
  have hfcont : Continuous f := (𝓕 F : 𝓢(V, ℂ)).continuous.smul hgcont
  have hfnorm (ξ : V) : ‖f ξ‖ ≤ ‖(𝓕 F : 𝓢(V, ℂ)) ξ‖ * Real.sqrt K := by
    dsimp only [f]
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hg ξ) (norm_nonneg _)
  have hf : Integrable f := ((𝓕 F : 𝓢(V, ℂ)).integrable.norm.mul_const (Real.sqrt K)).mono'
    hfcont.aestronglyMeasurable (Filter.Eventually.of_forall hfnorm)
  have hnorm : ‖∫ ξ : V, f ξ‖ ≤ (∫ ξ : V, ‖(𝓕 F : 𝓢(V, ℂ)) ξ‖) * Real.sqrt K := by
    calc
      _ ≤ ∫ ξ : V, ‖f ξ‖ := norm_integral_le_integral_norm f
      _ ≤ ∫ ξ : V, ‖(𝓕 F : 𝓢(V, ℂ)) ξ‖ * Real.sqrt K :=
        integral_mono hf.norm ((𝓕 F : 𝓢(V, ℂ)).integrable.norm.mul_const (Real.sqrt K)) hfnorm
      _ = _ := integral_mul_const _ _
  have hvalue : (∫ ξ : V, f ξ) = toLp 2 (fun r => ∑ k, Z r k * F (x r + y k)) := by
    apply PiLp.ext
    intro r
    have hp := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : ρ => ℂ) r).integral_comp_comm hf
    change (∫ ξ : V, (f ξ).ofLp r) = (∫ ξ : V, f ξ).ofLp r at hp
    rw [← hp]
    change (∫ ξ : V, (𝓕 F : 𝓢(V, ℂ)) ξ *
      (incidenceRealChar ⟪ξ, x r⟫ * ∑ k, Z r k * incidenceRealChar ⟪ξ, y k⟫)) = _
    calc
      _ = ∫ ξ : V, ∑ k, Z r k *
          ((𝓕 F : 𝓢(V, ℂ)) ξ * incidenceRealChar ⟪ξ, x r⟫ * incidenceRealChar ⟪ξ, y k⟫) := by
        apply integral_congr_ae
        filter_upwards with ξ
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = ∑ k, ∫ ξ : V, Z r k *
          ((𝓕 F : 𝓢(V, ℂ)) ξ * incidenceRealChar ⟪ξ, x r⟫ * incidenceRealChar ⟪ξ, y k⟫) :=
        integral_finsetSum _ (fun k _ =>
          (incidenceSchwartz_inverse_split F (x r) (y k)).1.const_mul (Z r k))
      _ = ∑ k, Z r k * F (x r + y k) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [integral_const_mul, (incidenceSchwartz_inverse_split F (x r) (y k)).2]
  rw [hvalue] at hnorm
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  simpa only [PiLp.norm_sq_eq_of_L2, incidenceVectorEnergy,
    mul_pow, Real.sq_sqrt hK] using hsq

#print axioms incidenceInnerPhase_continuous
#print axioms incidenceSchwartz_inverse_split
#print axioms incidenceSchwartz_separation_energy

end PrimeGap182Audit
