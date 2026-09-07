import IncidenceGcdLattice
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Modulated Poisson summation for actual Schwartz functions

All phases are actual real additive characters. Modulation is constructed
as a Schwartz-space map using the proved temperate growth of exp(i x).
The summability and Fourier-translation identities are derived, not assumed.
-/

noncomputable section

namespace PrimeGap182Audit

open MeasureTheory Filter Asymptotics
open scoped BigOperators FourierTransform SchwartzMap

def incidenceRealChar (t : ℝ) : ℂ := (Real.fourierChar t : ℂ)

@[simp] theorem incidenceRealChar_zero : incidenceRealChar 0 = 1 := by
  simp [incidenceRealChar]

@[simp] theorem incidenceRealChar_norm (t : ℝ) : ‖incidenceRealChar t‖ = 1 :=
  Circle.norm_coe _

theorem incidenceRealChar_add (s t : ℝ) :
    incidenceRealChar (s + t) = incidenceRealChar s * incidenceRealChar t := by
  simp [incidenceRealChar, AddChar.map_add_eq_mul]

theorem incidenceRealChar_fourier (n : ℤ) (x : ℝ) :
    fourier n (x : UnitAddCircle) = incidenceRealChar ((n : ℝ) * x) := by
  rw [fourier_coe_apply]
  simp only [incidenceRealChar, Real.fourierChar_apply, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_intCast, Complex.ofReal_one, div_one]
  congr 1
  ring

theorem incidenceRealChar_temperate (θ : ℝ) :
    (fun x : ℝ => incidenceRealChar (-θ * x)).HasTemperateGrowth := by
  change ((fun t : ℝ => Complex.exp (t * Complex.I)) ∘
    (fun x : ℝ => 2 * Real.pi * (-θ * x))).HasTemperateGrowth
  exact Complex.hasTemperateGrowth_exp_mul_I.comp (by fun_prop)

def incidenceModulatedSchwartz (θ : ℝ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => incidenceRealChar (-θ * x)) f

theorem incidenceModulatedSchwartz_apply (θ : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    incidenceModulatedSchwartz θ f x = incidenceRealChar (-θ * x) * f x := by
  simpa only [incidenceModulatedSchwartz, smul_eq_mul] using
    SchwartzMap.smulLeftCLM_apply_apply (incidenceRealChar_temperate θ) f x

theorem incidenceFourier_modulation (θ : ℝ) (f : 𝓢(ℝ, ℂ)) (y : ℝ) :
    𝓕 (incidenceModulatedSchwartz θ f) y = 𝓕 f (y + θ) := by
  change 𝓕 (fun x => incidenceModulatedSchwartz θ f x) y = 𝓕 (fun x => f x) (y + θ)
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  congr 1 with x
  simp only [Circle.smul_def, smul_eq_mul, incidenceModulatedSchwartz_apply]
  change incidenceRealChar (-(x * y)) * (incidenceRealChar (-θ * x) * f x) =
    incidenceRealChar (-(x * (y + θ))) * f x
  rw [← mul_assoc, ← incidenceRealChar_add]
  congr 2
  ring

/-- Absolute summability of every real translate of a Schwartz function on the integers. -/
theorem incidenceSchwartz_sample_norm_summable (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Summable (fun n : ℤ => ‖f (x + (n : ℝ))‖) := by
  let g : 𝓢(ℝ, ℂ) := f.compSubConstCLM ℂ (-x)
  have hs : Summable (fun n : ℤ => g (n : ℝ)) := by
    apply summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    simpa only [Function.comp_def, Real.norm_eq_abs] using
      (g.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite
  simpa only [g, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, add_comm] using hs.norm

theorem incidencePoisson_modulated_norm_summable (f : 𝓢(ℝ, ℂ)) (θ x : ℝ) :
    Summable (fun n : ℤ => ‖𝓕 f ((n : ℝ) + θ) * incidenceRealChar ((n : ℝ) * x)‖) := by
  simp only [norm_mul, incidenceRealChar_norm, mul_one]
  simpa only [add_comm] using incidenceSchwartz_sample_norm_summable (𝓕 f) θ

/-- The full modulated, translated Poisson identity, with its absolute
convergence proved from the actual Schwartz functions. -/
theorem incidencePoisson_modulated (f : 𝓢(ℝ, ℂ)) (θ x : ℝ) :
    HasSum (fun n : ℤ => 𝓕 f ((n : ℝ) + θ) * incidenceRealChar ((n : ℝ) * x))
      (∑' k : ℤ, incidenceRealChar (-θ * (x + (k : ℝ))) * f (x + (k : ℝ))) := by
  let g := incidenceModulatedSchwartz θ f
  have hp := SchwartzMap.tsum_eq_tsum_fourier g x
  change (∑' k : ℤ, g (x + (k : ℝ))) =
    ∑' n : ℤ, 𝓕 g (n : ℝ) * fourier n (x : UnitAddCircle) at hp
  simp only [g, incidenceModulatedSchwartz_apply, incidenceFourier_modulation,
    incidenceRealChar_fourier] at hp
  exact (incidencePoisson_modulated_norm_summable f θ x).of_norm.hasSum_iff.mpr hp.symm

/-- A translated sample with a modulation in the integer variable. -/
theorem incidencePoisson_translated (f : 𝓢(ℝ, ℂ)) (θ x : ℝ) :
    HasSum (fun n : ℤ => 𝓕 f ((n : ℝ) + θ) * incidenceRealChar (((n : ℝ) + θ) * x))
      (∑' k : ℤ, f (x + (k : ℝ)) * incidenceRealChar (-θ * (k : ℝ))) := by
  have hp := (incidencePoisson_modulated f θ x).mul_left (incidenceRealChar (θ * x))
  have ht (n : ℤ) :
      incidenceRealChar (θ * x) *
        (𝓕 f ((n : ℝ) + θ) * incidenceRealChar ((n : ℝ) * x)) =
        𝓕 f ((n : ℝ) + θ) * incidenceRealChar (((n : ℝ) + θ) * x) := by
    calc
      _ = 𝓕 f ((n : ℝ) + θ) *
          (incidenceRealChar (θ * x) * incidenceRealChar ((n : ℝ) * x)) := by ring
      _ = _ := by rw [← incidenceRealChar_add]; congr 2; ring
  have hv : incidenceRealChar (θ * x) *
      (∑' k : ℤ, incidenceRealChar (-θ * (x + (k : ℝ))) * f (x + (k : ℝ))) =
      ∑' k : ℤ, f (x + (k : ℝ)) * incidenceRealChar (-θ * (k : ℝ)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [← mul_assoc, ← incidenceRealChar_add]
    rw [show θ * x + -θ * (x + (k : ℝ)) = -θ * (k : ℝ) by ring]
    ring
  rw [hv] at hp
  exact hp.congr_fun (fun n => (ht n).symm)

#print axioms incidencePoisson_translated

#print axioms incidenceFourier_modulation
#print axioms incidenceSchwartz_sample_norm_summable
#print axioms incidencePoisson_modulated

end PrimeGap182Audit
