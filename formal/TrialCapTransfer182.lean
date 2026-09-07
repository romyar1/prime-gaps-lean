import PhysicalRestoration182
import BandRadialGeometry182

/-! Exact physical-law transfer from the inward trial cap to the larger
arithmetic coefficient cap. Restriction is not probability conditioning:
the exponential physical scaling is retained. The generic restriction
argument follows the proved baseline full-configuration cap identity. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace PrimeGap182

def trialAmbientMeasure (κ : ℝ) : Measure (FiniteMeasure ℝ) :=
  ENNReal.ofReal (Real.exp Real.eulerMascheroniConstant * κ) • PrimeGap186.fragmentLaw κ

def trialAmbientProduct (κ : ℝ) (d : ℕ) : Measure (Fin d → FiniteMeasure ℝ) :=
  Measure.pi (fun _ : Fin d => trialAmbientMeasure κ)

instance trialAmbientMeasure_finite (κ : ℝ) : IsFiniteMeasure (trialAmbientMeasure κ) := by
  let : IsProbabilityMeasure (PrimeGap186.fragmentLaw κ) := PrimeGap186.fragmentLaw_isProbabilityMeasure κ
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top

instance trialAmbientProduct_finite (κ : ℝ) (d : ℕ) : IsFiniteMeasure (trialAmbientProduct κ d) := by
  unfold trialAmbientProduct
  infer_instance

theorem trial_coefficient_cap_gap :
    PrimeGap182Analytic.selbergFragmentCap182 - (trialLargestCap : ℝ) =
      40569403 / 32255864832000 ∧
    (trialLargestCap : ℝ) < PrimeGap182Analytic.selbergFragmentCap182 := by
  norm_num [PrimeGap182Analytic.selbergFragmentCap182, PrimeGap182Analytic.selbergRho182,
    trialLargestCap]

theorem trialAmbient_cap_restrict (κ : ℝ) (hκ : (trialLargestCap : ℝ) ≤ κ) :
    (trialAmbientMeasure κ).restrict
      {X : FiniteMeasure ℝ | (X : Measure ℝ) (Set.Ioi (trialLargestCap : ℝ)) = 0} =
      trialPhysicalMeasure :=
  (PrimeGap186.fragmentLaw_full_configuration_cap_restriction κ (trialLargestCap : ℝ)
    (by norm_num [trialLargestCap]) hκ).2

theorem trialAmbient_pi_cap_restrict (κ : ℝ) (hκ : (trialLargestCap : ℝ) ≤ κ) (d : ℕ) :
    MeasurableSet {X : Fin d → FiniteMeasure ℝ | TrialCapAllowed trialLargestCap X} ∧
      (trialAmbientProduct κ d).restrict {X | TrialCapAllowed trialLargestCap X} =
        trialProductMeasure d := by
  let C : Set (FiniteMeasure ℝ) := {X | (X : Measure ℝ) (Set.Ioi (trialLargestCap : ℝ)) = 0}
  have hc := PrimeGap186.fragmentLaw_full_configuration_cap_restriction κ (trialLargestCap : ℝ)
    (by norm_num [trialLargestCap]) hκ
  have heq : {X : Fin d → FiniteMeasure ℝ | TrialCapAllowed trialLargestCap X} =
      Set.univ.pi (fun _ : Fin d => C) := by
    ext X
    simp only [TrialCapAllowed, C, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const]
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact MeasurableSet.univ_pi fun _ => hc.1
  · rw [heq]
    change (Measure.pi (fun _ : Fin d => trialAmbientMeasure κ)).restrict
      (Set.univ.pi fun _ : Fin d => C) = _
    rw [Measure.restrict_pi_pi]
    exact congrArg Measure.pi (funext fun _ => trialAmbient_cap_restrict κ hκ)

theorem trialAmbient_integral_eq (κ : ℝ) (hκ : (trialLargestCap : ℝ) ≤ κ) (d : ℕ)
    (f : (Fin d → FiniteMeasure ℝ) → ℝ)
    (hf : ∀ᵐ X ∂trialAmbientProduct κ d, f X ≠ 0 → TrialCapAllowed trialLargestCap X) :
    (∫ X, f X ∂trialAmbientProduct κ d) = ∫ X, f X ∂trialProductMeasure d := by
  have hz : ∀ᵐ X ∂trialAmbientProduct κ d,
      X ∉ {X | TrialCapAllowed trialLargestCap X} → f X = 0 :=
    hf.mono fun _ hX => not_imp_comm.mp hX
  calc
    _ = ∫ X in {X | TrialCapAllowed trialLargestCap X}, f X ∂trialAmbientProduct κ d :=
      (setIntegral_eq_integral_of_ae_compl_eq_zero hz).symm
    _ = _ := by rw [(trialAmbient_pi_cap_restrict κ hκ d).2]

theorem trialAmbient_fiber_eq (κ : ℝ) (hκ : (trialLargestCap : ℝ) ≤ κ)
    (d : ℕ) (i : Fin (d + 1)) (f : (Fin (d + 1) → FiniteMeasure ℝ) → ℝ)
    (hf : ∀ᵐ X ∂trialAmbientProduct κ (d + 1), f X ≠ 0 → TrialCapAllowed trialLargestCap X) :
    (∀ᵐ Y ∂trialAmbientProduct κ d,
      (∫ Z : FiniteMeasure ℝ, f (i.insertNth Z Y) ∂trialAmbientMeasure κ) =
        (∫ Z : FiniteMeasure ℝ, f (i.insertNth Z Y) ∂trialPhysicalMeasure) ∧
      (¬ TrialCapAllowed trialLargestCap Y →
        (∫ Z : FiniteMeasure ℝ, f (i.insertNth Z Y) ∂trialAmbientMeasure κ) = 0)) ∧
    ∀ᵐ Y ∂trialProductMeasure d,
      (∫ Z : FiniteMeasure ℝ, f (i.insertNth Z Y) ∂trialAmbientMeasure κ) =
        (∫ Z : FiniteMeasure ℝ, f (i.insertNth Z Y) ∂trialPhysicalMeasure) := by
  let C : Set (FiniteMeasure ℝ) :=
    {Z | (Z : Measure ℝ) (Set.Ioi (trialLargestCap : ℝ)) = 0}
  have hcap : (trialAmbientMeasure κ).restrict C = trialPhysicalMeasure := trialAmbient_cap_restrict κ hκ
  have hins : MeasurePreserving
      (fun p : (Fin d → FiniteMeasure ℝ) × FiniteMeasure ℝ =>
        (i.insertNth p.2 p.1 : Fin (d + 1) → FiniteMeasure ℝ))
      ((trialAmbientProduct κ d).prod (trialAmbientMeasure κ)) (trialAmbientProduct κ (d + 1)) := by
    simpa only [trialAmbientProduct, Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Equiv.coe_fn_mk, Prod.swap] using
      ((measurePreserving_piFinSuccAbove (fun _ : Fin (d + 1) => trialAmbientMeasure κ) i).symm.comp
        (Measure.measurePreserving_swap (μ := trialAmbientProduct κ d) (ν := trialAmbientMeasure κ)))
  have hcurr := Measure.ae_ae_of_ae_prod (hins.quasiMeasurePreserving.ae hf)
  have hmain : ∀ᵐ Y ∂trialAmbientProduct κ d,
      (∫ Z : FiniteMeasure ℝ, f (i.insertNth Z Y) ∂trialAmbientMeasure κ) =
        (∫ Z : FiniteMeasure ℝ, f (i.insertNth Z Y) ∂trialPhysicalMeasure) ∧
      (¬ TrialCapAllowed trialLargestCap Y →
        (∫ Z : FiniteMeasure ℝ, f (i.insertNth Z Y) ∂trialAmbientMeasure κ) = 0) := by
    filter_upwards [hcurr] with Y hY
    have hz : ∀ᵐ Z ∂trialAmbientMeasure κ, Z ∉ C → f (i.insertNth Z Y) = 0 := by
      filter_upwards [hY] with Z hZ hnot
      by_contra hne
      apply hnot
      simpa only [C, Set.mem_ofPred_eq, Fin.insertNth_apply_same] using hZ hne i
    refine ⟨?_, ?_⟩
    · rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hz, hcap]
    · intro hnot
      apply integral_eq_zero_of_ae
      filter_upwards [hY] with Z hZ
      by_contra hne
      apply hnot
      intro j
      simpa only [Fin.insertNth_apply_succAbove] using hZ hne (i.succAbove j)
  have hle : trialProductMeasure d ≤ trialAmbientProduct κ d := by
    rw [← (trialAmbient_pi_cap_restrict κ hκ d).2]
    exact Measure.restrict_le_self
  exact ⟨hmain, (ae_mono hle) (hmain.mono fun _ hY => hY.1)⟩

theorem trialAmbient_fiber_function_integral_eq (κ : ℝ) (hκ : (trialLargestCap : ℝ) ≤ κ)
    (d r : ℕ) (i : Fin (d + 1)) (f : Fin r → (Fin (d + 1) → FiniteMeasure ℝ) → ℝ)
    (Ψ : (Fin d → FiniteMeasure ℝ) → (Fin r → ℝ) → ℝ)
    (hΨ : ∀ Y, Ψ Y (fun _ => 0) = 0)
    (hf : ∀ j : Fin r, ∀ᵐ X ∂trialAmbientProduct κ (d + 1),
      f j X ≠ 0 → TrialCapAllowed trialLargestCap X) :
    (∫ Y, Ψ Y (fun j => ∫ Z : FiniteMeasure ℝ, f j (i.insertNth Z Y) ∂trialAmbientMeasure κ)
      ∂trialAmbientProduct κ d) =
      ∫ Y, Ψ Y (fun j => ∫ Z : FiniteMeasure ℝ, f j (i.insertNth Z Y) ∂trialPhysicalMeasure)
        ∂trialProductMeasure d := by
  let U : Fin r → (Fin d → FiniteMeasure ℝ) → ℝ := fun j Y =>
    ∫ Z : FiniteMeasure ℝ, f j (i.insertNth Z Y) ∂trialAmbientMeasure κ
  let V : Fin r → (Fin d → FiniteMeasure ℝ) → ℝ := fun j Y =>
    ∫ Z : FiniteMeasure ℝ, f j (i.insertNth Z Y) ∂trialPhysicalMeasure
  have hfaces : ∀ᵐ Y ∂trialAmbientProduct κ d, ∀ j : Fin r,
      U j Y = V j Y ∧ (¬ TrialCapAllowed trialLargestCap Y → U j Y = 0) :=
    ae_all_iff.mpr fun j => (trialAmbient_fiber_eq κ hκ d i (f j) (hf j)).1
  have hphysical : ∀ᵐ Y ∂trialProductMeasure d, ∀ j : Fin r, U j Y = V j Y :=
    ae_all_iff.mpr fun j => (trialAmbient_fiber_eq κ hκ d i (f j) (hf j)).2
  have hsupport : ∀ᵐ Y ∂trialAmbientProduct κ d,
      Ψ Y (fun j => U j Y) ≠ 0 → TrialCapAllowed trialLargestCap Y := by
    filter_upwards [hfaces] with Y hY hne
    by_contra hnot
    have hz : (fun j => U j Y) = fun _ => 0 := funext fun j => (hY j).2 hnot
    exact hne (by rw [hz, hΨ Y])
  calc
    _ = ∫ Y, Ψ Y (fun j => U j Y) ∂trialProductMeasure d :=
      trialAmbient_integral_eq κ hκ d (fun Y => Ψ Y (fun j => U j Y)) hsupport
    _ = _ := integral_congr_ae (hphysical.mono fun Y hY => congrArg (Ψ Y) (funext hY))

theorem trialSourceStepFunction_cap (X : Fin 39 → FiniteMeasure ℝ)
    (hX : trialSourceStepFunction X ≠ 0) : TrialCapAllowed trialLargestCap X := by
  have hF : trialStepFunction X ≠ 0 := by
    intro hf
    exact hX (by simp only [trialSourceStepFunction, hf, mul_zero])
  exact (trialStepFunction_support X hF).2.2.1

theorem trialSourceStepFunction_ambient_square (κ : ℝ) (hκ : (trialLargestCap : ℝ) ≤ κ) :
    (∫ X, trialSourceStepFunction X ^ 2 ∂trialAmbientProduct κ 39) =
      trialRootPair trialSourceStepFunction trialSourceStepFunction := by
  have h := trialAmbient_integral_eq κ hκ 39 (fun X => trialSourceStepFunction X ^ 2)
    (ae_of_all _ fun X hX => trialSourceStepFunction_cap X
      ((pow_ne_zero_iff (by decide : 2 ≠ 0)).mp hX))
  simpa only [trialRootPair, pow_two] using h

theorem trialSourceStepFunction_ambient_face (κ : ℝ) (hκ : (trialLargestCap : ℝ) ≤ κ)
    (w : (Fin 38 → FiniteMeasure ℝ) → ℝ) (i : Fin 39) :
    (∫ Y, w Y * (∫ Z : FiniteMeasure ℝ, trialSourceStepFunction (i.insertNth Z Y)
      ∂trialAmbientMeasure κ) ^ 2 ∂trialAmbientProduct κ 38) =
      ∫ Y, w Y * trialErasure trialSourceStepFunction i Y ^ 2 ∂trialProductMeasure 38 :=
  trialAmbient_fiber_function_integral_eq κ hκ 38 1 i (fun _ => trialSourceStepFunction)
    (fun Y v => w Y * v 0 ^ 2) (fun _ => by norm_num)
    (fun _ => ae_of_all _ trialSourceStepFunction_cap)

theorem physical_restored_energy_coefficient_cap182 (h : PhysicalSourceBounds182) :
    0 < (trialRhoStar : ℝ) * (∑ i : Fin 39,
        ∫ Y, trialActualFaceMultiplier Y *
          (∫ Z : FiniteMeasure ℝ, trialSourceStepFunction (i.insertNth Z Y)
            ∂PrimeGap182Analytic.selbergPhysicalMeasure182) ^ 2
          ∂Measure.pi (fun _ : Fin 38 => PrimeGap182Analytic.selbergPhysicalMeasure182)) -
      ∫ X, trialSourceStepFunction X ^ 2
        ∂Measure.pi (fun _ : Fin 39 => PrimeGap182Analytic.selbergPhysicalMeasure182) := by
  change 0 < (trialRhoStar : ℝ) * (∑ i : Fin 39,
        ∫ Y, trialActualFaceMultiplier Y *
          (∫ Z : FiniteMeasure ℝ, trialSourceStepFunction (i.insertNth Z Y)
            ∂trialAmbientMeasure PrimeGap182Analytic.selbergFragmentCap182) ^ 2
          ∂trialAmbientProduct PrimeGap182Analytic.selbergFragmentCap182 38) -
      ∫ X, trialSourceStepFunction X ^ 2 ∂trialAmbientProduct PrimeGap182Analytic.selbergFragmentCap182 39
  simp_rw [trialSourceStepFunction_ambient_face _ trial_coefficient_cap_gap.2.le,
    trialSourceStepFunction_ambient_square _ trial_coefficient_cap_gap.2.le]
  simpa only [trialRestoredEnergy, trialFacePair, pow_two, mul_assoc] using
    physical_restored_energy_positive182 h

#print axioms trialAmbient_pi_cap_restrict
#print axioms trialAmbient_fiber_function_integral_eq
#print axioms physical_restored_energy_coefficient_cap182

end PrimeGap182
