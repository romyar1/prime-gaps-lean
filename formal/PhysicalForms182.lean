import SourcePartitionMoments182

/-! Actual bilinear forms and erasure adjunction for the physical trial law.
All functions used below are constructed measurable bounded profiles.  The
simplex support condition supplies the already proved erasure norm bound. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

structure TrialRegularProfile (f : (Fin 39 → FiniteMeasure ℝ) → ℝ) : Prop where
  measurable : Measurable f
  bounded : ∃ B : ℝ, ∀ X, ‖f X‖ ≤ B
  support : ∀ X, (trialRadius : ℝ) < trialTotalMass X → f X = 0

theorem trial_regular_step : TrialRegularProfile trialStepFunction :=
  ⟨measurable_trialStepFunction, bounded_trialStepFunction, trialStepFunction_mass_support⟩

theorem trial_regular_source : TrialRegularProfile trialSourceStepFunction := by
  refine ⟨measurable_trialSourceStepFunction, ?_, trialSourceStepFunction_mass_support⟩
  obtain ⟨B, hB⟩ := bounded_trialStepFunction
  refine ⟨B, fun X => ?_⟩
  change ‖trialActualOuterMask X * trialStepFunction X‖ ≤ B
  by_cases h : TrialActualOuter X
  · simpa only [trialActualOuterMask, h, ite_true, one_mul] using hB X
  · simp only [trialActualOuterMask, h, ite_false, zero_mul, norm_zero]
    exact (norm_nonneg (trialStepFunction X)).trans (hB X)

namespace TrialRegularProfile

variable {f g : (Fin 39 → FiniteMeasure ℝ) → ℝ}

theorem integrable (hf : TrialRegularProfile f) : Integrable f (trialProductMeasure 39) := by
  obtain ⟨B, hB⟩ := hf.bounded
  exact Integrable.of_bound hf.measurable.aestronglyMeasurable B (ae_of_all _ hB)

theorem integrable_sq (hf : TrialRegularProfile f) :
    Integrable (fun X => f X ^ 2) (trialProductMeasure 39) := by
  obtain ⟨B, hB⟩ := hf.bounded
  simpa only [pow_two] using hf.integrable.mul_bdd hf.measurable.aestronglyMeasurable
    (ae_of_all _ hB)

theorem memLp (hf : TrialRegularProfile f) : MemLp f 2 (trialProductMeasure 39) :=
  (memLp_two_iff_integrable_sq hf.measurable.aestronglyMeasurable).mpr hf.integrable_sq

theorem add (hf : TrialRegularProfile f) (hg : TrialRegularProfile g) :
    TrialRegularProfile (fun X => f X + g X) := by
  refine ⟨hf.measurable.add hg.measurable, ?_, ?_⟩
  · obtain ⟨B, hB⟩ := hf.bounded
    obtain ⟨C, hC⟩ := hg.bounded
    exact ⟨B + C, fun X => (norm_add_le _ _).trans (add_le_add (hB X) (hC X))⟩
  · intro X hX
    rw [hf.support X hX, hg.support X hX, add_zero]

theorem sub (hf : TrialRegularProfile f) (hg : TrialRegularProfile g) :
    TrialRegularProfile (fun X => f X - g X) := by
  refine ⟨hf.measurable.sub hg.measurable, ?_, ?_⟩
  · obtain ⟨B, hB⟩ := hf.bounded
    obtain ⟨C, hC⟩ := hg.bounded
    exact ⟨B + C, fun X => (norm_sub_le _ _).trans (add_le_add (hB X) (hC X))⟩
  · intro X hX
    rw [hf.support X hX, hg.support X hX, sub_self]

theorem const_mul (hf : TrialRegularProfile f) (a : ℝ) :
    TrialRegularProfile (fun X => a * f X) := by
  refine ⟨hf.measurable.const_mul a, ?_, ?_⟩
  · obtain ⟨B, hB⟩ := hf.bounded
    refine ⟨‖a‖ * B, fun X => ?_⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB X) (norm_nonneg _)
  · intro X hX
    rw [hf.support X hX, mul_zero]

end TrialRegularProfile

def trialResidual (X : Fin 39 → FiniteMeasure ℝ) : ℝ :=
  trialStepFunction X - trialSourceStepFunction X

theorem trial_regular_residual : TrialRegularProfile trialResidual :=
  trial_regular_step.sub trial_regular_source

def trialErasure (f : (Fin 39 → FiniteMeasure ℝ) → ℝ)
    (i : Fin 39) (Y : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  ∫ X : FiniteMeasure ℝ, f (i.insertNth X Y) ∂trialPhysicalMeasure

theorem measurable_trialErasure {f : (Fin 39 → FiniteMeasure ℝ) → ℝ}
    (hf : TrialRegularProfile f) (i : Fin 39) : Measurable (trialErasure f i) := by
  let : IsFiniteMeasure trialPhysicalMeasure := trialPhysicalMeasure_finite
  have hins : Measurable
      (fun Z : FiniteMeasure ℝ × (Fin 38 → FiniteMeasure ℝ) => f (i.insertNth Z.1 Z.2)) :=
    hf.measurable.comp
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 39 => FiniteMeasure ℝ) i).symm.measurable
  exact (hins.stronglyMeasurable.integral_prod_left' (μ := trialPhysicalMeasure)).measurable

theorem bounded_trialErasure {f : (Fin 39 → FiniteMeasure ℝ) → ℝ}
    (hf : TrialRegularProfile f) (i : Fin 39) :
    ∃ B : ℝ, ∀ Y, ‖trialErasure f i Y‖ ≤ B := by
  let : IsFiniteMeasure trialPhysicalMeasure := trialPhysicalMeasure_finite
  obtain ⟨B, hB⟩ := hf.bounded
  exact ⟨B * trialPhysicalMeasure.real Set.univ, fun Y =>
    norm_integral_le_of_norm_le_const (ae_of_all _ fun X => hB (i.insertNth X Y))⟩

theorem integrable_trialErasure_fiber {f : (Fin 39 → FiniteMeasure ℝ) → ℝ}
    (hf : TrialRegularProfile f) (i : Fin 39) (Y : Fin 38 → FiniteMeasure ℝ) :
    Integrable (fun X : FiniteMeasure ℝ => f (i.insertNth X Y)) trialPhysicalMeasure := by
  let : IsFiniteMeasure trialPhysicalMeasure := trialPhysicalMeasure_finite
  obtain ⟨B, hB⟩ := hf.bounded
  have hi : Measurable (fun X : FiniteMeasure ℝ =>
      (i.insertNth X Y : Fin 39 → FiniteMeasure ℝ)) := by
    exact (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 39 => FiniteMeasure ℝ) i).symm.measurable.comp
      (measurable_id.prodMk measurable_const)
  exact Integrable.of_bound (hf.measurable.comp hi).aestronglyMeasurable B
    (ae_of_all _ fun X => hB (i.insertNth X Y))

theorem trialErasure_sub {f g : (Fin 39 → FiniteMeasure ℝ) → ℝ}
    (hf : TrialRegularProfile f) (hg : TrialRegularProfile g) (i : Fin 39) (Y) :
    trialErasure (fun X => f X - g X) i Y = trialErasure f i Y - trialErasure g i Y :=
  integral_sub (integrable_trialErasure_fiber hf i Y) (integrable_trialErasure_fiber hg i Y)

theorem trialErasure_add {f g : (Fin 39 → FiniteMeasure ℝ) → ℝ}
    (hf : TrialRegularProfile f) (hg : TrialRegularProfile g) (i : Fin 39) (Y) :
    trialErasure (fun X => f X + g X) i Y = trialErasure f i Y + trialErasure g i Y :=
  integral_add (integrable_trialErasure_fiber hf i Y) (integrable_trialErasure_fiber hg i Y)

theorem trialErasure_const_mul (f : (Fin 39 → FiniteMeasure ℝ) → ℝ)
    (a : ℝ) (i : Fin 39) (Y) :
    trialErasure (fun X => a * f X) i Y = a * trialErasure f i Y := integral_const_mul _ _

theorem trial_integrable_bounded_product {d : ℕ}
    {f g : (Fin d → FiniteMeasure ℝ) → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hfb : ∃ B : ℝ, ∀ X, ‖f X‖ ≤ B) (hgb : ∃ B : ℝ, ∀ X, ‖g X‖ ≤ B) :
    Integrable (fun X => f X * g X) (trialProductMeasure d) := by
  obtain ⟨B, hB⟩ := hfb
  obtain ⟨C, hC⟩ := hgb
  exact (Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ hB)).mul_bdd
    hg.aestronglyMeasurable (ae_of_all _ hC)

theorem trial_bounded_mul {α : Type*} {f g : α → ℝ}
    (hf : ∃ B : ℝ, ∀ X, ‖f X‖ ≤ B) (hg : ∃ B : ℝ, ∀ X, ‖g X‖ ≤ B) :
    ∃ B : ℝ, ∀ X, ‖f X * g X‖ ≤ B := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨C, hC⟩ := hg
  refine ⟨|B| * |C|, fun X => ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((hB X).trans (le_abs_self _)) ((hC X).trans (le_abs_self _))
    (norm_nonneg _) (abs_nonneg _)

def trialRootPair (f g : (Fin 39 → FiniteMeasure ℝ) → ℝ) : ℝ :=
  ∫ X, f X * g X ∂trialProductMeasure 39

def trialFacePair (w : (Fin 38 → FiniteMeasure ℝ) → ℝ)
    (f g : (Fin 39 → FiniteMeasure ℝ) → ℝ) : ℝ :=
  (trialRhoStar : ℝ) * ∑ i : Fin 39,
    ∫ Y, w Y * trialErasure f i Y * trialErasure g i Y ∂trialProductMeasure 38

theorem integrable_trialFacePair_integrand
    {w : (Fin 38 → FiniteMeasure ℝ) → ℝ} (hw : Measurable w)
    (hwb : ∃ B : ℝ, ∀ Y, ‖w Y‖ ≤ B)
    {f g : (Fin 39 → FiniteMeasure ℝ) → ℝ}
    (hf : TrialRegularProfile f) (hg : TrialRegularProfile g) (i : Fin 39) :
    Integrable (fun Y => w Y * trialErasure f i Y * trialErasure g i Y) (trialProductMeasure 38) :=
  trial_integrable_bounded_product (hw.mul (measurable_trialErasure hf i))
    (measurable_trialErasure hg i) (trial_bounded_mul hwb (bounded_trialErasure hf i))
    (bounded_trialErasure hg i)

theorem trialRootPair_symm (f g : (Fin 39 → FiniteMeasure ℝ) → ℝ) :
    trialRootPair f g = trialRootPair g f := by
  apply integral_congr_ae
  exact ae_of_all _ fun X => mul_comm _ _

theorem trialFacePair_symm (w : (Fin 38 → FiniteMeasure ℝ) → ℝ)
    (f g : (Fin 39 → FiniteMeasure ℝ) → ℝ) : trialFacePair w f g = trialFacePair w g f := by
  unfold trialFacePair
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  exact ae_of_all _ fun Y => by ring

theorem trialErasure_adjoint {f : (Fin 39 → FiniteMeasure ℝ) → ℝ}
    (hf : TrialRegularProfile f) (i : Fin 39)
    {H : (Fin 38 → FiniteMeasure ℝ) → ℝ}
    (hH : Measurable H) (hHb : ∃ B : ℝ, ∀ Y, ‖H Y‖ ≤ B) :
    (∫ X, f X * H (i.removeNth X) ∂trialProductMeasure 39) =
      ∫ Y, trialErasure f i Y * H Y ∂trialProductMeasure 38 := by
  let : IsFiniteMeasure trialPhysicalMeasure := trialPhysicalMeasure_finite
  let e : (FiniteMeasure ℝ × (Fin 38 → FiniteMeasure ℝ)) ≃ᵐ
      (Fin 39 → FiniteMeasure ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 39 => FiniteMeasure ℝ) i).symm
  have he : MeasurePreserving e (trialPhysicalMeasure.prod (trialProductMeasure 38))
      (trialProductMeasure 39) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin 39 => trialPhysicalMeasure) i).symm
  have hr : Measurable (fun X : Fin 39 → FiniteMeasure ℝ => i.removeNth X) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply (i.succAbove j)
  have hraw : Integrable (fun X => f X * H (i.removeNth X)) (trialProductMeasure 39) :=
    trial_integrable_bounded_product hf.measurable (hH.comp hr) hf.bounded
      (by obtain ⟨B, hB⟩ := hHb; exact ⟨B, fun X => hB (i.removeNth X)⟩)
  calc
    _ = ∫ Z, f (e Z) * H (i.removeNth (e Z))
        ∂trialPhysicalMeasure.prod (trialProductMeasure 38) := (he.integral_comp' _).symm
    _ = ∫ Y, ∫ X : FiniteMeasure ℝ, f (i.insertNth X Y) * H Y
        ∂trialPhysicalMeasure ∂trialProductMeasure 38 := by
      have hh : Integrable (fun Z => f (e Z) * H (i.removeNth (e Z)))
          (trialPhysicalMeasure.prod (trialProductMeasure 38)) :=
        he.integrable_comp_of_integrable hraw
      rw [integral_prod_symm _ hh]
      apply integral_congr_ae
      filter_upwards [] with Y
      change (∫ X : FiniteMeasure ℝ, f (i.insertNth X Y) *
        H (i.removeNth (i.insertNth X Y : Fin 39 → FiniteMeasure ℝ))
        ∂trialPhysicalMeasure) = _
      simp only [Fin.removeNth_insertNth]
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun Y => integral_mul_const _ _

theorem trialErasure_energy_bound {f : (Fin 39 → FiniteMeasure ℝ) → ℝ}
    (hf : TrialRegularProfile f) :
    (∑ i : Fin 39, ∫ Y, trialErasure f i Y ^ 2 ∂trialProductMeasure 38) ≤
      4 * trialRootPair f f := by
  simpa only [trialRootPair, trialErasure, pow_two] using
    trial_physical_face_operator_bound f hf.memLp (ae_of_all _ hf.support)

#print axioms trialErasure_adjoint
#print axioms trialErasure_energy_bound

end PrimeGap182
