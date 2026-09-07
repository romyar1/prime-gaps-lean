import PhysicalSources182

/-!
The actual 39-coordinate erasure norm bound, using the Dickman mass density
of the constructed fragment law.  The weighted fiber argument is adapted
from the checked generic argument at baseline lines 195794--196156, with
39 coordinates and weight 38 in each fiber.  No operator bound is assumed.
-/

noncomputable section
open MeasureTheory PrimeGap186
open scoped BigOperators ENNReal InnerProductSpace

namespace PrimeGap182

theorem trialPhysicalMeasure_mass_map :
    Measure.map (fun X : FiniteMeasure ℝ => (X.mass : ℝ)) trialPhysicalMeasure =
        (volume.restrict (Set.Ici (0 : ℝ))).withDensity
          (fun t => ENNReal.ofReal (dickmanRho (t / (trialLargestCap : ℝ)))) ∧
      Measure.map (fun X : FiniteMeasure ℝ => (X.mass : ℝ)) trialPhysicalMeasure ≤
        volume.restrict (Set.Ici (0 : ℝ)) := by
  have hcap : 0 < (trialLargestCap : ℝ) :=
    by norm_num [trialLargestCap]
  have heq : Measure.map (fun X : FiniteMeasure ℝ => (X.mass : ℝ))
      trialPhysicalMeasure =
      (volume.restrict (Set.Ici (0 : ℝ))).withDensity
        (fun t => ENNReal.ofReal (dickmanRho (t / (trialLargestCap : ℝ)))) := by
    have hm : Measurable (fun X : FiniteMeasure ℝ => (X.mass : ℝ)) :=
      ((Measure.measurable_coe MeasurableSet.univ).comp
        measurable_subtype_coe).ennreal_toReal
    simpa only [trialPhysicalMeasure, Measure.map_smul _ hm.aemeasurable] using
      normalized_fragmentLaw_mass_eq_dickman (trialLargestCap : ℝ) hcap
  refine ⟨heq, ?_⟩
  rw [heq]
  have hle : (fun t : ℝ => ENNReal.ofReal
      (dickmanRho (t / (trialLargestCap : ℝ)))) ≤ᵐ[volume.restrict (Set.Ici 0)]
      (1 : ℝ → ℝ≥0∞) := by
    filter_upwards [] with t
    exact ENNReal.ofReal_le_one.mpr (dickmanRho_analytic.2.2.2.2.2.1 _).2
  simpa only [withDensity_one] using withDensity_mono hle

theorem trial_inverse_face_fiber (a : ℝ) (ha : 0 < a) :
    (∫ X : FiniteMeasure ℝ in {X | (X.mass : ℝ) ≤ a},
      (a + 38 * (X.mass : ℝ))⁻¹ ∂trialPhysicalMeasure) ≤ Real.log 39 / 38 := by
  have hm : Measurable (fun X : FiniteMeasure ℝ => (X.mass : ℝ)) :=
    ((Measure.measurable_coe MeasurableSet.univ).comp measurable_subtype_coe).ennreal_toReal
  have hreal : Measurable (fun t : ℝ => (a + 38 * t)⁻¹) :=
    (measurable_const.add (measurable_const.mul measurable_id)).inv
  have hdom :
      (Measure.map (fun X : FiniteMeasure ℝ => (X.mass : ℝ))
        trialPhysicalMeasure).restrict (Set.Iic a) ≤ volume.restrict (Set.Icc 0 a) := by
    calc
      _ ≤ (volume.restrict (Set.Ici (0 : ℝ))).restrict (Set.Iic a) :=
        Measure.restrict_mono_measure trialPhysicalMeasure_mass_map.2 _
      _ = _ := by
        rw [Measure.restrict_restrict measurableSet_Iic, Set.Iic_inter_Ici]
  have hcont : ContinuousOn (fun t : ℝ => (a + 38 * t)⁻¹) (Set.Icc 0 a) := by
    apply (continuous_const.add (continuous_const.mul continuous_id)).continuousOn.inv₀
    intro t ht
    change a + 38 * t ≠ 0
    exact ne_of_gt (by nlinarith [ht.1])
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc 0 a)]
      (fun t : ℝ => (a + 38 * t)⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact inv_nonneg.mpr (by nlinarith [ht.1])
  have heval : (∫ t : ℝ in Set.Icc 0 a, (a + 38 * t)⁻¹) = Real.log 39 / 38 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha.le]
    rw [intervalIntegral.integral_comp_add_mul (fun t : ℝ => t⁻¹)
      (by norm_num : (38 : ℝ) ≠ 0) a]
    simp only [mul_zero, add_zero, smul_eq_mul]
    rw [integral_inv_of_pos ha (by linarith : 0 < a + 38 * a)]
    rw [show (a + 38 * a) / a = 39 by field_simp; ring]
    ring
  calc
    _ = ∫ t : ℝ in Set.Iic a, (a + 38 * t)⁻¹
        ∂Measure.map (fun X : FiniteMeasure ℝ => (X.mass : ℝ)) trialPhysicalMeasure :=
      (setIntegral_map measurableSet_Iic hreal.aestronglyMeasurable hm.aemeasurable).symm
    _ ≤ ∫ t : ℝ in Set.Icc 0 a, (a + 38 * t)⁻¹ :=
      integral_mono_measure hdom hnonneg hcont.integrableOn_Icc
    _ = _ := heval

theorem trial_weighted_face_fiber
    (a : ℝ) (ha : 0 ≤ a) (f : FiniteMeasure ℝ → ℝ)
    (hf : MemLp f 2 trialPhysicalMeasure)
    (hsupport : ∀ᵐ X ∂trialPhysicalMeasure, a < (X.mass : ℝ) → f X = 0) :
    Integrable (fun X => (a + 38 * (X.mass : ℝ)) * f X ^ 2) trialPhysicalMeasure ∧
      (∫ X, f X ∂trialPhysicalMeasure) ^ 2 ≤
        (Real.log 39 / 38) *
          ∫ X, (a + 38 * (X.mass : ℝ)) * f X ^ 2 ∂trialPhysicalMeasure := by
  let : IsFiniteMeasure trialPhysicalMeasure := trialPhysicalMeasure_finite
  have hm : Measurable (fun X : FiniteMeasure ℝ => (X.mass : ℝ)) :=
    ((Measure.measurable_coe MeasurableSet.univ).comp measurable_subtype_coe).ennreal_toReal
  let w : FiniteMeasure ℝ → ℝ := fun X => a + 38 * (X.mass : ℝ)
  have hwm : Measurable w := measurable_const.add (measurable_const.mul hm)
  have hw0 (X : FiniteMeasure ℝ) : 0 ≤ w X := by
    dsimp only [w]
    nlinarith [X.mass.coe_nonneg]
  have hemeas : AEStronglyMeasurable (fun X => w X * f X ^ 2)
      trialPhysicalMeasure := hwm.aestronglyMeasurable.mul (hf.aestronglyMeasurable.pow 2)
  have henergy : Integrable (fun X => w X * f X ^ 2) trialPhysicalMeasure := by
    apply (hf.integrable_sq.const_mul (39 * a)).mono' hemeas
    filter_upwards [hsupport] with X hs
    rw [Real.norm_of_nonneg (mul_nonneg (hw0 X) (sq_nonneg _))]
    by_cases hX : (X.mass : ℝ) ≤ a
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      dsimp only [w]
      linarith
    · rw [hs (lt_of_not_ge hX)]
      simp
  refine ⟨henergy, ?_⟩
  by_cases ha0 : a = 0
  · subst a
    have hmassNe : ∀ᵐ X ∂trialPhysicalMeasure, (X.mass : ℝ) ≠ 0 :=
      ae_of_ae_map hm.aemeasurable
        ((ae_mono trialPhysicalMeasure_mass_map.2)
          (Measure.ae_ne (volume.restrict (Set.Ici (0 : ℝ))) 0))
    have hfzero : f =ᵐ[trialPhysicalMeasure] 0 := by
      filter_upwards [hsupport, hmassNe] with X hs hX
      exact hs (lt_of_le_of_ne X.mass.coe_nonneg (Ne.symm hX))
    have hezero : (fun X => w X * f X ^ 2) =ᵐ[trialPhysicalMeasure] 0 := by
      filter_upwards [hfzero] with X hX
      simp only [hX, Pi.zero_apply, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    rw [integral_eq_zero_of_ae hfzero, integral_eq_zero_of_ae hezero]
    norm_num
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  let s : Set (FiniteMeasure ℝ) := {X | (X.mass : ℝ) ≤ a}
  let μ : Measure (FiniteMeasure ℝ) := trialPhysicalMeasure.restrict s
  have hw (X : FiniteMeasure ℝ) : 0 < w X := by
    dsimp only [w]
    nlinarith [X.mass.coe_nonneg]
  let u : FiniteMeasure ℝ → ℝ := fun X => f X * Real.sqrt (w X)
  let v : FiniteMeasure ℝ → ℝ := fun X => (Real.sqrt (w X))⁻¹
  have hsm : Measurable (fun X : FiniteMeasure ℝ => Real.sqrt (w X)) :=
    hwm.sqrt
  have hum : AEStronglyMeasurable u μ :=
    (hf.restrict s).aestronglyMeasurable.mul hsm.aestronglyMeasurable
  have husq : Integrable (fun X => u X ^ 2) μ := by
    apply henergy.integrableOn.congr
    filter_upwards [] with X
    dsimp only [u]
    rw [mul_pow, Real.sq_sqrt (hw0 X)]
    ring
  have hu : MemLp u 2 μ := (memLp_two_iff_integrable_sq hum).mpr husq
  have hv : MemLp v 2 μ := by
    apply MemLp.of_bound hsm.inv.aestronglyMeasurable ((Real.sqrt a)⁻¹)
    filter_upwards [] with X
    change ‖(Real.sqrt (w X))⁻¹‖ ≤ (Real.sqrt a)⁻¹
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    apply inv_anti₀ (Real.sqrt_pos.mpr ha')
    apply Real.sqrt_le_sqrt
    dsimp only [w]
    nlinarith [X.mass.coe_nonneg]
  have huv : ⟪hu.toLp u, hv.toLp v⟫_ℝ = ∫ X, f X ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with X hX hY
    rw [hX, hY, Real.inner_apply]
    exact mul_inv_cancel_right₀ (ne_of_gt (Real.sqrt_pos.mpr (hw X))) (f X)
  have huu : ⟪hu.toLp u, hu.toLp u⟫_ℝ = ∫ X, w X * f X ^ 2 ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp] with X hX
    rw [hX, Real.inner_apply, ← pow_two]
    dsimp only [u]
    rw [mul_pow, Real.sq_sqrt (hw0 X)]
    ring
  have hvv : ⟪hv.toLp v, hv.toLp v⟫_ℝ = ∫ X, (w X)⁻¹ ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv.coeFn_toLp] with X hX
    rw [hX, Real.inner_apply, ← pow_two]
    dsimp only [v]
    rw [inv_pow, Real.sq_sqrt (hw0 X)]
  have hcs := real_inner_mul_inner_self_le (hu.toLp u) (hv.toLp v)
  rw [huv, huu, hvv, ← pow_two] at hcs
  have hrestoreF : (∫ X, f X ∂μ) = ∫ X, f X ∂trialPhysicalMeasure := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hsupport] with X hX
    exact fun hn => hX (lt_of_not_ge hn)
  have hrestoreE : (∫ X, w X * f X ^ 2 ∂μ) =
      ∫ X, w X * f X ^ 2 ∂trialPhysicalMeasure := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hsupport] with X hX
    intro hn
    rw [hX (lt_of_not_ge hn)]
    simp
  have hinv : (∫ X, (w X)⁻¹ ∂μ) ≤ Real.log 39 / 38 :=
    trial_inverse_face_fiber a ha'
  have hEnonneg : 0 ≤ ∫ X, w X * f X ^ 2 ∂μ :=
    integral_nonneg fun X => mul_nonneg (hw0 X) (sq_nonneg _)
  have hfinal := hcs.trans (mul_le_mul_of_nonneg_left hinv hEnonneg)
  rw [hrestoreF, hrestoreE] at hfinal
  simpa only [mul_comm] using hfinal

theorem trial_simplex_face_energy
    (S : ℝ) (hS : 0 < S) (f : (Fin 39 → FiniteMeasure ℝ) → ℝ)
    (hf : MemLp f 2 (Measure.pi (fun _ : Fin 39 => trialPhysicalMeasure)))
    (hsupport : ∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => trialPhysicalMeasure),
      S < ∑ i : Fin 39, ((X i).mass : ℝ) → f X = 0) :
    (∀ i : Fin 39,
      MemLp (fun Y : Fin 38 → FiniteMeasure ℝ =>
        ∫ X : FiniteMeasure ℝ, f (i.insertNth X Y) ∂trialPhysicalMeasure)
        2 (Measure.pi (fun _ : Fin 38 => trialPhysicalMeasure))) ∧
      (∑ i : Fin 39,
        ∫ Y : Fin 38 → FiniteMeasure ℝ,
          (∫ X : FiniteMeasure ℝ, f (i.insertNth X Y) ∂trialPhysicalMeasure) ^ 2
          ∂Measure.pi (fun _ : Fin 38 => trialPhysicalMeasure)) ≤
        (S * 39 * Real.log 39 / 38) *
          ∫ X : Fin 39 → FiniteMeasure ℝ, f X ^ 2
            ∂Measure.pi (fun _ : Fin 39 => trialPhysicalMeasure) := by
  classical
  let μ : Measure (FiniteMeasure ℝ) := trialPhysicalMeasure
  let ν : Measure (Fin 38 → FiniteMeasure ℝ) := Measure.pi (fun _ => μ)
  let πμ : Measure (Fin 39 → FiniteMeasure ℝ) := Measure.pi (fun _ => μ)
  let : IsFiniteMeasure μ := trialPhysicalMeasure_finite
  have hf' : MemLp f 2 πμ := hf
  have hmass : Measurable (fun X : FiniteMeasure ℝ => (X.mass : ℝ)) :=
    ((Measure.measurable_coe MeasurableSet.univ).comp measurable_subtype_coe).ennreal_toReal
  let total : (Fin 39 → FiniteMeasure ℝ) → ℝ := fun X =>
    ∑ j : Fin 39, ((X j).mass : ℝ)
  let retained : (Fin 38 → FiniteMeasure ℝ) → ℝ := fun Y =>
    ∑ j : Fin 38, ((Y j).mass : ℝ)
  let W : Fin 39 → (Fin 39 → FiniteMeasure ℝ) → ℝ := fun i X =>
    (S - total X + 39 * ((X i).mass : ℝ)) * f X ^ 2
  let c : ℝ := Real.log 39 / 38
  have hsupport' : ∀ᵐ X ∂πμ, S < total X → f X = 0 := hsupport
  have htotal_meas : Measurable total :=
    Finset.measurable_sum Finset.univ fun i _ => hmass.comp (measurable_pi_apply i)
  have hcoord (i : Fin 39) (X : Fin 39 → FiniteMeasure ℝ) :
      ((X i).mass : ℝ) ≤ total X :=
    Finset.single_le_sum (fun j _ => (X j).mass.coe_nonneg) (Finset.mem_univ i)
  have hWbounds (i : Fin 39) : ∀ᵐ X ∂πμ,
      ‖W i X‖ ≤ (39 * S) * f X ^ 2 := by
    filter_upwards [hsupport'] with X hs
    by_cases hX : total X ≤ S
    · have hw0 : 0 ≤ S - total X + 39 * ((X i).mass : ℝ) := by
        have hm0 := (X i).mass.coe_nonneg
        linarith
      have hw : S - total X + 39 * ((X i).mass : ℝ) ≤ 39 * S := by
        have hi := hcoord i X
        linarith
      have hprod : 0 ≤ W i X := mul_nonneg hw0 (sq_nonneg _)
      rw [Real.norm_of_nonneg hprod]
      exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    · have hz : f X = 0 := hs (lt_of_not_ge hX)
      simp only [W, hz, zero_pow (by norm_num : 2 ≠ 0), mul_zero, norm_zero, le_refl]
  have hW (i : Fin 39) : Integrable (W i) πμ := by
    have hwmeas : Measurable (fun X : Fin 39 → FiniteMeasure ℝ =>
        S - total X + 39 * ((X i).mass : ℝ)) :=
      (measurable_const.sub htotal_meas).add
        (measurable_const.mul (hmass.comp (measurable_pi_apply i)))
    apply (hf'.integrable_sq.const_mul (39 * S)).mono
      (hwmeas.aestronglyMeasurable.mul (hf'.aestronglyMeasurable.pow 2))
    filter_upwards [hWbounds i] with X hX
    exact hX.trans_eq (Real.norm_of_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hS.le) (sq_nonneg _))).symm
  let e (i : Fin 39) :
      (FiniteMeasure ℝ × (Fin 38 → FiniteMeasure ℝ)) ≃ᵐ
        (Fin 39 → FiniteMeasure ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 39 => FiniteMeasure ℝ) i).symm
  have he (i : Fin 39) : MeasurePreserving (e i) (μ.prod ν) πμ :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin 39 => μ) i).symm
  let F : Fin 39 → (FiniteMeasure ℝ × (Fin 38 → FiniteMeasure ℝ)) → ℝ :=
    fun i Z => f (e i Z)
  let V : Fin 39 → (Fin 38 → FiniteMeasure ℝ) → ℝ := fun i Y =>
    ∫ X : FiniteMeasure ℝ, F i (X, Y) ∂μ
  let Q : Fin 39 → (Fin 38 → FiniteMeasure ℝ) → ℝ := fun i Y =>
    ∫ X : FiniteMeasure ℝ, W i (e i (X, Y)) ∂μ
  have hF (i : Fin 39) : MemLp (F i) 2 (μ.prod ν) :=
    hf'.comp_measurePreserving (he i)
  have hWcomp (i : Fin 39) :
      Integrable (fun Z => W i (e i Z)) (μ.prod ν) :=
    (he i).integrable_comp_of_integrable (hW i)
  have hQ (i : Fin 39) : Integrable (Q i) ν :=
    (hWcomp i).integral_prod_right
  have hVm (i : Fin 39) : AEStronglyMeasurable (V i) ν :=
    (hF i).aestronglyMeasurable.prod_swap.integral_prod_right'
  have htotal_insert (i : Fin 39) (X : FiniteMeasure ℝ)
      (Y : Fin 38 → FiniteMeasure ℝ) :
      total (i.insertNth X Y) = (X.mass : ℝ) + retained Y := by
    dsimp only [total, retained]
    rw [Fin.sum_univ_succAbove _ i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  have hweight (i : Fin 39) (X : FiniteMeasure ℝ)
      (Y : Fin 38 → FiniteMeasure ℝ) :
      W i (e i (X, Y)) =
        (S - retained Y + 38 * (X.mass : ℝ)) * F i (X, Y) ^ 2 := by
    change W i (i.insertNth X Y) =
      (S - retained Y + 38 * (X.mass : ℝ)) * f (i.insertNth X Y) ^ 2
    dsimp only [W]
    rw [htotal_insert, Fin.insertNth_apply_same]
    ring
  have hFibre (i : Fin 39) :
      ∀ᵐ Y ∂ν, MemLp (fun X : FiniteMeasure ℝ => F i (X, Y)) 2 μ := by
    filter_upwards [(hF i).aestronglyMeasurable.prodMk_right,
      (hF i).integrable_sq.prod_left_ae] with Y hm hsq
    exact (memLp_two_iff_integrable_sq hm).2 hsq
  have hsupportFibre (i : Fin 39) : ∀ᵐ Y ∂ν, ∀ᵐ X ∂μ,
      S < (X.mass : ℝ) + retained Y → F i (X, Y) = 0 := by
    have hpull : ∀ᵐ Z ∂μ.prod ν, S < total (e i Z) → F i Z = 0 :=
      (he i).quasiMeasurePreserving.ae hsupport'
    have hswap : ∀ᵐ Z ∂ν.prod μ, S < total (e i Z.swap) → F i Z.swap = 0 :=
      (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae hpull
    filter_upwards [Measure.ae_ae_of_ae_prod hswap] with Y hY
    filter_upwards [hY] with X hX
    change S < total (i.insertNth X Y) → f (i.insertNth X Y) = 0 at hX
    rw [htotal_insert] at hX
    exact hX
  have hface (i : Fin 39) : ∀ᵐ Y ∂ν, V i Y ^ 2 ≤ c * Q i Y := by
    filter_upwards [hFibre i, hsupportFibre i] with Y hFY hsY
    by_cases hs : retained Y ≤ S
    · have hsupp : ∀ᵐ X ∂μ,
          S - retained Y < (X.mass : ℝ) → F i (X, Y) = 0 := by
        filter_upwards [hsY] with X hX
        intro hmassX
        exact hX (by linarith)
      have h := (trial_weighted_face_fiber (S - retained Y) (sub_nonneg.mpr hs)
        (fun X : FiniteMeasure ℝ => F i (X, Y)) hFY hsupp).2
      have hQeq : Q i Y = ∫ X : FiniteMeasure ℝ,
          (S - retained Y + 38 * (X.mass : ℝ)) * F i (X, Y) ^ 2 ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun X => hweight i X Y
      simpa only [V, c, hQeq] using h
    · have hzero : (fun X : FiniteMeasure ℝ => F i (X, Y)) =ᵐ[μ] 0 := by
        filter_upwards [hsY] with X hX
        exact hX (by
          have hm0 := X.mass.coe_nonneg
          linarith [lt_of_not_ge hs])
      have hVzero : V i Y = 0 := integral_eq_zero_of_ae hzero
      have hQzero : Q i Y = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [hzero] with X hX
        rw [hweight, hX]
        simp
      simp only [hVzero, hQzero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, le_refl]
  have hV2 (i : Fin 39) : Integrable (fun Y => V i Y ^ 2) ν := by
    apply ((hQ i).const_mul c).mono' ((hVm i).pow 2)
    filter_upwards [hface i] with Y hY
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hY
  have hQintegral (i : Fin 39) : (∫ Y, Q i Y ∂ν) = ∫ X, W i X ∂πμ := by
    calc
      (∫ Y, Q i Y ∂ν) = ∫ Z, W i (e i Z) ∂μ.prod ν :=
        (integral_prod_symm (fun Z => W i (e i Z)) (hWcomp i)).symm
      _ = ∫ X, W i X ∂πμ := (he i).integral_comp' (W i)
  have hfaceIntegral (i : Fin 39) :
      (∫ Y, V i Y ^ 2 ∂ν) ≤ c * ∫ X, W i X ∂πμ := by
    calc
      (∫ Y, V i Y ^ 2 ∂ν) ≤ ∫ Y, c * Q i Y ∂ν :=
        integral_mono_ae (hV2 i) ((hQ i).const_mul c) (hface i)
      _ = c * ∫ X, W i X ∂πμ := by rw [integral_const_mul, hQintegral]
  have hsumW (X : Fin 39 → FiniteMeasure ℝ) :
      (∑ i : Fin 39, W i X) = (39 * S) * f X ^ 2 := by
    dsimp only [W]
    rw [← Finset.sum_mul]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    change (39 * (S - total X) + 39 * total X) * f X ^ 2 = (39 * S) * f X ^ 2
    ring
  refine ⟨?_, ?_⟩
  · intro i
    change MemLp (V i) 2 ν
    exact (memLp_two_iff_integrable_sq (hVm i)).2 (hV2 i)
  · change (∑ i : Fin 39, ∫ Y, V i Y ^ 2 ∂ν) ≤
      (S * 39 * Real.log 39 / 38) * ∫ X, f X ^ 2 ∂πμ
    calc
      (∑ i : Fin 39, ∫ Y, V i Y ^ 2 ∂ν) ≤
          ∑ i : Fin 39, c * ∫ X, W i X ∂πμ :=
        Finset.sum_le_sum fun i _ => hfaceIntegral i
      _ = c * ∫ X, ∑ i : Fin 39, W i X ∂πμ := by
        rw [← Finset.mul_sum, ← integral_finsetSum Finset.univ (fun i _ => hW i)]
      _ = c * ((39 * S) * ∫ X, f X ^ 2 ∂πμ) := by
        simp_rw [hsumW]
        rw [integral_const_mul]
      _ = (S * 39 * Real.log 39 / 38) * ∫ X, f X ^ 2 ∂πμ := by
        dsimp only [c]
        ring


theorem trial_face_operator_constant :
    (trialRadius : ℝ) * 39 * Real.log 39 / 38 < 4 := by
  have hsum : (39 : ℝ) < ∑ j ∈ Finset.range 12,
      (367 / 100 : ℝ) ^ j / (j.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hexp : (39 : ℝ) < Real.exp (367 / 100) :=
    hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 367 / 100) 12)
  have hlog : Real.log 39 < (367 / 100 : ℝ) :=
    (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 39)).mpr hexp
  norm_num [trialRadius] at ⊢
  linarith

theorem trial_physical_face_operator_bound
    (f : (Fin 39 → FiniteMeasure ℝ) → ℝ)
    (hf : MemLp f 2 (trialProductMeasure 39))
    (hsupport : ∀ᵐ X ∂trialProductMeasure 39,
      (trialRadius : ℝ) < ∑ i : Fin 39, ((X i).mass : ℝ) → f X = 0) :
    (∑ i : Fin 39,
      ∫ Y : Fin 38 → FiniteMeasure ℝ,
        (∫ X : FiniteMeasure ℝ, f (i.insertNth X Y) ∂trialPhysicalMeasure) ^ 2
        ∂trialProductMeasure 38) ≤
      4 * ∫ X : Fin 39 → FiniteMeasure ℝ, f X ^ 2 ∂trialProductMeasure 39 := by
  have h := (trial_simplex_face_energy (trialRadius : ℝ)
    (by norm_num [trialRadius]) f hf hsupport).2
  exact h.trans (mul_le_mul_of_nonneg_right trial_face_operator_constant.le
    (integral_nonneg fun _ => sq_nonneg _))

#print axioms trialPhysicalMeasure_mass_map
#print axioms trial_simplex_face_energy
#print axioms trial_physical_face_operator_bound

end PrimeGap182
