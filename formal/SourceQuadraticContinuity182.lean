import SourceQuadraticTools182
import SourceSmoothSupport182

/-! L² continuity of the actual physical hybrid energy, uniformly in the
true deficit parameter on any fixed compact interval. The additional
negative H² coefficient is arbitrary and explicit. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace PrimeGap182

def trialPhysicalHybridEnergy (κ extra : ℝ)
    (f : (Fin 39 → FiniteMeasure ℝ) → ℝ)
    (H : Fin 3 → (Fin 38 → FiniteMeasure ℝ) → ℝ) : ℝ :=
  (trialRhoStar : ℝ) * (∑ i : Fin 39, ∫ Y,
    trialHybridCoefficient κ extra (trialFaceKernel Y) (fun b => H b Y) *
      trialErasure f i Y ^ 2 ∂trialProductMeasure 38) -
    ∫ X, f X ^ 2 ∂trialProductMeasure 39

theorem trial_hybrid_energy_l2_continuous182 (κmax extra ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ κ : ℝ, 0 ≤ κ → κ ≤ κmax →
      ∀ (f : (Fin 39 → FiniteMeasure ℝ) → ℝ)
        (H : Fin 3 → (Fin 38 → FiniteMeasure ℝ) → ℝ),
        MemLp f 2 (trialProductMeasure 39) → (∀ b, Measurable (H b)) →
        (∀ b Y, 0 ≤ H b Y ∧ H b Y ≤ 1) →
        (∀ᵐ X ∂trialProductMeasure 39, (trialRadius : ℝ) < trialTotalMass X → f X = 0) →
        (∫ X, (f X - trialSourceStepFunction X) ^ 2 ∂trialProductMeasure 39) < δ →
        (∀ b : Fin 3, (∫ Y, (H b Y - trialApproxFaceActual b Y) ^ 2 ∂trialProductMeasure 38) < δ) →
        |trialPhysicalHybridEnergy κ extra f H -
          trialPhysicalHybridEnergy κ extra trialSourceStepFunction trialApproxFaceActual| < ε := by
  classical
  let : IsFiniteMeasure trialPhysicalMeasure := trialPhysicalMeasure_finite
  let μ39 := trialProductMeasure 39
  let μ38 := trialProductMeasure 38
  let g := trialSourceStepFunction
  let I (f : (Fin 39 → FiniteMeasure ℝ) → ℝ) := ∫ X, f X ^ 2 ∂μ39
  let M := trialApproxFaceActual
  let ρ : ℝ := trialRhoStar
  have hρ : 0 < ρ := trialRhoStar_pos
  obtain ⟨B, hB, hPB, hPLip⟩ := trialHybridCoefficient_control κmax extra
  obtain ⟨Croot, hCroot⟩ := trial_regular_source.bounded
  let C := Croot * trialPhysicalMeasure.real Set.univ
  have hreference (i : Fin 39) (Y : Fin 38 → FiniteMeasure ℝ) :
      trialErasure g i Y ^ 2 ≤ C ^ 2 := by
    have hn : ‖trialErasure g i Y‖ ≤ C :=
      norm_integral_le_of_norm_le_const (ae_of_all _ fun Z => hCroot (i.insertNth Z Y))
    have ha : |trialErasure g i Y| ≤ C := by simpa only [Real.norm_eq_abs] using hn
    exact sq_le_sq.mpr (ha.trans (le_abs_self C))
  have hg : MemLp g 2 μ39 := trialSourceStepFunction_memLp
  have hgsupport : ∀ᵐ X ∂μ39, (trialRadius : ℝ) < trialTotalMass X → g X = 0 :=
    ae_of_all _ trialSourceStepFunction_mass_support
  have hMm (b : Fin 3) : Measurable (M b) := measurable_trialApproxFaceActual b
  have hMunit (b : Fin 3) (Y : Fin 38 → FiniteMeasure ℝ) : 0 ≤ M b Y ∧ M b Y ≤ 1 := by
    rcases trialApproxFaceActual_bits b Y with h | h <;> simp [M, h]
  let A : ℝ := 4 * ρ * B + 1
  let D : ℝ := 39 * ρ * C ^ 2 * B
  let T : ℝ := A * I g + 3 * D * μ38.real Set.univ
  let K : ℝ := A + 3 * D
  have hA : 0 < A := by dsimp only [A]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  obtain ⟨r, hr, hrsmall⟩ := exists_pos_mul_lt (half_pos hε) T
  let k : ℝ := 1 + r⁻¹
  have hk : 0 < k := by dsimp only [k]; positivity
  obtain ⟨δ, hδ, hδsmall⟩ := exists_pos_mul_lt (half_pos hε) (K * k)
  refine ⟨δ, hδ, ?_⟩
  intro κ hκ hκm f H hf hHm hHunit hfsupport hfe hHe
  let P (Y : Fin 38 → FiniteMeasure ℝ) (h : Fin 3 → ℝ) :=
    trialHybridCoefficient κ extra (trialFaceKernel Y) h
  let J (f : (Fin 39 → FiniteMeasure ℝ) → ℝ)
      (H : Fin 3 → (Fin 38 → FiniteMeasure ℝ) → ℝ) :=
    ∑ i : Fin 39, ∫ Y, P Y (fun b => H b Y) * trialErasure f i Y ^ 2 ∂μ38
  let e : (Fin 39 → FiniteMeasure ℝ) → ℝ := fun X => f X - g X
  let E (b : Fin 3) : ℝ := ∫ Y, (H b Y - M b Y) ^ 2 ∂μ38
  have he : MemLp e 2 μ39 := hf.sub hg
  have hesupport : ∀ᵐ X ∂μ39, (trialRadius : ℝ) < trialTotalMass X → e X = 0 := by
    filter_upwards [hfsupport, hgsupport] with X hfX hgX hX
    simp only [e, hfX hX, hgX hX, sub_self]
  have hfgface (i : Fin 39) : MemLp (trialErasure g i) 2 μ38 :=
    (trial_simplex_face_energy (trialRadius : ℝ) (by norm_num [trialRadius]) g hg hgsupport).1 i
  have hfface (i : Fin 39) : MemLp (trialErasure f i) 2 μ38 :=
    (trial_simplex_face_energy (trialRadius : ℝ) (by norm_num [trialRadius]) f hf hfsupport).1 i
  have hsub (i : Fin 39) :
      (fun Y => trialErasure f i Y - trialErasure g i Y) =ᵐ[μ38] trialErasure e i := by
    let ins : (FiniteMeasure ℝ × (Fin 38 → FiniteMeasure ℝ)) ≃ᵐ
        (Fin 39 → FiniteMeasure ℝ) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 39 => FiniteMeasure ℝ) i).symm
    have hins : MeasurePreserving ins (trialPhysicalMeasure.prod μ38) μ39 :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin 39 => trialPhysicalMeasure) i).symm
    have hfi := hins.integrable_comp_of_integrable (MemLp.integrable one_le_two hf)
    have hgi := hins.integrable_comp_of_integrable (MemLp.integrable one_le_two hg)
    simp only [Function.comp_def, ins, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Equiv.coe_fn_mk] at hfi hgi
    filter_upwards [hfi.prod_left_ae, hgi.prod_left_ae] with Y hfY hgY
    exact (integral_sub hfY hgY).symm
  have hunitLp (v : (Fin 38 → FiniteMeasure ℝ) → ℝ) (hv : Measurable v)
      (hvb : ∀ Y, 0 ≤ v Y ∧ v Y ≤ 1) : MemLp v 2 μ38 := by
    refine MemLp.of_bound hv.aestronglyMeasurable 1 (ae_of_all _ fun Y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hvb Y).1]
    exact (hvb Y).2
  have hE (b : Fin 3) : Integrable (fun Y => (H b Y - M b Y) ^ 2) μ38 :=
    ((hunitLp (H b) (hHm b) (hHunit b)).sub
      (hunitLp (M b) (hMm b) (hMunit b))).integrable_sq
  have hKm : Measurable trialFaceKernel := measurable_trialFaceKernel
  have hPHmeas : Measurable (fun Y => P Y (fun b => H b Y)) := by
    unfold P trialHybridCoefficient trialPhysicalHybridPolynomial
    fun_prop
  have hPMmeas : Measurable (fun Y => P Y (fun b => M b Y)) := by
    unfold P trialHybridCoefficient trialPhysicalHybridPolynomial
    fun_prop
  have hPHbound : ∀ᵐ Y ∂μ38, ‖P Y (fun b => H b Y)‖ ≤ B := by
    refine ae_of_all _ fun Y => ?_
    simpa only [P, Real.norm_eq_abs] using hPB κ _ hκ hκm (trialFaceKernel_bounds Y).1
      (trialFaceKernel_bounds Y).2.le _ (fun b => hHunit b Y)
  have hPMbound : ∀ᵐ Y ∂μ38, ‖P Y (fun b => M b Y)‖ ≤ B := by
    refine ae_of_all _ fun Y => ?_
    simpa only [P, Real.norm_eq_abs] using hPB κ _ hκ hκm (trialFaceKernel_bounds Y).1
      (trialFaceKernel_bounds Y).2.le _ (fun b => hMunit b Y)
  have hroot : |I f - I g| ≤ r * I g + k * I e := by
    simpa only [I, e, k, one_mul] using
      PrimeGap186.trial_weighted_square_l2_error μ39 r hr f g (fun _ => 1) 1 (by norm_num) hf hg
        aestronglyMeasurable_const (ae_of_all _ fun _ => by norm_num)
  have hmaskrow (i : Fin 39) :
      |(∫ Y, P Y (fun b => H b Y) * trialErasure g i Y ^ 2 ∂μ38) -
        ∫ Y, P Y (fun b => M b Y) * trialErasure g i Y ^ 2 ∂μ38| ≤
      C ^ 2 * B * (3 * r * μ38.real Set.univ + k * ∑ b : Fin 3, E b) := by
    have hH := (hfgface i).integrable_sq.bdd_mul hPHmeas.aestronglyMeasurable hPHbound
    have hM := (hfgface i).integrable_sq.bdd_mul hPMmeas.aestronglyMeasurable hPMbound
    have hcoeff (Y : Fin 38 → FiniteMeasure ℝ) :
        |P Y (fun b => H b Y) - P Y (fun b => M b Y)| ≤
          B * ∑ b : Fin 3, |H b Y - M b Y| :=
      hPLip κ _ hκ hκm (trialFaceKernel_bounds Y).1 (trialFaceKernel_bounds Y).2.le
        _ _ (fun b => hHunit b Y) (fun b => hMunit b Y)
    exact trial_weighted_square_coefficients_error μ38 r hr (trialErasure g i)
      (fun Y => P Y (fun b => H b Y)) (fun Y => P Y (fun b => M b Y))
      (fun b Y => H b Y - M b Y) C B hB.le hH hM hE (hreference i) hcoeff
  have hrow (i : Fin 39) :
      |(∫ Y, P Y (fun b => H b Y) * trialErasure f i Y ^ 2 ∂μ38) -
        ∫ Y, P Y (fun b => M b Y) * trialErasure g i Y ^ 2 ∂μ38| ≤
      B * (r * (∫ Y, trialErasure g i Y ^ 2 ∂μ38) + k * ∫ Y, trialErasure e i Y ^ 2 ∂μ38) +
        C ^ 2 * B * (3 * r * μ38.real Set.univ + k * ∑ b : Fin 3, E b) := by
    have hh := PrimeGap186.trial_weighted_square_l2_error μ38 r hr
      (trialErasure f i) (trialErasure g i) (fun Y => P Y (fun b => H b Y))
      B hB.le (hfface i) (hfgface i) hPHmeas.aestronglyMeasurable hPHbound
    have heq : (∫ Y, (trialErasure f i Y - trialErasure g i Y) ^ 2 ∂μ38) =
        ∫ Y, trialErasure e i Y ^ 2 ∂μ38 := integral_congr_ae ((hsub i).pow_const 2)
    rw [heq] at hh
    exact (abs_sub_le _ (∫ Y, P Y (fun b => H b Y) * trialErasure g i Y ^ 2 ∂μ38) _).trans
      (add_le_add hh (hmaskrow i))
  have hfaceg : (∑ i : Fin 39, ∫ Y, trialErasure g i Y ^ 2 ∂μ38) ≤ 4 * I g :=
    trial_physical_face_operator_bound g hg hgsupport
  have hfacee : (∑ i : Fin 39, ∫ Y, trialErasure e i Y ^ 2 ∂μ38) ≤ 4 * I e :=
    trial_physical_face_operator_bound e he hesupport
  have hfaces : |J f H - J g M| ≤
      4 * B * (r * I g + k * I e) +
        39 * C ^ 2 * B * (3 * r * μ38.real Set.univ + k * ∑ b : Fin 3, E b) := by
    calc
      _ = |∑ i : Fin 39,
          ((∫ Y, P Y (fun b => H b Y) * trialErasure f i Y ^ 2 ∂μ38) -
            ∫ Y, P Y (fun b => M b Y) * trialErasure g i Y ^ 2 ∂μ38)| := by
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ i : Fin 39,
          |(∫ Y, P Y (fun b => H b Y) * trialErasure f i Y ^ 2 ∂μ38) -
            ∫ Y, P Y (fun b => M b Y) * trialErasure g i Y ^ 2 ∂μ38| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 39,
          (B * (r * (∫ Y, trialErasure g i Y ^ 2 ∂μ38) + k * ∫ Y, trialErasure e i Y ^ 2 ∂μ38) +
            C ^ 2 * B * (3 * r * μ38.real Set.univ + k * ∑ b : Fin 3, E b)) :=
        Finset.sum_le_sum fun i _ => hrow i
      _ = B * (r * (∑ i : Fin 39, ∫ Y, trialErasure g i Y ^ 2 ∂μ38) +
          k * (∑ i : Fin 39, ∫ Y, trialErasure e i Y ^ 2 ∂μ38)) +
          39 * C ^ 2 * B * (3 * r * μ38.real Set.univ + k * ∑ b : Fin 3, E b) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ ≤ B * (r * (4 * I g) + k * (4 * I e)) +
          39 * C ^ 2 * B * (3 * r * μ38.real Set.univ + k * ∑ b : Fin 3, E b) :=
        add_le_add (mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left hfaceg hr.le)
            (mul_le_mul_of_nonneg_left hfacee hk.le)) hB.le) le_rfl
      _ = _ := by ring
  have hQ : |trialPhysicalHybridEnergy κ extra f H - trialPhysicalHybridEnergy κ extra g M| ≤
      T * r + (A * I e + D * ∑ b : Fin 3, E b) * k := by
    change |(ρ * J f H - I f) - (ρ * J g M - I g)| ≤ _
    calc
      _ = |ρ * (J f H - J g M) - (I f - I g)| := by congr 1; ring
      _ ≤ ρ * |J f H - J g M| + |I f - I g| := by
        simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos hρ] using
          norm_sub_le (ρ * (J f H - J g M)) (I f - I g)
      _ ≤ ρ * (4 * B * (r * I g + k * I e) +
          39 * C ^ 2 * B * (3 * r * μ38.real Set.univ + k * ∑ b : Fin 3, E b)) +
          (r * I g + k * I e) :=
        add_le_add (mul_le_mul_of_nonneg_left hfaces hρ.le) hroot
      _ = _ := by dsimp only [T, A, D]; ring
  have herrors : A * I e + D * ∑ b : Fin 3, E b < (A + 3 * D) * δ := by
    have hfsmall : A * I e < A * δ := mul_lt_mul_of_pos_left hfe hA
    have hsum : (∑ b : Fin 3, E b) ≤ 3 * δ := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using
        Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin 3))) => (hHe b).le)
    have hmsmall := mul_le_mul_of_nonneg_left hsum hD
    nlinarith only [hfsmall, hmsmall]
  have hsmall : (A * I e + D * ∑ b : Fin 3, E b) * k < ε / 2 := by
    calc
      _ < ((A + 3 * D) * δ) * k := mul_lt_mul_of_pos_right herrors hk
      _ = (K * k) * δ := by dsimp only [K]; ring
      _ < ε / 2 := hδsmall
  exact hQ.trans_lt (by linarith only [hrsmall, hsmall])

#print axioms trial_hybrid_energy_l2_continuous182

end PrimeGap182
