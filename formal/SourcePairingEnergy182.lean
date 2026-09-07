import SourcePairingMoments182

/-! The actual limiting source-pairing coefficient dominates the positive
smooth hybrid energy. The true sharp deficit occurs in both mixed terms;
its proved upper bound is used only for the negative correction square. -/

noncomputable section
open MeasureTheory Filter PrimeGap186 PrimeGap182Analytic
open scoped BigOperators Topology Pointwise

namespace PrimeGap182.TrialSmoothProfiles182
open SieveFaceRole182

theorem continuous_sieveFaceProfile (P : TrialSmoothProfiles182) (i : Fin 39) (r : SieveFaceRole182) :
    Continuous (P.sieveFaceProfile i r) := by
  cases r
  · exact P.continuous_bandErasure i
  · exact P.continuous_bandMaskedFace 0 i
  · exact (P.continuous_bandMaskedFace 1 i).sub (P.continuous_bandMaskedFace 0 i)
  · exact (P.continuous_bandErasure i).sub (P.continuous_bandMaskedFace 0 i)
  · exact (P.continuous_bandMaskedFace 2 i).sub (P.continuous_bandMaskedFace 0 i)
  · exact (P.continuous_bandErasure i).sub (P.continuous_bandMaskedFace 2 i)

theorem bounded_sieveFaceProfile (P : TrialSmoothProfiles182) (i : Fin 39) (r : SieveFaceRole182) :
    Bornology.IsBounded (Set.range (P.sieveFaceProfile i r)) := by
  have hb (b : Fin 3) : Bornology.IsBounded (Set.range (P.bandMaskedFace b i)) :=
    ((P.compact_bandMaskedFace b i).isCompact_range (P.continuous_bandMaskedFace b i)).isBounded
  have hsub (f g : (Fin 38 → Fin (P.m + 1) → ℝ) → ℝ) (hf : Bornology.IsBounded (Set.range f))
      (hg : Bornology.IsBounded (Set.range g)) : Bornology.IsBounded (Set.range (fun x => f x - g x)) := by
    apply (isBounded_sub hf hg).subset
    rintro _ ⟨x, rfl⟩
    exact Set.sub_mem_sub (Set.mem_range_self x) (Set.mem_range_self x)
  cases r
  · exact P.bounded_bandErasure i
  · exact hb 0
  · exact hsub _ _ (hb 1) (hb 0)
  · exact hsub _ _ (P.bounded_bandErasure i) (hb 0)
  · exact hsub _ _ (hb 2) (hb 0)
  · exact hsub _ _ (P.bounded_bandErasure i) (hb 2)

theorem integrable_sieveFaceProfile_mul (P : TrialSmoothProfiles182) (i : Fin 39)
    (r s : SieveFaceRole182) :
    Integrable (fun Y => P.sieveFaceProfile i r Y * P.sieveFaceProfile i s Y)
      (Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 P.a)) := by
  have hb := isBounded_range_mul_comp (P.bounded_sieveFaceProfile i r)
    (P.bounded_sieveFaceProfile i s) id id
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  exact Integrable.of_bound ((P.continuous_sieveFaceProfile i r).mul
    (P.continuous_sieveFaceProfile i s)).aestronglyMeasurable C
    (ae_of_all _ fun Y => hC _ ⟨Y, rfl⟩)

def sieveKernelIntegral (P : TrialSmoothProfiles182) (i : Fin 39) : ℝ :=
  ∫ Y, bandFaceKernel182 Y * P.sieveFaceProfile i rootMinusSubtraction Y ^ 2
    ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 P.a)

theorem integrable_sieveKernel (P : TrialSmoothProfiles182) (i : Fin 39) :
    Integrable (fun Y => bandFaceKernel182 Y * P.sieveFaceProfile i rootMinusSubtraction Y ^ 2)
      (Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 P.a)) := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (P.bounded_sieveFaceProfile i rootMinusSubtraction)
  apply trial_integrable_bounded_weight_square _ _ _ measurable_bandFaceKernel182
    (P.continuous_sieveFaceProfile i rootMinusSubtraction).measurable
    (B := 1097 / 500) (C := C)
  · intro Y
    have hb := trialPairKernel_bounds (bandFaceCellSum182 Y)
    simpa only [bandFaceKernel182, Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2.le
  · intro Y
    exact hC _ ⟨Y, rfl⟩

def sievePairCoefficient (k : Fin 6) : ℝ :=
  let t : ℝ := 1 - (trialLambda : ℝ)
  ![2, -1, 2 * t, 2 * t, -t ^ 2, -trialHybridLoss⁻¹ * t ^ 2] k

def sieveMainCoefficient (P : TrialSmoothProfiles182) : ℝ :=
  (trialRhoStar : ℝ) * (∑ i : Fin 39,
    ((∑ k : Fin 6, sievePairCoefficient k *
      (selbergWeightMean182 (sievePairWeight k) * P.sievePairIntegral i k)) -
        trialHybridLoss * P.sieveKernelIntegral i)) -
    ∫ X, P.F X ^ 2 ∂Measure.pi (fun _ : Fin 39 => selbergBandMeasure182 P.a)

theorem integrable_hybridFace (P : TrialSmoothProfiles182) (κ : ℝ) (i : Fin 39) :
    Integrable (fun Y => trialPerturbedHybridPolynomial κ (bandFaceKernel182 Y)
      (P.bandErasure i Y) (P.bandMaskedFace 0 i Y) (P.bandMaskedFace 2 i Y)
      (P.bandMaskedFace 1 i Y - P.bandMaskedFace 0 i Y))
      (Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 P.a)) := by
  let t : ℝ := 1 - (trialLambda : ℝ)
  have h₁ := ((P.integrable_sieveFaceProfile_mul i root base).const_mul 2).sub
      (P.integrable_sieveFaceProfile_mul i base base)
  have h₂ := h₁.add ((P.integrable_sieveFaceProfile_mul i rootMinusBase correction).const_mul
    (2 * t * (1 - κ)))
  have h₃ := h₂.add ((P.integrable_sieveFaceProfile_mul i subtractionMinusBase correction).const_mul
    (2 * t * κ))
  have h₄ := h₃.sub ((P.integrable_sieveFaceProfile_mul i correction correction).const_mul
    (t ^ 2 + t ^ 2 * (trialConvexKappaBound : ℝ) / trialHybridLoss))
  have h := h₄.sub ((P.integrable_sieveKernel i).const_mul trialHybridLoss)
  convert h using 1
  funext Y
  rw [trialPerturbedHybridPolynomial_eq]
  simp only [sieveFaceProfile, t, Pi.add_apply, Pi.sub_apply]
  ring

theorem hybridFace_le_source_integrals (P : TrialSmoothProfiles182) (i : Fin 39) :
    (∫ Y, trialPerturbedHybridPolynomial SharpMean.sharpMass (bandFaceKernel182 Y)
      (P.bandErasure i Y) (P.bandMaskedFace 0 i Y) (P.bandMaskedFace 2 i Y)
      (P.bandMaskedFace 1 i Y - P.bandMaskedFace 0 i Y)
      ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 P.a)) ≤
        (∑ k : Fin 6, sievePairCoefficient k *
          (selbergWeightMean182 (sievePairWeight k) * P.sievePairIntegral i k)) -
            trialHybridLoss * P.sieveKernelIntegral i := by
  let f (k : Fin 6) (Y : Fin 38 → Fin (P.m + 1) → ℝ) := sievePairCoefficient k *
    (selbergWeightMean182 (sievePairWeight k) *
      (P.sieveFaceProfile i (sievePairLeft k) Y * P.sieveFaceProfile i (sievePairRight k) Y))
  have hf (k : Fin 6) : Integrable (f k) (Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 P.a)) :=
    ((P.integrable_sieveFaceProfile_mul i _ _).const_mul _).const_mul _
  have heq : (∑ k : Fin 6, sievePairCoefficient k *
      (selbergWeightMean182 (sievePairWeight k) * P.sievePairIntegral i k)) -
        trialHybridLoss * P.sieveKernelIntegral i =
      ∫ Y, (∑ k : Fin 6, f k Y) -
        trialHybridLoss * (bandFaceKernel182 Y * P.sieveFaceProfile i rootMinusSubtraction Y ^ 2)
        ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 P.a) := by
    rw [integral_sub (integrable_finsetSum _ fun k _ => hf k)
      ((P.integrable_sieveKernel i).const_mul _), integral_finsetSum _ (fun k _ => hf k)]
    simp only [f, integral_const_mul, sievePairIntegral, sieveKernelIntegral]
  rw [heq]
  apply integral_mono (P.integrable_hybridFace SharpMean.sharpMass i)
    ((integrable_finsetSum _ fun k _ => hf k).sub ((P.integrable_sieveKernel i).const_mul _))
  intro Y
  have hκ := SharpMean.sharpMass_lt_convexKappaBound.le
  have hη : 0 < trialHybridLoss := by norm_num [trialHybridLoss, trialKappa, trialLambda]
  have hnonneg : 0 ≤ ((1 - (trialLambda : ℝ)) ^ 2 / trialHybridLoss) *
      ((trialConvexKappaBound : ℝ) - SharpMean.sharpMass) *
      (P.bandMaskedFace 1 i Y - P.bandMaskedFace 0 i Y) ^ 2 :=
    mul_nonneg (mul_nonneg (div_nonneg (sq_nonneg _) hη.le) (sub_nonneg.mpr hκ)) (sq_nonneg _)
  dsimp only
  rw [trialPerturbedHybridPolynomial_eq]
  simp only [f, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    sievePairCoefficient, sievePairWeight, sievePairLeft, sievePairRight, selbergWeightMean182,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, sieveFaceProfile, Pi.sub_apply]
  apply sub_nonneg.mp
  convert hnonneg using 1 <;> first | rfl | ring

theorem bandHybridEnergy_le_sieveMainCoefficient (P : TrialSmoothProfiles182) :
    P.bandHybridEnergy SharpMean.sharpMass ≤ P.sieveMainCoefficient := by
  apply sub_le_sub_right
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum fun i _ => P.hybridFace_le_source_integrals i
  · norm_num [trialRhoStar]

#print axioms integrable_hybridFace
#print axioms bandHybridEnergy_le_sieveMainCoefficient

end PrimeGap182.TrialSmoothProfiles182
