import FaceOperator182
import PairKernelDomination182

/-! Pointwise cap support, the actual projected trial, and signed face bounds. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

theorem trialCapAllowed_mono {d : ℕ} {a b : ℚ} (hab : a ≤ b)
    {X : Fin d → FiniteMeasure ℝ} (hX : TrialCapAllowed a X) : TrialCapAllowed b X := by
  intro i
  exact measure_mono_null (Set.Ioi_subset_Ioi (Rat.cast_le.mpr hab)) (hX i)

theorem trialTotalMass_cell_bound {d : ℕ} (X : Fin d → FiniteMeasure ℝ) :
    trialTotalMass X ≤ (((∑ i, trialCellIndex (X i)) + d : ℕ) : ℝ) * (trialMesh : ℝ) := by
  have hm : (0 : ℝ) < (trialMesh : ℝ) := Rat.cast_pos.mpr trialMesh_pos
  have hcell (i : Fin d) : (X i).mass ≤
      ((trialCellIndex (X i) : ℝ) + 1) * (trialMesh : ℝ) :=
    (div_le_iff₀ hm).mp (Nat.lt_floor_add_one ((X i).mass / (trialMesh : ℝ))).le
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hcell i)
  simpa only [trialTotalMass, ← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_sum]
    using hs

theorem trialShell_bounds (role : Fin 5) :
    ∀ s ∈ trialShells role, (0 : ℚ) ≤ s.lower ∧ s.upper ≤ trialRadius ∧
      s.cap ≤ trialLargestCap ∧ s.cap ≤ trialPrimeCap := by
  fin_cases role <;> decide +kernel

theorem trialShellDomain_total_bound {d : ℕ} (role : Fin 5)
    {X : Fin d → FiniteMeasure ℝ} (hX : TrialShellDomain role X) :
    trialTotalMass X ≤ (trialRadius : ℝ) := by
  obtain ⟨i, hi⟩ := hX
  have hb := trialShell_bounds role _ (List.get_mem _ i)
  have hupper := hi.2.2.1.trans hb.2.1
  have hcast : ((((∑ j, trialCellIndex (X j)) + d : ℕ) : ℝ) * (trialMesh : ℝ)) ≤
      (trialRadius : ℝ) := by
    simpa only [Rat.cast_mul, Rat.cast_natCast] using (Rat.cast_le (K := ℝ)).mpr hupper
  exact (trialTotalMass_cell_bound X).trans hcast

theorem trialShellDomain_cap {d : ℕ} (role : Fin 5)
    {X : Fin d → FiniteMeasure ℝ} (hX : TrialShellDomain role X) :
    TrialCapAllowed trialLargestCap X ∧ TrialCapAllowed trialPrimeCap X := by
  obtain ⟨i, hi⟩ := hX
  have hb := trialShell_bounds role _ (List.get_mem _ i)
  exact ⟨trialCapAllowed_mono hb.2.2.1 hi.2.2.2,
    trialCapAllowed_mono hb.2.2.2 hi.2.2.2⟩

theorem trialMask_values {d : ℕ} (role : Fin 5) (X : Fin d → FiniteMeasure ℝ) :
    trialMask role X = 0 ∨ trialMask role X = 1 := by
  unfold trialMask
  split_ifs <;> simp

theorem trialStepFunction_support (X : Fin 39 → FiniteMeasure ℝ)
    (hX : trialStepFunction X ≠ 0) :
    TrialShellDomain 0 X ∧ trialTotalMass X ≤ (trialRadius : ℝ) ∧
      TrialCapAllowed trialLargestCap X ∧ TrialCapAllowed trialPrimeCap X := by
  have hdomain : TrialShellDomain 0 X := by
    by_contra hn
    exact hX (by simp [trialStepFunction, trialMask, hn])
  exact ⟨hdomain, trialShellDomain_total_bound 0 hdomain, trialShellDomain_cap 0 hdomain⟩

theorem trialStepFunction_mass_support :
    ∀ X : Fin 39 → FiniteMeasure ℝ,
      (trialRadius : ℝ) < trialTotalMass X → trialStepFunction X = 0 := by
  intro X hmass
  by_contra hn
  exact not_lt_of_ge (trialStepFunction_support X hn).2.1 hmass

theorem trialSourceStepFunction_mass_support :
    ∀ X : Fin 39 → FiniteMeasure ℝ,
      (trialRadius : ℝ) < trialTotalMass X → trialSourceStepFunction X = 0 := by
  intro X hmass
  simp only [trialSourceStepFunction, trialStepFunction_mass_support X hmass, mul_zero]

theorem trialStepFunction_memLp : MemLp trialStepFunction 2 (trialProductMeasure 39) :=
  (memLp_two_iff_integrable_sq measurable_trialStepFunction.aestronglyMeasurable).mpr
    integrable_trialStepFunction_sq

theorem trialSourceStepFunction_memLp :
    MemLp trialSourceStepFunction 2 (trialProductMeasure 39) :=
  (memLp_two_iff_integrable_sq measurable_trialSourceStepFunction.aestronglyMeasurable).mpr
    integrable_trialSourceStepFunction_sq

theorem trialMarginal_energy_bound :
    (∑ i : Fin 39, ∫ Y, trialMarginal i Y ^ 2 ∂trialProductMeasure 38) ≤
      4 * ∫ X, trialStepFunction X ^ 2 ∂trialProductMeasure 39 :=
  trial_physical_face_operator_bound _ trialStepFunction_memLp
    (ae_of_all _ trialStepFunction_mass_support)

theorem trialSourceMarginal_energy_bound :
    (∑ i : Fin 39, ∫ Y : Fin 38 → FiniteMeasure ℝ,
      (∫ X : FiniteMeasure ℝ, trialSourceStepFunction (i.insertNth X Y)
        ∂trialPhysicalMeasure) ^ 2 ∂trialProductMeasure 38) ≤
      4 * ∫ X, trialSourceStepFunction X ^ 2 ∂trialProductMeasure 39 :=
  trial_physical_face_operator_bound _ trialSourceStepFunction_memLp
    (ae_of_all _ trialSourceStepFunction_mass_support)

theorem trialActualMask_bounds (Y : Fin 38 → FiniteMeasure ℝ) :
    (0 ≤ trialActualBaseMask Y ∧ trialActualBaseMask Y ≤ trialMask 1 Y) ∧
    (0 ≤ trialActualEnlargedMask Y ∧ trialActualEnlargedMask Y ≤ trialMask 2 Y) ∧
      (0 ≤ trialActualSubtractionMask Y ∧ trialActualSubtractionMask Y ≤ trialMask 3 Y) := by
  classical
  have hmono {P Q : Prop} (h : P → Q) :
      (0 : ℝ) ≤ (if P then 1 else 0) ∧
        (if P then (1 : ℝ) else 0) ≤ (if Q then 1 else 0) := by
    classical
    by_cases hP : P <;> by_cases hQ : Q <;> simp_all
  exact ⟨hmono (fun h => h.1), hmono (fun h => h.1), hmono (fun h => h.1)⟩

theorem trialHybridLoss_nonneg : 0 ≤ trialHybridLoss := by
  norm_num [trialHybridLoss, trialKappa, trialLambda]

theorem trialFaceMultiplier_bounds (Y : Fin 38 → FiniteMeasure ℝ) :
    -(trialHybridLoss * (1097 / 500)) ≤ trialActualFaceMultiplier Y ∧
      trialActualFaceMultiplier Y ≤ trialCapFaceMultiplier Y ∧
      trialCapFaceMultiplier Y ≤ 1 ∧
      trialCapFaceMultiplier Y - trialActualFaceMultiplier Y ≤
        1 + trialHybridLoss * (1097 / 500) := by
  have hl : (0 : ℝ) ≤ (trialLambda : ℝ) := by norm_num [trialLambda]
  have hl1 : (trialLambda : ℝ) ≤ (1 : ℝ) := by norm_num [trialLambda]
  have hk := trialFaceKernel_bounds Y
  have hc := trialActualMask_bounds Y
  have hc1 := trialMask_values 1 Y
  have hc2 := trialMask_values 2 Y
  have hc3 := trialMask_values 3 Y
  have hm1' : 0 ≤ trialMask 1 Y ∧ trialMask 1 Y ≤ 1 := by rcases hc1 with h | h <;> simp [h]
  have hm2' : 0 ≤ trialMask 2 Y ∧ trialMask 2 Y ≤ 1 := by rcases hc2 with h | h <;> simp [h]
  have hm3' : 0 ≤ trialMask 3 Y ∧ trialMask 3 Y ≤ 1 := by rcases hc3 with h | h <;> simp [h]
  have hd := trialHybridLoss_nonneg
  have hb : 0 ≤ trialHybridLoss * trialFaceKernel Y := mul_nonneg hd hk.1
  have hbk : trialHybridLoss * trialFaceKernel Y ≤ trialHybridLoss * (1097 / 500) :=
    mul_le_mul_of_nonneg_left hk.2.le hd
  have hw0 : 0 ≤ (trialLambda : ℝ) * trialActualBaseMask Y +
      (1 - (trialLambda : ℝ)) * trialActualEnlargedMask Y +
      trialHybridLoss * trialFaceKernel Y * trialActualSubtractionMask Y :=
    add_nonneg (add_nonneg (mul_nonneg hl hc.1.1)
      (mul_nonneg (sub_nonneg.mpr hl1) hc.2.1.1)) (mul_nonneg hb hc.2.2.1)
  have hdiff : 0 ≤ (trialLambda : ℝ) * (trialMask 1 Y - trialActualBaseMask Y) +
      (1 - (trialLambda : ℝ)) * (trialMask 2 Y - trialActualEnlargedMask Y) +
      trialHybridLoss * trialFaceKernel Y * (trialMask 3 Y - trialActualSubtractionMask Y) :=
    add_nonneg (add_nonneg (mul_nonneg hl (sub_nonneg.mpr hc.1.2))
      (mul_nonneg (sub_nonneg.mpr hl1) (sub_nonneg.mpr hc.2.1.2)))
      (mul_nonneg hb (sub_nonneg.mpr hc.2.2.2))
  have hwcap : (trialLambda : ℝ) * trialMask 1 Y +
      (1 - (trialLambda : ℝ)) * trialMask 2 Y ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hm1'.2 hl,
      mul_le_mul_of_nonneg_left hm2'.2 (sub_nonneg.mpr hl1)]
  have hlast : trialHybridLoss * trialFaceKernel Y * trialMask 3 Y ≤
      trialHybridLoss * trialFaceKernel Y :=
    mul_le_of_le_one_right hb hm3'.2
  dsimp only [trialActualFaceMultiplier, trialCapFaceMultiplier]
  constructor
  · linarith
  constructor
  · nlinarith only [hdiff]
  constructor
  · linarith
  · nlinarith only [hw0, hwcap, hlast, hbk]

#print axioms trialStepFunction_mass_support
#print axioms trialSourceMarginal_energy_bound
#print axioms trialFaceMultiplier_bounds

end PrimeGap182
