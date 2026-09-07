import TrialCapGeometry182

/-!
The actual 512 radial blocks partition retained cell sums.  The identities
hold for signed profiles and distinct auxiliary constructions: orthogonality
is proved only for the disjoint limiting profiles, not for an arithmetic
square before its mixed terms have been estimated.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PrimeGap182

def trialFaceCellSum (Y : Fin 38 → FiniteMeasure ℝ) : ℕ :=
  ∑ i, trialCellIndex (Y i)

def trialFaceBlockMask (b : Fin 512) (Y : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  if trialFaceCellSum Y < trialCellCount ∧ trialFaceCellSum Y / 768 = b.val then 1 else 0

def trialBlockProfile (f : (Fin 39 → FiniteMeasure ℝ) → ℝ)
    (i : Fin 39) (b : Fin 512) (X : Fin 39 → FiniteMeasure ℝ) : ℝ :=
  trialFaceBlockMask b (i.removeNth X) * f X

theorem measurable_trialFaceCellSum : Measurable trialFaceCellSum :=
  Finset.measurable_sum _ fun i _ => measurable_trialCellIndex.comp (measurable_pi_apply i)

theorem measurable_trialFaceBlockMask (b : Fin 512) : Measurable (trialFaceBlockMask b) := by
  unfold trialFaceBlockMask
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurableSet_lt measurable_trialFaceCellSum measurable_const).inter
    (measurableSet_eq_fun
      ((measurable_of_countable (fun j : ℕ => j / 768)).comp measurable_trialFaceCellSum)
      measurable_const)

theorem measurable_trialBlockProfile {f : (Fin 39 → FiniteMeasure ℝ) → ℝ}
    (hf : Measurable f) (i : Fin 39) (b : Fin 512) :
    Measurable (trialBlockProfile f i b) := by
  change Measurable (fun X : Fin 39 → FiniteMeasure ℝ =>
    trialFaceBlockMask b (fun j : Fin 38 => X (i.succAbove j)) * f X)
  apply Measurable.mul _ hf
  apply (measurable_trialFaceBlockMask b).comp
  exact measurable_pi_lambda _ fun j => measurable_pi_apply (i.succAbove j)

theorem trialFaceBlockMask_values (b : Fin 512) (Y : Fin 38 → FiniteMeasure ℝ) :
    trialFaceBlockMask b Y = 0 ∨ trialFaceBlockMask b Y = 1 := by
  unfold trialFaceBlockMask
  split_ifs <;> simp

theorem trialFaceBlockMask_disjoint {b c : Fin 512} (hbc : b ≠ c)
    (Y : Fin 38 → FiniteMeasure ℝ) :
    trialFaceBlockMask b Y * trialFaceBlockMask c Y = 0 := by
  unfold trialFaceBlockMask
  split_ifs with hb hc
  · exact False.elim (hbc (Fin.ext (hb.2.symm.trans hc.2)))
  all_goals norm_num

theorem trialFaceBlockMask_partition (Y : Fin 38 → FiniteMeasure ℝ) :
    (∑ b : Fin 512, trialFaceBlockMask b Y) =
      if trialFaceCellSum Y < trialCellCount then 1 else 0 := by
  classical
  by_cases hY : trialFaceCellSum Y < trialCellCount
  · have hb : trialFaceCellSum Y / 768 < 512 := by
      rw [trialCellCount_eq] at hY
      omega
    let b : Fin 512 := ⟨trialFaceCellSum Y / 768, hb⟩
    rw [ite_eq_left hY, Finset.sum_eq_single b]
    · simp [trialFaceBlockMask, hY, b]
    · intro c _ hcb
      have hne : trialFaceCellSum Y / 768 ≠ c.val := by
        intro hc
        exact hcb (Fin.ext hc.symm)
      simp [trialFaceBlockMask, hne]
    · simp
  · simp [trialFaceBlockMask, hY]

theorem trialBlockProfile_erasure (f : (Fin 39 → FiniteMeasure ℝ) → ℝ)
    (i : Fin 39) (b : Fin 512) (Y : Fin 38 → FiniteMeasure ℝ) :
    (∫ X : FiniteMeasure ℝ, trialBlockProfile f i b (i.insertNth X Y)
      ∂trialPhysicalMeasure) = trialFaceBlockMask b Y *
        (∫ X : FiniteMeasure ℝ, f (i.insertNth X Y) ∂trialPhysicalMeasure) := by
  simp only [trialBlockProfile, Fin.removeNth_insertNth, integral_const_mul]

theorem trialBlockErasure_mul_eq_zero (f g : (Fin 39 → FiniteMeasure ℝ) → ℝ)
    (i : Fin 39) {b c : Fin 512} (hbc : b ≠ c) (Y : Fin 38 → FiniteMeasure ℝ) :
    (∫ X : FiniteMeasure ℝ, trialBlockProfile f i b (i.insertNth X Y)
      ∂trialPhysicalMeasure) *
      (∫ X : FiniteMeasure ℝ, trialBlockProfile g i c (i.insertNth X Y)
        ∂trialPhysicalMeasure) = 0 := by
  rw [trialBlockProfile_erasure, trialBlockProfile_erasure]
  calc
    _ = (trialFaceBlockMask b Y * trialFaceBlockMask c Y) *
        ((∫ X : FiniteMeasure ℝ, f (i.insertNth X Y) ∂trialPhysicalMeasure) *
          (∫ X : FiniteMeasure ℝ, g (i.insertNth X Y) ∂trialPhysicalMeasure)) := by ring
    _ = 0 := by rw [trialFaceBlockMask_disjoint hbc, zero_mul]

theorem trialBlockErasure_cross_integral_zero
    (f g : (Fin 39 → FiniteMeasure ℝ) → ℝ) (i : Fin 39)
    {b c : Fin 512} (hbc : b ≠ c) (w : (Fin 38 → FiniteMeasure ℝ) → ℝ) :
    (∫ Y : Fin 38 → FiniteMeasure ℝ, w Y *
      ((∫ X : FiniteMeasure ℝ, trialBlockProfile f i b (i.insertNth X Y)
        ∂trialPhysicalMeasure) *
        (∫ X : FiniteMeasure ℝ, trialBlockProfile g i c (i.insertNth X Y)
          ∂trialPhysicalMeasure)) ∂trialProductMeasure 38) = 0 := by
  simp only [trialBlockErasure_mul_eq_zero f g i hbc, mul_zero, integral_zero]

theorem trialMarginal_zero_of_cellSum_ge (i : Fin 39)
    (Y : Fin 38 → FiniteMeasure ℝ) (hY : trialCellCount ≤ trialFaceCellSum Y) :
    trialMarginal i Y = 0 := by
  change (∫ X : FiniteMeasure ℝ, trialStepFunction (i.insertNth X Y)
    ∂trialPhysicalMeasure) = 0
  apply integral_eq_zero_of_ae
  filter_upwards [] with X
  by_contra hf
  have hroot := (trialStepFunction_support (i.insertNth X Y) hf).1
  obtain ⟨b, hb⟩ := hroot
  have hsum : (∑ j : Fin 39, trialCellIndex ((i.insertNth X Y : Fin 39 → FiniteMeasure ℝ) j)) =
      trialCellIndex X + trialFaceCellSum Y := by
    rw [Fin.sum_univ_succAbove _ i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, trialFaceCellSum]
  have hlt := hb.1
  rw [hsum] at hlt
  omega

theorem trialMarginal_block_partition (i : Fin 39) (Y : Fin 38 → FiniteMeasure ℝ) :
    (∑ b : Fin 512, trialFaceBlockMask b Y * trialMarginal i Y) = trialMarginal i Y := by
  rw [← Finset.sum_mul, trialFaceBlockMask_partition]
  split_ifs with hY
  · simp
  · rw [trialMarginal_zero_of_cellSum_ge i Y (Nat.le_of_not_gt hY)]
    simp

theorem trialFaceBlock_square_partition (g : (Fin 38 → FiniteMeasure ℝ) → ℝ)
    (hsupport : ∀ Y, trialCellCount ≤ trialFaceCellSum Y → g Y = 0)
    (Y : Fin 38 → FiniteMeasure ℝ) :
    (∑ b : Fin 512, (trialFaceBlockMask b Y * g Y) ^ 2) = g Y ^ 2 := by
  have hid (b : Fin 512) : (trialFaceBlockMask b Y * g Y) ^ 2 =
      trialFaceBlockMask b Y * g Y ^ 2 := by
    rcases trialFaceBlockMask_values b Y with h | h <;> simp [h]
  simp_rw [hid]
  rw [← Finset.sum_mul, trialFaceBlockMask_partition]
  split_ifs with hY
  · simp
  · rw [hsupport Y (Nat.le_of_not_gt hY)]
    simp

theorem trialFaceBlock_kernel_value (b : Fin 512) (Y : Fin 38 → FiniteMeasure ℝ)
    (hb : trialFaceBlockMask b Y = 1) :
    trialFaceKernel Y = trialPairKernel (b.val * 768) := by
  have hcond : trialFaceCellSum Y < trialCellCount ∧
      trialFaceCellSum Y / 768 = b.val := by
    by_contra hn
    simp [trialFaceBlockMask, hn] at hb
  have hfirst : b.val * 768 < trialCellCount := by
    rw [trialCellCount_eq]
    have hi := b.isLt
    omega
  have hdiv : b.val * 768 / 768 = b.val := by omega
  have hstop : trialKernelStop (trialFaceCellSum Y) = trialKernelStop (b.val * 768) := by
    simp only [trialKernelStop, trialKernelBlock_eq, hcond.2, hdiv]
  have hrad : trialKernelRadius (trialFaceCellSum Y) = trialKernelRadius (b.val * 768) := by
    simp only [trialKernelRadius, hstop]
  change trialPairKernel (trialFaceCellSum Y) = trialPairKernel (b.val * 768)
  simp only [trialPairKernel, trialPairKernelRat, ite_eq_left hcond.1,
    ite_eq_left hfirst, hrad]

theorem trialFaceBlock_weighted_square_partition (g : (Fin 38 → FiniteMeasure ℝ) → ℝ)
    (hsupport : ∀ Y, trialCellCount ≤ trialFaceCellSum Y → g Y = 0)
    (Y : Fin 38 → FiniteMeasure ℝ) :
    (∑ b : Fin 512, trialPairKernel (b.val * 768) * (trialFaceBlockMask b Y * g Y) ^ 2) =
      trialFaceKernel Y * g Y ^ 2 := by
  have hid (b : Fin 512) :
      trialPairKernel (b.val * 768) * (trialFaceBlockMask b Y * g Y) ^ 2 =
        trialFaceBlockMask b Y * (trialFaceKernel Y * g Y ^ 2) := by
    rcases trialFaceBlockMask_values b Y with hb | hb
    · simp [hb]
    · rw [← trialFaceBlock_kernel_value b Y hb, hb]
      simp
  simp_rw [hid]
  rw [← Finset.sum_mul, trialFaceBlockMask_partition]
  split_ifs with hY
  · simp
  · rw [hsupport Y (Nat.le_of_not_gt hY)]
    simp

#print axioms trialFaceBlockMask_partition
#print axioms trialBlockProfile_erasure
#print axioms trialBlockErasure_cross_integral_zero
#print axioms trialMarginal_block_partition
#print axioms trialFaceBlock_square_partition
#print axioms trialFaceBlock_weighted_square_partition

end PrimeGap182
