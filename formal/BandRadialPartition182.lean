import BandRadialMoments182

/-!
Exact reconstruction of the erased sieve root and its physical kernel
energy from the 512 radial blocks. The arithmetic reconstruction uses
the profile support, while the weighted energy identity also holds
outside the blocks because the literal kernel is extended by zero.
-/

noncomputable section
open scoped BigOperators ENNReal Topology
open Filter MeasureTheory PrimeGap186

namespace PrimeGap182Analytic

def bandFaceKernel182 {m : ℕ} (Y : Fin 38 → Fin (m + 1) → ℝ) : ℝ :=
  PrimeGap182.trialPairKernel (bandFaceCellSum182 Y)

theorem bandFaceBlockMask182_partition {m : ℕ} (Y : Fin 38 → Fin (m + 1) → ℝ) :
    (∑ b : Fin 512, bandFaceBlockMask182 b Y) =
      if bandFaceCellSum182 Y < PrimeGap182.trialCellCount then 1 else 0 := by
  classical
  by_cases hY : bandFaceCellSum182 Y < PrimeGap182.trialCellCount
  · have hb : bandFaceCellSum182 Y / 768 < 512 := by
      rw [PrimeGap182.trialCellCount_eq] at hY
      omega
    let b : Fin 512 := ⟨bandFaceCellSum182 Y / 768, hb⟩
    rw [ite_eq_left hY, Finset.sum_eq_single b]
    · simp [bandFaceBlockMask182, hY, b]
    · intro c _ hcb
      have hne : bandFaceCellSum182 Y / 768 ≠ c.val := fun hc => hcb (Fin.ext hc.symm)
      simp [bandFaceBlockMask182, hne]
    · simp
  · simp [bandFaceBlockMask182, hY]

theorem bandFaceBlockKernel182_value {m : ℕ} (b : Fin 512) (Y : Fin 38 → Fin (m + 1) → ℝ)
    (hb : bandFaceBlockMask182 b Y = 1) :
    bandFaceKernel182 Y = PrimeGap182.trialPairKernel (b.val * 768) := by
  have hc : bandFaceCellSum182 Y < PrimeGap182.trialCellCount ∧ bandFaceCellSum182 Y / 768 = b.val := by
    by_contra hn
    simp [bandFaceBlockMask182, hn] at hb
  have hfirst : b.val * 768 < PrimeGap182.trialCellCount := by
    rw [PrimeGap182.trialCellCount_eq]
    have hi := b.isLt
    omega
  have hdiv : b.val * 768 / 768 = b.val := by omega
  have hstop : PrimeGap182.trialKernelStop (bandFaceCellSum182 Y) =
      PrimeGap182.trialKernelStop (b.val * 768) := by
    simp only [PrimeGap182.trialKernelStop, PrimeGap182.trialKernelBlock_eq, hc.2, hdiv]
  have hrad : PrimeGap182.trialKernelRadius (bandFaceCellSum182 Y) =
      PrimeGap182.trialKernelRadius (b.val * 768) := by
    simp only [PrimeGap182.trialKernelRadius, hstop]
  simp only [bandFaceKernel182, PrimeGap182.trialPairKernel, PrimeGap182.trialPairKernelRat,
    ite_eq_left hc.1, ite_eq_left hfirst, hrad]

theorem bandFaceBlock_weighted_square_partition182 {m : ℕ}
    (g : (Fin 38 → Fin (m + 1) → ℝ) → ℝ) (Y : Fin 38 → Fin (m + 1) → ℝ) :
    (∑ b : Fin 512, PrimeGap182.trialPairKernel (b.val * 768) *
      (bandFaceBlockMask182 b Y * g Y) ^ 2) = bandFaceKernel182 Y * g Y ^ 2 := by
  have hid (b : Fin 512) :
      PrimeGap182.trialPairKernel (b.val * 768) * (bandFaceBlockMask182 b Y * g Y) ^ 2 =
        bandFaceBlockMask182 b Y * (bandFaceKernel182 Y * g Y ^ 2) := by
    rcases bandFaceBlockMask182_values b Y with hb | hb
    · simp [hb]
    · rw [← bandFaceBlockKernel182_value b Y hb, hb]
      simp
  simp_rw [hid]
  rw [← Finset.sum_mul, bandFaceBlockMask182_partition]
  split_ifs with hY
  · simp
  · simp only [bandFaceKernel182, PrimeGap182.trialPairKernel, PrimeGap182.trialPairKernelRat,
      ite_eq_right hY, Rat.cast_zero, zero_mul]

theorem bandBlockFace182_sum {m : ℕ} (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (hG : ∀ Y, G Y ≠ 0 → bandFaceCellSum182 Y < PrimeGap182.trialCellCount)
    (Y : Fin 38 → Fin (m + 1) → ℝ) : (∑ b : Fin 512, bandBlockFace182 G b Y) = G Y := by
  simp only [bandBlockFace182, ← Finset.sum_mul, bandFaceBlockMask182_partition]
  by_cases hz : G Y = 0
  · simp [hz]
  · rw [ite_eq_left (hG Y hz), one_mul]

theorem bandBlockProfile182_sum {m : ℕ} (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (i : Fin 39)
    (hF : ∀ X, F X ≠ 0 → bandFaceCellSum182 (i.removeNth X) < PrimeGap182.trialCellCount)
    (X : Fin 39 → Fin (m + 1) → ℝ) : (∑ b : Fin 512, bandBlockProfile182 F i b X) = F X := by
  simp only [bandBlockProfile182, ← Finset.sum_mul, bandFaceBlockMask182_partition]
  by_cases hz : F X = 0
  · simp [hz]
  · rw [ite_eq_left (hF X hz), one_mul]

theorem canonicalBandArray182_finsetSum {J : Type*} {d m : ℕ} (s : Finset J)
    (H : Finset ℕ) (a : Fin (m + 2) → ℝ)
    (F : J → (Fin d → Fin (m + 1) → ℝ) → ℝ) (x : ℝ) :
    canonicalBandArray182 H a (fun X => ∑ j ∈ s, F j X) x =
      ∑ j ∈ s, canonicalBandArray182 H a (F j) x := by
  classical
  have h := PrimeGap182.Selberg.canonical_diagonal_finset_smul s (fun _ => (1 : ℝ))
    ((Fintype.piFinset (fun _ : Fin d => (selbergPrimorial182 H x).divisors)).filter
      (fun r => Squarefree (∏ k, r k)))
    (fun r => fragmentBandMasses a (primeLogConfiguration (x ^ selbergRho182) r))
    (selbergNormalizer182 H x) F
  simpa only [canonicalBandArray182, one_mul, one_smul, finPiFinset_eq_classical] using h

theorem erasedBandArray182_finsetSum {J : Type*} {m : ℕ} (s : Finset J)
    (H : Finset ℕ) (a : Fin (m + 2) → ℝ) (i : Fin 39)
    (G : J → (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : J → (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (x : ℝ) :
    erasedBandArray182 H a i (fun Y => ∑ j ∈ s, G j Y) (fun X => ∑ j ∈ s, F j X) x =
      ∑ j ∈ s, erasedBandArray182 H a i (G j) (F j) x := by
  classical
  simp only [erasedBandArray182, canonicalBandArray182_finsetSum, selbergErasedArray39]
  have h := PrimeGap182.Selberg.weighted_erasure_finset_smul s (fun _ => (1 : ℝ)) i
    (fun j => canonicalBandArray182 H a (F j) x)
  simp only [one_smul] at h
  rw [h, Finset.sum_add_distrib]

theorem radialBandArray182_sum {m : ℕ} (H : Finset ℕ) (a : Fin (m + 2) → ℝ) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hG : ∀ Y, G Y ≠ 0 → bandFaceCellSum182 Y < PrimeGap182.trialCellCount)
    (hF : ∀ X, F X ≠ 0 → bandFaceCellSum182 (i.removeNth X) < PrimeGap182.trialCellCount)
    (x : ℝ) : (∑ b : Fin 512, radialBandArray182 H a i G F b x) = erasedBandArray182 H a i G F x := by
  have h := erasedBandArray182_finsetSum Finset.univ H a i
    (bandBlockFace182 G) (bandBlockProfile182 F i) x
  simp only [bandBlockFace182_sum G hG, bandBlockProfile182_sum F i hF] at h
  exact h.symm

theorem sampledSelbergRoot_finsetSum {J ι : Type*} [Fintype ι] (s : Finset J)
    (y : J → ((ι → ℕ) →₀ ℝ)) (v : ι → ℕ) :
    sampledSelbergRoot (∑ j ∈ s, y j) v = ∑ j ∈ s, sampledSelbergRoot (y j) v := by
  classical
  have h := PrimeGap182.Selberg.selberg_divisor_root_finset_combination s (fun _ => (1 : ℝ)) y v
  simpa only [sampledSelbergRoot, one_smul, one_mul] using h

theorem radialErasedValue182_eq_erased_root {m : ℕ} (H : Finset ℕ) (a : Fin (m + 2) → ℝ)
    (h : Fin 39 → ℕ) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hG : ∀ Y, G Y ≠ 0 → bandFaceCellSum182 Y < PrimeGap182.trialCellCount)
    (hF : ∀ X, F X ≠ 0 → bandFaceCellSum182 (i.removeNth X) < PrimeGap182.trialCellCount)
    (x : ℝ) (n : ℕ) : radialErasedValue182 h i (radialBandArray182 H a i G F) x n =
      sampledSelbergRoot (erasedBandArray182 H a i G F x) (fun k => n + h (i.succAbove k)) := by
  unfold radialErasedValue182
  rw [← sampledSelbergRoot_finsetSum, radialBandArray182_sum H a i G F hG hF]

theorem bandRadialEnergy182_kernel_identity {m : ℕ} (a : Fin (m + 2) → ℝ) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hG : Measurable G) (hF : Measurable F)
    (hbG : Bornology.IsBounded (Set.range G)) (hbF : Bornology.IsBounded (Set.range F)) :
    (∑ b : Fin 512, PrimeGap182.trialPairKernel (b.val * 768) * bandRadialEnergy182 a i G F b) =
      ∫ Y, bandFaceKernel182 Y * bandCombinedFace182 a i G F Y ^ 2
        ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a) := by
  obtain ⟨hm, hb⟩ := bandCombinedFace182_regular a i G F hG hF hbG hbF
  have hint (b : Fin 512) : Integrable (fun Y => PrimeGap182.trialPairKernel (b.val * 768) *
      (bandFaceBlockMask182 b Y * bandCombinedFace182 a i G F Y) ^ 2)
      (Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a)) := by
    have hbprod := isBounded_range_mul_comp (bandFaceBlockMask182_bounded b) hb id id
    have hbq : Bornology.IsBounded (Set.range (fun Y =>
        (bandFaceBlockMask182 b Y * bandCombinedFace182 a i G F Y) ^ 2)) := by
      simpa only [pow_two, id_eq] using isBounded_range_mul_comp hbprod hbprod id id
    exact (integrable_of_measurable_of_bounded_range _ _
      (((measurable_bandFaceBlockMask182 b).mul hm).pow_const 2) hbq).const_mul _
  calc
    _ = ∑ b : Fin 512, ∫ Y, PrimeGap182.trialPairKernel (b.val * 768) *
        (bandFaceBlockMask182 b Y * bandCombinedFace182 a i G F Y) ^ 2
          ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a) := by
      simp only [integral_const_mul, bandRadialEnergy182]
    _ = ∫ Y, ∑ b : Fin 512, PrimeGap182.trialPairKernel (b.val * 768) *
        (bandFaceBlockMask182 b Y * bandCombinedFace182 a i G F Y) ^ 2
          ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a) :=
      (integral_finsetSum Finset.univ (fun b _ => hint b)).symm
    _ = _ := integral_congr_ae (Eventually.of_forall fun Y =>
      bandFaceBlock_weighted_square_partition182 (bandCombinedFace182 a i G F) Y)

#print axioms radialBandArray182_sum
#print axioms radialErasedValue182_eq_erased_root
#print axioms bandRadialEnergy182_kernel_identity

end PrimeGap182Analytic
