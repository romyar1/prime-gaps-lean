import BandRadialPartition182

/-!
Sharp exceptional-term control for the original, unpartitioned erased
Selberg root. The right side is the actual fragment-law integral with
the literal finite step kernel. All radial decomposition, mixed moments,
prime-pair mass and auxiliary sieve inputs are proved in the imports.
-/

noncomputable section
open scoped BigOperators ENNReal Topology
open Filter MeasureTheory PrimeGap186

namespace PrimeGap182Analytic

def bandSharpMoment182 {m : ℕ} (H : Finset ℕ) (a : Fin (m + 2) → ℝ)
    (h : Fin 39 → ℕ) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (x : ℝ) (res : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
    if Nat.ModEq (presievingModulus H x) n res then
      sharpDefect x (41361 / 100000) (n + h i) *
        sampledSelbergRoot (erasedBandArray182 H a i G F x) (fun k => n + h (i.succAbove k)) ^ 2 else 0

def bandKernelEnergy182 {m : ℕ} (a : Fin (m + 2) → ℝ) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) : ℝ :=
  ∫ Y, bandFaceKernel182 Y * bandCombinedFace182 a i G F Y ^ 2
    ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a)

def physicalBandErased182 {m : ℕ} (a : Fin (m + 2) → ℝ) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (Y : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  G (fun k => fragmentBandMasses a (Y k)) +
    ∫ t : FiniteMeasure ℝ, F (fun k => fragmentBandMasses a
      (i.insertNth (α := fun _ => FiniteMeasure ℝ) t Y k)) ∂selbergPhysicalMeasure182

def physicalBandKernelEnergy182 {m : ℕ} (a : Fin (m + 2) → ℝ) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) : ℝ :=
  ∫ Y, PrimeGap182.trialFaceKernel Y * physicalBandErased182 a i G F Y ^ 2
    ∂Measure.pi (fun _ : Fin 38 => selbergPhysicalMeasure182)

theorem bandSharpMoment182_eq_radial {m : ℕ} (H : Finset ℕ) (a : Fin (m + 2) → ℝ)
    (h : Fin 39 → ℕ) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hG : ∀ Y, G Y ≠ 0 → bandFaceCellSum182 Y < PrimeGap182.trialCellCount)
    (hF : ∀ X, F X ≠ 0 → bandFaceCellSum182 (i.removeNth X) < PrimeGap182.trialCellCount)
    (x : ℝ) (res : ℕ) : bandSharpMoment182 H a h i G F x res =
      radialSharpMoment182 H h i (radialBandArray182 H a i G F) x res := by
  simp only [bandSharpMoment182, radialSharpMoment182,
    radialErasedValue182_eq_erased_root H a h i G F hG hF]

theorem measurable_bandFaceKernel182 {m : ℕ} : Measurable (@bandFaceKernel182 m) := by
  have hs : Measurable (@bandFaceCellSum182 m) :=
    Finset.measurable_sum _ fun k _ => measurable_bandCellIndex182.comp (measurable_pi_apply k)
  exact (measurable_of_countable PrimeGap182.trialPairKernel).comp hs

theorem bandFaceKernel182_pullback {m : ℕ} (a : Fin (m + 2) → ℝ) (ha : Monotone a)
    (Y : Fin 38 → FiniteMeasure ℝ)
    (hY : ∀ k, (Y k).restrict (Set.Ioc (a 0) (a (Fin.last (m + 1)))) = Y k) :
    bandFaceKernel182 (fun k => fragmentBandMasses a (Y k)) = PrimeGap182.trialFaceKernel Y := by
  have hs (k : Fin 38) : (∑ j, fragmentBandMasses a (Y k) j) = ((Y k).mass : ℝ) := by
    rw [sum_fragmentBandMasses a ha, hY k]
  simp only [bandFaceKernel182, bandFaceCellSum182, bandCellIndex182, hs,
    PrimeGap182.trialFaceKernel, PrimeGap182.trialCellIndex]

theorem bandKernelEnergy182_eq_physical {m : ℕ} (a : Fin (m + 2) → ℝ)
    (ha : StrictMono a) (ha0 : a 0 = 0) (haLast : a (Fin.last (m + 1)) = selbergFragmentCap182)
    (i : Fin 39) (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (hG : Measurable G) (hF : Measurable F) :
    bandKernelEnergy182 a i G F = physicalBandKernelEnergy182 a i G F := by
  let Ψ : (Fin 38 → Fin (m + 1) → ℝ) → (Fin 1 → ℝ) → ℝ :=
    fun Y v => bandFaceKernel182 Y * (G Y + v 0) ^ 2
  have hΨ : Measurable (Function.uncurry Ψ) := by
    exact (measurable_bandFaceKernel182.comp measurable_fst).mul
      (((hG.comp measurable_fst).add ((measurable_pi_apply 0).comp measurable_snd)).pow_const 2)
  have hraw := PrimeGap182.Selberg.fragment_band_law_fiber_function_integral_pullback
    selbergFragmentCap182 a 38 1 i (fun _ => F) (fun _ => hF) Ψ hΨ
  have hbase : bandKernelEnergy182 a i G F =
      ∫ Y, bandFaceKernel182 (fun k => fragmentBandMasses a (Y k)) * physicalBandErased182 a i G F Y ^ 2
        ∂Measure.pi (fun _ : Fin 38 => selbergPhysicalMeasure182) := by
    simpa only [Ψ, bandKernelEnergy182, bandCombinedFace182, physicalBandErased182,
      selbergBandMeasure182, selbergPhysicalMeasure182] using hraw
  rw [hbase]
  have hc : ∀ᵐ c ∂selbergPhysicalMeasure182,
      c.restrict (Set.Ioc (0 : ℝ) selbergFragmentCap182) = c :=
    Measure.ae_smul_measure (ae_restrict_Ioc_fragmentLaw selbergFragmentCap182) _
  have hall : ∀ᵐ Y ∂Measure.pi (fun _ : Fin 38 => selbergPhysicalMeasure182), ∀ k,
      (Y k).restrict (Set.Ioc (0 : ℝ) selbergFragmentCap182) = Y k :=
    eventually_all.mpr fun k =>
      (Measure.tendsto_eval_ae_ae
        (μ := fun _ : Fin 38 => selbergPhysicalMeasure182) (i := k)).eventually hc
  apply integral_congr_ae
  filter_upwards [hall] with Y hY
  have hcap : ∀ k, (Y k).restrict (Set.Ioc (a 0) (a (Fin.last (m + 1)))) = Y k := by
    simpa only [ha0, haLast] using hY
  rw [bandFaceKernel182_pullback a ha.monotone Y hcap]

theorem physical_sharp_exceptional_moment_upper182 {H : Finset ℕ} (hH : H.card = 39) {m : ℕ}
    (a : Fin (m + 2) → ℝ) (ha : StrictMono a) (ha0 : a 0 = 0)
    (haLast : a (Fin.last (m + 1)) = selbergFragmentCap182) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hG : Measurable G) (hF : Measurable F)
    (hbG : Bornology.IsBounded (Set.range G)) (hbF : Bornology.IsBounded (Set.range F))
    (hcG : ∀ᵐ Y ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a), ContinuousAt G Y)
    (hcF : ∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => selbergBandMeasure182 a), ContinuousAt F X)
    (hsG : ∀ Y, G Y ≠ 0 → bandFaceCellSum182 Y < PrimeGap182.trialCellCount)
    (hsF : ∀ X, F X ≠ 0 → bandFaceCellSum182 (i.removeNth X) < PrimeGap182.trialCellCount)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ x : ℝ in atTop, ∀ res : ℕ,
      bandSharpMoment182 H a (H.orderEmbOfFin hH) i G F x res ≤
        sieveMomentScale182 H x * (physicalBandKernelEnergy182 a i G F + ε) := by
  have hmain := band_radial_sharp_exceptional_moment_upper182 hH a ha ha0 haLast i G F
    hG hF hbG hbF hcG hcF ε hε
  have henergy : (∑ b : Fin 512,
      PrimeGap182.trialPairKernel (b.val * 768) * bandRadialEnergy182 a i G F b) =
      physicalBandKernelEnergy182 a i G F :=
    (bandRadialEnergy182_kernel_identity a i G F hG hF hbG hbF).trans
      (bandKernelEnergy182_eq_physical a ha ha0 haLast i G F hG hF)
  rw [henergy] at hmain
  filter_upwards [hmain] with x hx
  intro res
  rw [bandSharpMoment182_eq_radial H a (H.orderEmbOfFin hH) i G F hsG hsF]
  exact hx res

#print axioms bandKernelEnergy182_eq_physical
#print axioms physical_sharp_exceptional_moment_upper182

end PrimeGap182Analytic
