import BandRadialArrays182

/-!
Harmonic convergence and the sharp exceptional moment for actual sampled
finite-band profiles. No harmonic-limit or amplitude assumptions remain
in the final theorem: they follow from the regularity of the two signed
profiles and the proved radial geometry.
-/

noncomputable section
open scoped BigOperators ENNReal Topology
open Filter MeasureTheory PrimeGap186

namespace PrimeGap182Analytic

def bandCombinedFace182 {m : ℕ} (a : Fin (m + 2) → ℝ) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (Y : Fin 38 → Fin (m + 1) → ℝ) : ℝ :=
  G Y + ∫ t, F (i.insertNth t Y) ∂selbergBandMeasure182 a

def bandRadialEnergy182 {m : ℕ} (a : Fin (m + 2) → ℝ) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (b : Fin 512) : ℝ :=
  ∫ Y, (bandFaceBlockMask182 b Y * bandCombinedFace182 a i G F Y) ^ 2
    ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a)

theorem bandCombinedFace182_radial {m : ℕ} (a : Fin (m + 2) → ℝ) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (b : Fin 512) (Y : Fin 38 → Fin (m + 1) → ℝ) :
    bandCombinedFace182 a i (bandBlockFace182 G b) (bandBlockProfile182 F i b) Y =
      bandFaceBlockMask182 b Y * bandCombinedFace182 a i G F Y := by
  simp only [bandCombinedFace182, bandBlockFace182, bandBlockProfile182_erasure, mul_add]

theorem bandRadialEnergy182_nonneg {m : ℕ} (a : Fin (m + 2) → ℝ) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (b : Fin 512) :
    0 ≤ bandRadialEnergy182 a i G F b := integral_nonneg fun _ => sq_nonneg _

theorem bandCombinedFace182_regular {m : ℕ} (a : Fin (m + 2) → ℝ) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hG : Measurable G) (hF : Measurable F)
    (hbG : Bornology.IsBounded (Set.range G)) (hbF : Bornology.IsBounded (Set.range F)) :
    Measurable (bandCombinedFace182 a i G F) ∧
      Bornology.IsBounded (Set.range (bandCombinedFace182 a i G F)) := by
  have hins : Measurable
      (fun p : (Fin 38 → Fin (m + 1) → ℝ) × (Fin (m + 1) → ℝ) =>
        i.insertNth (α := fun _ => Fin (m + 1) → ℝ) p.2 p.1) :=
    (continuous_snd.finInsertNth i continuous_fst).measurable
  refine ⟨hG.add ((hF.comp hins).stronglyMeasurable.integral_prod_right'.measurable), ?_⟩
  obtain ⟨MG, _, hMG⟩ := hbG.exists_pos_norm_le
  obtain ⟨MF, _, hMF⟩ := hbF.exists_pos_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨MG + (selbergBandMeasure182 a).real Set.univ * MF, ?_⟩
  rintro _ ⟨Y, rfl⟩
  have hi : ‖∫ t, F (i.insertNth t Y) ∂selbergBandMeasure182 a‖ ≤
      (selbergBandMeasure182 a).real Set.univ * MF := by
    simpa only [mul_comm] using (norm_integral_le_of_norm_le_const
      (μ := selbergBandMeasure182 a) (Eventually.of_forall fun t => hMF _ ⟨i.insertNth t Y, rfl⟩))
  exact (norm_add_le _ _).trans (add_le_add (hMG _ ⟨Y, rfl⟩) hi)

theorem erasedBandArray182_harmonic_tendsto {H : Finset ℕ} {m : ℕ}
    (a : Fin (m + 2) → ℝ) (ha : StrictMono a) (ha0 : a 0 = 0)
    (haLast : a (Fin.last (m + 1)) = selbergFragmentCap182) (i : Fin 39)
    (G G' : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F F' : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hG : Measurable G) (hG' : Measurable G') (hF : Measurable F) (hF' : Measurable F')
    (hbG : Bornology.IsBounded (Set.range G)) (hbG' : Bornology.IsBounded (Set.range G'))
    (hbF : Bornology.IsBounded (Set.range F)) (hbF' : Bornology.IsBounded (Set.range F'))
    (hcG : ∀ᵐ Y ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a), ContinuousAt G Y)
    (hcG' : ∀ᵐ Y ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a), ContinuousAt G' Y)
    (hcF : ∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => selbergBandMeasure182 a), ContinuousAt F X)
    (hcF' : ∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => selbergBandMeasure182 a), ContinuousAt F' X) :
    Tendsto (fun x => selbergNormalizer182 H x ^ 38 *
      mixedHarmonic (fun r : Fin 38 → ℕ => ∏ k, ((r k).totient : ℝ))
        (erasedBandArray182 H a i G F x) (erasedBandArray182 H a i G' F' x)) atTop
      (nhds (∫ Y, bandCombinedFace182 a i G F Y * bandCombinedFace182 a i G' F' Y
        ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a))) := by
  have h := PrimeGap182.Selberg.canonical_and_erased_polarized_harmonic_tendsto (𝓗 := H)
    i selbergFragmentCap182 (by norm_num [selbergFragmentCap182, selbergRho182])
    a ha ha0 haLast G G' F F' hG hG' hF hF' hbG hbG' hbF hbF' hcG hcG' hcF hcF'
  simpa only [mixedHarmonic, erasedBandArray182, canonicalBandArray182, selbergErasedArray39,
    selbergNormalizer182, selbergPrimorial182, selbergRho182, bandCombinedFace182,
    selbergBandMeasure182, finPiFinset_eq_classical] using h

theorem radialBandArray182_bounds {H : Finset ℕ} (hH : H.card = 39) {m : ℕ}
    (a : Fin (m + 2) → ℝ) (ha : StrictMono a) (ha0 : a 0 = 0)
    (haLast : a (Fin.last (m + 1)) = selbergFragmentCap182) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hbG : Bornology.IsBounded (Set.range G)) (hbF : Bornology.IsBounded (Set.range F)) :
    ∃ M : Fin 512 → ℝ, (∀ b, 0 ≤ M b) ∧ RadialArrayBounds182 H (radialBandArray182 H a i G F) M := by
  have hb (b : Fin 512) := erasedBandArray182_amplitude hH a i
    (bandBlockFace182 G b) (bandBlockProfile182 F i b)
    (isBounded_range_mul_comp (bandFaceBlockMask182_bounded b) hbG id id)
    (isBounded_range_mul_comp (bandFaceBlockMask182_bounded b) hbF
      (fun X : Fin 39 → Fin (m + 1) → ℝ => i.removeNth X) id)
  choose M hM hbound using hb
  refine ⟨M, fun b => (hM b).le, ?_⟩
  have hall := eventually_all.mpr hbound
  filter_upwards [hall, eventually_gt_atTop (1 : ℝ)] with x hx hxx
  intro b
  refine ⟨?_, hx b⟩
  intro r hr
  obtain ⟨hsf, hdiv, _⟩ := radialBandArray182_support_data H a i G F b x r hr
  exact ⟨hsf, hdiv, radialBandArray182_radius H a ha ha0 haLast i G F b x hxx r hr⟩

theorem radialBandArray182_diagonal_tendsto {H : Finset ℕ} {m : ℕ}
    (a : Fin (m + 2) → ℝ) (ha : StrictMono a) (ha0 : a 0 = 0)
    (haLast : a (Fin.last (m + 1)) = selbergFragmentCap182) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hG : Measurable G) (hF : Measurable F)
    (hbG : Bornology.IsBounded (Set.range G)) (hbF : Bornology.IsBounded (Set.range F))
    (hcG : ∀ᵐ Y ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a), ContinuousAt G Y)
    (hcF : ∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => selbergBandMeasure182 a), ContinuousAt F X)
    (b : Fin 512) : Tendsto (fun x => selbergNormalizer182 H x ^ 38 *
      diagonalHarmonic (fun r : Fin 38 → ℕ => ∏ k, ((r k).totient : ℝ))
        (radialBandArray182 H a i G F b x)) atTop (nhds (bandRadialEnergy182 a i G F b)) := by
  obtain ⟨hmG, hbGb, hcGb⟩ := bandBlockFace182_regular a ha ha0 haLast G hG hbG hcG b
  obtain ⟨hmF, hbFb, hcFb⟩ := bandBlockProfile182_regular a ha ha0 haLast F hF hbF hcF i b
  have h := erasedBandArray182_harmonic_tendsto (H := H) a ha ha0 haLast i
    (bandBlockFace182 G b) (bandBlockFace182 G b) (bandBlockProfile182 F i b) (bandBlockProfile182 F i b)
    hmG hmG hmF hmF hbGb hbGb hbFb hbFb hcGb hcGb hcFb hcFb
  simpa only [mixedHarmonic_self, radialBandArray182, bandCombinedFace182_radial,
    bandRadialEnergy182, pow_two] using h

theorem radialBandArray182_cross_tendsto_zero {H : Finset ℕ} {m : ℕ}
    (a : Fin (m + 2) → ℝ) (ha : StrictMono a) (ha0 : a 0 = 0)
    (haLast : a (Fin.last (m + 1)) = selbergFragmentCap182) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hG : Measurable G) (hF : Measurable F)
    (hbG : Bornology.IsBounded (Set.range G)) (hbF : Bornology.IsBounded (Set.range F))
    (hcG : ∀ᵐ Y ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a), ContinuousAt G Y)
    (hcF : ∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => selbergBandMeasure182 a), ContinuousAt F X)
    (b c : Fin 512) (hbc : b ≠ c) : Tendsto (fun x => selbergNormalizer182 H x ^ 38 *
      mixedHarmonic (fun r : Fin 38 → ℕ => ∏ k, ((r k).totient : ℝ))
        (radialBandArray182 H a i G F b x) (radialBandArray182 H a i G F c x)) atTop (nhds 0) := by
  obtain ⟨hmGb, hbGb, hcGb⟩ := bandBlockFace182_regular a ha ha0 haLast G hG hbG hcG b
  obtain ⟨hmFb, hbFb, hcFb⟩ := bandBlockProfile182_regular a ha ha0 haLast F hF hbF hcF i b
  obtain ⟨hmGc, hbGc, hcGc⟩ := bandBlockFace182_regular a ha ha0 haLast G hG hbG hcG c
  obtain ⟨hmFc, hbFc, hcFc⟩ := bandBlockProfile182_regular a ha ha0 haLast F hF hbF hcF i c
  have h := erasedBandArray182_harmonic_tendsto (H := H) a ha ha0 haLast i
    (bandBlockFace182 G b) (bandBlockFace182 G c) (bandBlockProfile182 F i b) (bandBlockProfile182 F i c)
    hmGb hmGc hmFb hmFc hbGb hbGc hbFb hbFc hcGb hcGc hcFb hcFc
  simpa only [radialBandArray182, bandCombinedFace182, bandBlock_combined_cross_zero a G F i hbc,
    integral_zero] using h

theorem band_radial_sharp_exceptional_moment_upper182 {H : Finset ℕ} (hH : H.card = 39) {m : ℕ}
    (a : Fin (m + 2) → ℝ) (ha : StrictMono a) (ha0 : a 0 = 0)
    (haLast : a (Fin.last (m + 1)) = selbergFragmentCap182) (i : Fin 39)
    (G : (Fin 38 → Fin (m + 1) → ℝ) → ℝ)
    (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (hG : Measurable G) (hF : Measurable F)
    (hbG : Bornology.IsBounded (Set.range G)) (hbF : Bornology.IsBounded (Set.range F))
    (hcG : ∀ᵐ Y ∂Measure.pi (fun _ : Fin 38 => selbergBandMeasure182 a), ContinuousAt G Y)
    (hcF : ∀ᵐ X ∂Measure.pi (fun _ : Fin 39 => selbergBandMeasure182 a), ContinuousAt F X)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ x : ℝ in atTop, ∀ res : ℕ,
      radialSharpMoment182 H (H.orderEmbOfFin hH) i (radialBandArray182 H a i G F) x res ≤
        sieveMomentScale182 H x * ((∑ b : Fin 512,
          PrimeGap182.trialPairKernel (b.val * 768) * bandRadialEnergy182 a i G F b) + ε) := by
  obtain ⟨M, hM, hdata⟩ := radialBandArray182_bounds hH a ha ha0 haLast i G F hbG hbF
  exact radial_sharp_exceptional_moment_upper182 hH i (radialBandArray182 H a i G F) M
    (bandRadialEnergy182 a i G F) hM (bandRadialEnergy182_nonneg a i G F) hdata
    (radialBandArray182_diagonal_tendsto a ha ha0 haLast i G F hG hF hbG hbF hcG hcF)
    (radialBandArray182_cross_tendsto_zero a ha ha0 haLast i G F hG hF hbG hbF hcG hcF) ε hε

#print axioms erasedBandArray182_harmonic_tendsto
#print axioms radialBandArray182_bounds
#print axioms radialBandArray182_cross_tendsto_zero
#print axioms band_radial_sharp_exceptional_moment_upper182

end PrimeGap182Analytic
