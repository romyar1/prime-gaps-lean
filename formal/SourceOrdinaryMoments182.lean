import OrdinarySelberg182
import SourceBandEnergy182
import SharpDeficitBound182

/-! The ordinary square moment of the constructed source-supported trial.
The sampled root, finite interval, residue class, and normalization are
the actual arithmetic definitions. The new support radius is proved
from the profile's band support; no moment limit is assumed. -/

noncomputable section
open MeasureTheory Filter PrimeGap186
open scoped BigOperators Topology

namespace PrimeGap182Analytic

def ordinaryMomentScale182 (H : Finset ℕ) (x : ℝ) : ℝ :=
  x / (presievingModulus H x : ℝ) / selbergNormalizer182 H x ^ 39

open Classical in
def bandOrdinaryMoment182 {m : ℕ} (H : Finset ℕ) (a : Fin (m + 2) → ℝ)
    (h : Fin 39 → ℕ) (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ) (x : ℝ) (res : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
    if Nat.ModEq (presievingModulus H x) n res then
      sampledSelbergRoot (canonicalBandArray182 H a F x) (fun k => n + h k) ^ 2 else 0

theorem ordinaryMomentScale182_pos (H : Finset ℕ) (x : ℝ) (hx : 1 < x) :
    0 < ordinaryMomentScale182 H x := by
  have hρ : 0 < selbergRho182 := by norm_num [selbergRho182]
  exact div_pos (div_pos (zero_lt_one.trans hx) (Nat.cast_pos.mpr (presieving_pos H x)))
    (pow_pos (fragmentNormalization_pos H x _ (Real.one_lt_rpow hx hρ)) 39)

theorem sieveMomentScale182_eq_rho_mul (H : Finset ℕ) (x : ℝ) (hx : 1 < x) :
    sieveMomentScale182 H x = selbergRho182 * ordinaryMomentScale182 H x := by
  have hρ : 0 < selbergRho182 := by norm_num [selbergRho182]
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hB : 0 < fragmentNormalization (presievingModulus H x) x :=
    fragmentNormalization_pos H x x hx
  have hBR : selbergNormalizer182 H x =
      selbergRho182 * fragmentNormalization (presievingModulus H x) x := by
    unfold selbergNormalizer182 fragmentNormalization
    rw [Real.log_rpow hx0]
    ring
  unfold sieveMomentScale182 ordinaryMomentScale182
  rw [hBR]
  field_simp [hB.ne', hρ.ne']

end PrimeGap182Analytic

namespace PrimeGap182
open PrimeGap182Analytic
namespace TrialSmoothProfiles182

theorem root_sample_radius (P : TrialSmoothProfiles182) (W : ℕ) (R : ℝ) (hR : 1 < R)
    (r : Fin 39 → ℕ) (hsq : Squarefree (∏ j, r j))
    (hdiv : ∀ j, r j ∈ (∏ p ∈ fragmentPrimes W R selbergFragmentCap182, p).divisors)
    (hF : P.F (fun j => fragmentBandMasses P.a (primeLogConfiguration R (r j))) ≠ 0) :
    ((∏ j, r j : ℕ) : ℝ) ≤ R ^ (trialRadius : ℝ) := by
  have hκ : 0 < selbergFragmentCap182 := by norm_num [selbergFragmentCap182, selbergRho182]
  have hfull (j : Fin 39) : (primeLogConfiguration R (r j)).restrict
      (Set.Ioc (P.a 0) (P.a (Fin.last (P.m + 1)))) = primeLogConfiguration R (r j) := by
    rw [P.zero, P.last]
    exact primeLogConfiguration_restrict_of_fragment_divisor W R selbergFragmentCap182
      hR hκ (r j) (hdiv j)
  have hband := (P.F_support (subset_closure hF)).2.2.2.2
  change (∑ j, ∑ k, fragmentBandMasses P.a (primeLogConfiguration R (r j)) k) <
    (trialRadius : ℝ) at hband
  simp_rw [sum_fragmentBandMasses P.a P.strictMono.monotone, hfull] at hband
  rw [primeLogConfiguration_total_mass 39 R hR r hsq] at hband
  exact (Real.logb_le_iff_le_rpow hR (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hsq.ne_zero))).mp hband.le

theorem ordinary_square_moment (P : TrialSmoothProfiles182)
    {H : Finset ℕ} (hH : H.card = 39) :
    UniformScaledLimit atTop
      (bandOrdinaryMoment182 H P.a (H.orderEmbOfFin hH) P.F)
      (ordinaryMomentScale182 H)
      (∫ X, P.F X ^ 2 ∂Measure.pi (fun _ : Fin 39 => selbergBandMeasure182 P.a)) := by
  have hκ : 0 < selbergFragmentCap182 := by norm_num [selbergFragmentCap182, selbergRho182]
  have hS : (0 : ℝ) < trialRadius := by norm_num [trialRadius]
  have hsmall : (2624989 / 10000000 : ℝ) * (trialRadius : ℝ) < 1 / 2 := by
    norm_num [trialRadius]
  have hraw := PrimeGap182.Selberg.canonical39_fixed_band_ordinary_square_radius
    (𝓗 := H) (h𝓗_card := hH) selbergFragmentCap182 hκ (trialRadius : ℝ) hS hsmall
    P.a P.strictMono P.zero P.last P.F P.F_smooth.continuous.measurable
    (P.F_compact.isCompact_range P.F_smooth.continuous).isBounded
    P.root_sample_radius (ae_of_all _ fun _ => P.F_smooth.continuous.continuousAt)
  simpa only [UniformScaledLimit, bandOrdinaryMoment182, ordinaryMomentScale182,
    canonicalBandArray182, selbergNormalizer182, selbergPrimorial182, selbergRho182,
    selbergBandMeasure182, sampledSelbergRoot_fin, finPiFinset_eq_classical, mul_comm] using hraw

theorem ordinary_square_moment_physical (P : TrialSmoothProfiles182)
    {H : Finset ℕ} (hH : H.card = 39) :
    UniformScaledLimit atTop
      (bandOrdinaryMoment182 H P.a (H.orderEmbOfFin hH) P.F)
      (ordinaryMomentScale182 H)
      (∫ X, P.rootPhysical X ^ 2 ∂trialAmbientProduct selbergFragmentCap182 39) := by
  rw [← P.bandRootEnergy_pullback]
  exact P.ordinary_square_moment hH

#print axioms root_sample_radius
#print axioms ordinary_square_moment
#print axioms ordinary_square_moment_physical

end TrialSmoothProfiles182

theorem positive_band_profiles_at_actual_sharp_deficit182 (h : PhysicalSourceBounds182) :
    ∃ P : TrialSmoothProfiles182, 0 < P.bandHybridEnergy SharpMean.sharpMass := by
  obtain ⟨P, hP⟩ := physical_positive_admissible_band_profiles182 h
  exact ⟨P, hP SharpMean.sharpMass SharpMean.sharpMass_nonneg
    SharpMean.sharpMass_lt_convexKappaBound.le⟩

#print axioms positive_band_profiles_at_actual_sharp_deficit182

end PrimeGap182
