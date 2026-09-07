import SourcePairingAlgebra182
import SourcePairingEnergy182

/-! The exact first-moment lower bound for the constructed arithmetic
arrays, and the unconditional exceptional-square bound in band coordinates. -/

noncomputable section
open MeasureTheory Filter PrimeGap186 PrimeGap182Analytic
open scoped BigOperators Topology

namespace PrimeGap182.TrialSmoothProfiles182
open SieveFaceRole182

theorem sum_sievePairCoefficient (v : Fin 6 → ℝ) :
    (∑ k : Fin 6, sievePairCoefficient k * v k) =
      2 * v 0 - v 1 + 2 * (1 - (trialLambda : ℝ)) * v 2 +
      2 * (1 - (trialLambda : ℝ)) * v 3 - (1 - (trialLambda : ℝ)) ^ 2 * v 4 -
      trialHybridLoss⁻¹ * (1 - (trialLambda : ℝ)) ^ 2 * v 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change 2 * v 0 + (-1 * v 1 +
    (2 * (1 - (trialLambda : ℝ)) * v 2 + (2 * (1 - (trialLambda : ℝ)) * v 3 +
    (-(1 - (trialLambda : ℝ)) ^ 2 * v 4 +
      -trialHybridLoss⁻¹ * (1 - (trialLambda : ℝ)) ^ 2 * v 5)))) = _
  ring

theorem sieveKernelIntegral_eq_physical (P : TrialSmoothProfiles182) (i : Fin 39) :
    P.sieveKernelIntegral i = ∫ Y, trialFaceKernel Y *
      (P.coefficientErasure i Y - P.facePhysical 2 Y * P.coefficientErasure i Y) ^ 2
        ∂trialAmbientProduct selbergFragmentCap182 38 := by
  rw [← P.physicalBandKernelEnergy_eq]
  rw [← bandKernelEnergy182_eq_physical P.a P.strictMono P.zero P.last i
    (P.exceptionalFace i) P.F (P.continuous_exceptionalFace i).measurable
    P.F_smooth.continuous.measurable]
  unfold sieveKernelIntegral bandKernelEnergy182
  apply integral_congr_ae
  exact ae_of_all _ fun Y => by
    dsimp only [sieveFaceProfile, bandCombinedFace182, exceptionalFace, bandErasure]
    ring

theorem sieve_exceptional_moment_upper (P : TrialSmoothProfiles182) {H : Finset ℕ}
    (hH : H.card = 39) (i : Fin 39) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ res : ℕ,
      bandSharpMoment182 H P.a (H.orderEmbOfFin hH) i (P.exceptionalFace i) P.F x res ≤
        sieveMomentScale182 H x * (P.sieveKernelIntegral i + ε) := by
  rw [P.sieveKernelIntegral_eq_physical i]
  exact P.sharp_exceptional_moment_upper hH i ε hε

theorem sum_primeIndicator_orderEmb (H : Finset ℕ) (hH : H.card = 39) (n : ℕ) :
    (∑ i : Fin 39, primeIndicator (n + H.orderEmbOfFin hH i)) =
      ((H.filter (fun h => (n + h).Prime)).card : ℝ) := by
  classical
  calc
    _ = ∑ h ∈ Finset.univ.map (H.orderEmbOfFin hH).toEmbedding, primeIndicator (n + h) :=
      (Finset.sum_map _ _ _).symm
    _ = _ := by rw [H.map_orderEmbOfFin_univ hH]; simp only [primeIndicator, Finset.sum_boole]

theorem sieve_first_moment_lower (P : TrialSmoothProfiles182) {H : Finset ℕ} (hH : H.card = 39)
    (x : ℝ) (hx : 1 < x) (res : ℕ) :
    (∑ i : Fin 39, ∑ k : Fin 6, sievePairCoefficient k *
      P.sievePairMoment H (H.orderEmbOfFin hH) i k x res) -
        trialHybridLoss * (∑ i : Fin 39,
          bandSharpMoment182 H P.a (H.orderEmbOfFin hH) i (P.exceptionalFace i) P.F x res) -
          bandOrdinaryMoment182 H P.a (H.orderEmbOfFin hH) P.F x res ≤
            bandPrimeMoment182 H P.a (H.orderEmbOfFin hH) P.F x res := by
  classical
  let h := H.orderEmbOfFin hH
  let I := (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => Nat.ModEq (presievingModulus H x) n res)
  have hη : 0 < trialHybridLoss := by norm_num [trialHybridLoss, trialKappa, trialLambda]
  have hpoint (n : ℕ) (hn : n ∈ I) :
      (∑ i : Fin 39, ∑ k : Fin 6, sievePairCoefficient k * P.sievePairValue H h i k x n) -
        trialHybridLoss * (∑ i : Fin 39, P.sieveExceptionalValue H h i x n) -
        P.bandRoot H h x n ^ 2 ≤
          (((H.filter (fun h => (n + h).Prime)).card : ℝ) - 1) * P.bandRoot H h x n ^ 2 := by
    have hxn (i : Fin 39) : x ≤ ((n + h i : ℕ) : ℝ) :=
      (Nat.le_of_ceil_le (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1).trans
        (by exact_mod_cast Nat.le_add_right n (h i))
    have hterm (i : Fin 39) :
        (∑ k : Fin 6, sievePairCoefficient k * P.sievePairValue H h i k x n) -
          trialHybridLoss * P.sieveExceptionalValue H h i x n =
        tailCompletion (primeIndicator (n + h i)) (sharpDefect x (41361 / 100000) (n + h i))
          (P.bandRoot H h x n) (P.bandMask H h i 0 x n) (P.bandMask H h i 2 x n)
          ((1 - (trialLambda : ℝ)) * (P.bandMask H h i 1 x n - P.bandMask H h i 0 x n))
          trialHybridLoss := by
      rw [sum_sievePairCoefficient]
      exact (P.tailCompletion_eq_source_pairings H h i x hx n (hxn i) _ _).symm
    have hle := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      tailCompletion_le (primeIndicator (n + h i)) (sharpDefect x (41361 / 100000) (n + h i))
        (P.bandRoot H h x n) (P.bandMask H h i 0 x n) (P.bandMask H h i 2 x n)
        ((1 - (trialLambda : ℝ)) * (P.bandMask H h i 1 x n - P.bandMask H h i 0 x n))
        trialHybridLoss (primeIndicator_nonneg _) (sharpDefect_nonneg _ _ _) hη
    simp_rw [← hterm] at hle
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      sum_primeIndicator_orderEmb H hH n] at hle
    nlinarith only [hle]
  have hM (i : Fin 39) (k : Fin 6) : P.sievePairMoment H h i k x res =
      ∑ n ∈ I, P.sievePairValue H h i k x n := by
    rw [Finset.sum_filter]
    rfl
  have hE (i : Fin 39) : bandSharpMoment182 H P.a h i (P.exceptionalFace i) P.F x res =
      ∑ n ∈ I, P.sieveExceptionalValue H h i x n := by
    rw [Finset.sum_filter]
    rfl
  have hO : bandOrdinaryMoment182 H P.a h P.F x res = ∑ n ∈ I, P.bandRoot H h x n ^ 2 := by
    rw [Finset.sum_filter]
    rfl
  have hPS : (∑ i : Fin 39, ∑ k : Fin 6, sievePairCoefficient k * P.sievePairMoment H h i k x res) =
      ∑ n ∈ I, ∑ i : Fin 39, ∑ k : Fin 6, sievePairCoefficient k * P.sievePairValue H h i k x n := by
    simp_rw [hM, Finset.mul_sum]
    calc
      _ = ∑ i : Fin 39, ∑ n ∈ I, ∑ k : Fin 6, sievePairCoefficient k * P.sievePairValue H h i k x n :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hES : (∑ i : Fin 39, bandSharpMoment182 H P.a h i (P.exceptionalFace i) P.F x res) =
      ∑ n ∈ I, ∑ i : Fin 39, P.sieveExceptionalValue H h i x n := by
    simp_rw [hE]
    exact Finset.sum_comm
  have hp := Finset.sum_le_sum hpoint
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hp
  rw [← hPS, ← hES, ← hO] at hp
  simpa only [I, h, Finset.sum_filter, bandPrimeMoment182, bandRoot] using hp

#print axioms sieve_exceptional_moment_upper
#print axioms sieve_first_moment_lower

end PrimeGap182.TrialSmoothProfiles182
