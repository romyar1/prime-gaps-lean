import WeightMeans182

/-! Exact linearity and prime-slice erasure of the actual sampled band
arrays. The 38-coordinate base and subtraction arrays are sampled from
the masked marginals themselves. -/

noncomputable section
open MeasureTheory Filter PrimeGap186
open scoped BigOperators Topology

namespace PrimeGap182Analytic

theorem canonicalBandArray182_zero {d m : ℕ} (H : Finset ℕ)
    (a : Fin (m + 2) → ℝ) (x : ℝ) :
    canonicalBandArray182 H a (fun _ : Fin d → Fin (m + 1) → ℝ => 0) x = 0 := by
  classical
  simp only [canonicalBandArray182, zero_div, Finsupp.single_zero, Finset.sum_const_zero]

theorem canonicalBandArray182_sub {d m : ℕ} (H : Finset ℕ)
    (a : Fin (m + 2) → ℝ) (F G : (Fin d → Fin (m + 1) → ℝ) → ℝ) (x : ℝ) :
    canonicalBandArray182 H a (fun X => F X - G X) x =
      canonicalBandArray182 H a F x - canonicalBandArray182 H a G x := by
  classical
  simp only [canonicalBandArray182, sub_div, Finsupp.single_sub, Finset.sum_sub_distrib]

theorem canonicalBandArray182_neg {d m : ℕ} (H : Finset ℕ)
    (a : Fin (m + 2) → ℝ) (F : (Fin d → Fin (m + 1) → ℝ) → ℝ) (x : ℝ) :
    canonicalBandArray182 H a (fun X => -F X) x = -canonicalBandArray182 H a F x := by
  simpa only [zero_sub, canonicalBandArray182_zero] using
    canonicalBandArray182_sub H a (fun _ => 0) F x

theorem selbergErasedArray39_zero (i : Fin 39) :
    selbergErasedArray39 i 0 = 0 := by simp [selbergErasedArray39]

theorem sampledSelbergRoot_zero {d : ℕ} (v : Fin d → ℕ) :
    sampledSelbergRoot 0 v = 0 := by
  classical
  simp only [sampledSelbergRoot, Finsupp.support_zero, Finset.biUnion_empty, Finset.sum_empty]

theorem sampledSelbergRoot_neg {d : ℕ} (z : (Fin d → ℕ) →₀ ℝ) (v : Fin d → ℕ) :
    sampledSelbergRoot (-z) v = -sampledSelbergRoot z v := by
  simpa only [zero_sub, sampledSelbergRoot_zero] using sampledSelbergRoot_sub 0 z v

set_option maxHeartbeats 2000000 in
theorem canonicalBandArray182_weighted_erasure {m : ℕ} (H : Finset ℕ)
    (a : Fin (m + 2) → ℝ) (F : (Fin 39 → Fin (m + 1) → ℝ) → ℝ)
    (i : Fin 39) (h : Fin 39 → ℕ) (w : Fin 3) (x : ℝ) (hx : 1 < x) (n : ℕ)
    (hxn : x ≤ ((n + h i : ℕ) : ℝ)) :
    selbergWeight182 w x (n + h i) *
        sampledSelbergRoot (canonicalBandArray182 H a F x) (fun j => n + h j) =
      selbergWeight182 w x (n + h i) *
        sampledSelbergRoot (selbergErasedArray39 i (canonicalBandArray182 H a F x))
          (fun j => n + h (i.succAbove j)) := by
  have hs := sampledDiagonal39_sharp182_erasure x hx (presievingModulus H x)
    (selbergNormalizer182 H x ^ 39)
    (fun r => F (fun j => fragmentBandMasses a (primeLogConfiguration (x ^ selbergRho182) (r j))))
    i h n hxn
  have hy : sampledDiagonal39 (presievingModulus H x) (x ^ (2624989 / 10000000 : ℝ))
      ((17277 / 100000) / (2624989 / 10000000 : ℝ)) (selbergNormalizer182 H x ^ 39)
      (fun r => F (fun j => fragmentBandMasses a (primeLogConfiguration (x ^ selbergRho182) (r j)))) =
        canonicalBandArray182 H a F x := by
    simp only [sampledDiagonal39, canonicalBandArray182, selbergPrimorial182,
      selbergFragmentCap182, selbergRho182, finPiFinset_eq_classical]
  dsimp only at hs
  rw [hy] at hs
  fin_cases w
  · change primeIndicator (n + h i) * _ = primeIndicator (n + h i) * _
    simpa only [selbergRoot39, selbergErasedRoot39, sampledSelbergRoot_fin,
      finPiFinset_eq_classical] using hs.1
  · change sharpMinorant x (41361 / 100000) (n + h i) * _ =
      sharpMinorant x (41361 / 100000) (n + h i) * _
    simpa only [selbergRoot39, selbergErasedRoot39, sampledSelbergRoot_fin,
      finPiFinset_eq_classical] using hs.2.2
  · change sharpDefect x (41361 / 100000) (n + h i) * _ =
      sharpDefect x (41361 / 100000) (n + h i) * _
    simpa only [selbergRoot39, selbergErasedRoot39, sampledSelbergRoot_fin,
      finPiFinset_eq_classical] using hs.2.1

#print axioms canonicalBandArray182_sub
#print axioms canonicalBandArray182_weighted_erasure

end PrimeGap182Analytic
