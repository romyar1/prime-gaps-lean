import RadialArrayMoments182

/-!
The actual sharp-exceptional arithmetic square is bounded by the full
radial auxiliary square, then by the literal kernel applied to the block
energies.  All off-diagonal arithmetic terms have been retained and
estimated before the limit is assembled.
-/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic

def radialErasedValue182 (h : Fin 39 → ℕ) (i : Fin 39)
    (z : Fin 512 → ℝ → ((Fin 38 → ℕ) →₀ ℝ)) (x : ℝ) (n : ℕ) : ℝ :=
  ∑ b : Fin 512, sampledSelbergRoot (z b x) (fun k => n + h (i.succAbove k))

def radialSharpMoment182 (H : Finset ℕ) (h : Fin 39 → ℕ) (i : Fin 39)
    (z : Fin 512 → ℝ → ((Fin 38 → ℕ) →₀ ℝ)) (x : ℝ) (res : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
    if Nat.ModEq (presievingModulus H x) n res then
      sharpDefect x (41361 / 100000) (n + h i) * radialErasedValue182 h i z x n ^ 2 else 0

theorem radialSharpMoment182_le_weightedSquare (H : Finset ℕ) (h : Fin 39 → ℕ)
    (i : Fin 39) (z : Fin 512 → ℝ → ((Fin 38 → ℕ) →₀ ℝ)) :
    ∀ᶠ x : ℝ in atTop, ∀ res : ℕ,
      radialSharpMoment182 H h i z x res ≤ radialWeightedSquare182 H h i z x res := by
  classical
  have haux := sharp182_radial_majorant_actual_auxiliaries H Finset.univ
    radialAuxiliaryRadius182 (fun j b =>
      ⟨radialAuxiliaryRadius182_pos j b, radialAuxiliaryRadius182_lt_roughness j b⟩)
  filter_upwards [haux] with x hx
  intro res
  let N := Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊
  let P : Fin 1024 → Finset (ℕ × ℕ) := fun j =>
    markedPrimePairBin x (8639 / 50000) (41361 / 100000)
      (pairBinLeft (8639 / 50000) (41361 / 100000) j)
      (pairBinRight (8639 / 50000) (41361 / 100000) j)
  let w : Fin 1024 → ℝ := fun j =>
    pairHinge (19 / 50) (pairBinRight (8639 / 50000) (41361 / 100000) j)
  let F : Fin 1024 → (ℕ × ℕ) → ℕ → ℝ := fun j pq n =>
    if Nat.ModEq (presievingModulus H x) n res ∧ pq.1 * pq.2 ∣ n + h i then
      (∑ b : Fin 512, radialAuxiliaryProduct182 H h i j b z x n) ^ 2 else 0
  have hpoint (n : ℕ) (hn : n ∈ N) :
      (if Nat.ModEq (presievingModulus H x) n res then
        sharpDefect x (41361 / 100000) (n + h i) * radialErasedValue182 h i z x n ^ 2 else 0) ≤
      ∑ j : Fin 1024, w j * ∑ pq ∈ P j, F j pq n := by
    have hxn : x ≤ ((n + h i : ℕ) : ℝ) := by
      exact (Nat.le_ceil x).trans ((Nat.cast_le.mpr (Finset.mem_Icc.mp hn).1).trans
        (Nat.cast_le.mpr (Nat.le_add_right n (h i))))
    have hm := hx (n + h i) hxn
      (fun b => sampledSelbergRoot (z b x) (fun k => n + h (i.succAbove k)))
    by_cases hmod : Nat.ModEq (presievingModulus H x) n res
    · simpa only [F, w, P, hmod, true_and, ite_true,
        radialErasedValue182, radialAuxiliaryProduct182, auxiliaryProductValue] using hm
    · simp only [F, hmod, false_and, ite_false, Finset.sum_const_zero, mul_zero, le_refl]
  have hsum := Finset.sum_le_sum hpoint
  change radialSharpMoment182 H h i z x res ≤ _ at hsum
  have heq : (∑ n ∈ N, ∑ j : Fin 1024, w j * ∑ pq ∈ P j, F j pq n) =
      radialWeightedSquare182 H h i z x res := by
    rw [Finset.sum_comm]
    change (∑ j : Fin 1024, ∑ n ∈ N, w j * ∑ pq ∈ P j, F j pq n) =
      ∑ j : Fin 1024, w j * ∑ pq ∈ P j, ∑ n ∈ N, F j pq n
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum, Finset.sum_comm (s := N) (t := P j)]
  exact hsum.trans_eq heq

theorem radial_sharp_exceptional_moment_upper182 {H : Finset ℕ} (hH : H.card = 39)
    (i : Fin 39) (z : Fin 512 → ℝ → ((Fin 38 → ℕ) →₀ ℝ)) (M E : Fin 512 → ℝ)
    (hM : ∀ b, 0 ≤ M b) (hE : ∀ b, 0 ≤ E b) (hdata : RadialArrayBounds182 H z M)
    (hdiag : ∀ b, Tendsto (fun x => selbergNormalizer182 H x ^ 38 *
      diagonalHarmonic (fun r : Fin 38 → ℕ => ∏ k, ((r k).totient : ℝ)) (z b x))
        atTop (nhds (E b)))
    (hoff : ∀ b c, b ≠ c → Tendsto (fun x => selbergNormalizer182 H x ^ 38 *
      mixedHarmonic (fun r : Fin 38 → ℕ => ∏ k, ((r k).totient : ℝ)) (z b x) (z c x))
        atTop (nhds 0)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ res : ℕ,
      radialSharpMoment182 H (H.orderEmbOfFin hH) i z x res ≤
        sieveMomentScale182 H x *
          ((∑ b : Fin 512, PrimeGap182.trialPairKernel (b.val * 768) * E b) + ε) := by
  filter_upwards [radialSharpMoment182_le_weightedSquare H (H.orderEmbOfFin hH) i z,
    radial_weighted_square_upper182 hH i z M E hM hE hdata hdiag hoff ε hε] with x hx hy
  exact fun res => (hx res).trans (hy res)

#print axioms radialSharpMoment182_le_weightedSquare
#print axioms radial_sharp_exceptional_moment_upper182

end PrimeGap182Analytic
