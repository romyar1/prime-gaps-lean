import RadialAuxiliaryRadii182
import UniformSieveMoments182

/-!
Actual marked-bin moments for the sharp radial auxiliaries.  The remaining
array hypotheses concern the explicitly sampled erased arrays: support,
amplitude, and harmonic limits.  No prime-distribution hypothesis occurs
in this exceptional-square estimate.
-/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory PrimeGap186

namespace PrimeGap182Analytic

def selbergRho182 : ℝ := 2624989 / 10000000

def selbergFragmentCap182 : ℝ := (17277 / 100000) / selbergRho182

def selbergNormalizer182 (H : Finset ℕ) (x : ℝ) : ℝ :=
  fragmentNormalization (presievingModulus H x) (x ^ selbergRho182)

def selbergPrimorial182 (H : Finset ℕ) (x : ℝ) : ℕ :=
  ∏ p ∈ fragmentPrimes (presievingModulus H x) (x ^ selbergRho182) selbergFragmentCap182, p

def sieveMomentScale182 (H : Finset ℕ) (x : ℝ) : ℝ :=
  x / (presievingModulus H x : ℝ) /
    fragmentNormalization (presievingModulus H x) x / selbergNormalizer182 H x ^ 38

theorem sieveMomentScale182_pos (H : Finset ℕ) (x : ℝ) (hx : 1 < x) :
    0 < sieveMomentScale182 H x := by
  have hρ : 0 < selbergRho182 := by norm_num [selbergRho182]
  have hR : 1 < x ^ selbergRho182 := Real.one_lt_rpow hx hρ
  exact div_pos (div_pos (div_pos (zero_lt_one.trans hx)
    (Nat.cast_pos.mpr (presieving_pos H x))) (fragmentNormalization_pos H x x hx))
    (pow_pos (fragmentNormalization_pos H x _ hR) 38)

theorem sieveMomentScale182_eventually_nonneg (H : Finset ℕ) :
    ∀ᶠ x : ℝ in atTop, 0 ≤ sieveMomentScale182 H x := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact (sieveMomentScale182_pos H x hx).le

def RadialArrayBounds182 (H : Finset ℕ)
    (z : Fin 512 → ℝ → ((Fin 38 → ℕ) →₀ ℝ)) (M : Fin 512 → ℝ) : Prop :=
  ∀ᶠ x : ℝ in atTop, ∀ b : Fin 512,
    (∀ r ∈ (z b x).support, Squarefree (∏ k, r k) ∧
      (∀ k, r k ∈ (selbergPrimorial182 H x).divisors) ∧
        ((∏ k, r k : ℕ) : ℝ) ≤ x ^ radialSieveRadius182 b) ∧
    (∀ r, |z b x r| ≤ M b / selbergNormalizer182 H x ^ 38)

def radialAuxiliaryProduct182 (H : Finset ℕ) (h : Fin 39 → ℕ) (i : Fin 39)
    (j : Fin 1024) (b : Fin 512) (z : Fin 512 → ℝ → ((Fin 38 → ℕ) →₀ ℝ))
    (x : ℝ) (n : ℕ) : ℝ :=
  auxiliaryProductValue h i (sharpAuxiliaryArray H (radialAuxiliaryRadius182 j b) x) (z b x) n

def radialMarkedCross182 (H : Finset ℕ) (h : Fin 39 → ℕ) (i : Fin 39)
    (j : Fin 1024) (b c : Fin 512) (z : Fin 512 → ℝ → ((Fin 38 → ℕ) →₀ ℝ))
    (x : ℝ) (res : ℕ) : ℝ := by
  classical
  exact ∑ pq ∈ markedPrimePairBin x (8639 / 50000) (41361 / 100000)
      (pairBinLeft (8639 / 50000) (41361 / 100000) j)
      (pairBinRight (8639 / 50000) (41361 / 100000) j),
    ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
      if Nat.ModEq (presievingModulus H x) n res ∧ pq.1 * pq.2 ∣ n + h i then
        radialAuxiliaryProduct182 H h i j b z x n * radialAuxiliaryProduct182 H h i j c z x n
      else 0

theorem sharpAuxiliaryArray_common_bounds182 (H : Finset ℕ) (j : Fin 1024) (b : Fin 512) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ᶠ x : ℝ in atTop,
      (∀ t ∈ (sharpAuxiliaryArray H (radialAuxiliaryRadius182 j b) x).support,
        t 0 ∈ (selbergPrimorial182 H x).divisors ∧
          (t 0 : ℝ) ≤ x ^ radialAuxiliaryRadius182 j b) ∧
      (∀ t, |sharpAuxiliaryArray H (radialAuxiliaryRadius182 j b) x t| ≤
        N / fragmentNormalization (presievingModulus H x) x) := by
  obtain ⟨N, hN, haux⟩ := sharpAuxiliaryArray_bounds H _ (radialAuxiliaryRadius182_pos j b)
  refine ⟨N, hN, ?_⟩
  have hρ : 0 < selbergRho182 := by norm_num [selbergRho182]
  have hle : radialAuxiliaryRadius182 j b / selbergRho182 ≤ selbergFragmentCap182 :=
    div_le_div_of_nonneg_right (radialAuxiliaryRadius182_lt_coefficient_cap j b).le hρ.le
  filter_upwards [haux] with x hx
  obtain ⟨hx, _, hbound, hsupp⟩ := hx
  have hc := (fragment_divisors_common_cap (presievingModulus H x) x selbergRho182
    selbergFragmentCap182 (radialAuxiliaryRadius182 j b) hx hρ).2
  rw [max_eq_left hle] at hc
  exact ⟨fun t ht => ⟨hc (hsupp t ht).1, (hsupp t ht).2⟩, hbound⟩

theorem radial_marked_diagonal_limit182 {H : Finset ℕ} (hH : H.card = 39)
    (i : Fin 39) (j : Fin 1024) (b : Fin 512)
    (z : Fin 512 → ℝ → ((Fin 38 → ℕ) →₀ ℝ)) (M : Fin 512 → ℝ)
    (hM : ∀ c, 0 ≤ M c) (hdata : RadialArrayBounds182 H z M) (E : ℝ)
    (hZ : Tendsto (fun x => selbergNormalizer182 H x ^ 38 *
      diagonalHarmonic (fun r : Fin 38 → ℕ => ∏ k, ((r k).totient : ℝ)) (z b x))
        atTop (nhds E)) :
    UniformScaledLimit atTop (radialMarkedCross182 H (H.orderEmbOfFin hH) i j b b z)
      (sieveMomentScale182 H) (pairBinMass182 j * (E / radialAuxiliaryRadius182 j b)) := by
  classical
  let U : ℝ → ((Fin 1 → ℕ) →₀ ℝ) := sharpAuxiliaryArray H (radialAuxiliaryRadius182 j b)
  let Bx : ℝ → ℝ := fun x => fragmentNormalization (presievingModulus H x) x
  let B : ℝ → ℝ := selbergNormalizer182 H
  let A : ℝ → ℝ := fun x => x / (presievingModulus H x : ℝ)
  let denU : (Fin 1 → ℕ) → ℝ := fun t => ((t 0).totient : ℝ)
  let denZ : (Fin 38 → ℕ) → ℝ := fun r => ∏ k, ((r k).totient : ℝ)
  let P : ℝ → ℝ := fun x => ∑ pq ∈ markedPrimePairBin x (8639 / 50000) (41361 / 100000)
    (pairBinLeft (8639 / 50000) (41361 / 100000) j)
    (pairBinRight (8639 / 50000) (41361 / 100000) j), 1 / ((pq.1 * pq.2 : ℕ) : ℝ)
  let Efun : ℝ → ℝ := fun x => P x *
    (diagonalHarmonic denU (U x) * diagonalHarmonic denZ (z b x))
  have hp := pairBin182_margins j
  have hP : Tendsto P atTop (nhds (pairBinMass182 j)) := by
    simpa only [P, pairBinMass182, one_div] using
      markedPrimePairBin_harmonic_tendsto_general (8639 / 50000) (41361 / 100000)
        _ _ (by norm_num) hp.1 hp.2.1 hp.2.2
  have hU : Tendsto (fun x => Bx x * diagonalHarmonic denU (U x)) atTop
      (nhds (1 / radialAuxiliaryRadius182 j b)) :=
    sharpAuxiliaryArray_energy_tendsto H _ (radialAuxiliaryRadius182_pos j b)
  have hlim : Tendsto (fun x => (Bx x * B x ^ 38) * Efun x) atTop
      (nhds (pairBinMass182 j * (E / radialAuxiliaryRadius182 j b))) := by
    convert hP.mul (hU.mul hZ) using 1
    · funext x
      dsimp only [Efun, B]
      ring
    · congr 1
      ring
  have hpos : ∀ᶠ x : ℝ in atTop, 0 ≤ A x ∧ 0 < Bx x * B x ^ 38 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hR : 1 < x ^ selbergRho182 := Real.one_lt_rpow hx (by norm_num [selbergRho182])
    exact ⟨div_nonneg (zero_lt_one.trans hx).le (Nat.cast_nonneg _),
      mul_pos (fragmentNormalization_pos H x x hx)
        (pow_pos (fragmentNormalization_pos H x _ hR) 38)⟩
  obtain ⟨N, hN, haux⟩ := sharpAuxiliaryArray_common_bounds182 H j b
  have herr : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, ∀ res : ℕ,
      |radialMarkedCross182 H (H.orderEmbOfFin hH) i j b b z x res - A x * Efun x| ≤
        ε * (A x / (Bx x * B x ^ 38)) := by
    intro ε hε
    have hc := mixed_auxiliary_marked_bin_uniform (𝓗 := H) (h𝓗_card := hH)
      i selbergFragmentCap182 (radialSieveRadius182 b) (radialAuxiliaryRadius182 j b)
      (radialSieveRadius182 b) (radialAuxiliaryRadius182 j b) (M b) N (M b) N
      (8639 / 50000) (41361 / 100000)
      (pairBinLeft (8639 / 50000) (41361 / 100000) j)
      (pairBinRight (8639 / 50000) (41361 / 100000) j)
      (by norm_num [selbergFragmentCap182, selbergRho182])
      (radialSieveRadius182_nonneg b) (radialSieveRadius182_nonneg b)
      (radialAuxiliaryRadius182_pos j b) (radialAuxiliaryRadius182_pos j b)
      (hM b) hN (hM b) hN (by norm_num) (by norm_num)
      ((by norm_num : (0 : ℝ) ≤ 2 * (8639 / 50000)).trans (hp.1.trans hp.2.1.le))
      (by norm_num [selbergFragmentCap182, selbergRho182])
      (radialAuxiliaryRadius182_crt_margin j b) (radialAuxiliaryRadius182_crt_margin j b) ε hε
    filter_upwards [hc, haux, hdata] with x hcx hux hzx
    intro res
    have he := hcx.2.2.2 (U x) (U x) (z b x) (z b x)
      hux.1 hux.1 (hzx b).1 (hzx b).1 hux.2 hux.2 (hzx b).2 (hzx b).2 res
    simpa only [radialMarkedCross182, radialAuxiliaryProduct182, U, A, B, Bx,
      Efun, P, denU, denZ, selbergNormalizer182, selbergRho182,
      mixedHarmonic_self, div_mul_eq_div_div, mul_left_comm] using he
  have hfinal := PrimeGap182.Selberg.uniform_scaled_error_of_normalized_tendsto
    (radialMarkedCross182 H (H.orderEmbOfFin hH) i j b b z) A
    (fun x => Bx x * B x ^ 38) Efun _ hpos hlim herr
  simpa only [UniformScaledLimit, sieveMomentScale182, A, Bx, B, div_mul_eq_div_div] using hfinal

theorem radial_marked_cross_limit182 {H : Finset ℕ} (hH : H.card = 39)
    (i : Fin 39) (j : Fin 1024) (b c : Fin 512)
    (z : Fin 512 → ℝ → ((Fin 38 → ℕ) →₀ ℝ)) (M : Fin 512 → ℝ)
    (hM : ∀ d, 0 ≤ M d) (hdata : RadialArrayBounds182 H z M)
    (hZ : Tendsto (fun x => selbergNormalizer182 H x ^ 38 *
      mixedHarmonic (fun r : Fin 38 → ℕ => ∏ k, ((r k).totient : ℝ)) (z b x) (z c x))
        atTop (nhds 0)) :
    UniformScaledLimit atTop (radialMarkedCross182 H (H.orderEmbOfFin hH) i j b c z)
      (sieveMomentScale182 H) 0 := by
  classical
  obtain ⟨Nb, hNb, hUb⟩ := sharpAuxiliaryArray_common_bounds182 H j b
  obtain ⟨Nc, hNc, hUc⟩ := sharpAuxiliaryArray_common_bounds182 H j c
  have hp := pairBin182_margins j
  have hc := mixed_marked_bin_vanishes_of_harmonic_orthogonality
    (𝓗 := H) (h𝓗_card := hH) i selbergFragmentCap182
    (radialSieveRadius182 b) (radialAuxiliaryRadius182 j b)
    (radialSieveRadius182 c) (radialAuxiliaryRadius182 j c) (M b) Nb (M c) Nc
    (8639 / 50000) (41361 / 100000)
    (pairBinLeft (8639 / 50000) (41361 / 100000) j)
    (pairBinRight (8639 / 50000) (41361 / 100000) j)
    (by norm_num [selbergFragmentCap182, selbergRho182])
    (radialSieveRadius182_nonneg b) (radialSieveRadius182_nonneg c)
    (radialAuxiliaryRadius182_pos j b) (radialAuxiliaryRadius182_pos j c)
    (hM b) hNb (hM c) hNc (by norm_num) (by norm_num)
    ((by norm_num : (0 : ℝ) ≤ 2 * (8639 / 50000)).trans (hp.1.trans hp.2.1.le))
    (by norm_num [selbergFragmentCap182, selbergRho182])
    (radialAuxiliaryRadius182_crt_margin j b) (radialAuxiliaryRadius182_crt_margin j c)
    (sharpAuxiliaryArray H (radialAuxiliaryRadius182 j b))
    (sharpAuxiliaryArray H (radialAuxiliaryRadius182 j c)) (z b) (z c)
    (1 / radialAuxiliaryRadius182 j b) (1 / radialAuxiliaryRadius182 j c)
  have hd : ∀ᶠ x : ℝ in atTop,
      (∀ t ∈ (sharpAuxiliaryArray H (radialAuxiliaryRadius182 j b) x).support,
        t 0 ∈ (selbergPrimorial182 H x).divisors ∧ (t 0 : ℝ) ≤ x ^ radialAuxiliaryRadius182 j b) ∧
      (∀ t ∈ (sharpAuxiliaryArray H (radialAuxiliaryRadius182 j c) x).support,
        t 0 ∈ (selbergPrimorial182 H x).divisors ∧ (t 0 : ℝ) ≤ x ^ radialAuxiliaryRadius182 j c) ∧
      (∀ r ∈ (z b x).support, Squarefree (∏ k, r k) ∧
        (∀ k, r k ∈ (selbergPrimorial182 H x).divisors) ∧
          ((∏ k, r k : ℕ) : ℝ) ≤ x ^ radialSieveRadius182 b) ∧
      (∀ r ∈ (z c x).support, Squarefree (∏ k, r k) ∧
        (∀ k, r k ∈ (selbergPrimorial182 H x).divisors) ∧
          ((∏ k, r k : ℕ) : ℝ) ≤ x ^ radialSieveRadius182 c) ∧
      (∀ t, |sharpAuxiliaryArray H (radialAuxiliaryRadius182 j b) x t| ≤
        Nb / fragmentNormalization (presievingModulus H x) x) ∧
      (∀ t, |sharpAuxiliaryArray H (radialAuxiliaryRadius182 j c) x t| ≤
        Nc / fragmentNormalization (presievingModulus H x) x) ∧
      (∀ r, |z b x r| ≤ M b / selbergNormalizer182 H x ^ 38) ∧
      (∀ r, |z c x r| ≤ M c / selbergNormalizer182 H x ^ 38) := by
    filter_upwards [hUb, hUc, hdata] with x hbx hcx hzx
    exact ⟨hbx.1, hcx.1, (hzx b).1, (hzx c).1, hbx.2, hcx.2, (hzx b).2, (hzx c).2⟩
  have hfinal := hc hd
    (sharpAuxiliaryArray_energy_tendsto H _ (radialAuxiliaryRadius182_pos j b))
    (sharpAuxiliaryArray_energy_tendsto H _ (radialAuxiliaryRadius182_pos j c)) hZ
  simpa only [UniformScaledLimit, radialMarkedCross182, radialAuxiliaryProduct182,
    sieveMomentScale182, selbergNormalizer182, selbergRho182, mul_zero, sub_zero] using hfinal

def radialMarkedSquare182 (H : Finset ℕ) (h : Fin 39 → ℕ) (i : Fin 39)
    (j : Fin 1024) (z : Fin 512 → ℝ → ((Fin 38 → ℕ) →₀ ℝ)) (x : ℝ) (res : ℕ) : ℝ := by
  classical
  exact ∑ pq ∈ markedPrimePairBin x (8639 / 50000) (41361 / 100000)
      (pairBinLeft (8639 / 50000) (41361 / 100000) j)
      (pairBinRight (8639 / 50000) (41361 / 100000) j),
    ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
      if Nat.ModEq (presievingModulus H x) n res ∧ pq.1 * pq.2 ∣ n + h i then
        (∑ b : Fin 512, radialAuxiliaryProduct182 H h i j b z x n) ^ 2 else 0

theorem radialMarkedSquare182_eq_sum_cross (H : Finset ℕ) (h : Fin 39 → ℕ) (i : Fin 39)
    (j : Fin 1024) (z : Fin 512 → ℝ → ((Fin 38 → ℕ) →₀ ℝ)) (x : ℝ) (res : ℕ) :
    radialMarkedSquare182 H h i j z x res =
      ∑ b : Fin 512, ∑ c : Fin 512, radialMarkedCross182 H h i j b c z x res := by
  classical
  let P := markedPrimePairBin x (8639 / 50000) (41361 / 100000)
    (pairBinLeft (8639 / 50000) (41361 / 100000) j)
    (pairBinRight (8639 / 50000) (41361 / 100000) j)
  let N := Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊
  let F : (ℕ × ℕ) → ℕ → Fin 512 → Fin 512 → ℝ := fun pq n b c =>
    if Nat.ModEq (presievingModulus H x) n res ∧ pq.1 * pq.2 ∣ n + h i then
      radialAuxiliaryProduct182 H h i j b z x n * radialAuxiliaryProduct182 H h i j c z x n else 0
  have hp (pq : ℕ × ℕ) (n : ℕ) :
      (if Nat.ModEq (presievingModulus H x) n res ∧ pq.1 * pq.2 ∣ n + h i then
        (∑ b : Fin 512, radialAuxiliaryProduct182 H h i j b z x n) ^ 2 else 0) =
        ∑ b : Fin 512, ∑ c : Fin 512, F pq n b c := by
    by_cases hc : Nat.ModEq (presievingModulus H x) n res ∧ pq.1 * pq.2 ∣ n + h i
    · simp only [F, ite_eq_left hc]
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    · simp only [F, ite_eq_right hc, Finset.sum_const_zero]
  change (∑ pq ∈ P, ∑ n ∈ N, _) = ∑ b : Fin 512, ∑ c : Fin 512,
    ∑ pq ∈ P, ∑ n ∈ N, F pq n b c
  simp_rw [hp]
  calc
    _ = ∑ pq ∈ P, ∑ b : Fin 512, ∑ c : Fin 512, ∑ n ∈ N, F pq n b c := by
      apply Finset.sum_congr rfl
      intro pq _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]

theorem radial_marked_square_limit182 {H : Finset ℕ} (hH : H.card = 39)
    (i : Fin 39) (j : Fin 1024)
    (z : Fin 512 → ℝ → ((Fin 38 → ℕ) →₀ ℝ)) (M E : Fin 512 → ℝ)
    (hM : ∀ b, 0 ≤ M b) (hdata : RadialArrayBounds182 H z M)
    (hdiag : ∀ b, Tendsto (fun x => selbergNormalizer182 H x ^ 38 *
      diagonalHarmonic (fun r : Fin 38 → ℕ => ∏ k, ((r k).totient : ℝ)) (z b x))
        atTop (nhds (E b)))
    (hoff : ∀ b c, b ≠ c → Tendsto (fun x => selbergNormalizer182 H x ^ 38 *
      mixedHarmonic (fun r : Fin 38 → ℕ => ∏ k, ((r k).totient : ℝ)) (z b x) (z c x))
        atTop (nhds 0)) :
    UniformScaledLimit atTop (radialMarkedSquare182 H (H.orderEmbOfFin hH) i j z)
      (sieveMomentScale182 H)
      (∑ b : Fin 512, pairBinMass182 j * (E b / radialAuxiliaryRadius182 j b)) := by
  classical
  let d : Fin 512 → Fin 512 → ℝ := fun b c =>
    if b = c then pairBinMass182 j * (E b / radialAuxiliaryRadius182 j b) else 0
  have hpair (b c : Fin 512) :
      UniformScaledLimit atTop (radialMarkedCross182 H (H.orderEmbOfFin hH) i j b c z)
        (sieveMomentScale182 H) (d b c) := by
    by_cases hbc : b = c
    · subst c
      simpa only [d, ite_true] using radial_marked_diagonal_limit182 hH i j b z M hM hdata (E b) (hdiag b)
    · simpa only [d, ite_eq_right hbc] using
        radial_marked_cross_limit182 hH i j b c z M hM hdata (hoff b c hbc)
  have hsum := uniformScaledLimit_finsetSum Finset.univ
    (fun b x res => ∑ c : Fin 512, radialMarkedCross182 H (H.orderEmbOfFin hH) i j b c z x res)
    (sieveMomentScale182 H) (fun b => ∑ c : Fin 512, d b c)
    (sieveMomentScale182_eventually_nonneg H) (fun b _ =>
      uniformScaledLimit_finsetSum Finset.univ
        (fun c => radialMarkedCross182 H (H.orderEmbOfFin hH) i j b c z)
        (sieveMomentScale182 H) (d b) (sieveMomentScale182_eventually_nonneg H)
        (fun c _ => hpair b c))
  have hd : (∑ b : Fin 512, ∑ c : Fin 512, d b c) =
      ∑ b : Fin 512, pairBinMass182 j * (E b / radialAuxiliaryRadius182 j b) := by
    apply Finset.sum_congr rfl
    intro b _
    simp [d]
  rw [hd] at hsum
  exact hsum.congr (Eventually.of_forall fun x res =>
    (radialMarkedSquare182_eq_sum_cross H (H.orderEmbOfFin hH) i j z x res).symm)

def radialWeightedSquare182 (H : Finset ℕ) (h : Fin 39 → ℕ) (i : Fin 39)
    (z : Fin 512 → ℝ → ((Fin 38 → ℕ) →₀ ℝ)) (x : ℝ) (res : ℕ) : ℝ :=
  ∑ j : Fin 1024,
    pairHinge (19 / 50) (pairBinRight (8639 / 50000) (41361 / 100000) j) *
      radialMarkedSquare182 H h i j z x res

theorem radial_weighted_square_upper182 {H : Finset ℕ} (hH : H.card = 39)
    (i : Fin 39) (z : Fin 512 → ℝ → ((Fin 38 → ℕ) →₀ ℝ)) (M E : Fin 512 → ℝ)
    (hM : ∀ b, 0 ≤ M b) (hE : ∀ b, 0 ≤ E b) (hdata : RadialArrayBounds182 H z M)
    (hdiag : ∀ b, Tendsto (fun x => selbergNormalizer182 H x ^ 38 *
      diagonalHarmonic (fun r : Fin 38 → ℕ => ∏ k, ((r k).totient : ℝ)) (z b x))
        atTop (nhds (E b)))
    (hoff : ∀ b c, b ≠ c → Tendsto (fun x => selbergNormalizer182 H x ^ 38 *
      mixedHarmonic (fun r : Fin 38 → ℕ => ∏ k, ((r k).totient : ℝ)) (z b x) (z c x))
        atTop (nhds 0)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ res : ℕ,
      radialWeightedSquare182 H (H.orderEmbOfFin hH) i z x res ≤
        sieveMomentScale182 H x *
          ((∑ b : Fin 512, PrimeGap182.trialPairKernel (b.val * 768) * E b) + ε) := by
  let w : Fin 1024 → ℝ := fun j =>
    pairHinge (19 / 50) (pairBinRight (8639 / 50000) (41361 / 100000) j)
  have hsum := uniformScaledLimit_weighted_sum Finset.univ w
    (fun j => radialMarkedSquare182 H (H.orderEmbOfFin hH) i j z) (sieveMomentScale182 H)
    (fun j => ∑ b : Fin 512, pairBinMass182 j * (E b / radialAuxiliaryRadius182 j b))
    (sieveMomentScale182_eventually_nonneg H)
    (fun j _ => radial_marked_square_limit182 hH i j z M E hM hdata hdiag hoff)
  have hmain : (∑ j : Fin 1024, w j *
      (∑ b : Fin 512, pairBinMass182 j * (E b / radialAuxiliaryRadius182 j b))) ≤
      ∑ b : Fin 512, PrimeGap182.trialPairKernel (b.val * 768) * E b := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro b _
    calc
      _ = (∑ j : Fin 1024, w j * pairBinMass182 j / radialAuxiliaryRadius182 j b) * E b := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (radial_pair_bin_energy_le_kernel b) (hE b)
  exact hsum.eventually_upper (sieveMomentScale182_eventually_nonneg H) hmain ε hε

#print axioms sharpAuxiliaryArray_common_bounds182
#print axioms radial_marked_diagonal_limit182
#print axioms radial_marked_cross_limit182
#print axioms radial_marked_square_limit182
#print axioms radial_weighted_square_upper182

end PrimeGap182Analytic
