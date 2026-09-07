import HarmanShortSW182
import HarmanAnalyticInterfaces182

/-! Distribution of each actual short Harman convolution, at the new
roughness and splitting thresholds. Type zero, smooth Type I, genuine
coprimality-filtered coefficient SW, bilinear Type II, cutoff errors, and
subpower losses are all accounted for. The final analytic premise is the
explicit uniform SourceBilinearEstimate, with no distribution axiom.
Adapted from Apache-2.0 PrimeGaps186 at the generator's source hash. -/

noncomputable section
open scoped BigOperators Topology ContDiff
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

open Classical in
theorem sifted_short_geometric_coefficient_bounds
    (x Θ M : ℝ) (hx : 1 < x) (hΘ : 1 < Θ) (hΘ₂ : Θ ≤ 2) (hM : 0 < M)
    (j : Fin 6) :
    let η : ℝ → ℝ := fun u =>
      if 0 < u then
        Real.smoothTransition (Real.log u / Real.log Θ + 1) -
          Real.smoothTransition (Real.log u / Real.log Θ)
      else 0
    let z := x ^ ((8639 : ℝ) / 50000)
    let M0 := x ^ (1 - (34941 : ℝ) / 100000)
    let S0 : ℕ → ℝ := fun n =>
      if (n : ℝ) ≤ M0 then
        ∑ ps ∈ siftedPrimeTuples x j, ∑ d ∈ n.divisorsAntidiagonal,
          if d.1 = ps.prod then smallPrimeMobius z d.2 else 0
      else 0
    let α : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc 1 (Nat.floor (Θ * M)),
      Finsupp.single n ((η ((n : ℝ) / M) * S0 n : ℝ) : ℂ)
    (∀ n : ℕ, α n = ((η ((n : ℝ) / M) * S0 n : ℝ) : ℂ)) ∧
      (∀ n ∈ α.support, M / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * M) ∧
      ∀ n : ℕ, ‖α n‖ ≤ (n.divisors.card : ℝ) ^ 3 := by
  intro η z M0 S0 α
  obtain ⟨B, _, hprofile⟩ := sifted_short_geometric_profiles
  obtain ⟨_, hsupp, hrange, _⟩ := hprofile Θ hΘ hΘ₂
  change Function.support (fun u => (η u : ℂ)) = Set.Ioo Θ⁻¹ Θ at hsupp
  have hΘ0 : 0 < Θ := zero_lt_one.trans hΘ
  have hhalf : (1 / 2 : ℝ) ≤ Θ⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hΘ0 hΘ₂
  have hηmem (n : ℕ) (hn : η ((n : ℝ) / M) ≠ 0) :
      n ∈ Finset.Icc 1 (Nat.floor (Θ * M)) ∧
        M / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * M := by
    have hn' : (η ((n : ℝ) / M) : ℂ) ≠ 0 := by exact_mod_cast hn
    have hh : Θ⁻¹ < (n : ℝ) / M ∧ (n : ℝ) / M < Θ := by
      change (n : ℝ) / M ∈ Set.Ioo Θ⁻¹ Θ
      rw [← hsupp]
      exact hn'
    have hn0 : 0 < (n : ℝ) :=
      (mul_pos (inv_pos.mpr hΘ0) hM).trans ((lt_div_iff₀ hM).mp hh.1)
    have hnupper : (n : ℝ) ≤ Θ * M := ((div_lt_iff₀ hM).mp hh.2).le
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.cast_pos.mp hn0, Nat.le_floor hnupper⟩, ?_, ?_⟩
    · have hh' := (le_div_iff₀ hM).mp (hhalf.trans hh.1.le)
      linarith
    · exact hnupper.trans (mul_le_mul_of_nonneg_right hΘ₂ hM.le)
  have happly (n : ℕ) : α n = ((η ((n : ℝ) / M) * S0 n : ℝ) : ℂ) := by
    simp only [α, Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
    by_cases hn : n ∈ Finset.Icc 1 (Nat.floor (Θ * M))
    · simp [hn]
    · have hz : η ((n : ℝ) / M) = 0 := by
        by_contra he
        exact hn (hηmem n he).1
      simp [hn, hz]
  refine ⟨happly, ?_, ?_⟩
  · intro n hn
    have he : η ((n : ℝ) / M) ≠ 0 := by
      intro hz
      have hn' := Finsupp.mem_support_iff.mp hn
      rw [happly, hz, zero_mul, Complex.ofReal_zero] at hn'
      exact hn' rfl
    exact (hηmem n he).2
  · intro n
    rw [happly, Complex.ofReal_mul, norm_mul]
    have hηnorm : ‖(η ((n : ℝ) / M) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hrange _).1]
      exact (hrange _).2
    have hS := (sifted_short_source_bounds x hx j n).1
    change ‖(S0 n : ℂ)‖ ≤ (n.divisors.card : ℝ) ^ 3 at hS
    exact (mul_le_mul_of_nonneg_right hηnorm (norm_nonneg _)).trans
      (by simpa only [one_mul] using hS)

open Classical in
theorem sifted_short_geometric_free_eq
    (Θ N : ℝ) (hΘ : 1 < Θ) (hΘ₂ : Θ ≤ 2) (hN : 0 < N) :
    let η : ℝ → ℝ := fun u =>
      if 0 < u then
        Real.smoothTransition (Real.log u / Real.log Θ + 1) -
          Real.smoothTransition (Real.log u / Real.log Θ)
      else 0
    positiveCompactProfileSequence (fun u => (η u : ℂ)) 2 N 0 =
      ∑ n ∈ Finset.Icc 1 (Nat.floor (Θ * N)), Finsupp.single n
        ((η ((n : ℝ) / N) * (ArithmeticFunction.zeta n : ℝ) : ℝ) : ℂ) := by
  intro η
  obtain ⟨B, _, hprofile⟩ := sifted_short_geometric_profiles
  obtain ⟨_, hsupp, _, _⟩ := hprofile Θ hΘ hΘ₂
  change Function.support (fun u => (η u : ℂ)) = Set.Ioo Θ⁻¹ Θ at hsupp
  have hΘ0 : 0 < Θ := zero_lt_one.trans hΘ
  have hhalf : (1 / 2 : ℝ) ≤ Θ⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hΘ0 hΘ₂
  have hs : Function.support (fun u => (η u : ℂ)) ⊆ Set.Icc (1 / 2 : ℝ) 2 := by
    rw [hsupp]
    exact Set.Ioo_subset_Icc_self.trans (Set.Icc_subset_Icc hhalf hΘ₂)
  ext n
  rw [positiveCompactProfileSequence_apply (1 / 2) 2 N (by norm_num) hN _ hs]
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
  by_cases hn : n ∈ Finset.Icc 1 (Nat.floor (Θ * N))
  · have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    simp [hn, ArithmeticFunction.zeta_apply_ne hn0]
  · have he : (η ((n : ℝ) / N) : ℂ) = 0 := by
      by_contra hne
      have hh : Θ⁻¹ < (n : ℝ) / N ∧ (n : ℝ) / N < Θ := by
        change (n : ℝ) / N ∈ Set.Ioo Θ⁻¹ Θ
        rw [← hsupp]
        exact hne
      have hnpos : 0 < (n : ℝ) :=
        (mul_pos (inv_pos.mpr hΘ0) hN).trans ((lt_div_iff₀ hN).mp hh.1)
      exact hn (Finset.mem_Icc.mpr ⟨Nat.cast_pos.mp hnpos,
        Nat.le_floor ((div_lt_iff₀ hN).mp hh.2).le⟩)
    simp [hn, he]

open Classical in
theorem sifted_short_geometric_all_moduli_siegelWalfisz
    (ε C A D : ℝ) (hε : 0 < ε) (hC : 0 < C) (hA : 0 < A) (hD : 1 ≤ D) :
    ∃ K X0 : ℝ, 0 < K ∧ Real.exp 1 ≤ X0 ∧
      ∀ x : ℝ, X0 ≤ x → ∀ M : ℝ, x ^ ε ≤ M → M ≤ x ^ C →
      ∀ j : Fin 6, ∀ u v : ℝ,
      ∀ q : ℕ, 0 < q → ∀ r0 : ℕ, 0 < r0 → ∀ a : ℕ, Nat.Coprime a q →
      let Θ := 1 + (Real.log x) ^ (-D)
      let η : ℝ → ℝ := fun u =>
        if 0 < u then
          Real.smoothTransition (Real.log u / Real.log Θ + 1) -
            Real.smoothTransition (Real.log u / Real.log Θ)
        else 0
      let z := x ^ ((8639 : ℝ) / 50000)
      let M0 := x ^ (1 - (34941 : ℝ) / 100000)
      let S0 : ℕ → ℝ := fun n =>
        if (n : ℝ) ≤ M0 then
          ∑ ps ∈ siftedPrimeTuples x j, ∑ d ∈ n.divisorsAntidiagonal,
            if d.1 = ps.prod then smallPrimeMobius z d.2 else 0
        else 0
      let α : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc 1 (Nat.floor (Θ * M)),
        Finsupp.single n ((η ((n : ℝ) / M) * S0 n : ℝ) : ℂ)
      ‖fullDiscrepancy
        (α.filter (fun n : ℕ => u ≤ (n : ℝ) ∧ (n : ℝ) ≤ v ∧ Nat.Coprime n r0)) q a‖ ≤
        K * ((q * r0).divisors.card : ℝ) * M / (Real.log x) ^ A := by
  obtain ⟨B, hB, hprofile⟩ := sifted_short_geometric_profile_bounds D hD
  have hB1 : 0 < B 1 := hB 1
  obtain ⟨K, X1, hK, hX1, hsw⟩ :=
    sifted_short_weighted_all_moduli_siegelWalfisz
      ε 2 (1 / 2) C A (D + 1) hε (by norm_num) (by norm_num) hC hA (by linarith)
  refine ⟨K, max X1 (Real.exp (1 + 2 * B 1)), hK, hX1.trans (le_max_left _ _), ?_⟩
  intro x hx M hML hMU j u v q hq r0 hr0 a ha Θ η z M0 S0 α
  have hx1 := (le_max_left _ _).trans hx
  have hxexp := (le_max_right _ _).trans hx
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le (hX1.trans hx1)
  have hlog1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr (hX1.trans hx1)
  have hlog : 0 < Real.log x := zero_lt_one.trans_le hlog1
  have hlogB : 1 + 2 * B 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hx0).mpr hxexp
  have hxgt : 1 < x := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le
    (hX1.trans hx1)
  have hM : 0 < M := (Real.rpow_pos_of_pos hx0 ε).trans_le hML
  obtain ⟨hΘ, hΘ₂, hηsmooth, hηsupport, hηrange, hηderiv⟩ :=
    hprofile x (hX1.trans hx1)
  change 1 < Θ at hΘ
  change Θ ≤ 2 at hΘ₂
  change ContDiff ℝ ∞ (fun u => (η u : ℂ)) at hηsmooth
  change Function.support (fun u => (η u : ℂ)) = Set.Ioo Θ⁻¹ Θ at hηsupport
  change ∀ u : ℝ, 0 ≤ η u ∧ η u ≤ 1 at hηrange
  change ∀ (r : ℕ) (u : ℝ), ‖iteratedDeriv r (fun u => (η u : ℂ)) u‖ ≤
    B r * (Real.log x) ^ (D * (r : ℝ)) at hηderiv
  have hbound (t : ℝ) : ‖deriv (fun u => (η u : ℂ)) t‖ ≤
      B 1 * (Real.log x) ^ D := by
    simpa only [iteratedDeriv_one, Nat.cast_one, mul_one] using hηderiv 1 t
  let w : ℕ → ℂ := fun n => (η ((n : ℝ) / M) : ℂ)
  let NN := Nat.floor (2 * M)
  have hterminal : ‖w NN‖ ≤ 1 := by
    change ‖(η ((NN : ℝ) / M) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hηrange _).1]
    exact (hηrange _).2
  have hstep (n : ℕ) : ‖w (n + 1) - w n‖ ≤ B 1 * (Real.log x) ^ D / M := by
    have hm := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t (_ : t ∈ (Set.univ : Set ℝ)) => hηsmooth.differentiable (by simp) t)
      (fun t _ => hbound t) (convex_univ : Convex ℝ (Set.univ : Set ℝ))
      (Set.mem_univ ((n : ℝ) / M)) (Set.mem_univ (((n + 1 : ℕ) : ℝ) / M))
    have hdist : ‖(((n + 1 : ℕ) : ℝ) / M) - (n : ℝ) / M‖ = 1 / M := by
      rw [show (((n + 1 : ℕ) : ℝ) / M) - (n : ℝ) / M = 1 / M by push_cast; ring]
      exact Real.norm_of_nonneg (by positivity)
    calc
      _ ≤ B 1 * (Real.log x) ^ D *
          ‖(((n + 1 : ℕ) : ℝ) / M) - (n : ℝ) / M‖ := hm
      _ = B 1 * (Real.log x) ^ D / M := by rw [hdist]; ring
  have hvar : ‖w NN‖ + (∑ n ∈ Finset.Ico 1 NN, ‖w (n + 1) - w n‖) ≤
      (Real.log x) ^ (D + 1) := by
    have hcard : ((Finset.Ico 1 NN).card : ℝ) ≤ 2 * M := by
      calc
        _ ≤ (NN : ℝ) := by exact_mod_cast (show (Finset.Ico 1 NN).card ≤ NN by simp)
        _ ≤ 2 * M := Nat.floor_le (by positivity)
    have hs : (∑ n ∈ Finset.Ico 1 NN, ‖w (n + 1) - w n‖) ≤
        2 * B 1 * (Real.log x) ^ D := by
      calc
        _ ≤ ∑ _n ∈ Finset.Ico 1 NN, B 1 * (Real.log x) ^ D / M :=
          Finset.sum_le_sum (fun n _ => hstep n)
        _ = ((Finset.Ico 1 NN).card : ℝ) * (B 1 * (Real.log x) ^ D / M) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * M) * (B 1 * (Real.log x) ^ D / M) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 2 * B 1 * (Real.log x) ^ D := by field_simp [hM.ne']
    have hp : 1 ≤ (Real.log x) ^ D := Real.one_le_rpow hlog1 (by linarith)
    calc
      _ ≤ 1 + 2 * B 1 * (Real.log x) ^ D := add_le_add hterminal hs
      _ ≤ (1 + 2 * B 1) * (Real.log x) ^ D := by nlinarith only [hp]
      _ ≤ Real.log x * (Real.log x) ^ D :=
        mul_le_mul_of_nonneg_right hlogB (Real.rpow_nonneg hlog.le D)
      _ = (Real.log x) ^ (D + 1) := by rw [Real.rpow_add hlog, Real.rpow_one]; ring
  have hα := sifted_short_geometric_coefficient_bounds x Θ M hxgt hΘ hΘ₂ hM j
  change (∀ n : ℕ, α n = ((η ((n : ℝ) / M) * S0 n : ℝ) : ℂ)) ∧
    (∀ n ∈ α.support, M / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * M) ∧
    ∀ n : ℕ, ‖α n‖ ≤ (n.divisors.card : ℝ) ^ 3 at hα
  have heq :
      α.filter (fun n : ℕ => u ≤ (n : ℝ) ∧ (n : ℝ) ≤ v ∧ Nat.Coprime n r0) =
        ∑ n ∈ Finset.Icc 1 NN, Finsupp.single n
          (if max (M / 2) u ≤ (n : ℝ) ∧ (n : ℝ) ≤ v ∧ Nat.Coprime n r0
           then w n * (S0 n : ℂ) else 0) := by
    ext n
    rw [Finsupp.filter_apply]
    simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
    have hw : w n * (S0 n : ℂ) = α n := by
      rw [hα.1 n, Complex.ofReal_mul]
    rw [hw]
    by_cases hn : α n = 0
    · simp [hn]
    · have hs := hα.2.1 n (Finsupp.mem_support_iff.mpr hn)
      have hn0 : 0 < n := by
        have hh : 0 < (n : ℝ) := (half_pos hM).trans_le hs.1
        exact_mod_cast hh
      have hm : n ∈ Finset.Icc 1 NN :=
        Finset.mem_Icc.mpr ⟨hn0, Nat.le_floor hs.2⟩
      simp only [hm, ite_true, max_le_iff, hs.1, true_and]
  rw [heq]
  simpa only [S0, z, M0, NN] using
    hsw x hx1 M hML hMU j (max (M / 2) u) v
      (by simpa only [one_div, inv_mul_eq_div] using le_max_left (M / 2) u)
      w hvar q hq r0 hr0 a ha

open Classical in
theorem sifted_short_geometric_typeII_coherent_log_saving_of_bilinear
    (j : ℕ) («ω» δ σ C D : ℝ)
    (_hω : 0 < «ω») (_hδ : 0 < δ) (hσ : 0 < σ) (hC : 1 ≤ C) (hD : 1 ≤ D)
    (hσhalf : σ < 1 / 2)
    (hsource : SourceBilinearEstimate j «ω» δ σ) :
    ∀ A : ℝ, 0 < A →
      ∃ K X : ℝ, 0 < K ∧ Real.exp 1 ≤ X ∧
        ∀ x : ℝ, X ≤ x → ∀ l : Fin 6, ∀ M N : ℝ,
        x / C ≤ M * N → M * N ≤ C * x → 1 ≤ N →
        x ^ (1 / 2 - σ) ≤ M → M ≤ x ^ (1 / 2 : ℝ) →
        let Θ := 1 + (Real.log x) ^ (-D)
        let η : ℝ → ℝ := fun u =>
          if 0 < u then
            Real.smoothTransition (Real.log u / Real.log Θ + 1) -
              Real.smoothTransition (Real.log u / Real.log Θ)
          else 0
        let z := x ^ ((8639 : ℝ) / 50000)
        let M0 := x ^ (1 - (34941 : ℝ) / 100000)
        let S0 : ℕ → ℝ := fun n =>
          if (n : ℝ) ≤ M0 then
            ∑ ps ∈ siftedPrimeTuples x l, ∑ d ∈ n.divisorsAntidiagonal,
              if d.1 = ps.prod then smallPrimeMobius z d.2 else 0
          else 0
        let α : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc 1 (Nat.floor (Θ * M)),
          Finsupp.single n ((η ((n : ℝ) / M) * S0 n : ℝ) : ℂ)
        let β : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc 1 (Nat.floor (Θ * N)),
          Finsupp.single n
            ((η ((n : ℝ) / N) * (ArithmeticFunction.zeta n : ℝ) : ℝ) : ℂ)
        ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
        ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
          (∑ q ∈ (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
              q ∣ (∏ p ∈ I, p) ∧
                Nonempty (DenseDivisibilityWitness
                  ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩
                  j q)),
            ‖fullDiscrepancy (finiteConvolution α β) q a‖) ≤
              K * x / (Real.log x) ^ A := by
  have hε : 0 < (1 / 2 : ℝ) - σ := sub_pos.mpr hσhalf
  let ι := Fin 6 × ℝ × ℝ
  let good (x : ℝ) (b : ι) : Prop :=
    x / C ≤ b.2.1 * b.2.2 ∧ b.2.1 * b.2.2 ≤ C * x ∧ 1 ≤ b.2.2 ∧
      x ^ (1 / 2 - σ) ≤ b.2.1 ∧ b.2.1 ≤ x ^ (1 / 2 : ℝ)
  let Θ (x : ℝ) := 1 + (Real.log x) ^ (-D)
  let η (x : ℝ) : ℝ → ℝ := fun u =>
    if 0 < u then
      Real.smoothTransition (Real.log u / Real.log (Θ x) + 1) -
        Real.smoothTransition (Real.log u / Real.log (Θ x))
    else 0
  let S0 (x : ℝ) (l : Fin 6) : ℕ → ℝ := fun n =>
    if (n : ℝ) ≤ x ^ (1 - (34941 : ℝ) / 100000) then
      ∑ ps ∈ siftedPrimeTuples x l, ∑ d ∈ n.divisorsAntidiagonal,
        if d.1 = ps.prod then smallPrimeMobius (x ^ ((8639 : ℝ) / 50000)) d.2 else 0
    else 0
  let rawShort (x : ℝ) (b : ι) : ℕ →₀ ℂ :=
    ∑ n ∈ Finset.Icc 1 (Nat.floor (Θ x * b.2.1)), Finsupp.single n
      ((η x ((n : ℝ) / b.2.1) * S0 x b.1 n : ℝ) : ℂ)
  let rawFree (x : ℝ) (b : ι) : ℕ →₀ ℂ :=
    positiveCompactProfileSequence (fun u => (η x u : ℂ)) 2 b.2.2 0
  let C₀ : ℝ := max C 2
  let X₀ : ℝ := Real.exp 1
  let Mformal (x : ℝ) (b : ι) : ℝ :=
    if good x b then b.2.2 else x ^ (1 / 2 : ℝ)
  let Nformal (x : ℝ) (b : ι) : ℝ :=
    if good x b then b.2.1 else x ^ (1 / 2 : ℝ)
  let α (x : ℝ) (b : ι) : ℕ →₀ ℂ := if good x b then rawFree x b else 0
  let β (x : ℝ) (b : ι) : ℕ →₀ ℂ := if good x b then rawShort x b else 0
  have hC₀ : 1 ≤ C₀ := hC.trans (le_max_left _ _)
  have hCC₀ : C ≤ C₀ := le_max_left _ _
  have htwoC₀ : (2 : ℝ) ≤ C₀ := le_max_right _ _
  have hxOne (x : ℝ) (hx : X₀ ≤ x) : 1 ≤ x :=
    (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans hx
  have hxPos (x : ℝ) (hx : X₀ ≤ x) : 0 < x :=
    zero_lt_one.trans_le (hxOne x hx)
  have hxGt (x : ℝ) (hx : X₀ ≤ x) : 1 < x :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hx
  have hlog (x : ℝ) (hx : X₀ ≤ x) : 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le (hxPos x hx)).mpr hx
  obtain ⟨B, _, hprofiles⟩ := sifted_short_geometric_profile_bounds D hD
  have hp (x : ℝ) (hx : X₀ ≤ x) :
      1 < Θ x ∧ Θ x ≤ 2 ∧
        Function.support (fun u => (η x u : ℂ)) ⊆ Set.Icc (1 / 2 : ℝ) 2 ∧
        (∀ u : ℝ, 0 ≤ η x u ∧ η x u ≤ 1) := by
    obtain ⟨hΘ, hΘ₂, _, hs, hr, _⟩ := hprofiles x hx
    refine ⟨hΘ, hΘ₂, ?_, hr⟩
    change Function.support (fun u => (η x u : ℂ)) = Set.Ioo (Θ x)⁻¹ (Θ x) at hs
    rw [hs]
    apply Set.Ioo_subset_Icc_self.trans
    apply Set.Icc_subset_Icc _ hΘ₂
    simpa only [one_div] using
      one_div_le_one_div_of_le (zero_lt_one.trans hΘ) hΘ₂
  have hshort (x : ℝ) (hx : X₀ ≤ x) (b : ι) (hg : good x b) :
      (∀ n : ℕ, rawShort x b n = ((η x ((n : ℝ) / b.2.1) * S0 x b.1 n : ℝ) : ℂ)) ∧
        (∀ n ∈ (rawShort x b).support,
          b.2.1 / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * b.2.1) ∧
        ∀ n : ℕ, ‖rawShort x b n‖ ≤ (n.divisors.card : ℝ) ^ 3 := by
    have hM : 0 < b.2.1 := (Real.rpow_pos_of_pos (hxPos x hx) _).trans_le hg.2.2.2.1
    exact sifted_short_geometric_coefficient_bounds x (Θ x) b.2.1
      (hxGt x hx) (hp x hx).1 (hp x hx).2.1 hM b.1
  have hfree (x : ℝ) (hx : X₀ ≤ x) (b : ι) (hg : good x b) :
      (∀ n ∈ (rawFree x b).support,
        b.2.2 / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * b.2.2) ∧
        ∀ n : ℕ, ‖rawFree x b n‖ ≤ (n.divisors.card : ℝ) ^ 3 := by
    have hN : 0 < b.2.2 := zero_lt_one.trans_le hg.2.2.1
    have happly (n : ℕ) : rawFree x b n = (η x ((n : ℝ) / b.2.2) : ℂ) :=
      positiveCompactProfileSequence_apply (1 / 2) 2 b.2.2 (by norm_num) hN
        (fun u => (η x u : ℂ)) (hp x hx).2.2.1 n
    refine ⟨?_, ?_⟩
    · intro n hn
      have he : (η x ((n : ℝ) / b.2.2) : ℂ) ≠ 0 := by
        simpa only [happly] using Finsupp.mem_support_iff.mp hn
      have hs := (hp x hx).2.2.1 he
      have hl := (le_div_iff₀ hN).mp hs.1
      exact ⟨by linarith, (div_le_iff₀ hN).mp hs.2⟩
    · intro n
      rw [happly]
      by_cases hn : n = 0
      · subst n
        simp [η]
      · have htau : (1 : ℝ) ≤ (n.divisors.card : ℝ) := by
          exact_mod_cast Finset.one_le_card.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩
        have hrange := (hp x hx).2.2.2 ((n : ℝ) / b.2.2)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrange.1]
        exact hrange.2.trans (one_le_pow₀ htau)
  have hscale : ∀ x : ℝ, X₀ ≤ x → ∀ b : ι,
      x / C₀ ≤ Mformal x b * Nformal x b ∧
        Mformal x b * Nformal x b ≤ C₀ * x ∧
        x ^ (1 / 2 - σ) ≤ Nformal x b ∧ Nformal x b ≤ x ^ (1 / 2 : ℝ) := by
    intro x hx b
    by_cases hg : good x b
    · simp only [Mformal, Nformal, ite_eq_left hg]
      rw [mul_comm b.2.2 b.2.1]
      exact ⟨(div_le_div_of_nonneg_left (hxPos x hx).le
          (zero_lt_one.trans_le hC) hCC₀).trans hg.1,
        hg.2.1.trans (mul_le_mul_of_nonneg_right hCC₀ (hxPos x hx).le), hg.2.2.2⟩
    · simp only [Mformal, Nformal, ite_eq_right hg]
      have hsq : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
        rw [← Real.rpow_add (hxPos x hx)]
        norm_num
      rw [hsq]
      exact ⟨div_le_self (hxPos x hx).le hC₀,
        le_mul_of_one_le_left (hxPos x hx).le hC₀,
        Real.rpow_le_rpow_of_exponent_le (hxOne x hx) (by linarith), le_rfl⟩
  have hsupport : ∀ x : ℝ, X₀ ≤ x → ∀ b : ι,
      (∀ n ∈ (α x b).support,
        (1 / 2 : ℝ) * Mformal x b ≤ (n : ℝ) ∧ (n : ℝ) ≤ C₀ * Mformal x b) ∧
      (∀ n ∈ (β x b).support,
        (1 / 2 : ℝ) * Nformal x b ≤ (n : ℝ) ∧ (n : ℝ) ≤ C₀ * Nformal x b) := by
    intro x hx b
    by_cases hg : good x b
    · simp only [α, β, Mformal, Nformal, ite_eq_left hg]
      have hM : 0 < b.2.1 := (Real.rpow_pos_of_pos (hxPos x hx) _).trans_le hg.2.2.2.1
      have hN : 0 < b.2.2 := zero_lt_one.trans_le hg.2.2.1
      constructor
      · intro n hn
        obtain ⟨hl, hu⟩ := (hfree x hx b hg).1 n hn
        exact ⟨by linarith, hu.trans (mul_le_mul_of_nonneg_right htwoC₀ hN.le)⟩
      · intro n hn
        obtain ⟨hl, hu⟩ := (hshort x hx b hg).2.1 n hn
        exact ⟨by linarith, hu.trans (mul_le_mul_of_nonneg_right htwoC₀ hM.le)⟩
    · constructor
      · intro n hn
        simp only [α, ite_eq_right hg, Finsupp.support_zero, Finset.notMem_empty] at hn
      · intro n hn
        simp only [β, ite_eq_right hg, Finsupp.support_zero, Finset.notMem_empty] at hn
  have hcoeff : ∀ x : ℝ, X₀ ≤ x → ∀ b : ι, ∀ n : ℕ,
      ‖α x b n‖ ≤ 1 * (n.divisors.card : ℝ) ^ 3 * (Real.log x) ^ 3 ∧
      ‖β x b n‖ ≤ 1 * (n.divisors.card : ℝ) ^ 3 * (Real.log x) ^ 3 := by
    intro x hx b n
    have hlogpow : 1 ≤ (Real.log x) ^ (3 : ℕ) := one_le_pow₀ (hlog x hx)
    have hbound : (n.divisors.card : ℝ) ^ 3 ≤
        1 * (n.divisors.card : ℝ) ^ 3 * (Real.log x) ^ 3 := by
      simpa only [one_mul] using
        le_mul_of_one_le_right (pow_nonneg (Nat.cast_nonneg _) 3) hlogpow
    by_cases hg : good x b
    · simp only [α, β, ite_eq_left hg]
      exact ⟨((hfree x hx b hg).2 n).trans hbound,
        ((hshort x hx b hg).2.2 n).trans hbound⟩
    · simp only [α, β, ite_eq_right hg, Finsupp.zero_apply, norm_zero, one_mul, and_self]
      exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
        (pow_nonneg (zero_le_one.trans (hlog x hx)) _)
  have hSW : ∀ A : ℝ, 0 < A →
      ∃ KSW XSW : ℝ, 0 < KSW ∧ X₀ ≤ XSW ∧
        ∀ x : ℝ, XSW ≤ x → ∀ b : ι,
        ∀ q r a : ℕ, 0 < q → 0 < r → Nat.Coprime a q →
          ‖fullDiscrepancy ((β x b).filter (fun n : ℕ => Nat.Coprime n r)) q a‖ ≤
            KSW * ((q * r).divisors.card : ℝ) ^ 1 * Nformal x b /
              (Real.log x) ^ A := by
    intro A hA
    obtain ⟨KSW, XSW, hKSW, hXSW, hsw⟩ :=
      sifted_short_geometric_all_moduli_siegelWalfisz
        (1 / 2 - σ) 1 A D hε (by norm_num) hA hD
    refine ⟨KSW, XSW, hKSW, hXSW, ?_⟩
    intro x hx b q r a hq hr ha
    have hx₀ : X₀ ≤ x := hXSW.trans hx
    by_cases hg : good x b
    · have hMU : b.2.1 ≤ x ^ (1 : ℝ) := hg.2.2.2.2.trans
        (Real.rpow_le_rpow_of_exponent_le (hxOne x hx₀) (by norm_num))
      have hd := hsw x hx b.2.1 hg.2.2.2.1 hMU b.1 0 (2 * b.2.1) q hq r hr a ha
      change ‖fullDiscrepancy ((rawShort x b).filter
        (fun n : ℕ => 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * b.2.1 ∧ Nat.Coprime n r)) q a‖ ≤
          KSW * ((q * r).divisors.card : ℝ) * b.2.1 / (Real.log x) ^ A at hd
      have hf : (rawShort x b).filter
          (fun n : ℕ => 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * b.2.1 ∧ Nat.Coprime n r) =
          (rawShort x b).filter (fun n : ℕ => Nat.Coprime n r) := by
        ext n
        simp only [Finsupp.filter_apply]
        by_cases hn : rawShort x b n = 0
        · simp [hn]
        · have hu := ((hshort x hx₀ b hg).2.1 n (Finsupp.mem_support_iff.mpr hn)).2
          simp only [Nat.cast_nonneg, hu, true_and]
      rw [hf] at hd
      simpa only [β, Nformal, ite_eq_left hg, pow_one] using hd
    · simp only [β, Nformal, ite_eq_right hg, Finsupp.filter_zero, fullDiscrepancy,
        progressionMass, reducedMass, Finsupp.support_zero, Finset.sum_empty,
        zero_div, sub_self, norm_zero]
      exact div_nonneg
        (mul_nonneg (mul_nonneg hKSW.le (pow_nonneg (Nat.cast_nonneg _) _))
          (Real.rpow_nonneg (hxPos x hx₀).le _))
        (Real.rpow_nonneg (zero_le_one.trans (hlog x hx₀)) _)
  intro A hA
  obtain ⟨K, X, hK, hX, hdist⟩ :=
    hsource
      Mformal Nformal α β (1 / 2) C₀ 1 X₀ 3 1
      (by norm_num) hC₀ (by norm_num) le_rfl hscale hsupport hcoeff hSW A hA
  refine ⟨K, X, hK, hX, ?_⟩
  intro x hx l M N hpL hpU hN hML hMU Θ0 η0 z M0 S00 α0 β0 I hI a ha
  let b : ι := (l, M, N)
  have hg : good x b := ⟨hpL, hpU, hN, hML, hMU⟩
  have hx₀ : X₀ ≤ x := hX.trans hx
  have hα : α x b = β0 := by
    simp only [α, ite_eq_left hg]
    exact sifted_short_geometric_free_eq (Θ x) N (hp x hx₀).1 (hp x hx₀).2.1
      (zero_lt_one.trans_le hN)
  have hβ : β x b = α0 := by
    simp only [β, ite_eq_left hg]
    rfl
  have hcomm : finiteConvolution β0 α0 = finiteConvolution α0 β0 := by
    unfold finiteConvolution
    rw [mul_comm]
  simpa only [hα, hβ, hcomm] using hdist x hx b I hI a ha

open Classical in
theorem sifted_short_geometric_smooth_log_saving
    (D «ω» δ γ₀ C : ℝ) (hD : 1 ≤ D)
    (hω : 0 < «ω») (hδ : 0 < δ) (hγ₀ : 0 < γ₀)
    (hgap : 1 / 4 + 7 * «ω» + 2 * δ < γ₀) (hγhi : γ₀ ≤ 1 / 2)
    (hC : 1 ≤ C) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ Real.exp 1 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ l : Fin 6, ∀ M N : ℝ,
        0 < M → x / C ≤ M * N → M * N ≤ C * x →
        x ^ γ₀ ≤ N → N ≤ C * Real.sqrt x →
      let Θ := 1 + (Real.log x) ^ (-D)
      let η : ℝ → ℝ := fun u => if 0 < u then
        Real.smoothTransition (Real.log u / Real.log Θ + 1) -
          Real.smoothTransition (Real.log u / Real.log Θ) else 0
      let z := x ^ ((8639 : ℝ) / 50000)
      let M0 := x ^ (1 - (34941 : ℝ) / 100000)
      let S0 : ℕ → ℝ := fun n => if (n : ℝ) ≤ M0 then
        ∑ ps ∈ siftedPrimeTuples x l, ∑ d ∈ n.divisorsAntidiagonal,
          if d.1 = ps.prod then smallPrimeMobius z d.2 else 0 else 0
      let α : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc 1 ⌊Θ * M⌋₊,
        Finsupp.single n ((η ((n : ℝ) / M) * S0 n : ℝ) : ℂ)
      let β : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc 1 ⌊Θ * N⌋₊,
        Finsupp.single n ((η ((n : ℝ) / N) *
          (ArithmeticFunction.zeta n : ℝ) : ℝ) : ℂ)
      ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
      ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
        (∑ q ∈ (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
            q ∣ (∏ p ∈ I, p) ∧ Nonempty
              (DenseDivisibilityWitness
                ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩ 1 q)),
          ‖fullDiscrepancy (finiteConvolution α β) q a‖) ≤
            K * x / (Real.log x) ^ A := by
  let ι := Fin 6 × ℝ × ℝ
  let good (x : ℝ) (i : ι) : Prop :=
    0 < i.2.1 ∧ x / C ≤ i.2.1 * i.2.2 ∧ i.2.1 * i.2.2 ≤ C * x ∧
      x ^ γ₀ ≤ i.2.2 ∧ i.2.2 ≤ C * Real.sqrt x
  let Θ (x : ℝ) := 1 + (Real.log x) ^ (-D)
  let η (x u : ℝ) : ℝ := if 0 < u then
    Real.smoothTransition (Real.log u / Real.log (Θ x) + 1) -
      Real.smoothTransition (Real.log u / Real.log (Θ x)) else 0
  let S0 (x : ℝ) (l : Fin 6) (n : ℕ) : ℝ :=
    if (n : ℝ) ≤ x ^ (1 - (34941 : ℝ) / 100000) then
      ∑ ps ∈ siftedPrimeTuples x l, ∑ d ∈ n.divisorsAntidiagonal,
        if d.1 = ps.prod then smallPrimeMobius (x ^ ((8639 : ℝ) / 50000)) d.2 else 0
    else 0
  let α₀ (x : ℝ) (i : ι) : ℕ →₀ ℂ :=
    ∑ n ∈ Finset.Icc 1 ⌊Θ x * i.2.1⌋₊,
      Finsupp.single n ((η x ((n : ℝ) / i.2.1) * S0 x i.1 n : ℝ) : ℂ)
  let Mf (x : ℝ) (i : ι) := if good x i then i.2.1 else Real.sqrt x
  let Nf (x : ℝ) (i : ι) := if good x i then i.2.2 else Real.sqrt x
  let αf (x : ℝ) (i : ι) : ℕ →₀ ℂ := if good x i then α₀ x i else 0
  let ψ (x : ℝ) (i : ι) : ℝ → ℂ :=
    if good x i then fun u => (η x u : ℂ) else 0
  let C' : ℝ := max C 2
  have hC' : 1 ≤ C' := hC.trans (le_max_left _ _)
  have hCC' : C ≤ C' := le_max_left _ _
  have htwoC' : 2 ≤ C' := le_max_right _ _
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hC'p : 0 < C' := zero_lt_one.trans_le hC'
  have hxpos (x : ℝ) (hx : Real.exp 1 ≤ x) : 0 < x :=
    (Real.exp_pos 1).trans_le hx
  have hxone (x : ℝ) (hx : Real.exp 1 ≤ x) : 1 ≤ x :=
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hx
  have hxgt (x : ℝ) (hx : Real.exp 1 ≤ x) : 1 < x :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hx
  have hlogone (x : ℝ) (hx : Real.exp 1 ≤ x) : 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le (hxpos x hx)).mpr hx
  obtain ⟨B, hB, hprofiles⟩ := sifted_short_geometric_profile_bounds D hD
  have hprofile (x : ℝ) (hx : Real.exp 1 ≤ x) := hprofiles x hx
  have hsuppη (x : ℝ) (hx : Real.exp 1 ≤ x) :
      Function.support (fun u => (η x u : ℂ)) ⊆ Set.Icc (1 / 2 : ℝ) C' := by
    have hp := hprofile x hx
    have hs := hp.2.2.2.1
    change Function.support (fun u => (η x u : ℂ)) = Set.Ioo (Θ x)⁻¹ (Θ x) at hs
    rw [hs]
    have hh : (1 / 2 : ℝ) ≤ (Θ x)⁻¹ := by
      simpa only [one_div] using
        one_div_le_one_div_of_le (zero_lt_one.trans hp.1) hp.2.1
    exact Set.Ioo_subset_Icc_self.trans
      (Set.Icc_subset_Icc hh (hp.2.1.trans htwoC'))
  have hscale : ∀ x : ℝ, Real.exp 1 ≤ x → ∀ i : ι,
      x / C' ≤ Mf x i * Nf x i ∧ Mf x i * Nf x i ≤ C' * x ∧
      x ^ γ₀ ≤ Nf x i ∧ Nf x i ≤ Real.sqrt x * C := by
    intro x hx i
    by_cases hg : good x i
    · simp only [Mf, Nf, ite_eq_left hg]
      exact ⟨(div_le_div_of_nonneg_left (hxpos x hx).le hCp hCC').trans hg.2.1,
        hg.2.2.1.trans (mul_le_mul_of_nonneg_right hCC' (hxpos x hx).le),
        hg.2.2.2.1, by simpa only [mul_comm] using hg.2.2.2.2⟩
    · simp only [Mf, Nf, ite_eq_right hg]
      rw [Real.mul_self_sqrt (hxpos x hx).le]
      refine ⟨div_le_self (hxpos x hx).le hC',
        le_mul_of_one_le_left (hxpos x hx).le hC', ?_, ?_⟩
      · rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le (hxone x hx) hγhi
      · exact le_mul_of_one_le_right (Real.sqrt_nonneg x) hC
  have hαsupport : ∀ x : ℝ, Real.exp 1 ≤ x → ∀ i : ι,
      ∀ n ∈ (αf x i).support,
        (1 / 2 : ℝ) * Mf x i ≤ (n : ℝ) ∧ (n : ℝ) ≤ C' * Mf x i := by
    intro x hx i n hn
    by_cases hg : good x i
    · have hp := hprofile x hx
      have hb := (sifted_short_geometric_coefficient_bounds x (Θ x) i.2.1
        (hxgt x hx) hp.1 hp.2.1 hg.1 i.1).2.1
      change ∀ n ∈ (α₀ x i).support,
        i.2.1 / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * i.2.1 at hb
      simp only [αf, ite_eq_left hg] at hn
      obtain ⟨hlo, hhi⟩ := hb n hn
      simp only [Mf, ite_eq_left hg]
      exact ⟨by linarith, hhi.trans
        (mul_le_mul_of_nonneg_right htwoC' hg.1.le)⟩
    · simp only [αf, ite_eq_right hg, Finsupp.support_zero, Finset.notMem_empty] at hn
  have hαbound : ∀ x : ℝ, Real.exp 1 ≤ x → ∀ i : ι, ∀ n : ℕ,
      ‖αf x i n‖ ≤ 1 * (n.divisors.card : ℝ) ^ 3 * (Real.log x) ^ 3 := by
    intro x hx i n
    by_cases hg : good x i
    · have hp := hprofile x hx
      have hb := (sifted_short_geometric_coefficient_bounds x (Θ x) i.2.1
        (hxgt x hx) hp.1 hp.2.1 hg.1 i.1).2.2 n
      change ‖α₀ x i n‖ ≤ (n.divisors.card : ℝ) ^ 3 at hb
      simp only [αf, ite_eq_left hg, one_mul]
      exact hb.trans (le_mul_of_one_le_right (by positivity)
        (one_le_pow₀ (hlogone x hx)))
    · simp only [αf, ite_eq_right hg, Finsupp.zero_apply, norm_zero, one_mul]
      exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
        (pow_nonneg (zero_le_one.trans (hlogone x hx)) _)
  have hψsmooth : ∀ x : ℝ, Real.exp 1 ≤ x → ∀ i : ι, ContDiff ℝ ∞ (ψ x i) := by
    intro x hx i
    by_cases hg : good x i
    · simpa only [ψ, ite_eq_left hg] using (hprofile x hx).2.2.1
    · simpa only [ψ, ite_eq_right hg, Pi.zero_def] using
        (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℂ)))
  have hψsupport : ∀ x : ℝ, Real.exp 1 ≤ x → ∀ i : ι,
      Function.support (ψ x i) ⊆ Set.Icc (1 / 2 : ℝ) C' := by
    intro x hx i
    by_cases hg : good x i
    · simpa only [ψ, ite_eq_left hg] using hsuppη x hx
    · simp only [ψ, ite_eq_right hg, Function.support_zero, Set.empty_subset]
  have hψbounds : ∀ J : ℕ, ∃ L E : ℝ, 0 ≤ L ∧
      ∀ x : ℝ, Real.exp 1 ≤ x → ∀ i : ι, ∀ r : ℕ, r ≤ J → ∀ t : ℝ,
        ‖iteratedDeriv r (ψ x i) t‖ ≤ L * (Real.log x) ^ E := by
    intro J
    let L : ℝ := ∑ r ∈ Finset.range (J + 1), B r
    have hL : 0 ≤ L := Finset.sum_nonneg (fun r _ => (hB r).le)
    refine ⟨L, D * J, hL, ?_⟩
    intro x hx i r hr t
    by_cases hg : good x i
    · have hb : B r ≤ L := Finset.single_le_sum (fun k _ => (hB k).le)
        (Finset.mem_range_succ_iff.mpr hr)
      have he : D * (r : ℝ) ≤ D * J :=
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hr) (zero_le_one.trans hD)
      have hd := (hprofile x hx).2.2.2.2.2 r t
      change ‖iteratedDeriv r (fun u => (η x u : ℂ)) t‖ ≤
        B r * (Real.log x) ^ (D * (r : ℝ)) at hd
      simp only [ψ, ite_eq_left hg]
      exact hd.trans (mul_le_mul hb
        (Real.rpow_le_rpow_of_exponent_le (hlogone x hx) he)
        (Real.rpow_nonneg (zero_le_one.trans (hlogone x hx)) _) hL)
    · simp only [ψ, ite_eq_right hg, iteratedDeriv_const_zero, norm_zero]
      exact mul_nonneg hL (Real.rpow_nonneg
        (zero_le_one.trans (hlogone x hx)) _)
  have hsub : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℝ in Filter.atTop, (1 : ℝ) ≤ x ^ ε ∧ C ≤ x ^ ε := by
    intro ε hε
    filter_upwards [(tendsto_rpow_atTop hε).eventually_ge_atTop C] with x hx
    exact ⟨hC.trans hx, hx⟩
  have hglobal := sourceSmoothFactor_dense_uniform_log_saving
    «ω» δ γ₀ hω hδ hγ₀ hgap hγhi Mf Nf αf ψ (fun _ => 1) (fun _ => C)
    (1 / 2) C' 1 (Real.exp 1) 3 (by norm_num) (by linarith) hC'
    (by norm_num) le_rfl (fun _ _ => ⟨zero_lt_one, hCp⟩) hsub
    hscale hαsupport hαbound hψsmooth hψsupport hψbounds
  dsimp only at hglobal
  intro A hA
  obtain ⟨K, X, hK, hX, hmain⟩ := hglobal A hA
  refine ⟨K, X, hK, hX, ?_⟩
  intro x hx l M N hM hMNlo hMNhi hNlo hNhi Θ₀ η₀ z M0 S α β I hI a ha
  let i : ι := (l, M, N)
  have hg : good x i := ⟨hM, hMNlo, hMNhi, hNlo, hNhi⟩
  have hxexp : Real.exp 1 ≤ x := hX.trans hx
  have hp := hprofile x hxexp
  have hN : 0 < N := (Real.rpow_pos_of_pos (hxpos x hxexp) γ₀).trans_le hNlo
  have hβeq : positiveCompactProfileSequence (ψ x i) C' (Nf x i) 0 = β := by
    simp only [ψ, Nf, ite_eq_left hg]
    change positiveCompactProfileSequence (fun u => (η x u : ℂ)) C' N 0 = β
    have heq : positiveCompactProfileSequence (fun u => (η x u : ℂ)) C' N 0 =
        positiveCompactProfileSequence (fun u => (η x u : ℂ)) 2 N 0 := by
      ext n
      rw [positiveCompactProfileSequence_apply (1 / 2) C' N (by norm_num) hN _
        (hsuppη x hxexp)]
      have hs2 : Function.support (fun u => (η x u : ℂ)) ⊆ Set.Icc (1 / 2 : ℝ) 2 := by
        rw [hp.2.2.2.1]
        have hh : (1 / 2 : ℝ) ≤ (Θ x)⁻¹ := by
          simpa only [one_div] using one_div_le_one_div_of_le
            (zero_lt_one.trans hp.1) hp.2.1
        exact Set.Ioo_subset_Icc_self.trans (Set.Icc_subset_Icc hh hp.2.1)
      rw [positiveCompactProfileSequence_apply (1 / 2) 2 N (by norm_num) hN _ hs2]
    rw [heq]
    exact sifted_short_geometric_free_eq (Θ x) N hp.1 hp.2.1 hN
  have hh := hmain x hx i I hI a ha
  rw [hβeq] at hh
  simpa only [αf, ite_eq_left hg, α₀, i, Θ, η, S0, mul_one] using hh

open Classical in
theorem sifted_short_pure_power_coherent_log_saving_of_bilinear
    (τ : ℝ) (hτ : 0 < τ) (hτsmall : τ ≤ 1 / 10 ^ 10)
    (j : ℕ) (hj : 1 ≤ j) («ω» δ : ℝ) (hω : 0 < «ω») (hδ : 0 < δ)
    (hlevel : (1 / 2 : ℝ) + 2 * «ω» < 58639 / 100000 - τ)
    (hsmooth : (1 / 4 : ℝ) + 7 * «ω» + 2 * δ < 34941 / 100000 - τ)
    (hsource : SourceBilinearEstimate j «ω» δ
      ((1 / 2 : ℝ) - 41361 / 100000 + τ)) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ Real.exp 1 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ l : Fin 6,
      let z := x ^ ((8639 : ℝ) / 50000)
      let M0 := x ^ (1 - (34941 : ℝ) / 100000)
      let S0 : ArithmeticFunction ℝ :=
        ⟨fun n => if (n : ℝ) ≤ M0 then
          ∑ ps ∈ siftedPrimeTuples x l, ∑ d ∈ n.divisorsAntidiagonal,
            if d.1 = ps.prod then smallPrimeMobius z d.2 else 0 else 0, by simp⟩
      let ρx : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
        Finsupp.single n
          (((S0 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ)
      ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
      ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
        (∑ q ∈ (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
            q ∣ (∏ p ∈ I, p) ∧ Nonempty
              (DenseDivisibilityWitness
                ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩ j q)),
          ‖fullDiscrepancy ρx q a‖) ≤ K * x / (Real.log x) ^ A := by
  let a₀ : ℝ := 41361 / 100000
  let b₀ : ℝ := 58639 / 100000
  let c₀ : ℝ := 34941 / 100000
  let σ : ℝ := 1 / 2 - a₀ + τ
  let γ₀ : ℝ := c₀ - τ
  let θ : ℝ := 1 / 2 + 2 * «ω»
  let ε : ℝ := (b₀ - τ - θ) / 2
  have hσ : 0 < σ := by dsimp only [σ, a₀]; linarith only [hτ]
  have hγ₀ : 0 < γ₀ := by dsimp only [γ₀, c₀]; linarith only [hτsmall]
  have hγhi : γ₀ ≤ (1 / 2 : ℝ) := by dsimp only [γ₀, c₀]; linarith only [hτ]
  have hθ : 0 < θ := by dsimp only [θ]; linarith
  have hθhi : θ < 1 := by dsimp only [θ] at *; linarith only [hlevel, hτ]
  have hε : 0 < ε := by
    change (1 / 2 : ℝ) + 2 * «ω» < b₀ - τ at hlevel
    dsimp only [ε, θ]
    linarith only [hlevel]

  intro A hA
  obtain ⟨D, hD, Kb, Xb, hKb, hXb, hboundary⟩ :=
    arithmeticFunction_zeta_closedCutoff_log_saving θ 3 A hθ hθhi hA
  let A' : ℝ := A + 2 * (D : ℝ) + 3
  have hA' : 0 < A' := by dsimp only [A']; positivity
  have hD' : 1 ≤ (D : ℝ) := by exact_mod_cast hD
  obtain ⟨Ks, Xs, hKs, hXs, hsmoothBoxes⟩ :=
    sifted_short_geometric_smooth_log_saving (D : ℝ) «ω» δ γ₀ 8
      hD' hω hδ hγ₀ hsmooth hγhi (by norm_num) A' hA'
  obtain ⟨Kt, Xt, hKt, hXt, htypeIIBoxes⟩ :=
    sifted_short_geometric_typeII_coherent_log_saving_of_bilinear j «ω» δ σ 8 (D : ℝ)
      hω hδ hσ (by norm_num) hD' (by dsimp [σ, a₀]; linarith only [hτsmall]) hsource A' hA'
  obtain ⟨Kz, Xz, hKz, hXz, hzeroBoxes⟩ :=
    arithmeticFunction_geometric_typeZero_log_saving (D : ℝ) 3 8 θ ε A'
      hD' (by norm_num) hθ hθhi hε hA'
  obtain ⟨Xτ, hXτ⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hτ).eventually_ge_atTop (8 : ℝ))
  let K : ℝ := Kb + 36 * (Ks + Kt + Kz)
  let X : ℝ := max Xb (max Xs (max Xt (max Xz Xτ)))
  refine ⟨K, X, by dsimp only [K]; positivity,
    hXb.trans (le_max_left _ _), ?_⟩
  intro x hx l z M0 S0 ρx I hI a ha
  have hxb : Xb ≤ x := (le_max_left _ _).trans hx
  have hxs : Xs ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxt : Xt ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  have hxz : Xz ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hx)))
  have hxτ : Xτ ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hx)))
  have hxexp : Real.exp 1 ≤ x := hXb.trans hxb
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hxexp
  have hxone : 1 ≤ x :=
    (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans hxexp
  have hxgt : 1 < x :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hxexp
  have hxτbound : 8 ≤ x ^ τ := hXτ x hxτ
  let ell : ℝ := Real.log x
  have hell : 1 ≤ ell := (Real.le_log_iff_exp_le hxpos).mpr hxexp
  have hellpos : 0 < ell := zero_lt_one.trans_le hell
  let Θ : ℝ := 1 + ell ^ (-(D : ℝ))
  let η : ℝ → ℝ := fun u => if 0 < u then
    Real.smoothTransition (Real.log u / Real.log Θ + 1) -
      Real.smoothTransition (Real.log u / Real.log Θ) else 0
  let R : ℕ := ⌈Real.log (2 * x) / Real.log Θ⌉₊
  let grid : Finset (Fin 2 → ℕ) :=
    Fintype.piFinset (fun _ : Fin 2 => Finset.range (R + 1))
  let scale (ν : Fin 2 → ℕ) (i : Fin 2) : ℝ := Θ ^ (ν i)
  let E : Finset (Fin 2 → ℕ) := grid.filter (fun ν =>
    x / Θ ^ 2 ≤ (∏ i : Fin 2, scale ν i) ∧
      (∏ i : Fin 2, scale ν i) ≤ (2 * x) * Θ ^ 2)
  let f : Fin 2 → ArithmeticFunction ℝ :=
    ![S0, (ArithmeticFunction.zeta : ArithmeticFunction ℝ)]
  let βm (ν : Fin 2 → ℕ) (i : Fin 2) : MonoidAlgebra ℂ ℕ :=
    ∑ n ∈ Finset.Icc 1 ⌊Θ * scale ν i⌋₊,
      MonoidAlgebra.single n ((η ((n : ℝ) / scale ν i) * f i n : ℝ) : ℂ)
  let α (ν : Fin 2 → ℕ) : ℕ →₀ ℂ := (βm ν 0).coeff
  let β (ν : Fin 2 → ℕ) : ℕ →₀ ℂ := (βm ν 1).coeff
  let F (ν : Fin 2 → ℕ) : ℕ →₀ ℂ := finiteConvolution (α ν) (β ν)
  let Q : Finset ℕ := (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun q =>
    q ∣ (∏ p ∈ I, p) ∧ Nonempty
      (DenseDivisibilityWitness
        ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩ j q))
  have hQ : Q ⊆ Finset.Icc 1 ⌊x ^ θ⌋₊ := Finset.filter_subset _ _
  have haq (q : ℕ) (hq : q ∈ Q) : Nat.Coprime a q :=
    ha.of_dvd_right (Finset.mem_filter.mp hq).2.1
  have hS0 (n : ℕ) : |S0 n| ≤ (n.divisors.card : ℝ) ^ 3 := by
    have hh := (sifted_short_source_bounds x hxgt l n).1
    simpa only [S0, ArithmeticFunction.coe_mk, Complex.norm_real,
      Real.norm_eq_abs] using hh
  have hΘ : 1 < Θ := lt_add_of_pos_right 1 (Real.rpow_pos_of_pos hellpos _)
  have hΘtwo : Θ ≤ 2 := by
    have hh := Real.rpow_le_one_of_one_le_of_nonpos hell
      (neg_nonpos.mpr (Nat.cast_nonneg D))
    dsimp only [Θ]
    linarith only [hh]
  have hΘpos : 0 < Θ := zero_lt_one.trans hΘ
  have hscale (ν : Fin 2 → ℕ) (i : Fin 2) : 1 ≤ scale ν i :=
    one_le_pow₀ hΘ.le
  have hscalePos (ν : Fin 2 → ℕ) (i : Fin 2) : 0 < scale ν i :=
    zero_lt_one.trans_le (hscale ν i)
  have hproduct (ν : Fin 2 → ℕ) :
      (∏ i : Fin 2, βm ν i).coeff = F ν := by
    simp only [Fin.prod_univ_two, F, finiteConvolution, α, β,
      MonoidAlgebra.ofCoeff_coeff]
  have hα (ν : Fin 2 → ℕ) :
      α ν = ∑ n ∈ Finset.Icc 1 ⌊Θ * scale ν 0⌋₊,
        Finsupp.single n ((η ((n : ℝ) / scale ν 0) * S0 n : ℝ) : ℂ) := by
    simp only [α, βm, f, Matrix.cons_val_zero, MonoidAlgebra.coeff_sum,
      MonoidAlgebra.coeff_single]
  have hβ (ν : Fin 2 → ℕ) :
      β ν = ∑ n ∈ Finset.Icc 1 ⌊Θ * scale ν 1⌋₊,
        Finsupp.single n ((η ((n : ℝ) / scale ν 1) *
          (ArithmeticFunction.zeta n : ℝ) : ℝ) : ℂ) := by
    simp only [β, βm, f, Matrix.cons_val_one, Matrix.cons_val_zero,
      MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, ArithmeticFunction.natCoe_apply]
  have hboundary' := hboundary x hxb S0 hS0 Q hQ (fun _ => a) haq
  change (∑ q ∈ Q, ‖fullDiscrepancy ρx q a -
    ∑ ν ∈ E, fullDiscrepancy (∏ i : Fin 2, βm ν i).coeff q a‖) ≤
      Kb * x / ell ^ A at hboundary'
  simp_rw [hproduct] at hboundary'
  obtain ⟨hcard, _, _, _, _⟩ :=
    arithmeticFunction_zeta_finite_smooth_box_boundary S0 3 hS0
      x (2 * x) Θ hxone (by linarith only [hxpos]) hΘ hΘtwo
  change E.card ≤ (R + 1) ^ 2 at hcard
  have hcardReal : (E.card : ℝ) ≤ 36 * ell ^ (2 * (D : ℝ) + 2) := by
    obtain ⟨_, _, hp⟩ := heathBrown_geometric_profiles_uniform
    have hcount := ((hp Θ hΘ hΘtwo).2.2.2.2 (2 * x)
      (by linarith only [hxone])).1
    change ((R + 1 : ℕ) : ℝ) ≤ 2 * Real.log (2 * x) / (Θ - 1) + 2 at hcount
    have hlog2 : Real.log 2 ≤ 1 := by
      simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
        Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hlog2x : Real.log (2 * x) ≤ 2 * ell := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hxpos.ne']
      change Real.log 2 + ell ≤ 2 * ell
      linarith only [hlog2, hell]
    have hinv : (Θ - 1)⁻¹ = ell ^ (D : ℝ) := by
      simp only [Θ, add_sub_cancel_left, Real.rpow_neg hellpos.le, inv_inv]
    have hpower : ell * ell ^ (D : ℝ) = ell ^ ((D : ℝ) + 1) := by
      rw [Real.rpow_add hellpos, Real.rpow_one]
      ring
    have hpowone : 1 ≤ ell ^ ((D : ℝ) + 1) :=
      Real.one_le_rpow hell (by positivity)
    have hcount' : ((R + 1 : ℕ) : ℝ) ≤ 6 * ell ^ ((D : ℝ) + 1) := by
      rw [div_eq_mul_inv, hinv] at hcount
      have hh := mul_le_mul_of_nonneg_right hlog2x
        (Real.rpow_nonneg hellpos.le (D : ℝ))
      nlinarith only [hcount, hh, hpower, hpowone]
    have hc : (E.card : ℝ) ≤ (((R + 1 : ℕ) : ℝ)) ^ 2 := by
      exact_mod_cast hcard
    calc
      (E.card : ℝ) ≤ (((R + 1 : ℕ) : ℝ)) ^ 2 := hc
      _ ≤ (6 * ell ^ ((D : ℝ) + 1)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hcount' 2
      _ = 36 * ell ^ (2 * (D : ℝ) + 2) := by
        have hh : (ell ^ ((D : ℝ) + 1)) ^ 2 = ell ^ (2 * (D : ℝ) + 2) := by
          rw [sq, ← Real.rpow_add hellpos]
          congr 1
          ring
        rw [mul_pow, hh]
        norm_num
  have hMN (ν : Fin 2 → ℕ) (hν : ν ∈ E) :
      x / 4 ≤ scale ν 0 * scale ν 1 ∧ scale ν 0 * scale ν 1 ≤ 8 * x := by
    have he := (Finset.mem_filter.mp hν).2
    simp only [Fin.prod_univ_two] at he
    have hΘsq : Θ ^ 2 ≤ (4 : ℝ) := by nlinarith only [hΘtwo, hΘpos]
    have hsqpos : 0 < Θ ^ 2 := pow_pos hΘpos 2
    exact ⟨(div_le_div_of_nonneg_left hxpos.le hsqpos hΘsq).trans he.1,
      he.2.trans (by nlinarith only [hΘsq, hxpos])⟩
  have hMupper (ν : Fin 2 → ℕ) (hαν : α ν ≠ 0) :
      scale ν 0 ≤ 2 * x ^ (1 - c₀) := by
    obtain ⟨n, hn⟩ := Finsupp.support_nonempty_iff.mpr hαν
    have hc := sifted_short_geometric_coefficient_bounds x Θ (scale ν 0)
      hxgt hΘ hΘtwo (hscalePos ν 0) l
    change (∀ n : ℕ, (∑ n ∈ Finset.Icc 1 ⌊Θ * scale ν 0⌋₊,
      Finsupp.single n ((η ((n : ℝ) / scale ν 0) * S0 n : ℝ) : ℂ)) n =
        ((η ((n : ℝ) / scale ν 0) * S0 n : ℝ) : ℂ)) ∧
      (∀ n ∈ (∑ n ∈ Finset.Icc 1 ⌊Θ * scale ν 0⌋₊,
        Finsupp.single n ((η ((n : ℝ) / scale ν 0) * S0 n : ℝ) : ℂ)).support,
        scale ν 0 / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * scale ν 0) ∧ _ at hc
    rw [← hα ν] at hc
    have hn0 : α ν n ≠ 0 := Finsupp.mem_support_iff.mp hn
    have hS0n : S0 n ≠ 0 := by
      intro hz
      rw [hc.1 n, hz, mul_zero, Complex.ofReal_zero] at hn0
      exact hn0 rfl
    have hs := (sifted_short_source_bounds x hxgt l n).2.2 hS0n
    change (n : ℝ) ≤ x ^ (1 - c₀) at hs
    have hnlo := (hc.2.1 n hn).1
    linarith only [hs, hnlo]
  have hNlower (ν : Fin 2 → ℕ) (hν : ν ∈ E) (hαν : α ν ≠ 0) :
      x ^ γ₀ ≤ scale ν 1 := by
    have hMhi := hMupper ν hαν
    have hprod := (hMN ν hν).1
    have hmul := mul_le_mul_of_nonneg_right hMhi (hscalePos ν 1).le
    have hp : x ^ c₀ * x ^ (1 - c₀) = x := by
      rw [← Real.rpow_add hxpos, show c₀ + (1 - c₀) = 1 by ring, Real.rpow_one]
    have hratio : x / (8 * x ^ (1 - c₀)) ≤ scale ν 1 := by
      apply (div_le_iff₀ (by positivity : 0 < 8 * x ^ (1 - c₀))).mpr
      nlinarith only [hprod, hmul]
    have heq : x / (8 * x ^ (1 - c₀)) = x ^ c₀ / 8 := by
      apply (div_eq_div_iff (by positivity) (by norm_num : (8 : ℝ) ≠ 0)).mpr
      nlinarith only [hp]
    rw [heq] at hratio
    have hg : x ^ γ₀ * 8 ≤ x ^ c₀ := by
      calc
        _ ≤ x ^ γ₀ * x ^ τ :=
          mul_le_mul_of_nonneg_left hxτbound (Real.rpow_nonneg hxpos.le _)
        _ = x ^ c₀ := by
          rw [← Real.rpow_add hxpos]
          congr 1
          dsimp only [γ₀]
          ring
    exact ((le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr hg).trans hratio
  have hbox (ν : Fin 2 → ℕ) (hν : ν ∈ E) :
      (∑ q ∈ Q, ‖fullDiscrepancy (F ν) q a‖) ≤
        (Ks + Kt + Kz) * x / ell ^ A' := by
    have hnonneg : 0 ≤ (Ks + Kt + Kz) * x / ell ^ A' := by positivity
    by_cases hαzero : α ν = 0
    · simpa [F, hαzero, finiteConvolution, fullDiscrepancy,
        progressionMass, reducedMass] using hnonneg
    have hMpos := hscalePos ν 0
    have hNpos := hscalePos ν 1
    have hMNone := hMN ν hν
    have hMNlo : x / 8 ≤ scale ν 0 * scale ν 1 :=
      (by linarith only [hxpos] : x / 8 ≤ x / 4).trans hMNone.1
    by_cases hnear : scale ν 1 ≤ 8 * Real.sqrt x
    · have hs := hsmoothBoxes x hxs l (scale ν 0) (scale ν 1) hMpos
        hMNlo hMNone.2 (hNlower ν hν hαzero) hnear I hI a ha
      change (∑ q ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun q =>
        q ∣ (∏ p ∈ I, p) ∧ Nonempty
          (DenseDivisibilityWitness
            ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩ 1 q)),
        ‖fullDiscrepancy (finiteConvolution
          (∑ n ∈ Finset.Icc 1 ⌊Θ * scale ν 0⌋₊,
            Finsupp.single n ((η ((n : ℝ) / scale ν 0) * S0 n : ℝ) : ℂ))
          (∑ n ∈ Finset.Icc 1 ⌊Θ * scale ν 1⌋₊,
            Finsupp.single n ((η ((n : ℝ) / scale ν 1) *
              (ArithmeticFunction.zeta n : ℝ) : ℝ) : ℂ))) q a‖) ≤
        Ks * x / ell ^ A' at hs
      rw [← hα ν, ← hβ ν] at hs
      have hsub : Q ⊆ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun q =>
        q ∣ (∏ p ∈ I, p) ∧ Nonempty
          (DenseDivisibilityWitness
            ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩ 1 q)) := by
        intro q hq
        obtain ⟨hqI, hqd, hqdense⟩ := Finset.mem_filter.mp hq
        exact Finset.mem_filter.mpr ⟨hqI, hqd,
          denseDivisibility_mono_order hqdense hj⟩
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)).trans
        (hs.trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith only [hKt, hKz]) hxpos.le)
          (Real.rpow_nonneg hellpos.le _)))
    have hfar : 8 * Real.sqrt x < scale ν 1 := lt_of_not_ge hnear
    have hMhi : scale ν 0 ≤ x ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      have hsqrt := Real.sq_sqrt hxpos.le
      have hsqrtpos := Real.sqrt_pos.2 hxpos
      by_contra hm
      have hm' : Real.sqrt x < scale ν 0 := lt_of_not_ge hm
      have hh := mul_lt_mul_of_pos_left hfar hMpos
      have hh' := mul_lt_mul_of_pos_right hm' (by positivity : 0 < 8 * Real.sqrt x)
      nlinarith only [hMNone.2, hsqrt, hh, hh']
    by_cases hmiddle : x ^ (a₀ - τ) ≤ scale ν 0
    · have ht := htypeIIBoxes x hxt l (scale ν 0) (scale ν 1)
        hMNlo hMNone.2 (hscale ν 1) (by
          have he : (1 / 2 : ℝ) - σ = a₀ - τ := by dsimp only [σ]; ring
          simpa only [he] using hmiddle) hMhi I hI a ha
      change (∑ q ∈ Q, ‖fullDiscrepancy (finiteConvolution
        (∑ n ∈ Finset.Icc 1 ⌊Θ * scale ν 0⌋₊,
          Finsupp.single n ((η ((n : ℝ) / scale ν 0) * S0 n : ℝ) : ℂ))
        (∑ n ∈ Finset.Icc 1 ⌊Θ * scale ν 1⌋₊,
          Finsupp.single n ((η ((n : ℝ) / scale ν 1) *
            (ArithmeticFunction.zeta n : ℝ) : ℝ) : ℂ))) q a‖) ≤
          Kt * x / ell ^ A' at ht
      rw [← hα ν, ← hβ ν] at ht
      exact ht.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only [hKs, hKz]) hxpos.le)
        (Real.rpow_nonneg hellpos.le _))
    have hshort : scale ν 0 < x ^ (a₀ - τ) := lt_of_not_ge hmiddle
    have hlarge : x ^ (θ + ε) ≤ scale ν 1 := by
      have hmul := mul_le_mul_of_nonneg_right hshort.le hNpos.le
      have hp : x ^ (b₀ + τ) * x ^ (a₀ - τ) = x := by
        rw [← Real.rpow_add hxpos,
          show b₀ + τ + (a₀ - τ) = 1 by dsimp only [a₀, b₀]; ring, Real.rpow_one]
      have hratio : x / (4 * x ^ (a₀ - τ)) ≤ scale ν 1 := by
        apply (div_le_iff₀ (by positivity : 0 < 4 * x ^ (a₀ - τ))).mpr
        nlinarith only [hMNone.1, hmul]
      have heq : x / (4 * x ^ (a₀ - τ)) = x ^ (b₀ + τ) / 4 := by
        apply (div_eq_div_iff (by positivity) (by norm_num : (4 : ℝ) ≠ 0)).mpr
        nlinarith only [hp]
      rw [heq] at hratio
      have hlarge' : x ^ b₀ ≤ x ^ (b₀ + τ) / 4 := by
        have hh := mul_le_mul_of_nonneg_left
          (show (4 : ℝ) ≤ x ^ τ by linarith only [hxτbound])
          (Real.rpow_nonneg hxpos.le b₀)
        rw [← Real.rpow_add hxpos] at hh
        exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr hh
      exact (Real.rpow_le_rpow_of_exponent_le hxone (by
        have he : θ < b₀ - τ := hlevel
        calc
          θ + ε = (θ + (b₀ - τ)) / 2 := by dsimp only [ε]; ring
          _ ≤ ((b₀ - τ) + (b₀ - τ)) / 2 :=
            div_le_div_of_nonneg_right (add_le_add he.le le_rfl) (by norm_num)
          _ = b₀ - τ := by ring
          _ ≤ b₀ := sub_le_self b₀ hτ.le : θ + ε ≤ b₀)).trans (hlarge'.trans hratio)
    have hz := hzeroBoxes x hxz (scale ν 0) (scale ν 1)
      (hscale ν 0) (hscale ν 1) hMNone.2 hlarge S0 hS0 Q hQ (fun _ => a) haq
    change (∑ q ∈ Q, ‖fullDiscrepancy (finiteConvolution
      (∑ n ∈ Finset.Icc 1 ⌊Θ * scale ν 0⌋₊,
        Finsupp.single n ((η ((n : ℝ) / scale ν 0) * S0 n : ℝ) : ℂ))
      (∑ n ∈ Finset.Icc 1 ⌊Θ * scale ν 1⌋₊,
        Finsupp.single n ((η ((n : ℝ) / scale ν 1) *
          (ArithmeticFunction.zeta n : ℝ) : ℝ) : ℂ))) q a‖) ≤
        Kz * x / ell ^ A' at hz
    rw [← hα ν, ← hβ ν] at hz
    exact hz.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith only [hKs, hKt]) hxpos.le)
      (Real.rpow_nonneg hellpos.le _))
  have htotal : (∑ ν ∈ E, ∑ q ∈ Q, ‖fullDiscrepancy (F ν) q a‖) ≤
      36 * (Ks + Kt + Kz) * x / ell ^ A := by
    calc
      _ ≤ ∑ _ν ∈ E, (Ks + Kt + Kz) * x / ell ^ A' :=
        Finset.sum_le_sum hbox
      _ = (E.card : ℝ) * ((Ks + Kt + Kz) * x / ell ^ A') := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (36 * ell ^ (2 * (D : ℝ) + 2)) *
          ((Ks + Kt + Kz) * x / ell ^ A') :=
        mul_le_mul_of_nonneg_right hcardReal (by positivity)
      _ ≤ 36 * (Ks + Kt + Kz) * x / ell ^ A := by
        have hp : ell ^ A' = ell ^ A * ell ^ (2 * (D : ℝ) + 2) * ell := by
          calc
            ell ^ A' = ell ^ ((A + (2 * (D : ℝ) + 2)) + 1) := by
              congr 1
              dsimp only [A']
              ring
            _ = ell ^ (A + (2 * (D : ℝ) + 2)) * ell := by
              rw [Real.rpow_add hellpos, Real.rpow_one]
            _ = _ := by rw [Real.rpow_add hellpos]
        rw [hp]
        have hpowpos := Real.rpow_pos_of_pos hellpos (2 * (D : ℝ) + 2)
        have hAp := Real.rpow_pos_of_pos hellpos A
        calc
          _ = (36 * (Ks + Kt + Kz) * x / ell ^ A) / ell := by
            field_simp [hAp.ne', hpowpos.ne', hellpos.ne']
          _ ≤ _ := div_le_self (by positivity) hell
  change (∑ q ∈ Q, ‖fullDiscrepancy ρx q a‖) ≤ K * x / ell ^ A
  calc
    _ ≤ ∑ q ∈ Q, (‖fullDiscrepancy ρx q a -
        ∑ ν ∈ E, fullDiscrepancy (F ν) q a‖ +
          ∑ ν ∈ E, ‖fullDiscrepancy (F ν) q a‖) := by
      apply Finset.sum_le_sum
      intro q hq
      exact (norm_le_norm_sub_add _ _).trans
        (add_le_add le_rfl (norm_sum_le _ _))
    _ = (∑ q ∈ Q, ‖fullDiscrepancy ρx q a -
        ∑ ν ∈ E, fullDiscrepancy (F ν) q a‖) +
          ∑ ν ∈ E, ∑ q ∈ Q, ‖fullDiscrepancy (F ν) q a‖ := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ Kb * x / ell ^ A + 36 * (Ks + Kt + Kz) * x / ell ^ A :=
      add_le_add hboundary' htotal
    _ = K * x / ell ^ A := by dsimp only [K]; ring

open Classical in
theorem sifted_short_subpower_coherent_log_saving_of_bilinear
    (τ : ℝ) (hτ : 0 < τ) (hτsmall : τ ≤ 1 / 10 ^ 10)
    (j : ℕ) (hj : 1 ≤ j) («ω» δ : ℝ) (hω : 0 < «ω») (hδ : 0 < δ)
    (hretreat : ∃ r : ℝ, 0 < r ∧
      (1 / 2 : ℝ) + 2 * («ω» + r) < 58639 / 100000 - τ ∧
      (1 / 4 : ℝ) + 7 * («ω» + r) + 2 * (δ + r) < 34941 / 100000 - τ ∧
      SourceBilinearEstimate j («ω» + r) (δ + r)
        ((1 / 2 : ℝ) - 41361 / 100000 + τ))
    (L0 : ℝ → ℝ) (hL0 : ∀ x : ℝ, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0)) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ 1 < X ∧
      ∀ x : ℝ, X ≤ x → ∀ l : Fin 6,
      ∀ Y : Set.Ici (1 : ℝ), (Y : ℝ) = x ^ δ →
      ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
      ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
      let z := x ^ ((8639 : ℝ) / 50000)
      let M0 := x ^ (1 - (34941 : ℝ) / 100000)
      let S0 : ArithmeticFunction ℝ :=
        ⟨fun n => if (n : ℝ) ≤ M0 then
          ∑ ps ∈ siftedPrimeTuples x l, ∑ d ∈ n.divisorsAntidiagonal,
            if d.1 = ps.prod then smallPrimeMobius z d.2 else 0 else 0, by simp⟩
      let ρx : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
        Finsupp.single n
          (((S0 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ)
      let Q : Finset ℕ :=
        (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω») * L0 x⌋₊).filter
          (fun q => q ∣ ∏ p ∈ I, p ∧
            Nonempty (DenseDivisibilityWitness Y j q))
      (∑ q ∈ Q, ‖fullDiscrepancy ρx q a‖) ≤ K * x / (Real.log x) ^ A := by
  obtain ⟨r, hr, hlevel', hsmooth', hsource'⟩ := hretreat
  obtain ⟨Xr, hXr⟩ := eventually_atTop.mp
    (central_subpower_modulus_family_subset j «ω» δ r hr L0 hL0 hL0sub)
  intro A hA
  obtain ⟨K, Xp, hK, hXp, hp⟩ :=
    sifted_short_pure_power_coherent_log_saving_of_bilinear τ hτ hτsmall j hj («ω» + r) (δ + r)
      (by linarith) (by linarith) hlevel' hsmooth' hsource' A hA
  refine ⟨K, max Xp Xr, hK,
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le
      (hXp.trans (le_max_left _ _)), ?_⟩
  intro x hx l Y hY I hI a ha z M0 S0 ρx Q
  have hxp : Xp ≤ x := (le_max_left _ _).trans hx
  have hxr : Xr ≤ x := (le_max_right _ _).trans hx
  have hsubset := hXr x hxr Y hY I
  have hbound := hp x hxp l I hI a ha
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun q _ _ => norm_nonneg (fullDiscrepancy ρx q a))).trans hbound

#print axioms sifted_short_geometric_coefficient_bounds
#print axioms sifted_short_geometric_all_moduli_siegelWalfisz
#print axioms sifted_short_geometric_typeII_coherent_log_saving_of_bilinear
#print axioms sifted_short_geometric_smooth_log_saving
#print axioms sifted_short_pure_power_coherent_log_saving_of_bilinear
#print axioms sifted_short_subpower_coherent_log_saving_of_bilinear

end PrimeGap182Analytic.Harman
