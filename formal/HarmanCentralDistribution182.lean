import HarmanCentralSources182
import HarmanSmallBoolean182
import HarmanFiveBoxes182

/-! Three actual Buchstab source distributions follow from the uniform
bilinear estimate. All prime tuple identities, monomial cuts, support
conditions and subpower modulus inclusions are proved explicitly.
Adapted from Apache-2.0 PrimeGaps186 at the checked source hash. -/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

open Classical in
theorem sourceT4_sub_sourceU1_coherent_log_saving_of_bilinear
    (j : ℕ) («ω» δ σ : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ)
    (hσgap : (1 / 2 : ℝ) - 41361 / 100000 < σ)
    (hretreat : ∃ r : ℝ, 0 < r ∧ «ω» + r < 1 / 4 ∧
      SourceBilinearEstimate j («ω» + r) (δ + r) σ)
    (L0 : ℝ → ℝ) (hL0 : ∀ x : ℝ, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0)) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ Real.exp 100 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ Y : Set.Ici (1 : ℝ), (Y : ℝ) = x ^ δ →
      ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
      ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
        let F : ℕ →₀ ℂ :=
          ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
            Finsupp.single n ((sourceT4 x n - sourceU1 x n : ℝ) : ℂ)
        let Q := (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω») * L0 x⌋₊).filter (fun q =>
          q ∣ (∏ p ∈ I, p) ∧
            Nonempty (DenseDivisibilityWitness Y j q))
        (∑ q ∈ Q, ‖fullDiscrepancy F q a‖) ≤ K * x / (Real.log x) ^ A := by
  intro A hA
  obtain ⟨K, Xb, hK, hXb, hbound⟩ :=
    central_small_prime_boolean_cut_subpower_coherent_log_saving_of_bilinear
      (arity := 3) (by norm_num) j «ω» δ σ hω hδ hσgap hretreat L0 hL0 hL0sub A hA
  obtain ⟨Xt, _hXt, htransport⟩ := sourceT4_sub_sourceU1_eventually_four_prime_finsupp
  obtain ⟨Xg, _hXg, hgeometry⟩ := sourceT4U1_eventually_compact_tuple_geometry
  refine ⟨2 * K, max Xb (max Xt Xg), by positivity,
    hXb.trans (le_max_left _ _), ?_⟩
  intro x hx Y hY I hI a ha F Q
  have hxb : Xb ≤ x := (le_max_left _ _).trans hx
  have hxt : Xt ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxg : Xg ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hx1 : 1 < x := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 100)).trans_le
    (hXb.trans hxb)
  let P := (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
    ⌊x ^ ((9 : ℝ) / 10)⌋₊).filter Nat.Prime
  let T := Fintype.piFinset (fun _ : Fin 4 => P)
  let N := Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊
  let α : (Fin 4 → ℕ) → Fin 4 → ℝ := fun p i => Real.logb x (p i : ℝ)
  let w : (Fin 4 → ℕ) → ℝ := fun p =>
    (if sourceT4ExponentMask (α p) then 1 else 0) -
      (if sourceU1ExponentMask (α p) then 1 else 0)
  let Cp (p : Fin 4 → ℕ) : Prop := (∏ i, p i) ∈ N ∧
    sourceT4ExponentMask (α p) = true ∧ sourceU1ExponentMask (α p) = false
  let Cm (p : Fin 4 → ℕ) : Prop := (∏ i, p i) ∈ N ∧
    sourceU1ExponentMask (α p) = true ∧ sourceT4ExponentMask (α p) = false
  have hCp : Cp = fun p => (∏ i, p i) ∈ N ∧
      sourceT4ExponentMask (α p) = true ∧ sourceU1ExponentMask (α p) = false := rfl
  have hCm : Cm = fun p => (∏ i, p i) ∈ N ∧
      sourceU1ExponentMask (α p) = true ∧ sourceT4ExponentMask (α p) = false := rfl
  clear_value Cp Cm
  let Fp : ℕ →₀ ℂ := ∑ p ∈ T, Finsupp.single (∏ i, p i) (if Cp p then 1 else 0)
  let Fm : ℕ →₀ ℂ := ∑ p ∈ T, Finsupp.single (∏ i, p i) (if Cm p then 1 else 0)
  let M := sourceT4U1MonomialCuts x
  have hFp : Fp = ∑ p ∈ T, Finsupp.single (∏ i, p i) (if Cp p then 1 else 0) := rfl
  have hFm : Fm = ∑ p ∈ T, Finsupp.single (∏ i, p i) (if Cm p then 1 else 0) := rfl
  have hM : M = sourceT4U1MonomialCuts x := rfl
  clear_value Fp Fm M
  have hMcard : M.card ≤ 32 := by
    rw [hM]
    exact sourceT4U1MonomialCuts_card_le x
  have hMdata : ∀ d ∈ M, d.numerator.Nonempty ∧ Disjoint d.numerator d.denominator ∧
      d.numerator.card + d.denominator.card ≤ 4 ∧ 0 < d.threshold := by
    rw [hM]
    exact sourceT4U1MonomialCuts_data x (zero_lt_one.trans hx1)
  have hprime (p : Fin 4 → ℕ) (hp : p ∈ T) (i : Fin 4) : (p i).Prime :=
    (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)).2
  have hbooleanp : ∀ p ∈ T, ∀ q ∈ T,
      (∀ d ∈ M,
        (if d.lower then
          if d.strict then d.threshold < d.value p else d.threshold ≤ d.value p
        else if d.strict then d.value p < d.threshold else d.value p ≤ d.threshold) ↔
        (if d.lower then
          if d.strict then d.threshold < d.value q else d.threshold ≤ d.value q
        else if d.strict then d.value q < d.threshold else d.value q ≤ d.threshold)) →
      (Cp p ↔ Cp q) := by
    intro p hp q hq ht
    rw [hCp]
    rw [hM] at ht
    exact (sourceT4U1MonomialCuts_boolean x hx1 p q
      (fun i => (hprime p hp i).pos) (fun i => (hprime q hq i).pos) ht).1
  have hbooleanm : ∀ p ∈ T, ∀ q ∈ T,
      (∀ d ∈ M,
        (if d.lower then
          if d.strict then d.threshold < d.value p else d.threshold ≤ d.value p
        else if d.strict then d.value p < d.threshold else d.value p ≤ d.threshold) ↔
        (if d.lower then
          if d.strict then d.threshold < d.value q else d.threshold ≤ d.value q
        else if d.strict then d.value q < d.threshold else d.value q ≤ d.threshold)) →
      (Cm p ↔ Cm q) := by
    intro p hp q hq ht
    rw [hCm]
    rw [hM] at ht
    exact (sourceT4U1MonomialCuts_boolean x hx1 p q
      (fun i => (hprime p hp i).pos) (fun i => (hprime q hq i).pos) ht).2
  have hsupp (p : Fin 4 → ℕ) (hp : p ∈ T)
      (hn : (∏ i, p i) ∈ N) (hw : w p ≠ 0) :
      ∃ S : Finset (Fin 4), S.Nonempty ∧ S ≠ Finset.univ ∧
        x ^ ((41361 : ℝ) / 100000) ≤ ((∏ i ∈ S, p i : ℕ) : ℝ) ∧
        ((∏ i ∈ S, p i : ℕ) : ℝ) ≤ x ^ ((58639 : ℝ) / 100000) :=
    (hgeometry x hxg p (hprime p hp) hn hw).2
  have hsuppp : ∀ p ∈ T, Cp p →
      (∏ i, p i) ∈ N ∧ ∃ S : Finset (Fin 4), S.Nonempty ∧ S ≠ Finset.univ ∧
        x ^ ((41361 : ℝ) / 100000) ≤ ((∏ i ∈ S, p i : ℕ) : ℝ) ∧
        ((∏ i ∈ S, p i : ℕ) : ℝ) ≤ x ^ ((58639 : ℝ) / 100000) := by
    intro p hp hC
    rw [hCp] at hC
    refine ⟨hC.1, hsupp p hp hC.1 ?_⟩
    simp [w, hC.2.1, hC.2.2]
  have hsuppm : ∀ p ∈ T, Cm p →
      (∏ i, p i) ∈ N ∧ ∃ S : Finset (Fin 4), S.Nonempty ∧ S ≠ Finset.univ ∧
        x ^ ((41361 : ℝ) / 100000) ≤ ((∏ i ∈ S, p i : ℕ) : ℝ) ∧
        ((∏ i ∈ S, p i : ℕ) : ℝ) ≤ x ^ ((58639 : ℝ) / 100000) := by
    intro p hp hC
    rw [hCm] at hC
    refine ⟨hC.1, hsupp p hp hC.1 ?_⟩
    simp [w, hC.2.1, hC.2.2]
  have hbp : (∑ q ∈ Q, ‖fullDiscrepancy Fp q a‖) ≤ K * x / (Real.log x) ^ A := by
    rw [hFp]
    exact hbound x hxb Y hY M Cp hMcard hMdata hbooleanp hsuppp I hI a ha
  have hbm : (∑ q ∈ Q, ‖fullDiscrepancy Fm q a‖) ≤ K * x / (Real.log x) ^ A := by
    rw [hFm]
    exact hbound x hxb Y hY M Cm hMcard hMdata hbooleanm hsuppm I hI a ha
  have hF : F = ∑ p ∈ T, Finsupp.single (∏ i, p i)
      (if (∏ i, p i) ∈ N then (w p : ℂ) else 0) := htransport x hxt
  have hdelta (q : ℕ) : fullDiscrepancy F q a =
      fullDiscrepancy Fp q a - fullDiscrepancy Fm q a := by
    rw [hF, hFp, hFm, hCp, hCm]
    exact sourceT4U1_tuple_discrepancy_split x T N q a
  calc
    _ ≤ ∑ q ∈ Q, (‖fullDiscrepancy Fp q a‖ + ‖fullDiscrepancy Fm q a‖) := by
      apply Finset.sum_le_sum
      intro q _hq
      rw [hdelta]
      exact norm_sub_le _ _
    _ = (∑ q ∈ Q, ‖fullDiscrepancy Fp q a‖) +
        ∑ q ∈ Q, ‖fullDiscrepancy Fm q a‖ := Finset.sum_add_distrib
    _ ≤ K * x / (Real.log x) ^ A + K * x / (Real.log x) ^ A := add_le_add hbp hbm
    _ = _ := by ring

open Classical in
theorem sourceLargeFirst_coherent_log_saving_of_bilinear
    (j : ℕ) («ω» δ σ : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ)
    (hσgap : (1 / 2 : ℝ) - 41361 / 100000 < σ)
    (hretreat : ∃ r : ℝ, 0 < r ∧ «ω» + r < 1 / 4 ∧
      SourceBilinearEstimate j («ω» + r) (δ + r) σ)
    (L0 : ℝ → ℝ) (hL0 : ∀ x : ℝ, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0)) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ Real.exp 100 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ Y : Set.Ici (1 : ℝ), (Y : ℝ) = x ^ δ →
      ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
      ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
        let F : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
          Finsupp.single n (sourceLargeFirst x n : ℂ)
        let Q := (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω») * L0 x⌋₊).filter (fun q =>
          q ∣ (∏ p ∈ I, p) ∧
            Nonempty (DenseDivisibilityWitness Y j q))
        (∑ q ∈ Q, ‖fullDiscrepancy F q a‖) ≤ K * x / (Real.log x) ^ A := by
  intro A hA
  obtain ⟨K, Xb, hK, hXb, hbound⟩ :=
    central_small_prime_boolean_cut_subpower_coherent_log_saving_of_bilinear
      (arity := 1) (by norm_num) j «ω» δ σ hω hδ hσgap hretreat
      L0 hL0 hL0sub A hA
  obtain ⟨Xf, hXf⟩ := eventually_atTop.mp sourceLargeFirst_eventually_finsupp
  obtain ⟨Xc, hXc⟩ := eventually_atTop.mp sourceLargeFirst_eventually_compact_central
  refine ⟨K, max Xb (max Xf Xc), hK, hXb.trans (le_max_left _ _), ?_⟩
  intro x hx Y hY I hI a ha F Q
  have hxb : Xb ≤ x := (le_max_left _ _).trans hx
  have hxf : Xf ≤ x := (le_max_left Xf Xc).trans ((le_max_right _ _).trans hx)
  have hxc : Xc ≤ x := (le_max_right Xf Xc).trans ((le_max_right _ _).trans hx)
  have hx0 : 0 < x := (Real.exp_pos 100).trans_le (hXb.trans hxb)
  let P := (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
    ⌊x ^ ((9 : ℝ) / 10)⌋₊).filter Nat.Prime
  let T := Fintype.piFinset (fun _ : Fin 2 => P)
  let C (p : Fin 2 → ℕ) : Prop :=
    x ≤ ((∏ i, p i : ℕ) : ℝ) ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x ∧
      x ^ ((41361 : ℝ) / 100000) ≤ (p 0 : ℝ) ∧
      (p 0 : ℝ) < Real.sqrt (3 * x) ∧ p 0 ≤ p 1
  have hCdef : C = fun p =>
      x ≤ ((∏ i, p i : ℕ) : ℝ) ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x ∧
        x ^ ((41361 : ℝ) / 100000) ≤ (p 0 : ℝ) ∧
        (p 0 : ℝ) < Real.sqrt (3 * x) ∧ p 0 ≤ p 1 := rfl
  clear_value C
  obtain ⟨M, hMcard, hM, hboolean⟩ := sourceLargeFirst_small_monomial_representation x hx0
  have hpositive (p : Fin 2 → ℕ) (hp : p ∈ T) (i : Fin 2) : 0 < p i :=
    (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)).2.pos
  have hbooleanC : ∀ p ∈ T, ∀ q ∈ T,
      (∀ d ∈ M,
        (if d.lower then
          if d.strict then d.threshold < d.value p else d.threshold ≤ d.value p
        else if d.strict then d.value p < d.threshold else d.value p ≤ d.threshold) ↔
        (if d.lower then
          if d.strict then d.threshold < d.value q else d.threshold ≤ d.value q
        else if d.strict then d.value q < d.threshold else d.value q ≤ d.threshold)) →
      (C p ↔ C q) := by
    intro p hp q hq ht
    rw [hCdef]
    exact hboolean p q (hpositive p hp) (hpositive q hq) ht
  have hsupport (p : Fin 2 → ℕ) (hp : p ∈ T) (hCp : C p) :
      (∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧
      ∃ S : Finset (Fin 2), S.Nonempty ∧ S ≠ Finset.univ ∧
        x ^ ((41361 : ℝ) / 100000) ≤ ((∏ i ∈ S, p i : ℕ) : ℝ) ∧
        ((∏ i ∈ S, p i : ℕ) : ℝ) ≤ x ^ ((58639 : ℝ) / 100000) := by
    rw [hCdef] at hCp
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hCp.1,
      (Nat.le_floor_iff (by positivity : 0 ≤ 2 * x)).mpr hCp.2.1⟩, ?_⟩
    exact (hXc x hxc).2 p hp hCp.2.2.1 hCp.2.2.2.1
  have hFeq : F = ∑ p ∈ T,
      Finsupp.single (∏ i, p i) (if C p then (1 : ℂ) else 0) := by
    rw [hCdef]
    have h := hXf x hxf
    refine h.trans (Finset.sum_congr rfl ?_)
    intro p _hp
    apply congrArg (Finsupp.single (∏ i, p i))
    exact @ite_cond_congr ℂ _ _ inferInstance (Classical.propDecidable _) _ _ rfl
  have h := hbound x hxb Y hY M C hMcard hM hbooleanC hsupport I hI a ha
  rw [hFeq]
  exact h

open Classical in
theorem sourceCentralPair_coherent_log_saving_of_bilinear
    (j : ℕ) («ω» δ σ : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ)
    (hσgap : (1 / 2 : ℝ) - 41361 / 100000 < σ)
    (hretreat : ∃ r : ℝ, 0 < r ∧ «ω» + r < 1 / 4 ∧
      SourceBilinearEstimate j («ω» + r) (δ + r) σ)
    (L0 : ℝ → ℝ) (hL0 : ∀ x : ℝ, 0 < L0 x)
    (hL0sub : Tendsto (fun x : ℝ => Real.log (L0 x) / Real.log x) atTop (nhds 0)) :
    ∀ A : ℝ, 0 < A → ∃ K X : ℝ, 0 < K ∧ Real.exp 100 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ Y : Set.Ici (1 : ℝ), (Y : ℝ) = x ^ δ →
      ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
      ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
        let F : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊,
          Finsupp.single n (sourceCentralPair x n : ℂ)
        let Q := (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω») * L0 x⌋₊).filter (fun q =>
          q ∣ (∏ p ∈ I, p) ∧
            Nonempty (DenseDivisibilityWitness Y j q))
        (∑ q ∈ Q, ‖fullDiscrepancy F q a‖) ≤ K * x / (Real.log x) ^ A := by
  intro A hA
  obtain ⟨K3, X3, hK3, hX3, hb3⟩ :=
    central_small_prime_boolean_cut_subpower_coherent_log_saving_of_bilinear
      (arity := 2) (by norm_num) j «ω» δ σ hω hδ hσgap hretreat
      L0 hL0 hL0sub A hA
  obtain ⟨K4, X4, hK4, _hX4, hb4⟩ :=
    central_small_prime_boolean_cut_subpower_coherent_log_saving_of_bilinear
      (arity := 3) (by norm_num) j «ω» δ σ hω hδ hσgap hretreat
      L0 hL0 hL0sub A hA
  obtain ⟨K5, X5, hK5, _hX5, hb5⟩ :=
    central_five_prime_boolean_cut_subpower_coherent_log_saving_of_bilinear
      j «ω» δ σ hω hδ hσgap hretreat
      L0 hL0 hL0sub A hA
  obtain ⟨Xf, _hXf, hfinite⟩ := sourceCentralPair_eventually_finsupp
  refine ⟨K3 + K4 + K5, max (max X3 X4) (max X5 Xf),
    add_pos (add_pos hK3 hK4) hK5,
    hX3.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro x hx Y hY I hI a ha F Q
  have hx3 : X3 ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hx4 : X4 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx5 : X5 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxf : Xf ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx1 : 1 < x :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 100)).trans_le (hX3.trans hx3)
  have hx2 : 0 ≤ 2 * x := by linarith
  let α (p : ℕ) : ℝ := Real.logb x (p : ℝ)
  let Ps := (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
    ⌊x ^ ((9 : ℝ) / 10)⌋₊).filter Nat.Prime
  let Pf := (Finset.Icc ⌈x ^ ((8639 : ℝ) / 50000)⌉₊
    ⌊x ^ ((31 : ℝ) / 100)⌋₊).filter Nat.Prime
  let T3 := Fintype.piFinset (fun _ : Fin 3 => Ps)
  let C3 (p : Fin 3 → ℕ) : Prop :=
    x ≤ ((∏ i, p i : ℕ) : ℝ) ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x ∧
      (8639 : ℝ) / 50000 ≤ α (p 1) ∧ α (p 1) < α (p 0) ∧
      α (p 0) < (41361 : ℝ) / 100000 ∧
      (41361 : ℝ) / 100000 ≤ α (p 0) + α (p 1) ∧
      α (p 0) + α (p 1) ≤ (58639 : ℝ) / 100000 ∧ p 1 ≤ p 2
  have hC3def : C3 = fun p =>
    x ≤ ((∏ i, p i : ℕ) : ℝ) ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x ∧
      (8639 : ℝ) / 50000 ≤ α (p 1) ∧ α (p 1) < α (p 0) ∧
      α (p 0) < (41361 : ℝ) / 100000 ∧
      (41361 : ℝ) / 100000 ≤ α (p 0) + α (p 1) ∧
      α (p 0) + α (p 1) ≤ (58639 : ℝ) / 100000 ∧ p 1 ≤ p 2 := rfl
  clear_value C3
  let F3 : ℕ →₀ ℂ := ∑ p ∈ T3, Finsupp.single (∏ i, p i)
    (if C3 p then 1 else 0)
  obtain ⟨M3, hM3card, hM3data, hM3bits⟩ :=
    sourceCentralPair_three_monomial_representation x hx1
  have hbits3 : ∀ p ∈ T3, ∀ q ∈ T3,
      (∀ d ∈ M3,
        (if d.lower then
          if d.strict then d.threshold < d.value p else d.threshold ≤ d.value p
        else if d.strict then d.value p < d.threshold else d.value p ≤ d.threshold) ↔
        (if d.lower then
          if d.strict then d.threshold < d.value q else d.threshold ≤ d.value q
        else if d.strict then d.value q < d.threshold else d.value q ≤ d.threshold)) →
      (C3 p ↔ C3 q) := by
    intro p hp q hq ht
    rw [hC3def]
    exact hM3bits p hp q hq ht
  have hs3 (p : Fin 3 → ℕ) (hp : p ∈ T3) (hC : C3 p) :
      (∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧
      ∃ S : Finset (Fin 3), S.Nonempty ∧ S ≠ Finset.univ ∧
        x ^ ((41361 : ℝ) / 100000) ≤ ((∏ i ∈ S, p i : ℕ) : ℝ) ∧
        ((∏ i ∈ S, p i : ℕ) : ℝ) ≤ x ^ ((58639 : ℝ) / 100000) := by
    rw [hC3def] at hC
    obtain ⟨hlo, hhi, _hξ, _hqp, _hpa, hpairlo, hpairhi, _horders⟩ := hC
    have hpos (i : Fin 3) : 0 < (p i : ℝ) :=
      Nat.cast_pos.mpr (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)).2.pos
    have hprod : ((∏ i ∈ ({0, 1} : Finset (Fin 3)), p i : ℕ) : ℝ) =
        (p 0 : ℝ) * p 1 := by simp
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hlo, (Nat.le_floor_iff hx2).mpr hhi⟩,
      {0, 1}, by decide, by decide, ?_, ?_⟩
    · rw [hprod]
      apply (Real.le_logb_iff_rpow_le hx1 (mul_pos (hpos 0) (hpos 1))).mp
      rw [Real.logb_mul (hpos 0).ne' (hpos 1).ne']
      exact hpairlo
    · rw [hprod]
      apply (Real.logb_le_iff_le_rpow hx1 (mul_pos (hpos 0) (hpos 1))).mp
      rw [Real.logb_mul (hpos 0).ne' (hpos 1).ne']
      exact hpairhi
  have h3 : (∑ q ∈ Q, ‖fullDiscrepancy F3 q a‖) ≤
      K3 * x / (Real.log x) ^ A :=
    hb3 x hx3 Y hY M3 C3 hM3card hM3data hbits3 hs3 I hI a ha
  let T4 := Fintype.piFinset (fun _ : Fin 4 => Ps)
  let C4 (p : Fin 4 → ℕ) : Prop :=
    x ≤ ((∏ i, p i : ℕ) : ℝ) ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x ∧
      (8639 : ℝ) / 50000 ≤ α (p 1) ∧ α (p 1) < α (p 0) ∧
      α (p 0) < (41361 : ℝ) / 100000 ∧
      (41361 : ℝ) / 100000 ≤ α (p 0) + α (p 1) ∧
      α (p 0) + α (p 1) ≤ (58639 : ℝ) / 100000 ∧ p 1 ≤ p 2 ∧ p 2 ≤ p 3
  have hC4def : C4 = fun p =>
    x ≤ ((∏ i, p i : ℕ) : ℝ) ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x ∧
      (8639 : ℝ) / 50000 ≤ α (p 1) ∧ α (p 1) < α (p 0) ∧
      α (p 0) < (41361 : ℝ) / 100000 ∧
      (41361 : ℝ) / 100000 ≤ α (p 0) + α (p 1) ∧
      α (p 0) + α (p 1) ≤ (58639 : ℝ) / 100000 ∧ p 1 ≤ p 2 ∧ p 2 ≤ p 3 := rfl
  clear_value C4
  let F4 : ℕ →₀ ℂ := ∑ p ∈ T4, Finsupp.single (∏ i, p i)
    (if C4 p then 1 else 0)
  obtain ⟨M4, hM4card, hM4data, hM4bits⟩ :=
    sourceCentralPair_four_monomial_representation x hx1
  have hbits4 : ∀ p ∈ T4, ∀ q ∈ T4,
      (∀ d ∈ M4,
        (if d.lower then
          if d.strict then d.threshold < d.value p else d.threshold ≤ d.value p
        else if d.strict then d.value p < d.threshold else d.value p ≤ d.threshold) ↔
        (if d.lower then
          if d.strict then d.threshold < d.value q else d.threshold ≤ d.value q
        else if d.strict then d.value q < d.threshold else d.value q ≤ d.threshold)) →
      (C4 p ↔ C4 q) := by
    intro p hp q hq ht
    rw [hC4def]
    exact hM4bits p hp q hq ht
  have hs4 (p : Fin 4 → ℕ) (hp : p ∈ T4) (hC : C4 p) :
      (∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧
      ∃ S : Finset (Fin 4), S.Nonempty ∧ S ≠ Finset.univ ∧
        x ^ ((41361 : ℝ) / 100000) ≤ ((∏ i ∈ S, p i : ℕ) : ℝ) ∧
        ((∏ i ∈ S, p i : ℕ) : ℝ) ≤ x ^ ((58639 : ℝ) / 100000) := by
    rw [hC4def] at hC
    obtain ⟨hlo, hhi, _hξ, _hqp, _hpa, hpairlo, hpairhi, _horders⟩ := hC
    have hpos (i : Fin 4) : 0 < (p i : ℝ) :=
      Nat.cast_pos.mpr (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)).2.pos
    have hprod : ((∏ i ∈ ({0, 1} : Finset (Fin 4)), p i : ℕ) : ℝ) =
        (p 0 : ℝ) * p 1 := by simp
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hlo, (Nat.le_floor_iff hx2).mpr hhi⟩,
      {0, 1}, by decide, by decide, ?_, ?_⟩
    · rw [hprod]
      apply (Real.le_logb_iff_rpow_le hx1 (mul_pos (hpos 0) (hpos 1))).mp
      rw [Real.logb_mul (hpos 0).ne' (hpos 1).ne']
      exact hpairlo
    · rw [hprod]
      apply (Real.logb_le_iff_le_rpow hx1 (mul_pos (hpos 0) (hpos 1))).mp
      rw [Real.logb_mul (hpos 0).ne' (hpos 1).ne']
      exact hpairhi
  have h4 : (∑ q ∈ Q, ‖fullDiscrepancy F4 q a‖) ≤
      K4 * x / (Real.log x) ^ A :=
    hb4 x hx4 Y hY M4 C4 hM4card hM4data hbits4 hs4 I hI a ha
  let T5 := Fintype.piFinset (fun _ : Fin 5 => Pf)
  let C5 (p : Fin 5 → ℕ) : Prop :=
    x ≤ ((∏ i, p i : ℕ) : ℝ) ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x ∧
      (8639 : ℝ) / 50000 ≤ α (p 1) ∧ α (p 1) < α (p 0) ∧
      α (p 0) < (41361 : ℝ) / 100000 ∧
      (41361 : ℝ) / 100000 ≤ α (p 0) + α (p 1) ∧
      α (p 0) + α (p 1) ≤ (58639 : ℝ) / 100000 ∧ p 1 ≤ p 2 ∧ p 2 ≤ p 3 ∧ p 3 ≤ p 4
  have hC5def : C5 = fun p =>
    x ≤ ((∏ i, p i : ℕ) : ℝ) ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 * x ∧
      (8639 : ℝ) / 50000 ≤ α (p 1) ∧ α (p 1) < α (p 0) ∧
      α (p 0) < (41361 : ℝ) / 100000 ∧
      (41361 : ℝ) / 100000 ≤ α (p 0) + α (p 1) ∧
      α (p 0) + α (p 1) ≤ (58639 : ℝ) / 100000 ∧ p 1 ≤ p 2 ∧ p 2 ≤ p 3 ∧ p 3 ≤ p 4 := rfl
  clear_value C5
  let F5 : ℕ →₀ ℂ := ∑ p ∈ T5, Finsupp.single (∏ i, p i)
    (if C5 p then 1 else 0)
  obtain ⟨M5, hM5card, hM5data, hM5bits⟩ :=
    sourceCentralPair_five_monomial_representation_wide x hx1
  have hbits5 : ∀ p ∈ T5, ∀ q ∈ T5,
      (∀ d ∈ M5,
        (if d.lower then
          if d.strict then d.threshold < d.value p else d.threshold ≤ d.value p
        else if d.strict then d.value p < d.threshold else d.value p ≤ d.threshold) ↔
        (if d.lower then
          if d.strict then d.threshold < d.value q else d.threshold ≤ d.value q
        else if d.strict then d.value q < d.threshold else d.value q ≤ d.threshold)) →
      (C5 p ↔ C5 q) := by
    intro p hp q hq ht
    rw [hC5def]
    exact hM5bits p hp q hq ht
  have hs5 (p : Fin 5 → ℕ) (hp : p ∈ T5) (hC : C5 p) :
      (∏ i, p i) ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ ∧
      ∃ S : Finset (Fin 5), (S.card = 2 ∨ S.card = 3) ∧
        x ^ ((41361 : ℝ) / 100000) ≤ ((∏ i ∈ S, p i : ℕ) : ℝ) ∧
        ((∏ i ∈ S, p i : ℕ) : ℝ) ≤ x ^ ((58639 : ℝ) / 100000) := by
    rw [hC5def] at hC
    obtain ⟨hlo, hhi, _hξ, _hqp, _hpa, hpairlo, hpairhi, _horders⟩ := hC
    have hpos (i : Fin 5) : 0 < (p i : ℝ) :=
      Nat.cast_pos.mpr (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)).2.pos
    have hprod : ((∏ i ∈ ({0, 1} : Finset (Fin 5)), p i : ℕ) : ℝ) =
        (p 0 : ℝ) * p 1 := by simp
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hlo, (Nat.le_floor_iff hx2).mpr hhi⟩,
      {0, 1}, Or.inl (by decide), ?_, ?_⟩
    · rw [hprod]
      apply (Real.le_logb_iff_rpow_le hx1 (mul_pos (hpos 0) (hpos 1))).mp
      rw [Real.logb_mul (hpos 0).ne' (hpos 1).ne']
      exact hpairlo
    · rw [hprod]
      apply (Real.logb_le_iff_le_rpow hx1 (mul_pos (hpos 0) (hpos 1))).mp
      rw [Real.logb_mul (hpos 0).ne' (hpos 1).ne']
      exact hpairhi
  have h5 : (∑ q ∈ Q, ‖fullDiscrepancy F5 q a‖) ≤
      K5 * x / (Real.log x) ^ A :=
    hb5 x hx5 Y hY M5 C5 hM5card hM5data hbits5 hs5 I hI a ha
  have hpi {n : ℕ} (t : Fin n → Finset ℕ) (dec : DecidableEq (Fin n)) :
      @Fintype.piFinset (Fin n) dec _ (fun _ => ℕ) t =
        @Fintype.piFinset (Fin n) (Classical.typeDecidableEq _) _ (fun _ => ℕ) t := by
    ext r
    simp only [Fintype.mem_piFinset]
  have hite (p : Prop) (dec : Decidable p) (z w : ℂ) :
      @ite ℂ p dec z w = @ite ℂ p (Classical.propDecidable p) z w :=
    @ite_cond_congr ℂ p p dec (Classical.propDecidable p) z w rfl
  have hidentity : F = F3 + F4 + F5 := by
    dsimp only [F3, F4, F5]
    rw [hC3def, hC4def, hC5def]
    simpa only [T3, T4, T5, α, and_assoc, hpi, hite] using hfinite x hxf
  have hadd (f g : ℕ →₀ ℂ) (q : ℕ) : fullDiscrepancy (f + g) q a =
      fullDiscrepancy f q a + fullDiscrepancy g q a := by
    simp_rw [fullDiscrepancy_eq_finsupp_sum]
    rw [Finsupp.sum_add_index' (fun n => by simp)
      (fun n z w => by split_ifs <;> ring)]
  rw [hidentity]
  calc
    _ ≤ ∑ q ∈ Q,
        (‖fullDiscrepancy F3 q a‖ + ‖fullDiscrepancy F4 q a‖ +
          ‖fullDiscrepancy F5 q a‖) := by
      apply Finset.sum_le_sum
      intro q _hq
      rw [hadd, hadd]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ = (∑ q ∈ Q, ‖fullDiscrepancy F3 q a‖) +
        (∑ q ∈ Q, ‖fullDiscrepancy F4 q a‖) +
        ∑ q ∈ Q, ‖fullDiscrepancy F5 q a‖ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ K3 * x / (Real.log x) ^ A + K4 * x / (Real.log x) ^ A +
        K5 * x / (Real.log x) ^ A := add_le_add (add_le_add h3 h4) h5
    _ = (K3 + K4 + K5) * x / (Real.log x) ^ A := by ring

#print axioms sourceT4_sub_sourceU1_coherent_log_saving_of_bilinear
#print axioms sourceLargeFirst_coherent_log_saving_of_bilinear
#print axioms sourceCentralPair_coherent_log_saving_of_bilinear

end PrimeGap182Analytic.Harman
