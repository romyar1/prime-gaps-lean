import HarmanAnalyticInterfaces182

/-!
# Actual Mobius and prime-factor boxes from the common bilinear estimate

All finite coefficients, both signs, support bounds, coprimality-filtered
Siegel--Walfisz estimates, and scale substitutions are proved. The old numeric
source disjunction is replaced by the explicit actual SourceBilinearEstimate.

Adapted from the hash-pinned Apache-2.0 public PrimeGaps186 source by
scripts/build_harman_long.py. No original source is modified.
-/

noncomputable section
open scoped BigOperators Topology
open Filter PrimeGap186

namespace PrimeGap182Analytic.Harman

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000

open Classical in
theorem harman_literal_box_typeII_coherent_log_saving_of_bilinear
    (j : ℕ) («ω» δ σ C : ℝ)
    (_hω : 0 < «ω») (_hδ : 0 < δ) (hσ : 0 < σ) (hC : 4 ≤ C)
    (hσhalf : σ < 1 / 2)
    (hsource : SourceBilinearEstimate j «ω» δ σ) :
    ∀ A : ℝ, 0 < A →
      ∃ K X : ℝ, 0 < K ∧ Real.exp 100 ≤ X ∧
        ∀ x : ℝ, X ≤ x → ∀ M N : ℝ, 0 < M → 0 < N →
        x / C ≤ M * N → M * N ≤ C * x →
        x ^ (1 / 2 - σ) ≤ min M N / 2 → min M N / 2 ≤ x ^ (1 / 2 : ℝ) →
        M ≤ x ^ (2 : ℝ) → N ≤ x ^ (2 : ℝ) →
        ∀ jA : Fin 3, ∀ jB : Fin 2, ∀ bA bB : Bool,
        ∀ P : ℕ → ℕ → Prop, ∀ L U : ℕ → ℕ → ℝ,
        ∀ z H fLo fHi loA hiA slo shi Zlo Zhi Lsd Usd loB hiB : ℝ,
        0 < z → 1 < H → 0 < Zlo → 0 < Zhi →
        M ≤ loA → hiA ≤ 2 * M → N ≤ loB → hiB ≤ 2 * N →
        let A0 : ℕ → ℤ := fun n =>
          if jA = 0 then
            if (1 < n ∧ ((max 1 (n.primeFactors.sup id) : ℕ) : ℝ) < z ∧
                ((n / n.minFac : ℕ) : ℝ) < H ∧ H ≤ (n : ℝ)) ∧
                fLo ≤ (n.minFac : ℝ) ∧ (n.minFac : ℝ) ≤ fHi
            then (if bA then |ArithmeticFunction.moebius n| else ArithmeticFunction.moebius n)
            else 0
          else
            ∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
              if (if jA = 1 then aa.1 = 1 else
                    Nat.Prime aa.1 ∧ z ≤ (aa.1 : ℝ) ∧ aa.1 ≤ bb.1) ∧
                  Nat.Prime bb.1 ∧ z ≤ (bb.1 : ℝ) ∧ 1 < bb.2 ∧
                  ((max 1 (bb.2.primeFactors.sup id) : ℕ) : ℝ) < z ∧
                  (P aa.1 bb.2 ∧ fLo ≤ (bb.2.minFac : ℝ) ∧
                    (bb.2.minFac : ℝ) ≤ fHi) ∧
                  L aa.1 bb.2 ≤ (bb.1 : ℝ) ∧ (bb.1 : ℝ) ≤ U aa.1 bb.2 ∧
                  ((aa.1 * bb.1 : ℕ) : ℝ) < H ∧
                  ((n / bb.2.minFac : ℕ) : ℝ) < H ∧ H ≤ (n : ℝ)
              then (if bA then |ArithmeticFunction.moebius bb.2|
                    else ArithmeticFunction.moebius bb.2) else 0
        let B0 : ℕ → ℤ := fun n =>
          ∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
            if (if jB = 0 then aa.1 = 1 else Nat.Prime aa.1) ∧
                slo ≤ (aa.1 : ℝ) ∧ (aa.1 : ℝ) ≤ shi ∧
                Zlo ≤ ((max 1 (bb.1.primeFactors.sup id) : ℕ) : ℝ) ∧
                ((max 1 (bb.1.primeFactors.sup id) : ℕ) : ℝ) < Zhi ∧
                Lsd ≤ ((aa.1 * bb.1 : ℕ) : ℝ) ∧ ((aa.1 * bb.1 : ℕ) : ℝ) ≤ Usd
            then (if bB then |ArithmeticFunction.moebius bb.1|
                  else ArithmeticFunction.moebius bb.1) else 0
        let α : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊,
          Finsupp.single n (if loA ≤ (n : ℝ) ∧ (n : ℝ) ≤ hiA then (A0 n : ℂ) else 0)
        let β : ℕ →₀ ℂ := ∑ n ∈ Finset.Icc 1 ⌊2 * N⌋₊,
          Finsupp.single n (if loB ≤ (n : ℝ) ∧ (n : ℝ) ≤ hiB then (B0 n : ℂ) else 0)
        ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
        ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
          (∑ q ∈ (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
              q ∣ (∏ p ∈ I, p) ∧
                Nonempty (DenseDivisibilityWitness
                  ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩
                  j q)),
            ‖fullDiscrepancy (finiteConvolution α β) q a‖) ≤
              K * x / (Real.log x) ^ A := by
  let η : ℝ := 1 / 2 - σ
  have hη : 0 < η := sub_pos.mpr hσhalf
  let ι := (Fin 16 → ℝ) × Fin 3 × Fin 2 × Bool × Bool ×
    (ℕ → ℕ → Prop) × (ℕ → ℕ → ℝ) × (ℕ → ℕ → ℝ)
  let rawA (d : ι) (n : ℕ) : ℤ :=
    if d.2.1 = 0 then
      if (1 < n ∧ ((max 1 (n.primeFactors.sup id) : ℕ) : ℝ) < d.1 2 ∧
          ((n / n.minFac : ℕ) : ℝ) < d.1 3 ∧ d.1 3 ≤ (n : ℝ)) ∧
          d.1 4 ≤ (n.minFac : ℝ) ∧ (n.minFac : ℝ) ≤ d.1 5
      then (if d.2.2.2.1 then |ArithmeticFunction.moebius n| else ArithmeticFunction.moebius n)
      else 0
    else
      ∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
        if (if d.2.1 = 1 then aa.1 = 1 else
              Nat.Prime aa.1 ∧ d.1 2 ≤ (aa.1 : ℝ) ∧ aa.1 ≤ bb.1) ∧
            Nat.Prime bb.1 ∧ d.1 2 ≤ (bb.1 : ℝ) ∧ 1 < bb.2 ∧
            ((max 1 (bb.2.primeFactors.sup id) : ℕ) : ℝ) < d.1 2 ∧
            (d.2.2.2.2.2.1 aa.1 bb.2 ∧ d.1 4 ≤ (bb.2.minFac : ℝ) ∧
              (bb.2.minFac : ℝ) ≤ d.1 5) ∧
            d.2.2.2.2.2.2.1 aa.1 bb.2 ≤ (bb.1 : ℝ) ∧
            (bb.1 : ℝ) ≤ d.2.2.2.2.2.2.2 aa.1 bb.2 ∧
            ((aa.1 * bb.1 : ℕ) : ℝ) < d.1 3 ∧
            ((n / bb.2.minFac : ℕ) : ℝ) < d.1 3 ∧ d.1 3 ≤ (n : ℝ)
        then (if d.2.2.2.1 then |ArithmeticFunction.moebius bb.2|
              else ArithmeticFunction.moebius bb.2) else 0
  let rawB (d : ι) (n : ℕ) : ℤ :=
    ∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
      if (if d.2.2.1 = 0 then aa.1 = 1 else Nat.Prime aa.1) ∧
          d.1 8 ≤ (aa.1 : ℝ) ∧ (aa.1 : ℝ) ≤ d.1 9 ∧
          d.1 10 ≤ ((max 1 (bb.1.primeFactors.sup id) : ℕ) : ℝ) ∧
          ((max 1 (bb.1.primeFactors.sup id) : ℕ) : ℝ) < d.1 11 ∧
          d.1 12 ≤ ((aa.1 * bb.1 : ℕ) : ℝ) ∧ ((aa.1 * bb.1 : ℕ) : ℝ) ≤ d.1 13
      then (if d.2.2.2.2.1 then |ArithmeticFunction.moebius bb.1|
            else ArithmeticFunction.moebius bb.1) else 0
  let sample (T lo hi : ℝ) (f : ℕ → ℤ) : ℕ →₀ ℂ :=
    ∑ n ∈ Finset.Icc 1 ⌊2 * T⌋₊,
      Finsupp.single n (if lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi then (f n : ℂ) else 0)
  let arow (d : ι) := sample (d.1 0) (d.1 6) (d.1 7) (rawA d)
  let brow (d : ι) := sample (d.1 1) (d.1 14) (d.1 15) (rawB d)
  let good (x : ℝ) (d : ι) : Prop :=
    0 < d.1 0 ∧ 0 < d.1 1 ∧
    x / C ≤ d.1 0 * d.1 1 ∧ d.1 0 * d.1 1 ≤ C * x ∧
    x ^ (1 / 2 - σ) ≤ min (d.1 0) (d.1 1) / 2 ∧
    min (d.1 0) (d.1 1) / 2 ≤ x ^ (1 / 2 : ℝ) ∧
    d.1 0 ≤ x ^ (2 : ℝ) ∧ d.1 1 ≤ x ^ (2 : ℝ) ∧
    0 < d.1 2 ∧ 1 < d.1 3 ∧ 0 < d.1 10 ∧ 0 < d.1 11 ∧
    d.1 0 ≤ d.1 6 ∧ d.1 7 ≤ 2 * d.1 0 ∧
    d.1 1 ≤ d.1 14 ∧ d.1 15 ≤ 2 * d.1 1
  let C₀ : ℝ := max C 4
  let X₀ : ℝ := Real.exp 100
  let Mformal (x : ℝ) (d : ι) : ℝ :=
    if good x d then 2 * max (d.1 0) (d.1 1) else x ^ (1 / 2 : ℝ)
  let Nformal (x : ℝ) (d : ι) : ℝ :=
    if good x d then min (d.1 0) (d.1 1) / 2 else x ^ (1 / 2 : ℝ)
  let α (x : ℝ) (d : ι) : ℕ →₀ ℂ :=
    if good x d then if d.1 0 ≤ d.1 1 then brow d else arow d else 0
  let β (x : ℝ) (d : ι) : ℕ →₀ ℂ :=
    if good x d then if d.1 0 ≤ d.1 1 then arow d else brow d else 0
  have hC₀four : 4 ≤ C₀ := le_max_right _ _
  have hC₀ : 1 ≤ C₀ := by linarith
  have hCpos : 0 < C := by linarith
  have hX₀ : Real.exp 1 ≤ X₀ := Real.exp_le_exp.mpr (by norm_num)
  have hxOne (x : ℝ) (hx : X₀ ≤ x) : 1 ≤ x :=
    (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 100)).trans hx
  have hxPos (x : ℝ) (hx : X₀ ≤ x) : 0 < x :=
    zero_lt_one.trans_le (hxOne x hx)
  have hlog (x : ℝ) (hx : X₀ ≤ x) : 1 ≤ Real.log x := by
    have h := (Real.le_log_iff_exp_le (hxPos x hx)).mpr hx
    linarith
  have hsampleValue (T lo hi : ℝ) (f : ℕ → ℤ) (n : ℕ) :
      sample T lo hi f n =
        if n ∈ Finset.Icc 1 ⌊2 * T⌋₊ then
          if lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi then (f n : ℂ) else 0
        else 0 := by
    simp only [sample, Finsupp.finsetSum_apply, Finsupp.single_apply,
      Finset.sum_ite_eq']
  have hsampleFilter (T lo hi : ℝ) (f : ℕ → ℤ) (r : ℕ) :
      (sample T lo hi f).filter (fun n : ℕ => Nat.Coprime n r) =
        ∑ n ∈ Finset.Icc 1 ⌊2 * T⌋₊, Finsupp.single n
          (if lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi ∧ Nat.Coprime n r then (f n : ℂ) else 0) := by
    dsimp only [sample]
    rw [Finsupp.filter_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    ext m
    simp only [Finsupp.filter_apply, Finsupp.single_apply]
    by_cases hnm : n = m
    · subst m
      by_cases hlo : lo ≤ (n : ℝ) <;> by_cases hhi : (n : ℝ) ≤ hi <;>
        by_cases hcop : Nat.Coprime n r <;> simp [hlo, hhi, hcop]
    · simp only [hnm, ite_false, ite_self]
  have hsampleSupport (T lo hi : ℝ) (f : ℕ → ℤ) (n : ℕ)
      (hn : n ∈ (sample T lo hi f).support) : lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi := by
    have hne := Finsupp.mem_support_iff.mp hn
    rw [hsampleValue] at hne
    split_ifs at hne with hmem hcut
    · exact hcut
    · exact (hne rfl).elim
    · exact (hne rfl).elim
  have hmu (b : Bool) (n : ℕ) :
      ‖((if b then |ArithmeticFunction.moebius n|
        else ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
    rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
      cases b <;> simp [h]
  have hcut (p : Prop) [Decidable p] (w : ℤ) (hw : ‖(w : ℂ)‖ ≤ 1) :
      ‖((if p then w else 0 : ℤ) : ℂ)‖ ≤ 1 := by
    by_cases hp : p
    · simpa only [ite_eq_left hp] using hw
    · simp only [ite_eq_right hp, Int.cast_zero, norm_zero, zero_le_one]
  have hrawA (d : ι) (n : ℕ) (hn : 0 < n) :
      ‖(rawA d n : ℂ)‖ ≤ (n.divisors.card : ℝ) ^ 2 := by
    by_cases hj : d.2.1 = 0
    · simp only [rawA, ite_eq_left hj]
      have hcard : (1 : ℝ) ≤ n.divisors.card := by
        have hc : 1 ≤ n.divisors.card := Finset.card_pos.mpr
          ⟨1, Nat.one_mem_divisors.mpr (Nat.ne_of_gt hn)⟩
        exact_mod_cast hc
      exact (hcut _ _ (hmu d.2.2.2.1 n)).trans
        (show (1 : ℝ) ≤ (n.divisors.card : ℝ) ^ 2 from one_le_pow₀ hcard)
    · have hh := norm_three_divisor_sum_le_divisor_sq n
        (fun s p h => ((if (if d.2.1 = 1 then s = 1 else
              Nat.Prime s ∧ d.1 2 ≤ (s : ℝ) ∧ s ≤ p) ∧
            Nat.Prime p ∧ d.1 2 ≤ (p : ℝ) ∧ 1 < h ∧
            ((max 1 (h.primeFactors.sup id) : ℕ) : ℝ) < d.1 2 ∧
            (d.2.2.2.2.2.1 s h ∧ d.1 4 ≤ (h.minFac : ℝ) ∧ (h.minFac : ℝ) ≤ d.1 5) ∧
            d.2.2.2.2.2.2.1 s h ≤ (p : ℝ) ∧ (p : ℝ) ≤ d.2.2.2.2.2.2.2 s h ∧
            ((s * p : ℕ) : ℝ) < d.1 3 ∧
            ((n / h.minFac : ℕ) : ℝ) < d.1 3 ∧ d.1 3 ≤ (n : ℝ)
          then (if d.2.2.2.1 then |ArithmeticFunction.moebius h|
                else ArithmeticFunction.moebius h) else 0 : ℤ) : ℂ)) (by
            intro aa _haa bb _hbb
            exact hcut _ _ (hmu d.2.2.2.1 bb.2))
      simpa only [rawA, ite_eq_right hj, Int.cast_sum] using hh
  have hrawB (d : ι) (n : ℕ) :
      ‖(rawB d n : ℂ)‖ ≤ (n.divisors.card : ℝ) ^ 2 := by
    have hh := norm_three_divisor_sum_le_divisor_sq n
      (fun s t _k => ((if (if d.2.2.1 = 0 then s = 1 else Nat.Prime s) ∧
          d.1 8 ≤ (s : ℝ) ∧ (s : ℝ) ≤ d.1 9 ∧
          d.1 10 ≤ ((max 1 (t.primeFactors.sup id) : ℕ) : ℝ) ∧
          ((max 1 (t.primeFactors.sup id) : ℕ) : ℝ) < d.1 11 ∧
          d.1 12 ≤ ((s * t : ℕ) : ℝ) ∧ ((s * t : ℕ) : ℝ) ≤ d.1 13
        then (if d.2.2.2.2.1 then |ArithmeticFunction.moebius t|
              else ArithmeticFunction.moebius t) else 0 : ℤ) : ℂ)) (by
          intro aa _haa bb _hbb
          exact hcut _ _ (hmu d.2.2.2.2.1 bb.1))
    simpa only [rawB, Int.cast_sum] using hh
  have hsampleNorm (T lo hi : ℝ) (f : ℕ → ℤ)
      (hf : ∀ n : ℕ, 0 < n → ‖(f n : ℂ)‖ ≤ (n.divisors.card : ℝ) ^ 2) (n : ℕ) :
      ‖sample T lo hi f n‖ ≤ (n.divisors.card : ℝ) ^ 2 := by
    rw [hsampleValue]
    split_ifs with hmem _hcut
    · exact hf n (Finset.mem_Icc.mp hmem).1
    · simpa only [norm_zero] using sq_nonneg (n.divisors.card : ℝ)
    · simpa only [norm_zero] using sq_nonneg (n.divisors.card : ℝ)
  have hrowNorm (d : ι) (n : ℕ) :
      ‖arow d n‖ ≤ (n.divisors.card : ℝ) ^ 2 ∧
      ‖brow d n‖ ≤ (n.divisors.card : ℝ) ^ 2 :=
    ⟨hsampleNorm _ _ _ _ (hrawA d) n,
      hsampleNorm _ _ _ _ (fun n _ => hrawB d n) n⟩
  have hscale : ∀ x : ℝ, X₀ ≤ x → ∀ d : ι,
      x / C₀ ≤ Mformal x d * Nformal x d ∧
      Mformal x d * Nformal x d ≤ C₀ * x ∧
      x ^ (1 / 2 - σ) ≤ Nformal x d ∧ Nformal x d ≤ x ^ (1 / 2 : ℝ) := by
    intro x hx d
    by_cases hg : good x d
    · have hgood := hg
      obtain ⟨_hM, _hN, hprodlo, hprodhi, hminlo, hminhi, _hrest⟩ := hgood
      simp only [Mformal, Nformal, ite_eq_left hg]
      have hp : 2 * max (d.1 0) (d.1 1) * (min (d.1 0) (d.1 1) / 2) =
          d.1 0 * d.1 1 := by
        calc
          _ = max (d.1 0) (d.1 1) * min (d.1 0) (d.1 1) := by ring
          _ = _ := max_mul_min _ _
      rw [hp]
      exact ⟨(div_le_div_of_nonneg_left (hxPos x hx).le hCpos
          (le_max_left _ _)).trans hprodlo,
        hprodhi.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hxPos x hx).le),
        hminlo, hminhi⟩
    · simp only [Mformal, Nformal, ite_eq_right hg]
      have hsq : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
        rw [← Real.rpow_add (hxPos x hx)]
        norm_num
      rw [hsq]
      exact ⟨div_le_self (hxPos x hx).le hC₀,
        le_mul_of_one_le_left (hxPos x hx).le hC₀,
        Real.rpow_le_rpow_of_exponent_le (hxOne x hx) (by linarith), le_rfl⟩
  have hsupport : ∀ x : ℝ, X₀ ≤ x → ∀ d : ι,
      (∀ n ∈ (α x d).support,
        (1 / 2 : ℝ) * Mformal x d ≤ (n : ℝ) ∧ (n : ℝ) ≤ C₀ * Mformal x d) ∧
      (∀ n ∈ (β x d).support,
        (1 / 2 : ℝ) * Nformal x d ≤ (n : ℝ) ∧ (n : ℝ) ≤ C₀ * Nformal x d) := by
    intro x _hx d
    by_cases hg : good x d
    · have hgood := hg
      obtain ⟨hM, hN, _hpL, _hpU, _hminL, _hminU, _hMU, _hNU,
          _hz, _hH, _hZl, _hZh, hAl, hAu, hBl, hBu⟩ := hgood
      have hCM := mul_le_mul_of_nonneg_right hC₀four hM.le
      have hCN := mul_le_mul_of_nonneg_right hC₀four hN.le
      have ha (n : ℕ) (hn : n ∈ (arow d).support) :
          d.1 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * d.1 0 := by
        obtain ⟨hl, hu⟩ := hsampleSupport _ _ _ _ n hn
        exact ⟨hAl.trans hl, hu.trans hAu⟩
      have hb (n : ℕ) (hn : n ∈ (brow d).support) :
          d.1 1 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * d.1 1 := by
        obtain ⟨hl, hu⟩ := hsampleSupport _ _ _ _ n hn
        exact ⟨hBl.trans hl, hu.trans hBu⟩
      by_cases hMN : d.1 0 ≤ d.1 1
      · simp only [α, β, Mformal, Nformal, ite_eq_left hg, ite_eq_left hMN,
          min_eq_left hMN, max_eq_right hMN]
        constructor
        · intro n hn
          obtain ⟨hl, hu⟩ := hb n hn
          constructor <;> nlinarith only [hl, hu, hCM, hCN]
        · intro n hn
          obtain ⟨hl, hu⟩ := ha n hn
          constructor <;> nlinarith only [hl, hu, hCM, hCN]
      · have hNM : d.1 1 ≤ d.1 0 := (lt_of_not_ge hMN).le
        simp only [α, β, Mformal, Nformal, ite_eq_left hg, ite_eq_right hMN,
          min_eq_right hNM, max_eq_left hNM]
        constructor
        · intro n hn
          obtain ⟨hl, hu⟩ := ha n hn
          constructor <;> nlinarith only [hl, hu, hCM, hCN]
        · intro n hn
          obtain ⟨hl, hu⟩ := hb n hn
          constructor <;> nlinarith only [hl, hu, hCM, hCN]
    · constructor
      · intro n hn
        exfalso
        simp only [α, ite_eq_right hg, Finsupp.support_zero, Finset.notMem_empty] at hn
      · intro n hn
        exfalso
        simp only [β, ite_eq_right hg, Finsupp.support_zero, Finset.notMem_empty] at hn
  have hcoeff : ∀ x : ℝ, X₀ ≤ x → ∀ d : ι, ∀ n : ℕ,
      ‖α x d n‖ ≤ 1 * (n.divisors.card : ℝ) ^ 2 * (Real.log x) ^ 2 ∧
      ‖β x d n‖ ≤ 1 * (n.divisors.card : ℝ) ^ 2 * (Real.log x) ^ 2 := by
    intro x hx d n
    have hraise : (n.divisors.card : ℝ) ^ 2 ≤
        1 * (n.divisors.card : ℝ) ^ 2 * (Real.log x) ^ 2 := by
      simpa only [one_mul] using le_mul_of_one_le_right
        (sq_nonneg (n.divisors.card : ℝ)) (one_le_pow₀ (hlog x hx))
    have ha := (hrowNorm d n).1.trans hraise
    have hb := (hrowNorm d n).2.trans hraise
    by_cases hg : good x d
    · by_cases hMN : d.1 0 ≤ d.1 1
      · simpa only [α, β, ite_eq_left hg, ite_eq_left hMN] using And.intro hb ha
      · simpa only [α, β, ite_eq_left hg, ite_eq_right hMN] using And.intro ha hb
    · simp only [α, β, ite_eq_right hg, Finsupp.zero_apply, norm_zero, one_mul, and_self]
      exact mul_nonneg (sq_nonneg (n.divisors.card : ℝ)) (sq_nonneg (Real.log x))
  have hSW : ∀ A : ℝ, 0 < A →
      ∃ KSW XSW : ℝ, 0 < KSW ∧ X₀ ≤ XSW ∧
        ∀ x : ℝ, XSW ≤ x → ∀ d : ι,
        ∀ q r a : ℕ, 0 < q → 0 < r → Nat.Coprime a q →
          ‖fullDiscrepancy ((β x d).filter (fun n : ℕ => Nat.Coprime n r)) q a‖ ≤
            KSW * ((q * r).divisors.card : ℝ) ^ 1 * Nformal x d /
              (Real.log x) ^ A := by
    intro A hA
    obtain ⟨Ku, Xu, hKu, _hXu, hunit⟩ :=
      harmanA_unit_minFac_interval_all_moduli_siegelWalfisz η 2 1 2 A
        hη (by norm_num) (by norm_num) (by norm_num) hA
    obtain ⟨Ka, Xa, hKa, _hXa, hnamed⟩ :=
      harmanA_named_all_moduli_siegelWalfisz η 2 1 2 A
        hη (by norm_num) (by norm_num) (by norm_num) hA
    obtain ⟨Kb, Xb, hKb, _hXb, hright⟩ :=
      harmanB_primeFactor_band_all_moduli_siegelWalfisz η 2 1 2 A
        hη (by norm_num) (by norm_num) (by norm_num) hA
    let Kall : ℝ := Ku + Ka + Kb
    refine ⟨2 * Kall, max X₀ (max Xu (max Xa Xb)), by dsimp [Kall]; positivity,
      le_max_left _ _, ?_⟩
    intro x hx d q r a hq hr ha
    have hx₀ : X₀ ≤ x := (le_max_left _ _).trans hx
    have hxu : Xu ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
    have hxa : Xa ≤ x := (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
    have hxb : Xb ≤ x := (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
    have hden : 0 ≤ (Real.log x) ^ A :=
      Real.rpow_nonneg (zero_le_one.trans (hlog x hx₀)) A
    have htau : 0 ≤ ((q * r).divisors.card : ℝ) := Nat.cast_nonneg _
    have hKall : 0 < Kall := by dsimp [Kall]; positivity
    have hrelax (K0 S : ℝ) (hK0 : K0 ≤ Kall) (hS : 0 ≤ S) :
        K0 * ((q * r).divisors.card : ℝ) * S / (Real.log x) ^ A ≤
          Kall * ((q * r).divisors.card : ℝ) * S / (Real.log x) ^ A :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK0 htau) hS) hden
    by_cases hg : good x d
    · have hgood := hg
      obtain ⟨hM, hN, _hpL, _hpU, hminL, _hminU, hMU, hNU,
          hz, hH, hZl, hZh, hAl, _hAu, hBl, _hBu⟩ := hgood
      have hML : x ^ η ≤ d.1 0 := by
        have hh := min_le_left (d.1 0) (d.1 1)
        have hpos := Real.rpow_pos_of_pos (hxPos x hx₀) η
        change x ^ η ≤ min (d.1 0) (d.1 1) / 2 at hminL
        linarith
      have hNL : x ^ η ≤ d.1 1 := by
        have hh := min_le_right (d.1 0) (d.1 1)
        have hpos := Real.rpow_pos_of_pos (hxPos x hx₀) η
        change x ^ η ≤ min (d.1 0) (d.1 1) / 2 at hminL
        linarith
      have hArow : ‖fullDiscrepancy ((arow d).filter (fun n : ℕ => Nat.Coprime n r)) q a‖ ≤
          Kall * ((q * r).divisors.card : ℝ) * d.1 0 / (Real.log x) ^ A := by
        by_cases hj : d.2.1 = 0
        · have hh := hunit x hxu (d.1 0) hML hMU (d.1 2) (d.1 3)
            (d.1 6) (d.1 7) (d.1 4) (d.1 5) hz hH
            (by simpa only [one_mul] using hAl) d.2.2.2.1 q hq r hr a ha
          have hu : ‖fullDiscrepancy ((arow d).filter (fun n : ℕ => Nat.Coprime n r)) q a‖ ≤
              Ku * ((q * r).divisors.card : ℝ) * d.1 0 / (Real.log x) ^ A := by
            simpa only [arow, hsampleFilter, rawA, ite_eq_left hj] using hh
          exact hu.trans (hrelax Ku _ (by dsimp [Kall]; linarith) hM.le)
        · let j0 : Fin 2 := if d.2.1 = 1 then 0 else 1
          let P0 : ℕ → ℕ → Prop := fun s h =>
            d.2.2.2.2.2.1 s h ∧ d.1 4 ≤ (h.minFac : ℝ) ∧ (h.minFac : ℝ) ≤ d.1 5
          have hh := hnamed x hxa (d.1 0) hML hMU j0 P0
            d.2.2.2.2.2.2.1 d.2.2.2.2.2.2.2 (d.1 2) (d.1 3)
            (d.1 6) (d.1 7) hz (by linarith) (by simpa only [one_mul] using hAl)
            d.2.2.2.1 q hq r hr a ha
          have hn : ‖fullDiscrepancy ((arow d).filter (fun n : ℕ => Nat.Coprime n r)) q a‖ ≤
              Ka * ((q * r).divisors.card : ℝ) * d.1 0 / (Real.log x) ^ A := by
            by_cases hj1 : d.2.1 = 1
            · simpa only [arow, hsampleFilter, rawA, ite_eq_right hj, j0, P0,
                ite_eq_left hj1, ite_eq_left (rfl : (0 : Fin 2) = 0), ite_true] using hh
            · simpa only [arow, hsampleFilter, rawA, ite_eq_right hj, j0, P0,
                ite_eq_right hj1, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)] using hh
          exact hn.trans (hrelax Ka _ (by dsimp [Kall]; linarith) hM.le)
      have hBrow : ‖fullDiscrepancy ((brow d).filter (fun n : ℕ => Nat.Coprime n r)) q a‖ ≤
          Kall * ((q * r).divisors.card : ℝ) * d.1 1 / (Real.log x) ^ A := by
        have hh := hright x hxb (d.1 1) hNL hNU d.2.2.1 d.2.2.2.2.1
          (d.1 8) (d.1 9) (d.1 10) (d.1 11) (d.1 12) (d.1 13)
          (d.1 14) (d.1 15) hZl hZh (by simpa only [one_mul] using hBl)
          q hq r hr a ha
        have hb : ‖fullDiscrepancy ((brow d).filter (fun n : ℕ => Nat.Coprime n r)) q a‖ ≤
            Kb * ((q * r).divisors.card : ℝ) * d.1 1 / (Real.log x) ^ A := by
          simpa only [brow, hsampleFilter, rawB] using hh
        exact hb.trans (hrelax Kb _ (by dsimp [Kall]; linarith) hN.le)
      by_cases hMN : d.1 0 ≤ d.1 1
      · simp only [β, Nformal, ite_eq_left hg, ite_eq_left hMN, min_eq_left hMN, pow_one]
        convert hArow using 1
        ring
      · have hNM : d.1 1 ≤ d.1 0 := (lt_of_not_ge hMN).le
        simp only [β, Nformal, ite_eq_left hg, ite_eq_right hMN, min_eq_right hNM, pow_one]
        convert hBrow using 1
        ring
    · simp only [β, Nformal, ite_eq_right hg, Finsupp.filter_zero, fullDiscrepancy,
        progressionMass, reducedMass, Finsupp.support_zero, Finset.sum_empty,
        zero_div, sub_self, norm_zero]
      exact div_nonneg
        (mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * Kall)
          (pow_nonneg htau _)) (Real.rpow_nonneg (hxPos x hx₀).le _)) hden
  intro A hA
  obtain ⟨K, X, hK, hX, hdist⟩ :=
    hsource Mformal Nformal α β (1 / 2) C₀ 1 X₀ 2 1 (by norm_num) hC₀ (by norm_num) hX₀
      hscale hsupport hcoeff hSW A hA
  refine ⟨K, X, hK, hX, ?_⟩
  intro x hx M N hM hN hpL hpU hminL hminU hMU hNU jA jB bA bB P L U
    z H fLo fHi loA hiA slo shi Zlo Zhi Lsd Usd loB hiB
    hz hH hZl hZh hAl hAu hBl hBu A0 B0 α0 β0 I hI a ha
  let v : Fin 16 → ℝ := ![M, N, z, H, fLo, fHi, loA, hiA,
    slo, shi, Zlo, Zhi, Lsd, Usd, loB, hiB]
  let d : ι := (v, jA, jB, bA, bB, P, L, U)
  have hg : good x d :=
    ⟨hM, hN, hpL, hpU, hminL, hminU, hMU, hNU,
      hz, hH, hZl, hZh, hAl, hAu, hBl, hBu⟩
  have hα : arow d = α0 := rfl
  have hβ : brow d = β0 := rfl
  have hd := hdist x hx d I hI a ha
  have hcomm : finiteConvolution β0 α0 = finiteConvolution α0 β0 := by
    unfold finiteConvolution
    rw [mul_comm]
  by_cases hMN : M ≤ N
  · have hMN' : d.1 0 ≤ d.1 1 := hMN
    simpa only [α, β, ite_eq_left hg, ite_eq_left hMN', hα, hβ, hcomm] using hd
  · have hMN' : ¬ d.1 0 ≤ d.1 1 := hMN
    simpa only [α, β, ite_eq_left hg, ite_eq_right hMN', hα, hβ] using hd

#print axioms harman_literal_box_typeII_coherent_log_saving_of_bilinear

end PrimeGap182Analytic.Harman

end
