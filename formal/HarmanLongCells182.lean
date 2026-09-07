import HarmanLongBoxes182
import HarmanLongGeometry182

/-!
# Actual active feature cells and mixed-cell boundary for the long branch

The signed and positive cells are actual independent-factor convolutions.
Their analytic estimates follow from SourceBilinearEstimate, and the mixed
boundary is controlled by the proved finite feature mesh bounds.

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
theorem sifted_long_active_feature_cell_log_saving_of_bilinear
    (j : ℕ) («ω» δ σ : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ) (hσ : 0 < σ) (hσhalf : σ < 1 / 2)
    (hσa : 1 / 2 - σ < (41361 : ℝ) / 100000)
    (hsource : SourceBilinearEstimate j «ω» δ σ) :
    ∀ E : ℝ, 0 < E →
      ∃ K X : ℝ, 0 < K ∧ Real.exp 100 ≤ X ∧
        ∀ x : ℝ, X ≤ x → ∀ l : Fin 6,
        let H := x ^ ((41361 : ℝ) / 100000)
        let z := x ^ ((8639 : ℝ) / 50000)
        let M0 := x ^ (1 - (34941 : ℝ) / 100000)
        let S := x ^ (1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000)
        let Bthreshold := x ^ ((58639 : ℝ) / 100000)
        let U := ⌊8 * x⌋₊
        let C := Finset.Icc 1 U
        let A := (Fintype.piFinset (fun _ : Fin 3 => C)).filter (fun a : Fin 3 → ℕ =>
          let u := a 0
          let v := a 1
          let h := a 2
          let r := u * v
          let m := r * h
          m ≤ U ∧
            (match l.val with
              | 0 => u = 1 ∧ v = 1
              | 1 | 2 | 3 => u = 1 ∧ v.Prime ∧ z ≤ (v : ℝ)
              | 4 => u.Prime ∧ v.Prime ∧ z ≤ (u : ℝ) ∧ u < v
              | _ => u.Prime ∧ v.Prime ∧ z ≤ (u : ℝ) ∧ u ≤ v) ∧
            (r : ℝ) < H ∧ 1 < h ∧ ((max 1 (h.primeFactors.sup id) : ℕ) : ℝ) < z ∧
            ((m / h.minFac : ℕ) : ℝ) < H ∧ H ≤ (m : ℝ))
        let B := (Fintype.piFinset (fun _ : Fin 3 => C)).filter (fun b : Fin 3 → ℕ =>
          let s := b 0
          let d := b 1
          let k := b 2
          let n := s * d * k
          n ≤ U ∧ (if l.val ≤ 1 then s = 1 else s.Prime ∧ z ≤ (s : ℝ)) ∧ (s : ℝ) < S)
        let feature (a b : Fin 3 → ℕ) : Fin 7 → ℕ :=
          ![a 0 * a 1 * a 2, (a 2).minFac, if l.val ≤ 3 then a 1 else a 0,
            b 0 * b 1 * b 2, b 0 * b 1, max 1 ((b 1).primeFactors.sup id), b 0]
        let Good (f : Fin 7 → ℕ) : Prop :=
          f 5 < f 1 ∧ M0 < ((f 0 * f 4 : ℕ) : ℝ) ∧
            x ≤ ((f 0 * f 3 : ℕ) : ℝ) ∧ ((f 0 * f 3 : ℕ) : ℝ) ≤ 2 * x ∧
            match l.val with
            | 2 => f 6 < f 2 ∧ ((f 2 * f 6 : ℕ) : ℝ) < H
            | 3 => f 6 < f 2 ∧ Bthreshold < ((f 2 * f 6 : ℕ) : ℝ)
            | 4 => f 6 < f 2
            | 5 => f 2 < f 6
            | _ => True
        ∀ (L : ℕ) (b : ℕ → ℕ) (lo hi : ℕ → ℝ) (h : ℝ),
          0 < h → h ≤ 1 →
        (∀ n i, 1 ≤ n →
          (b n = i ↔ (i ≤ L ∧ n = i) ∨
            (L < i ∧ L < n ∧ lo i ≤ (n : ℝ) ∧ (n : ℝ) < hi i))) →
        (∀ i, i ≤ L → lo i = (i : ℝ) ∧ hi i = (i : ℝ) + 1) →
        (∀ n, 1 ≤ n →
          lo (b n) ≤ (n : ℝ) ∧
            (n : ℝ) ≤ (if b n ≤ L then lo (b n) else hi (b n)) ∧
            (if b n ≤ L then lo (b n) else hi (b n)) ≤ (1 + h) * lo (b n)) →
        ∀ c : Fin 7 → ℕ,
        (∃ a ∈ A, ∃ d ∈ B, Good (feature a d) ∧
          ∀ r : Fin 7, b (feature a d r) = c r) →
        ∀ positive : Bool,
        let w : (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℂ := fun a d =>
          ((if positive then |ArithmeticFunction.moebius (a 2)|
            else ArithmeticFunction.moebius (a 2) : ℤ) : ℂ) *
          ((if positive then |ArithmeticFunction.moebius (d 1)|
            else ArithmeticFunction.moebius (d 1) : ℤ) : ℂ)
        let F : ℕ →₀ ℂ := ∑ a ∈ A, ∑ d ∈ B,
          Finsupp.single (feature a d 0 * feature a d 3)
            (if ∀ r : Fin 7, b (feature a d r) = c r then w a d else 0)
        ∀ I : Finset ℕ, (∀ p ∈ I, Nat.Prime p) →
        ∀ a : ℕ, Nat.Coprime a (∏ p ∈ I, p) →
          (∑ q ∈ (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
              q ∣ (∏ p ∈ I, p) ∧
                Nonempty (DenseDivisibilityWitness
                  ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩
                  j q)),
            ‖fullDiscrepancy F q a‖) ≤ K * x / (Real.log x) ^ E := by
  have hgeometry (x σ h M N m n : ℝ)
      (hx : 1 < x) (hx8 : 8 ≤ x)
      (hthreshold : 4 ≤ x ^ ((41361 : ℝ) / 100000 - (1 / 2 - σ)))
      (hh : h ≤ 1) (hM : 0 < M) (hN : 0 < N)
      (hm : M ≤ m ∧ m ≤ (1 + h) * M)
      (hn : N ≤ n ∧ n ≤ (1 + h) * N)
      (hprod : x ≤ m * n ∧ m * n ≤ 2 * x)
      (hma : x ^ ((41361 : ℝ) / 100000) ≤ m)
      (hna : x ^ ((41361 : ℝ) / 100000) ≤ n)
      (hmcap : m ≤ 2 * x) (hncap : n ≤ 2 * x) :
      x / 16 ≤ M * N ∧ M * N ≤ 16 * x ∧
        x ^ (1 / 2 - σ) ≤ min M N / 2 ∧
        min M N / 2 ≤ x ^ (1 / 2 : ℝ) ∧ M ≤ x ^ 2 ∧ N ≤ x ^ 2 := by
    clear * - x σ h M N m n hx hx8 hthreshold hh hM hN hm hn hprod hma hna hmcap hncap
    let a : ℝ := 41361 / 100000
    let c : ℝ := 1 / 2 - σ
    change 4 ≤ x ^ (a - c) at hthreshold
    change x ^ a ≤ m at hma
    change x ^ a ≤ n at hna
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hm0 : 0 < m := hM.trans_le hm.1
    have hn0 : 0 < n := hN.trans_le hn.1
    have hmhi : m ≤ 2 * M := hm.2.trans
      (mul_le_mul_of_nonneg_right (by linarith only [hh] : 1 + h ≤ 2) hM.le)
    have hnhi : n ≤ 2 * N := hn.2.trans
      (mul_le_mul_of_nonneg_right (by linarith only [hh] : 1 + h ≤ 2) hN.le)
    have hMN0 : 0 < M * N := mul_pos hM hN
    have hMNhi : M * N ≤ 2 * x :=
      (mul_le_mul hm.1 hn.1 hN.le hm0.le).trans hprod.2
    have hmnhi : m * n ≤ 4 * (M * N) := by
      calc
        m * n ≤ (2 * M) * (2 * N) :=
          mul_le_mul hmhi hnhi hn0.le (by positivity)
        _ = 4 * (M * N) := by ring
    have hpower : 4 * x ^ c ≤ x ^ a := by
      calc
        4 * x ^ c ≤ x ^ (a - c) * x ^ c :=
          mul_le_mul_of_nonneg_right hthreshold (Real.rpow_pos_of_pos hx0 c).le
        _ = x ^ a := by
          rw [← Real.rpow_add hx0]
          congr 1
          ring
    have hminlo : x ^ c ≤ min M N / 2 := by
      have hlow : 2 * x ^ c ≤ min M N :=
        le_min (by linarith only [hpower.trans hma, hmhi])
          (by linarith only [hpower.trans hna, hnhi])
      linarith only [hlow]
    have hmin0 : 0 ≤ min M N := le_min hM.le hN.le
    have hminsq : (min M N) ^ 2 ≤ M * N := by
      simpa only [pow_two] using
        mul_le_mul (min_le_left M N) (min_le_right M N) hmin0 hM.le
    have hminhi : min M N / 2 ≤ x ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      apply Real.le_sqrt_of_sq_le
      nlinarith only [hminsq, hMNhi, hx0]
    have htwo : 2 * x ≤ x ^ 2 := by
      have hx2 : (2 : ℝ) ≤ x := by linarith only [hx8]
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hx2 hx0.le
    exact ⟨by nlinarith only [hprod.1.trans hmnhi, hMN0],
      by nlinarith only [hMNhi, hx0],
      hminlo, hminhi, hm.1.trans (hmcap.trans htwo), hn.1.trans (hncap.trans htwo)⟩
  have hpush (U : ℕ) (P : ℕ → ℕ → ℕ → Prop)
      [∀ u v t, Decidable (P u v t)] (w : ℕ → ℕ → ℕ → ℂ) :
      (∑ v ∈ (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc 1 U)).filter
          (fun v => v 0 * v 1 * v 2 ≤ U ∧ P (v 0) (v 1) (v 2)),
        Finsupp.single (v 0 * v 1 * v 2) (w (v 0) (v 1) (v 2))) =
        ∑ n ∈ Finset.Icc 1 U, Finsupp.single n
          (∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
            if P aa.1 bb.1 bb.2 then w aa.1 bb.1 bb.2 else 0) := by
    clear * - U P w
    classical
    calc
      _ = ∑ v ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc 1 U),
          Finsupp.single (∏ j, v j)
            (if (∏ j, v j) ≤ U then
              if P (v 0) (v 1) (v 2) then w (v 0) (v 1) (v 2) else 0
            else 0) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro v _
        simp only [Fin.prod_univ_three]
        by_cases hcut : v 0 * v 1 * v 2 ≤ U <;>
          by_cases hp : P (v 0) (v 1) (v 2) <;> simp [hcut, hp]
      _ = _ := three_positive_factor_pushforward U
        (fun a b c => if P a b c then w a b c else 0)
  have hresize (U : ℕ) (M a b : ℝ)
      (hMU : ⌊2 * M⌋₊ ≤ U) (hb : b ≤ 2 * M) (w : ℕ → ℂ) :
      (∑ n ∈ Finset.Icc 1 U,
        Finsupp.single n (if a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b then w n else 0)) =
        ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊,
          Finsupp.single n (if a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b then w n else 0) := by
    clear * - U M a b hMU hb w
    classical
    symm
    apply Finset.sum_subset
    · intro n hn
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hMU⟩
    · intro n hn hnsmall
      have hnot : ¬(a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b) := by
        intro hband
        exact hnsmall (Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp hn).1, Nat.le_floor (hband.2.trans hb)⟩)
      simp [hnot]
  have hunitFiber (n : ℕ) (hn : 0 < n) (W : ℕ → ℂ) (P : ℕ → Prop)
      [DecidablePred P] :
      (∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
        if aa.1 = 1 ∧ bb.1 = 1 ∧ P bb.2 then W bb.2 else 0) =
        if P n then W n else 0 := by
    clear * - n hn W P
    have hmem : (1, n) ∈ n.divisorsAntidiagonal :=
      Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul n, hn.ne'⟩
    have hfirstNe (v : ℕ × ℕ) (hv : v ∈ n.divisorsAntidiagonal)
        (hne : v ≠ (1, n)) : v.1 ≠ 1 := by
      intro hfirst
      apply hne
      exact Prod.ext hfirst (by
        simpa [hfirst] using (Nat.mem_divisorsAntidiagonal.mp hv).1)
    calc
      _ = ∑ bb ∈ n.divisorsAntidiagonal,
          if bb.1 = 1 ∧ P bb.2 then W bb.2 else 0 := by
        refine (Finset.sum_eq_single_of_mem (1, n) hmem ?_).trans ?_
        · intro aa haa hne
          apply Finset.sum_eq_zero
          intro bb _
          exact ite_eq_right (fun h => hfirstNe aa haa hne h.1)
        · simp
      _ = if P n then W n else 0 := by
        refine (Finset.sum_eq_single_of_mem (1, n) hmem ?_).trans ?_
        · intro bb hbb hne
          exact ite_eq_right (fun h => hfirstNe bb hbb hne h.1)
        · simp
  have hBpredicate (l : Fin 6) (z S : ℝ) (b : ℕ → ℕ) (c : Fin 7 → ℕ)
      (lower upper : ℕ → ℕ)
      (hiff : ∀ n i : ℕ, 1 ≤ n →
        (b n = i ↔ lower i ≤ n ∧ n ≤ upper i))
      (hlo : ∀ i : ℕ, 1 ≤ lower i)
      (s d k : ℕ) (hs : 0 < s) (hd : 0 < d) (hk : 0 < k) :
      ((if l.val ≤ 1 then s = 1 else s.Prime ∧ z ≤ (s : ℝ)) ∧
        (s : ℝ) < S ∧ b (s * d * k) = c 3 ∧ b (s * d) = c 4 ∧
        b (max 1 (d.primeFactors.sup id)) = c 5 ∧ b s = c 6) ↔
      ((lower (c 3) : ℝ) ≤ ((s * d * k : ℕ) : ℝ) ∧
        ((s * d * k : ℕ) : ℝ) ≤ (upper (c 3) : ℝ)) ∧
      ((if (if l.val ≤ 1 then (0 : Fin 2) else 1) = 0
          then s = 1 else s.Prime) ∧
        max (lower (c 6) : ℝ) (if l.val ≤ 1 then 0 else z) ≤ (s : ℝ) ∧
        (s : ℝ) ≤ min (upper (c 6) : ℝ) ((⌈S⌉₊ - 1 : ℕ) : ℝ) ∧
        (lower (c 5) : ℝ) ≤ ((max 1 (d.primeFactors.sup id) : ℕ) : ℝ) ∧
        ((max 1 (d.primeFactors.sup id) : ℕ) : ℝ) <
          ((upper (c 5) + 1 : ℕ) : ℝ) ∧
        (lower (c 4) : ℝ) ≤ ((s * d : ℕ) : ℝ) ∧
        ((s * d : ℕ) : ℝ) ≤ (upper (c 4) : ℝ)) := by
    clear * - l z S b c lower upper hiff hlo s d k hs hd hk
    have hbin (m i : ℕ) (hm : 1 ≤ m) :
        b m = i ↔ (lower i : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (upper i : ℝ) := by
      simpa only [Nat.cast_le] using hiff m i hm
    have hscut : (s : ℝ) < S ↔ (s : ℝ) ≤ ((⌈S⌉₊ - 1 : ℕ) : ℝ) := by
      rw [← Nat.lt_ceil, Nat.cast_le]
      omega
    have hPmax :
        ((max 1 (d.primeFactors.sup id) : ℕ) : ℝ) ≤ (upper (c 5) : ℝ) ↔
        ((max 1 (d.primeFactors.sup id) : ℕ) : ℝ) <
          ((upper (c 5) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show max 1 (d.primeFactors.sup id) ≤ upper (c 5) ↔
        max 1 (d.primeFactors.sup id) < upper (c 5) + 1 by omega)
    have hloR : (0 : ℝ) ≤ (lower (c 6) : ℝ) := by
      exact_mod_cast (Nat.zero_le 1).trans (hlo (c 6))
    rw [hscut,
      hbin (s * d * k) (c 3) (Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos hs hd) hk)),
      hbin (s * d) (c 4) (Nat.succ_le_of_lt (Nat.mul_pos hs hd)),
      hbin (max 1 (d.primeFactors.sup id)) (c 5) (le_max_left _ _),
      hbin s (c 6) (Nat.succ_le_of_lt hs), ← hPmax]
    by_cases hl : l.val ≤ 1
    · simp only [ite_eq_left hl]
      rw [max_eq_left hloR]
      norm_num [le_min_iff]; tauto
    · simp only [ite_eq_right hl]
      norm_num [max_le_iff, le_min_iff]; tauto
  have hAunitPredicate (H z : ℝ) (hH : 1 < H) (b : ℕ → ℕ)
      (c : Fin 7 → ℕ) (lower upper : ℕ → ℕ)
      (hiff : ∀ n i : ℕ, 1 ≤ n →
        (b n = i ↔ lower i ≤ n ∧ n ≤ upper i))
      (hlabel : b 1 = c 2) (u v t : ℕ) :
      (((u = 1 ∧ v = 1) ∧ ((u * v : ℕ) : ℝ) < H ∧ 1 < t ∧
          ((max 1 (t.primeFactors.sup id) : ℕ) : ℝ) < z ∧
          ((u * v * t / t.minFac : ℕ) : ℝ) < H ∧
          H ≤ ((u * v * t : ℕ) : ℝ)) ∧
        (b (u * v * t) = c 0 ∧ b t.minFac = c 1 ∧ b v = c 2)) ↔
      u = 1 ∧ v = 1 ∧
        (b t = c 0 ∧
          ((1 < t ∧ ((max 1 (t.primeFactors.sup id) : ℕ) : ℝ) < z ∧
              ((t / t.minFac : ℕ) : ℝ) < H ∧ H ≤ (t : ℝ)) ∧
            (lower (c 1) : ℝ) ≤ (t.minFac : ℝ) ∧
            (t.minFac : ℝ) ≤ (upper (c 1) : ℝ))) := by
    clear * - H z hH b c lower upper hiff hlabel u v t
    have hminBin : b t.minFac = c 1 ↔
        (lower (c 1) : ℝ) ≤ (t.minFac : ℝ) ∧
        (t.minFac : ℝ) ≤ (upper (c 1) : ℝ) := by
      simpa only [Nat.cast_le] using
        hiff t.minFac (c 1) (Nat.succ_le_of_lt (Nat.minFac_pos t))
    by_cases hu : u = 1
    · subst u
      by_cases hv : v = 1
      · subst v
        simp [hH, hlabel, hminBin]; tauto
      · simp [hv]
    · simp [hu]
  intro E hE
  obtain ⟨K, X₀, hK, hX₀, htypeII⟩ :=
    harman_literal_box_typeII_coherent_log_saving_of_bilinear j «ω» δ σ 16
      hω hδ hσ (by norm_num) hσhalf hsource E hE
  have hpower : ∀ᶠ x : ℝ in Filter.atTop,
      4 ≤ x ^ ((41361 : ℝ) / 100000 - (1 / 2 - σ)) :=
    (tendsto_rpow_atTop (sub_pos.mpr hσa)).eventually (Filter.eventually_ge_atTop 4)
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp hpower
  refine ⟨K, max X₀ (max 8 X₁), hK, hX₀.trans (le_max_left _ _), ?_⟩
  intro x hx l H z M0 S Bthreshold U C A B feature Good
    L b lo hi h hh hh1 hcell hlowends hends c hactive positive w F I hI a ha
  have hx₀ : X₀ ≤ x := (le_max_left _ _).trans hx
  have hx8 : 8 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hx1 : 1 < x := by linarith only [hx8]
  have hxpos : 0 < x := zero_lt_one.trans hx1
  have hpow := hX₁ x ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  have hz : 0 < z := Real.rpow_pos_of_pos hxpos _
  have hH : 1 < H := Real.one_lt_rpow hx1 (by norm_num)
  let lower : ℕ → ℕ := fun i => max 1
    (if i ≤ L then i else max (L + 1) ⌈lo i⌉₊)
  let upper : ℕ → ℕ := fun i => if i ≤ L then i else ⌈hi i⌉₊ - 1
  have hclosed := harman_feature_cell_closed_interval L b lo hi hcell hlowends
  change (∀ i, 1 ≤ lower i) ∧
    (∀ n i, 1 ≤ n → (b n = i ↔ lower i ≤ n ∧ n ≤ upper i)) ∧
    (∀ n i, 1 ≤ n → b n = i →
      lo i ≤ (lower i : ℝ) ∧ (lower i : ℝ) ≤ (n : ℝ) ∧
      (n : ℝ) ≤ (upper i : ℝ) ∧
      (upper i : ℝ) ≤ (if i ≤ L then lo i else hi i)) at hclosed
  obtain ⟨hlower, hcellNat, hcellBounds⟩ := hclosed
  have hcellReal (n : ℕ) (r : Fin 7) (hn : 1 ≤ n) :
      b n = c r ↔ (lower (c r) : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (upper (c r) : ℝ) := by
    simpa only [Nat.cast_le] using hcellNat n (c r) hn
  obtain ⟨a₀, ha₀, d₀, hd₀, hgood, hkey⟩ := hactive
  obtain ⟨haT, _haU, haCase, _haR, haH, haCap, haPrevious, haCrossing⟩ :=
    Finset.mem_filter.mp ha₀
  obtain ⟨hdT, _hdU, _hdCase, _hdSmall⟩ := Finset.mem_filter.mp hd₀
  have haPos (i : Fin 3) : 1 ≤ a₀ i :=
    (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp haT i)).1
  have hdPos (i : Fin 3) : 1 ≤ d₀ i :=
    (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hdT i)).1
  let m₀ : ℕ := a₀ 0 * a₀ 1 * a₀ 2
  let n₀ : ℕ := d₀ 0 * d₀ 1 * d₀ 2
  have hmpos : 0 < m₀ := by
    dsimp only [m₀]
    exact Nat.mul_pos (Nat.mul_pos (haPos 0) (haPos 1)) (haPos 2)
  have hnpos : 0 < n₀ := by
    dsimp only [n₀]
    exact Nat.mul_pos (Nat.mul_pos (hdPos 0) (hdPos 1)) (hdPos 2)
  obtain ⟨_hprime, hlong, hprodLo, hprodHi, _hextra⟩ := hgood
  change M0 < ((m₀ * (d₀ 0 * d₀ 1) : ℕ) : ℝ) at hlong
  change x ≤ ((m₀ * n₀ : ℕ) : ℝ) at hprodLo
  change ((m₀ * n₀ : ℕ) : ℝ) ≤ 2 * x at hprodHi
  have hproduct : x ≤ (m₀ : ℝ) * (n₀ : ℝ) ∧ (m₀ : ℝ) * (n₀ : ℝ) ≤ 2 * x := by
    simpa only [Nat.cast_mul] using And.intro hprodLo hprodHi
  have hprevious : ((a₀ 0 * a₀ 1 * a₀ 2 : ℕ) : ℝ) /
      ((a₀ 2).minFac : ℝ) < H := by
    rw [← Nat.cast_div_charZero
      (dvd_mul_of_dvd_right (Nat.minFac_dvd (a₀ 2)) (a₀ 0 * a₀ 1))]
    exact haPrevious
  have hproductEq :
      a₀ 0 * a₀ 1 * d₀ 0 * a₀ 2 * d₀ 1 * d₀ 2 = m₀ * n₀ := by
    dsimp only [m₀, n₀]
    ring
  have hlongEq :
      a₀ 0 * a₀ 1 * d₀ 0 * a₀ 2 * d₀ 1 = m₀ * (d₀ 0 * d₀ 1) := by
    dsimp only [m₀]
    ring
  have hscales := restricted_harman_long_source_scales x hx1
    (a₀ 0 * a₀ 1) (d₀ 0) (a₀ 2) (d₀ 1) (d₀ 2)
    (hdPos 0) haH (hdPos 1) (hdPos 2) haCap hprevious haCrossing
    (by simpa only [hproductEq] using And.intro hprodLo hprodHi)
    (by simpa only [hlongEq] using hlong)
  have hma : x ^ ((41361 : ℝ) / 100000) ≤ (m₀ : ℝ) := hscales.1
  have hna : x ^ ((41361 : ℝ) / 100000) ≤ (n₀ : ℝ) := hscales.2.2.1.le
  have hmcap : (m₀ : ℝ) ≤ 2 * x :=
    (le_mul_of_one_le_right (Nat.cast_nonneg m₀) (by exact_mod_cast hnpos)).trans hproduct.2
  have hncap : (n₀ : ℝ) ≤ 2 * x :=
    (le_mul_of_one_le_left (Nat.cast_nonneg n₀) (by exact_mod_cast hmpos)).trans hproduct.2
  have hkm : b m₀ = c 0 := hkey 0
  have hkn : b n₀ = c 3 := hkey 3
  let M : ℝ := lo (c 0)
  let N : ℝ := lo (c 3)
  have hmEnds := hends m₀ hmpos
  have hnEnds := hends n₀ hnpos
  rw [hkm] at hmEnds
  rw [hkn] at hnEnds
  have hmBox : M ≤ (m₀ : ℝ) ∧ (m₀ : ℝ) ≤ (1 + h) * M :=
    ⟨hmEnds.1, hmEnds.2.1.trans hmEnds.2.2⟩
  have hnBox : N ≤ (n₀ : ℝ) ∧ (n₀ : ℝ) ≤ (1 + h) * N :=
    ⟨hnEnds.1, hnEnds.2.1.trans hnEnds.2.2⟩
  have hM : 0 < M := pos_of_mul_pos_right
    ((by exact_mod_cast hmpos : (0 : ℝ) < m₀).trans_le hmBox.2) (by linarith only [hh])
  have hN : 0 < N := pos_of_mul_pos_right
    ((by exact_mod_cast hnpos : (0 : ℝ) < n₀).trans_le hnBox.2) (by linarith only [hh])
  have hmClosed := hcellBounds m₀ (c 0) hmpos hkm
  have hnClosed := hcellBounds n₀ (c 3) hnpos hkn
  have hAl : M ≤ (lower (c 0) : ℝ) := hmClosed.1
  have hAu : (upper (c 0) : ℝ) ≤ 2 * M := by
    have hup := hmClosed.2.2.2.trans hmEnds.2.2
    have hlast := mul_le_mul_of_nonneg_right
      (by linarith only [hh1] : 1 + h ≤ 2) hM.le
    exact hup.trans hlast
  have hBl : N ≤ (lower (c 3) : ℝ) := hnClosed.1
  have hBu : (upper (c 3) : ℝ) ≤ 2 * N := by
    have hup := hnClosed.2.2.2.trans hnEnds.2.2
    exact hup.trans (mul_le_mul_of_nonneg_right
      (by linarith only [hh1] : 1 + h ≤ 2) hN.le)
  have hMU : ⌊2 * M⌋₊ ≤ U := Nat.floor_mono (by
    have hm := hmBox.1.trans hmcap
    linarith only [hm, hxpos])
  have hNU : ⌊2 * N⌋₊ ≤ U := Nat.floor_mono (by
    have hn := hnBox.1.trans hncap
    linarith only [hn, hxpos])
  obtain ⟨hpLo, hpHi, hminLo, hminHi, hMpow, hNpow⟩ :=
    hgeometry x σ h M N (m₀ : ℝ) (n₀ : ℝ) hx1 hx8 hpow hh1 hM hN
      hmBox hnBox hproduct hma hna hmcap hncap
  let caseA : ℕ → ℕ → Prop := fun u v =>
    match l.val with
    | 0 => u = 1 ∧ v = 1
    | 1 | 2 | 3 => u = 1 ∧ v.Prime ∧ z ≤ (v : ℝ)
    | 4 => u.Prime ∧ v.Prime ∧ z ≤ (u : ℝ) ∧ u < v
    | _ => u.Prime ∧ v.Prime ∧ z ≤ (u : ℝ) ∧ u ≤ v
  let baseA : ℕ → ℕ → ℕ → Prop := fun u v t =>
    caseA u v ∧ ((u * v : ℕ) : ℝ) < H ∧ 1 < t ∧
      ((max 1 (t.primeFactors.sup id) : ℕ) : ℝ) < z ∧
      ((u * v * t / t.minFac : ℕ) : ℝ) < H ∧ H ≤ ((u * v * t : ℕ) : ℝ)
  let baseB : ℕ → ℕ → ℕ → Prop := fun s _ _ =>
    (if l.val ≤ 1 then s = 1 else s.Prime ∧ z ≤ (s : ℝ)) ∧ (s : ℝ) < S
  let labelsA : (Fin 3 → ℕ) → Prop := fun v =>
    b (v 0 * v 1 * v 2) = c 0 ∧ b ((v 2).minFac) = c 1 ∧
      b (if l.val ≤ 3 then v 1 else v 0) = c 2
  let labelsB : (Fin 3 → ℕ) → Prop := fun v =>
    b (v 0 * v 1 * v 2) = c 3 ∧ b (v 0 * v 1) = c 4 ∧
      b (max 1 ((v 1).primeFactors.sup id)) = c 5 ∧ b (v 0) = c 6
  let PA : ℕ → ℕ → ℕ → Prop := fun u v t =>
    baseA u v t ∧ b (u * v * t) = c 0 ∧ b t.minFac = c 1 ∧
      b (if l.val ≤ 3 then v else u) = c 2
  let PB : ℕ → ℕ → ℕ → Prop := fun s d k =>
    baseB s d k ∧ b (s * d * k) = c 3 ∧ b (s * d) = c 4 ∧
      b (max 1 (d.primeFactors.sup id)) = c 5 ∧ b s = c 6
  let Ac := A.filter labelsA
  let Bc := B.filter labelsB
  let wZ : ℕ → ℤ := fun t =>
    if positive then |ArithmeticFunction.moebius t| else ArithmeticFunction.moebius t
  let wC : ℕ → ℂ := fun t => (wZ t : ℂ)
  let jA : Fin 3 := if l.val = 0 then 0 else if l.val ≤ 3 then 1 else 2
  let jB : Fin 2 := if l.val ≤ 1 then 0 else 1
  let P : ℕ → ℕ → Prop := fun u _ =>
    if l.val ≤ 3 then True else
      (lower (c 2) : ℝ) ≤ (u : ℝ) ∧ (u : ℝ) ≤ (upper (c 2) : ℝ)
  clear_value (hPdef : P = _)
  let Lfn : ℕ → ℕ → ℝ := fun u _ =>
    if l.val ≤ 3 then (lower (c 2) : ℝ)
    else if l.val = 4 then ((u + 1 : ℕ) : ℝ) else 0
  let Ufn : ℕ → ℕ → ℝ := fun _ _ =>
    if l.val ≤ 3 then (upper (c 2) : ℝ) else (U : ℝ)
  let slo : ℝ := max (lower (c 6) : ℝ) (if l.val ≤ 1 then 0 else z)
  let shi : ℝ := min (upper (c 6) : ℝ) ((⌈S⌉₊ - 1 : ℕ) : ℝ)
  let Zlo : ℝ := (lower (c 5) : ℝ)
  let Zhi : ℝ := ((upper (c 5) + 1 : ℕ) : ℝ)
  let unitP : ℕ → Prop := fun n =>
    (1 < n ∧ ((max 1 (n.primeFactors.sup id) : ℕ) : ℝ) < z ∧
      ((n / n.minFac : ℕ) : ℝ) < H ∧ H ≤ (n : ℝ)) ∧
      (lower (c 1) : ℝ) ≤ (n.minFac : ℝ) ∧
      (n.minFac : ℝ) ≤ (upper (c 1) : ℝ)
  let Acond : ℕ → ℕ → ℕ → ℕ → Prop := fun n u v t =>
    (if jA = 1 then u = 1 else u.Prime ∧ z ≤ (u : ℝ) ∧ u ≤ v) ∧
      v.Prime ∧ z ≤ (v : ℝ) ∧ 1 < t ∧
      ((max 1 (t.primeFactors.sup id) : ℕ) : ℝ) < z ∧
      (P u t ∧ (lower (c 1) : ℝ) ≤ (t.minFac : ℝ) ∧
        (t.minFac : ℝ) ≤ (upper (c 1) : ℝ)) ∧
      Lfn u t ≤ (v : ℝ) ∧ (v : ℝ) ≤ Ufn u t ∧
      ((u * v : ℕ) : ℝ) < H ∧
      ((n / t.minFac : ℕ) : ℝ) < H ∧ H ≤ (n : ℝ)
  let Bcond : ℕ → ℕ → ℕ → Prop := fun s d _ =>
    (if jB = 0 then s = 1 else s.Prime) ∧
      slo ≤ (s : ℝ) ∧ (s : ℝ) ≤ shi ∧
      Zlo ≤ ((max 1 (d.primeFactors.sup id) : ℕ) : ℝ) ∧
      ((max 1 (d.primeFactors.sup id) : ℕ) : ℝ) < Zhi ∧
      (lower (c 4) : ℝ) ≤ ((s * d : ℕ) : ℝ) ∧
      ((s * d : ℕ) : ℝ) ≤ (upper (c 4) : ℝ)
  let A0 : ℕ → ℤ := fun n =>
    if jA = 0 then if unitP n then wZ n else 0 else
      ∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
        if Acond n aa.1 bb.1 bb.2 then wZ bb.2 else 0
  let B0 : ℕ → ℤ := fun n =>
    ∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
      if Bcond aa.1 bb.1 bb.2 then wZ bb.1 else 0
  have hAc :
      Ac = (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc 1 U)).filter
        (fun v => v 0 * v 1 * v 2 ≤ U ∧ PA (v 0) (v 1) (v 2)) := by
    ext v
    simp only [Ac, A, C, PA, baseA, caseA, labelsA,
      Finset.mem_filter, and_assoc]
  have hBc :
      Bc = (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc 1 U)).filter
        (fun v => v 0 * v 1 * v 2 ≤ U ∧ PB (v 0) (v 1) (v 2)) := by
    ext v
    simp only [Bc, B, C, PB, baseB, labelsB, Finset.mem_filter, and_assoc]
  have hnamed (hl : l.val ≠ 0) (u v t : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v)
      (hvU : v ≤ U) :
      (caseA u v ∧ b (if l.val ≤ 3 then v else u) = c 2) ↔
        (if jA = 1 then u = 1 else u.Prime ∧ z ≤ (u : ℝ) ∧ u ≤ v) ∧
          v.Prime ∧ z ≤ (v : ℝ) ∧ P u t ∧
          Lfn u t ≤ (v : ℝ) ∧ (v : ℝ) ≤ Ufn u t := by
    rw [hPdef]
    clear * - hl hu hv hvU hcellReal
    have hvUR : (v : ℝ) ≤ (U : ℝ) := by exact_mod_cast hvU
    fin_cases l
    · exact (hl rfl).elim
    · simp [caseA, jA, Lfn, Ufn, hcellReal v 2 hv, and_assoc]
    · simp [caseA, jA, Lfn, Ufn, hcellReal v 2 hv, and_assoc]
    · simp [caseA, jA, Lfn, Ufn, hcellReal v 2 hv, and_assoc]
    · change (u.Prime ∧ v.Prime ∧ z ≤ (u : ℝ) ∧ u < v) ∧ b u = c 2 ↔
        (u.Prime ∧ z ≤ (u : ℝ) ∧ u ≤ v) ∧ v.Prime ∧ z ≤ (v : ℝ) ∧
          ((lower (c 2) : ℝ) ≤ (u : ℝ) ∧ (u : ℝ) ≤ (upper (c 2) : ℝ)) ∧
          ((u + 1 : ℕ) : ℝ) ≤ (v : ℝ) ∧ (v : ℝ) ≤ (U : ℝ)
      rw [hcellReal u 2 hu]
      constructor
      · rintro ⟨⟨hup, hvp, hzu, huv⟩, hbin⟩
        have huvR : (u : ℝ) ≤ (v : ℝ) := by exact_mod_cast huv.le
        have hsucc : ((u + 1 : ℕ) : ℝ) ≤ (v : ℝ) := by
          exact_mod_cast (Nat.succ_le_iff.mpr huv)
        exact ⟨⟨hup, hzu, huv.le⟩, hvp, hzu.trans huvR, hbin, hsucc, hvUR⟩
      · rintro ⟨⟨hup, hzu, _huv⟩, hvp, _hzv, hbin, hsucc, _hvU⟩
        have huv : u < v := Nat.lt_of_succ_le (by exact_mod_cast hsucc)
        exact ⟨⟨hup, hvp, hzu, huv⟩, hbin⟩
    · change (u.Prime ∧ v.Prime ∧ z ≤ (u : ℝ) ∧ u ≤ v) ∧ b u = c 2 ↔
        (u.Prime ∧ z ≤ (u : ℝ) ∧ u ≤ v) ∧ v.Prime ∧ z ≤ (v : ℝ) ∧
          ((lower (c 2) : ℝ) ≤ (u : ℝ) ∧ (u : ℝ) ≤ (upper (c 2) : ℝ)) ∧
          (0 : ℝ) ≤ (v : ℝ) ∧ (v : ℝ) ≤ (U : ℝ)
      rw [hcellReal u 2 hu]
      constructor
      · rintro ⟨⟨hup, hvp, hzu, huv⟩, hbin⟩
        have huvR : (u : ℝ) ≤ (v : ℝ) := by exact_mod_cast huv
        exact ⟨⟨hup, hzu, huv⟩, hvp, hzu.trans huvR, hbin, Nat.cast_nonneg v, hvUR⟩
      · rintro ⟨⟨hup, hzu, huv⟩, hvp, _hzv, hbin, _hv0, _hvU⟩
        exact ⟨⟨hup, hvp, hzu, huv⟩, hbin⟩
  have hPA_named (hl : l.val ≠ 0) (n u v t : ℕ) (hn : 1 ≤ n) (hnU : n ≤ U)
      (hu : 1 ≤ u) (hv : 1 ≤ v) (_ht : 1 ≤ t) (hproduct : u * v * t = n) :
      PA u v t ↔
        ((lower (c 0) : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (upper (c 0) : ℝ)) ∧
          Acond n u v t := by
    clear * - hl hn hnU hu hv hproduct hnamed hcellReal
    have hvd : v ∣ n := ⟨u * t, by rw [← hproduct]; ring⟩
    have hvU : v ≤ U := (Nat.le_of_dvd hn hvd).trans hnU
    by_cases ht1 : 1 < t
    · have hmin : 1 ≤ t.minFac := (Nat.minFac_prime ht1.ne').pos
      constructor
      · rintro ⟨⟨hcase, hr, _ht, hcap, hprev, hcross⟩, hpc, hmc, hnc⟩
        obtain ⟨hj, hpv, hzv, hP, hL, hU⟩ := (hnamed hl u v t hu hv hvU).mp ⟨hcase, hnc⟩
        have hpbin := (hcellReal n 0 hn).mp (by simpa only [hproduct] using hpc)
        have hmbin := (hcellReal t.minFac 1 hmin).mp hmc
        refine ⟨hpbin, hj, hpv, hzv, ht1, hcap, ⟨hP, hmbin⟩, hL, hU, hr, ?_, ?_⟩
        · simpa only [hproduct] using hprev
        · simpa only [hproduct] using hcross
      · rintro ⟨hpc, hj, hpv, hzv, _ht, hcap, ⟨hP, hml, hmu⟩, hL, hU, hr, hprev, hcross⟩
        obtain ⟨hcase, hnc⟩ := (hnamed hl u v t hu hv hvU).mpr
          ⟨hj, hpv, hzv, hP, hL, hU⟩
        refine ⟨⟨hcase, hr, ht1, hcap, ?_, ?_⟩, ?_, ?_, hnc⟩
        · simpa only [hproduct] using hprev
        · simpa only [hproduct] using hcross
        · simpa only [hproduct] using (hcellReal n 0 hn).mpr hpc
        · exact (hcellReal t.minFac 1 hmin).mpr ⟨hml, hmu⟩
    · simp only [PA, baseA, Acond, ht1, false_and, and_false]
  have hunitLabel (hl : l.val = 0) : b 1 = c 2 := by
    clear * - hl haCase hkey
    have hcase : a₀ 0 = 1 ∧ a₀ 1 = 1 := by simpa only [hl] using haCase
    simpa [feature, hl, hcase.2] using hkey 2
  have hPA_unit (hl : l.val = 0) (u v t : ℕ) :
      PA u v t ↔ u = 1 ∧ v = 1 ∧ (b t = c 0 ∧ unitP t) := by
    clear * - hl hAunitPredicate hH hcellNat hunitLabel
    simpa only [PA, baseA, caseA, unitP, hl, show (0 : ℕ) ≤ 3 from by decide,
      ite_true] using
      hAunitPredicate H z hH b c lower upper hcellNat (hunitLabel hl) u v t
  have hdivData (n : ℕ) (_hn : 1 ≤ n) (aa bb : ℕ × ℕ)
      (haa : aa ∈ n.divisorsAntidiagonal) (hbb : bb ∈ aa.2.divisorsAntidiagonal) :
      1 ≤ aa.1 ∧ 1 ≤ bb.1 ∧ 1 ≤ bb.2 ∧ aa.1 * bb.1 * bb.2 = n := by
    clear * - haa hbb
    refine ⟨Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal haa),
      Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hbb),
      Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hbb), ?_⟩
    rw [Nat.mul_assoc, (Nat.mem_divisorsAntidiagonal.mp hbb).1,
      (Nat.mem_divisorsAntidiagonal.mp haa).1]
  have hAraw (n : ℕ) (hn : 1 ≤ n) (hnU : n ≤ U) :
      (∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
        if PA aa.1 bb.1 bb.2 then wC bb.2 else 0) =
      if (lower (c 0) : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (upper (c 0) : ℝ)
        then (A0 n : ℂ) else 0 := by
    clear * - hn hnU hunitFiber hPA_unit hcellReal hPA_named hdivData
    by_cases hl : l.val = 0
    · calc
        _ = ∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
            if aa.1 = 1 ∧ bb.1 = 1 ∧ (b bb.2 = c 0 ∧ unitP bb.2)
              then wC bb.2 else 0 := by
          apply Finset.sum_congr rfl
          intro aa _
          apply Finset.sum_congr rfl
          intro bb _
          simp only [hPA_unit hl]
        _ = if b n = c 0 ∧ unitP n then wC n else 0 :=
          hunitFiber n hn wC (fun t => b t = c 0 ∧ unitP t)
        _ = _ := by
          simp only [hcellReal n 0 hn]
          simp [A0, jA, hl, wC, Int.cast_ite, ite_and]
    · have hjA : jA ≠ 0 := by
        dsimp only [jA]
        rw [ite_eq_right hl]
        split_ifs <;> decide
      simp only [A0, ite_eq_right hjA, Int.cast_sum, Int.cast_ite, Int.cast_zero]
      by_cases hc : (lower (c 0) : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (upper (c 0) : ℝ)
      · rw [ite_eq_left hc]
        apply Finset.sum_congr rfl
        intro aa haa
        apply Finset.sum_congr rfl
        intro bb hbb
        obtain ⟨hu, hv, ht, hp⟩ := hdivData n hn aa bb haa hbb
        simp only [hPA_named hl n aa.1 bb.1 bb.2 hn hnU hu hv ht hp, hc, true_and, wC]
      · rw [ite_eq_right hc]
        apply Finset.sum_eq_zero
        intro aa haa
        apply Finset.sum_eq_zero
        intro bb hbb
        obtain ⟨hu, hv, ht, hp⟩ := hdivData n hn aa bb haa hbb
        simp only [hPA_named hl n aa.1 bb.1 bb.2 hn hnU hu hv ht hp, hc, false_and, ite_false]
  have hBraw (n : ℕ) (hn : 1 ≤ n) :
      (∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
        if PB aa.1 bb.1 bb.2 then wC bb.1 else 0) =
      if (lower (c 3) : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (upper (c 3) : ℝ)
        then (B0 n : ℂ) else 0 := by
    clear * - hn hdivData hBpredicate hcellNat hlower
    have hpred (aa bb : ℕ × ℕ) (haa : aa ∈ n.divisorsAntidiagonal)
        (hbb : bb ∈ aa.2.divisorsAntidiagonal) :
        PB aa.1 bb.1 bb.2 ↔
          ((lower (c 3) : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (upper (c 3) : ℝ)) ∧
            Bcond aa.1 bb.1 bb.2 := by
      obtain ⟨hu, hv, ht, hp⟩ := hdivData n hn aa bb haa hbb
      simpa only [PB, baseB, Bcond, jB, slo, shi, Zlo, Zhi, hp, and_assoc] using
        hBpredicate l z S b c lower upper hcellNat hlower aa.1 bb.1 bb.2 hu hv ht
    simp only [B0, Int.cast_sum, Int.cast_ite, Int.cast_zero]
    by_cases hc : (lower (c 3) : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (upper (c 3) : ℝ)
    · rw [ite_eq_left hc]
      apply Finset.sum_congr rfl
      intro aa haa
      apply Finset.sum_congr rfl
      intro bb hbb
      simp only [hpred aa bb haa hbb, hc, true_and, wC]
    · rw [ite_eq_right hc]
      apply Finset.sum_eq_zero
      intro aa haa
      apply Finset.sum_eq_zero
      intro bb hbb
      simp only [hpred aa bb haa hbb, hc, false_and, ite_false]
  have hα :
      (∑ v ∈ Ac, Finsupp.single (v 0 * v 1 * v 2) (wC (v 2))) =
        ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊,
          Finsupp.single n
            (if (lower (c 0) : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (upper (c 0) : ℝ)
              then (A0 n : ℂ) else 0) := by
    clear * - hAc hpush hAraw hresize hMU hAu
    rw [hAc]
    calc
      _ = ∑ n ∈ Finset.Icc 1 U, Finsupp.single n
          (∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
            if PA aa.1 bb.1 bb.2 then wC bb.2 else 0) :=
        hpush U PA (fun _ _ t => wC t)
      _ = ∑ n ∈ Finset.Icc 1 U, Finsupp.single n
          (if (lower (c 0) : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (upper (c 0) : ℝ)
            then (A0 n : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact congrArg (Finsupp.single n)
          (hAraw n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2)
      _ = _ := hresize U M (lower (c 0) : ℝ) (upper (c 0) : ℝ) hMU hAu
        (fun n => (A0 n : ℂ))
  have hβ :
      (∑ v ∈ Bc, Finsupp.single (v 0 * v 1 * v 2) (wC (v 1))) =
        ∑ n ∈ Finset.Icc 1 ⌊2 * N⌋₊,
          Finsupp.single n
            (if (lower (c 3) : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (upper (c 3) : ℝ)
              then (B0 n : ℂ) else 0) := by
    clear * - hBc hpush hBraw hresize hNU hBu
    rw [hBc]
    calc
      _ = ∑ n ∈ Finset.Icc 1 U, Finsupp.single n
          (∑ aa ∈ n.divisorsAntidiagonal, ∑ bb ∈ aa.2.divisorsAntidiagonal,
            if PB aa.1 bb.1 bb.2 then wC bb.1 else 0) :=
        hpush U PB (fun _ d _ => wC d)
      _ = ∑ n ∈ Finset.Icc 1 U, Finsupp.single n
          (if (lower (c 3) : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (upper (c 3) : ℝ)
            then (B0 n : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact congrArg (Finsupp.single n) (hBraw n (Finset.mem_Icc.mp hn).1)
      _ = _ := hresize U N (lower (c 3) : ℝ) (upper (c 3) : ℝ) hNU hBu
        (fun n => (B0 n : ℂ))
  have hlabels (v d : Fin 3 → ℕ) :
      (∀ r : Fin 7, b (feature v d r) = c r) ↔ labelsA v ∧ labelsB d := by
    constructor
    · intro hk
      exact ⟨⟨hk 0, hk 1, hk 2⟩, hk 3, hk 4, hk 5, hk 6⟩
    · rintro ⟨⟨h0, h1, h2⟩, h3, h4, h5, h6⟩ r
      fin_cases r <;> assumption
  have hrectangle (A B : Finset (Fin 3 → ℕ))
      (p q : (Fin 3 → ℕ) → Prop) [DecidablePred p] [DecidablePred q]
      (wa wb : (Fin 3 → ℕ) → ℂ) :
      (∑ v ∈ A, ∑ d ∈ B,
        Finsupp.single ((v 0 * v 1 * v 2) * (d 0 * d 1 * d 2))
          (if p v ∧ q d then wa v * wb d else 0)) =
        finiteConvolution
          (∑ v ∈ A.filter p, Finsupp.single (v 0 * v 1 * v 2) (wa v))
          (∑ d ∈ B.filter q, Finsupp.single (d 0 * d 1 * d 2) (wb d)) := by
    clear * - A B p q wa wb
    rw [finiteConvolution_indexed_pushforward]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hp : p v
    · simp only [hp, true_and, ite_true]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hq : q d <;> simp [hq]
    · simp only [hp, false_and, ite_false, Finsupp.single_zero, Finset.sum_const_zero]
  have hF : F = finiteConvolution
      (∑ v ∈ Ac, Finsupp.single (v 0 * v 1 * v 2) (wC (v 2)))
      (∑ d ∈ Bc, Finsupp.single (d 0 * d 1 * d 2) (wC (d 1))) := by
    clear * - hrectangle hlabels
    have hproduct (v d : Fin 3 → ℕ) :
        feature v d 0 * feature v d 3 =
          (v 0 * v 1 * v 2) * (d 0 * d 1 * d 2) := rfl
    have hweight (v d : Fin 3 → ℕ) : w v d = wC (v 2) * wC (d 1) := rfl
    simpa only [F, Ac, Bc, hlabels, hproduct, hweight] using
      hrectangle A B labelsA labelsB (fun v => wC (v 2)) (fun d => wC (d 1))
  have hZlo : 0 < Zlo := by
    dsimp only [Zlo]
    exact_mod_cast zero_lt_one.trans_le (hlower (c 5))
  have hZhi : 0 < Zhi := by
    dsimp only [Zhi]
    exact_mod_cast Nat.succ_pos (upper (c 5))
  have hbound := htypeII x hx₀ M N hM hN hpLo hpHi hminLo hminHi
    (by simpa only [Real.rpow_two] using hMpow)
    (by simpa only [Real.rpow_two] using hNpow)
    jA jB positive positive P Lfn Ufn z H
    (lower (c 1) : ℝ) (upper (c 1) : ℝ)
    (lower (c 0) : ℝ) (upper (c 0) : ℝ)
    slo shi Zlo Zhi (lower (c 4) : ℝ) (upper (c 4) : ℝ)
    (lower (c 3) : ℝ) (upper (c 3) : ℝ)
    hz hH hZlo hZhi hAl hAu hBl hBu I hI a ha
  change (∑ q ∈ (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * «ω»)⌋₊).filter (fun q =>
      q ∣ (∏ p ∈ I, p) ∧
        Nonempty (DenseDivisibilityWitness
          ⟨max 1 (x ^ δ), show (1 : ℝ) ≤ max 1 (x ^ δ) from le_max_left _ _⟩
          j q)),
    ‖fullDiscrepancy (finiteConvolution
      (∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, Finsupp.single n
        (if (lower (c 0) : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (upper (c 0) : ℝ)
          then (A0 n : ℂ) else 0))
      (∑ n ∈ Finset.Icc 1 ⌊2 * N⌋₊, Finsupp.single n
        (if (lower (c 3) : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (upper (c 3) : ℝ)
          then (B0 n : ℂ) else 0))) q a‖) ≤
      K * x / (Real.log x) ^ E at hbound
  rw [← hα, ← hβ, ← hF] at hbound
  exact hbound

open Classical in
theorem harman_feature_boundary_full_cell_cover
    (l : Fin 6) (T0 x B h : ℝ) (hh : 0 ≤ h)
    (L : ℕ) (b : ℕ → ℕ) (lo hi : ℕ → ℝ)
    (hlow : ∀ n, b n ≤ L ↔ n ≤ L)
    (hsingleton : ∀ n, n ≤ L → b n = n)
    (horder : ∀ n m, b n < b m → n < m)
    (hdiameter : ∀ n m, 1 ≤ n → 1 ≤ m → L < b n → b n = b m →
      |(n : ℝ) - m| ≤ h * lo (b n))
    (hends : ∀ n, 1 ≤ n → lo (b n) ≤ (n : ℝ) ∧
      (n : ℝ) ≤ (if b n ≤ L then lo (b n) else hi (b n)) ∧
      (if b n ≤ L then lo (b n) else hi (b n)) ≤ (1 + h) * lo (b n))
    (g bad v : Fin 7 → ℕ)
    (hgpos : ∀ r, 1 ≤ g r) (hbadpos : ∀ r, 1 ≤ bad r) (hvpos : ∀ r, 1 ≤ v r)
    (hgb : ∀ r, b (g r) = b (bad r)) (hgv : ∀ r, b (g r) = b (v r)) :
    let Good : (Fin 7 → ℕ) → Prop := fun f =>
      f 5 < f 1 ∧ T0 < ((f 0 * f 4 : ℕ) : ℝ) ∧
      x ≤ ((f 0 * f 3 : ℕ) : ℝ) ∧ ((f 0 * f 3 : ℕ) : ℝ) ≤ 2 * x ∧
      match l.val with
      | 2 => f 6 < f 2 ∧ ((f 2 * f 6 : ℕ) : ℝ) < x ^ ((41361 : ℝ) / 100000)
      | 3 => f 6 < f 2 ∧ B < ((f 2 * f 6 : ℕ) : ℝ)
      | 4 => f 6 < f 2
      | 5 => f 2 < f 6
      | _ => True
    Good g → ¬Good bad →
      (L < min (v 5) (v 1) ∧
        ((max (v 5) (v 1) : ℕ) : ℝ) ≤ (1 + h) * ((min (v 5) (v 1) : ℕ) : ℝ)) ∨
      (T0 / (1 + h) ^ 2 ≤ ((v 0 * v 4 : ℕ) : ℝ) ∧
        ((v 0 * v 4 : ℕ) : ℝ) ≤ T0 * (1 + h) ^ 2) ∨
      (x / (1 + h) ^ 2 ≤ ((v 0 * v 3 : ℕ) : ℝ) ∧
        ((v 0 * v 3 : ℕ) : ℝ) ≤ x * (1 + h) ^ 2) ∨
      ((2 * x) / (1 + h) ^ 2 ≤ ((v 0 * v 3 : ℕ) : ℝ) ∧
        ((v 0 * v 3 : ℕ) : ℝ) ≤ (2 * x) * (1 + h) ^ 2) ∨
      (L < min (v 2) (v 6) ∧
        ((max (v 2) (v 6) : ℕ) : ℝ) ≤ (1 + h) * ((min (v 2) (v 6) : ℕ) : ℝ)) ∨
      (x ^ ((41361 : ℝ) / 100000) / (1 + h) ^ 2 ≤ ((v 2 * v 6 : ℕ) : ℝ) ∧
        ((v 2 * v 6 : ℕ) : ℝ) ≤ x ^ ((41361 : ℝ) / 100000) * (1 + h) ^ 2) ∨
      (B / (1 + h) ^ 2 ≤ ((v 2 * v 6 : ℕ) : ℝ) ∧
        ((v 2 * v 6 : ℕ) : ℝ) ≤ B * (1 + h) ^ 2) := by
  let u : ℕ → ℝ := fun q => if q ≤ L then lo q else hi q
  have hgends (r : Fin 7) : lo (b (g r)) ≤ (g r : ℝ) ∧
      (g r : ℝ) ≤ u (b (g r)) ∧ u (b (g r)) ≤ (1 + h) * lo (b (g r)) :=
    hends (g r) (hgpos r)
  have hbends (r : Fin 7) : lo (b (g r)) ≤ (bad r : ℝ) ∧
      (bad r : ℝ) ≤ u (b (g r)) ∧ u (b (g r)) ≤ (1 + h) * lo (b (g r)) := by
    rw [hgb r]
    exact hends (bad r) (hbadpos r)
  have hvends (r : Fin 7) : lo (b (g r)) ≤ (v r : ℝ) ∧
      (v r : ℝ) ≤ u (b (g r)) ∧ u (b (g r)) ≤ (1 + h) * lo (b (g r)) := by
    rw [hgv r]
    exact hends (v r) (hvpos r)
  have hlo0 (r : Fin 7) : 0 ≤ lo (b (g r)) := by
    have hgpositive : (0 : ℝ) < g r := by exact_mod_cast hgpos r
    have hmulpositive : 0 < (1 + h) * lo (b (g r)) :=
      hgpositive.trans_le ((hgends r).2.1.trans (hgends r).2.2)
    exact (pos_of_mul_pos_right hmulpositive (by positivity : (0 : ℝ) ≤ 1 + h)).le
  have hcomparison (a c : Fin 7) (hgood : g a < g c) (hbad : ¬bad a < bad c) :
      L < min (v a) (v c) ∧
        ((max (v a) (v c) : ℕ) : ℝ) ≤
          (1 + h) * ((min (v a) (v c) : ℕ) : ℝ) := by
    rcases (harman_strict_comparison_cells L b hlow hsingleton horder
      (g a) (g c)).mp hgood with hbetween | ⟨hhigh, heq, _⟩
    · have hbadbetween : b (bad a) < b (bad c) := by
        simpa only [hgb a, hgb c] using hbetween
      exact (hbad (horder (bad a) (bad c) hbadbetween)).elim
    · have hvhigh : L < b (v a) := by simpa only [hgv a] using hhigh
      have hveq : b (v a) = b (v c) := by simpa only [hgv a, hgv c] using heq
      exact harman_same_high_cell_comparison_band L b lo h hh hlow
        (fun n hn => (hends n hn).1) hdiameter (v a) (v c)
        (hvpos a) (hvpos c) hvhigh hveq
  have hproduct (a c : Fin 7) (T : ℝ)
      (hcross :
        (((g a * g c : ℕ) : ℝ) < T ∧ T ≤ ((bad a * bad c : ℕ) : ℝ)) ∨
        (((g a * g c : ℕ) : ℝ) ≤ T ∧ T < ((bad a * bad c : ℕ) : ℝ)) ∨
        (((bad a * bad c : ℕ) : ℝ) < T ∧ T ≤ ((g a * g c : ℕ) : ℝ)) ∨
        (((bad a * bad c : ℕ) : ℝ) ≤ T ∧ T < ((g a * g c : ℕ) : ℝ))) :
      T / (1 + h) ^ 2 ≤ ((v a * v c : ℕ) : ℝ) ∧
        ((v a * v c : ℕ) : ℝ) ≤ T * (1 + h) ^ 2 := by
    have hstraddle : lo (b (g a)) * lo (b (g c)) ≤ T ∧
        T ≤ u (b (g a)) * u (b (g c)) := by
      simp only [Nat.cast_mul] at hcross
      rw [← or_assoc] at hcross
      rcases hcross with hcross | hcross
      · exact harman_product_comparison_crossing T
          (lo (b (g a))) (u (b (g a))) (lo (b (g c))) (u (b (g c)))
          (g a) (g c) (bad a) (bad c) (hlo0 a) (hlo0 c)
          ⟨(hgends a).1, (hgends a).2.1⟩ ⟨(hgends c).1, (hgends c).2.1⟩
          ⟨(hbends a).1, (hbends a).2.1⟩ ⟨(hbends c).1, (hbends c).2.1⟩ hcross
      · exact harman_product_comparison_crossing T
          (lo (b (g a))) (u (b (g a))) (lo (b (g c))) (u (b (g c)))
          (bad a) (bad c) (g a) (g c) (hlo0 a) (hlo0 c)
          ⟨(hbends a).1, (hbends a).2.1⟩ ⟨(hbends c).1, (hbends c).2.1⟩
          ⟨(hgends a).1, (hgends a).2.1⟩ ⟨(hgends c).1, (hgends c).2.1⟩ hcross
    simpa only [Nat.cast_mul] using
      (harman_product_threshold_full_box_band h T
        (lo (b (g a))) (u (b (g a))) (lo (b (g c))) (u (b (g c)))
        (v a) (v c) hh (hlo0 a) (hlo0 c)
        ⟨(hvends a).1, (hvends a).2.1⟩ ⟨(hvends c).1, (hvends c).2.1⟩
        (hvends a).2.2 (hvends c).2.2 hstraddle)
  dsimp only
  rintro ⟨hgp, hgT0, hgxlow, hgxhigh, hgextra⟩ hbad
  simp only [not_and_or] at hbad
  rcases hbad with hbad | hbad | hbad | hbad | hbad
  · exact Or.inl (hcomparison 5 1 hgp hbad)
  · exact Or.inr (Or.inl (hproduct 0 4 T0
      (Or.inr (Or.inr (Or.inr ⟨le_of_not_gt hbad, hgT0⟩)))))
  · exact Or.inr (Or.inr (Or.inl (hproduct 0 3 x
      (Or.inr (Or.inr (Or.inl ⟨lt_of_not_ge hbad, hgxlow⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hproduct 0 3 (2 * x)
      (Or.inr (Or.inl ⟨hgxhigh, lt_of_not_ge hbad⟩))))))
  · fin_cases l
    · exact (hbad True.intro).elim
    · exact (hbad True.intro).elim
    · change g 6 < g 2 ∧ ((g 2 * g 6 : ℕ) : ℝ) < x ^ ((41361 : ℝ) / 100000)
        at hgextra
      change ¬(bad 6 < bad 2 ∧
        ((bad 2 * bad 6 : ℕ) : ℝ) < x ^ ((41361 : ℝ) / 100000)) at hbad
      rcases not_and_or.mp hbad with hbad | hbad
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
        simpa only [min_comm (v 6) (v 2), max_comm (v 6) (v 2)] using
          hcomparison 6 2 hgextra.1 hbad
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (hproduct 2 6 (x ^ ((41361 : ℝ) / 100000))
            (Or.inl ⟨hgextra.2, le_of_not_gt hbad⟩)))))))
    · change g 6 < g 2 ∧ B < ((g 2 * g 6 : ℕ) : ℝ) at hgextra
      change ¬(bad 6 < bad 2 ∧ B < ((bad 2 * bad 6 : ℕ) : ℝ)) at hbad
      rcases not_and_or.mp hbad with hbad | hbad
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
        simpa only [min_comm (v 6) (v 2), max_comm (v 6) (v 2)] using
          hcomparison 6 2 hgextra.1 hbad
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (hproduct 2 6 B
            (Or.inr (Or.inr (Or.inr ⟨le_of_not_gt hbad, hgextra.2⟩)))))))))
    · change g 6 < g 2 at hgextra
      change ¬bad 6 < bad 2 at hbad
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      simpa only [min_comm (v 6) (v 2), max_comm (v 6) (v 2)] using
        hcomparison 6 2 hgextra hbad
    · change g 2 < g 6 at hgextra
      change ¬bad 2 < bad 6 at hbad
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (hcomparison 2 6 hgextra hbad)))))

open Classical in
theorem harman_long_mixed_cell_mass_le
    (x R K h : ℝ) (L : ℕ) (l : Fin 6)
    (hx : Real.exp 100 ≤ x) (hL : 1 ≤ L) (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    let U := ⌊8 * x⌋₊
    (∀ i j : Fin 6, i ≠ j →
      (((Fintype.piFinset (fun _ : Fin 6 => Finset.Icc 1 U)).filter
        (fun v : Fin 6 → ℕ => (∏ r, v r) ≤ U ∧ 1 < v i ∧
          L < min (v i).minFac (max 1 ((v j).primeFactors.sup id)) ∧
          max ((v i).minFac : ℝ) ((max 1 ((v j).primeFactors.sup id) : ℕ) : ℝ) ≤
            (1 + h) * min ((v i).minFac : ℝ)
              ((max 1 ((v j).primeFactors.sup id) : ℕ) : ℝ))).card : ℝ) ≤
        K * x / (Real.log x) ^ R) →
    (∀ s : Finset (Fin 6), ∀ T : ℝ, x ^ (1 / 10 : ℝ) ≤ T → T ≤ x ^ (2 : ℝ) →
      (((Fintype.piFinset (fun _ : Fin 6 => Finset.Icc 1 U)).filter
        (fun v : Fin 6 → ℕ => (∏ r, v r) ≤ U ∧
          T / (1 + h) ^ 2 ≤ ((∏ r ∈ s, v r : ℕ) : ℝ) ∧
          ((∏ r ∈ s, v r : ℕ) : ℝ) ≤ T * (1 + h) ^ 2)).card : ℝ) ≤
        K * x / (Real.log x) ^ R) →
    let H := x ^ ((41361 : ℝ) / 100000)
    let z := x ^ ((8639 : ℝ) / 50000)
    let M0 := x ^ (1 - (34941 : ℝ) / 100000)
    let S := x ^ (1 - (34941 : ℝ) / 100000 - (41361 : ℝ) / 100000)
    let Bthreshold := x ^ ((58639 : ℝ) / 100000)
    let C := Finset.Icc 1 U
    let A := (Fintype.piFinset (fun _ : Fin 3 => C)).filter (fun a : Fin 3 → ℕ =>
      let u := a 0
      let v := a 1
      let h₀ := a 2
      let r := u * v
      let m := r * h₀
      m ≤ U ∧
        (match l.val with
          | 0 => u = 1 ∧ v = 1
          | 1 | 2 | 3 => u = 1 ∧ v.Prime ∧ z ≤ (v : ℝ)
          | 4 => u.Prime ∧ v.Prime ∧ z ≤ (u : ℝ) ∧ u < v
          | _ => u.Prime ∧ v.Prime ∧ z ≤ (u : ℝ) ∧ u ≤ v) ∧
        (r : ℝ) < H ∧ 1 < h₀ ∧ ((max 1 (h₀.primeFactors.sup id) : ℕ) : ℝ) < z ∧
        ((m / h₀.minFac : ℕ) : ℝ) < H ∧ H ≤ (m : ℝ))
    let B := (Fintype.piFinset (fun _ : Fin 3 => C)).filter (fun b : Fin 3 → ℕ =>
      let s := b 0
      let d := b 1
      let k := b 2
      let n := s * d * k
      n ≤ U ∧ (if l.val ≤ 1 then s = 1 else s.Prime ∧ z ≤ (s : ℝ)) ∧ (s : ℝ) < S)
    let feature (a b : Fin 3 → ℕ) : Fin 7 → ℕ :=
      ![a 0 * a 1 * a 2, (a 2).minFac, if l.val ≤ 3 then a 1 else a 0,
        b 0 * b 1 * b 2, b 0 * b 1, max 1 ((b 1).primeFactors.sup id), b 0]
    let Good (f : Fin 7 → ℕ) : Prop :=
      f 5 < f 1 ∧ M0 < ((f 0 * f 4 : ℕ) : ℝ) ∧
        x ≤ ((f 0 * f 3 : ℕ) : ℝ) ∧ ((f 0 * f 3 : ℕ) : ℝ) ≤ 2 * x ∧
        match l.val with
        | 2 => f 6 < f 2 ∧ ((f 2 * f 6 : ℕ) : ℝ) < H
        | 3 => f 6 < f 2 ∧ Bthreshold < ((f 2 * f 6 : ℕ) : ℝ)
        | 4 => f 6 < f 2
        | 5 => f 2 < f 6
        | _ => True
    ∀ (b : ℕ → ℕ) (lo hi : ℕ → ℝ),
      (∀ n, b n ≤ L ↔ n ≤ L) →
      (∀ n, n ≤ L → b n = n) →
      (∀ n m, b n < b m → n < m) →
      (∀ n m, 1 ≤ n → 1 ≤ m → L < b n → b n = b m →
        |(n : ℝ) - m| ≤ h * lo (b n)) →
      (∀ n, 1 ≤ n → lo (b n) ≤ (n : ℝ) ∧
        (n : ℝ) ≤ (if b n ≤ L then lo (b n) else hi (b n)) ∧
        (if b n ≤ L then lo (b n) else hi (b n)) ≤ (1 + h) * lo (b n)) →
    let T := A ×ˢ B
    let key (t : (Fin 3 → ℕ) × (Fin 3 → ℕ)) : Fin 7 → ℕ :=
      fun i => b (feature t.1 t.2 i)
    let cells := T.image key
    let cell (c : Fin 7 → ℕ) := T.filter (fun t => key t = c)
    let D := cells.filter (fun c =>
      (∃ t ∈ cell c, Good (feature t.1 t.2)) ∧
        ∃ t ∈ cell c, ¬Good (feature t.1 t.2))
    (∑ c ∈ D, ∑ t ∈ cell c,
      |(ArithmeticFunction.moebius (t.1 2) : ℝ) *
        (ArithmeticFunction.moebius (t.2 1) : ℝ)|) ≤
      7 * K * x / (Real.log x) ^ R := by
  intro U hprime hproduct H z M0 S Bthreshold C A B feature Good
    b lo hi hlow hsingleton horder hdiameter hends T key cells cell D
  let flat : ((Fin 3 → ℕ) × (Fin 3 → ℕ)) → Fin 6 → ℕ := fun t =>
    ![t.1 0, t.1 1, t.1 2, t.2 0, t.2 1, t.2 2]
  let named : Fin 6 := if l.val ≤ 3 then 1 else 0
  let C6 := Fintype.piFinset (fun _ : Fin 6 => C)
  let P (i j : Fin 6) := C6.filter (fun v : Fin 6 → ℕ =>
    (∏ r, v r) ≤ U ∧ 1 < v i ∧
      L < min (v i).minFac (max 1 ((v j).primeFactors.sup id)) ∧
      max ((v i).minFac : ℝ) ((max 1 ((v j).primeFactors.sup id) : ℕ) : ℝ) ≤
        (1 + h) * min ((v i).minFac : ℝ)
          ((max 1 ((v j).primeFactors.sup id) : ℕ) : ℝ))
  let V (s : Finset (Fin 6)) (q : ℝ) := C6.filter (fun v : Fin 6 → ℕ =>
    (∏ r, v r) ≤ U ∧
      q / (1 + h) ^ 2 ≤ ((∏ r ∈ s, v r : ℕ) : ℝ) ∧
      ((∏ r ∈ s, v r : ℕ) : ℝ) ≤ q * (1 + h) ^ 2)
  let bands : Fin 7 → Finset (Fin 6 → ℕ) :=
    ![P 2 4, V {0, 1, 2, 3, 4} M0, V Finset.univ x,
      V Finset.univ (2 * x), P named 3, V {named, 3} H,
      V {named, 3} Bthreshold]
  have hx2 : 2 ≤ x := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hxone : 1 ≤ x := by linarith only [hx2]
  have hxpos : 0 < x := zero_lt_one.trans_le hxone
  have hpower (q : ℝ) (hql : 1 / 10 ≤ q) (hqu : q ≤ 2) :
      x ^ (1 / 10 : ℝ) ≤ x ^ q ∧ x ^ q ≤ x ^ (2 : ℝ) :=
    ⟨Real.rpow_le_rpow_of_exponent_le hxone hql,
      Real.rpow_le_rpow_of_exponent_le hxone hqu⟩
  have hxband : x ^ (1 / 10 : ℝ) ≤ x ∧ x ≤ x ^ (2 : ℝ) := by
    simpa only [Real.rpow_one] using hpower 1 (by norm_num) (by norm_num)
  have htwoxband : x ^ (1 / 10 : ℝ) ≤ 2 * x ∧ 2 * x ≤ x ^ (2 : ℝ) := by
    refine ⟨hxband.1.trans (by linarith only [hxpos]), ?_⟩
    rw [Real.rpow_two]
    nlinarith only [hx2]
  have hMband : x ^ (1 / 10 : ℝ) ≤ M0 ∧ M0 ≤ x ^ (2 : ℝ) :=
    hpower _ (by norm_num) (by norm_num)
  have hHband : x ^ (1 / 10 : ℝ) ≤ H ∧ H ≤ x ^ (2 : ℝ) :=
    hpower _ (by norm_num) (by norm_num)
  have hBband : x ^ (1 / 10 : ℝ) ≤ Bthreshold ∧ Bthreshold ≤ x ^ (2 : ℝ) :=
    hpower _ (by norm_num) (by norm_num)
  have hnamedne : named ≠ 3 := by dsimp only [named]; split_ifs <;> decide
  have hcards (i : Fin 7) : ((bands i).card : ℝ) ≤ K * x / (Real.log x) ^ R := by
    fin_cases i
    · exact hprime 2 4 (by decide)
    · exact hproduct {0, 1, 2, 3, 4} M0 hMband.1 hMband.2
    · exact hproduct Finset.univ x hxband.1 hxband.2
    · exact hproduct Finset.univ (2 * x) htwoxband.1 htwoxband.2
    · exact hprime named 3 hnamedne
    · exact hproduct {named, 3} H hHband.1 hHband.2
    · exact hproduct {named, 3} Bthreshold hBband.1 hBband.2
  have haC (a : Fin 3 → ℕ) (ha : a ∈ A) (i : Fin 3) : a i ∈ C :=
    Fintype.mem_piFinset.mp (Finset.mem_filter.mp ha).1 i
  have hbC (d : Fin 3 → ℕ) (hd : d ∈ B) (i : Fin 3) : d i ∈ C :=
    Fintype.mem_piFinset.mp (Finset.mem_filter.mp hd).1 i
  have hah (a : Fin 3 → ℕ) (ha : a ∈ A) : 1 < a 2 := by
    obtain ⟨_, _, _, hh, _, _, _⟩ := (Finset.mem_filter.mp ha).2
    exact hh
  have hanamed (a : Fin 3 → ℕ) (ha : a ∈ A) :
      (if l.val ≤ 3 then a 1 else a 0) = 1 ∨
        (if l.val ≤ 3 then a 1 else a 0).Prime := by
    have hn := (Finset.mem_filter.mp ha).2.2.1
    fin_cases l
    · exact Or.inl hn.2
    · exact Or.inr hn.2.1
    · exact Or.inr hn.2.1
    · exact Or.inr hn.2.1
    · exact Or.inr hn.1
    · exact Or.inr hn.1
  have hbnamed (d : Fin 3 → ℕ) (hd : d ∈ B) : d 0 = 1 ∨ (d 0).Prime := by
    have hn := (Finset.mem_filter.mp hd).2.2.1
    by_cases hl : l.val ≤ 1
    · exact Or.inl (by simpa only [hl, ite_true] using hn)
    · have hs : (d 0).Prime ∧ z ≤ (d 0 : ℝ) := by
        simpa only [hl, ite_false] using hn
      exact Or.inr hs.1
  have hfpos (t : (Fin 3 → ℕ) × (Fin 3 → ℕ)) (ht : t ∈ T) :
      ∀ i : Fin 7, 1 ≤ feature t.1 t.2 i := by
    obtain ⟨ha, hd⟩ := Finset.mem_product.mp ht
    have hf := harman_long_feature_bounds l U t.1 t.2
      (fun i => Finset.mem_Icc.mp (haC _ ha i))
      (fun i => Finset.mem_Icc.mp (hbC _ hd i))
      (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp hd).2.1
    exact fun i => (hf i).1
  have hflat (t : (Fin 3 → ℕ) × (Fin 3 → ℕ)) (ht : t ∈ T) : flat t ∈ C6 := by
    obtain ⟨ha, hd⟩ := Finset.mem_product.mp ht
    apply Fintype.mem_piFinset.mpr
    intro i
    fin_cases i
    · exact haC _ ha 0
    · exact haC _ ha 1
    · exact haC _ ha 2
    · exact hbC _ hd 0
    · exact hbC _ hd 1
    · exact hbC _ hd 2
  have hflatnamed (t : (Fin 3 → ℕ) × (Fin 3 → ℕ)) :
      flat t named = if l.val ≤ 3 then t.1 1 else t.1 0 := by
    by_cases hl : l.val ≤ 3 <;> simp [flat, named, hl]
  have hfnamed (t : (Fin 3 → ℕ) × (Fin 3 → ℕ)) :
      feature t.1 t.2 2 = flat t named := by
    rw [hflatnamed]
    rfl
  have hfs (t : (Fin 3 → ℕ) × (Fin 3 → ℕ)) : feature t.1 t.2 6 = flat t 3 := rfl
  have hprod (t : (Fin 3 → ℕ) × (Fin 3 → ℕ)) :
      (∏ i : Fin 6, flat t i) = feature t.1 t.2 0 * feature t.1 t.2 3 := by
    change _ = (t.1 0 * t.1 1 * t.1 2) * (t.2 0 * t.2 1 * t.2 2)
    norm_num [flat, Fin.prod_univ_succ]
    ring
  have hprodlong (t : (Fin 3 → ℕ) × (Fin 3 → ℕ)) :
      (∏ i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 6)), flat t i) =
        feature t.1 t.2 0 * feature t.1 t.2 4 := by
    change _ = (t.1 0 * t.1 1 * t.1 2) * (t.2 0 * t.2 1)
    rw [Finset.prod_insert (by decide : (0 : Fin 6) ∉ ({1, 2, 3, 4} : Finset (Fin 6))),
      Finset.prod_insert (by decide : (1 : Fin 6) ∉ ({2, 3, 4} : Finset (Fin 6))),
      Finset.prod_insert (by decide : (2 : Fin 6) ∉ ({3, 4} : Finset (Fin 6))),
      Finset.prod_insert (by decide : (3 : Fin 6) ∉ ({4} : Finset (Fin 6))),
      Finset.prod_singleton]
    change t.1 0 * (t.1 1 * (t.1 2 * (t.2 0 * t.2 1))) = _
    ring
  have hprodname (t : (Fin 3 → ℕ) × (Fin 3 → ℕ)) :
      (∏ i ∈ ({named, 3} : Finset (Fin 6)), flat t i) =
        feature t.1 t.2 2 * feature t.1 t.2 6 := by
    by_cases hl : l.val ≤ 3 <;> simp [named, flat, feature, hl]
  have hinj : Set.InjOn flat (↑T : Set ((Fin 3 → ℕ) × (Fin 3 → ℕ))) := by
    intro t _ u _ heq
    apply Prod.ext
    · funext i
      fin_cases i
      · simpa [flat] using congrFun heq (0 : Fin 6)
      · simpa [flat] using congrFun heq (1 : Fin 6)
      · simpa [flat] using congrFun heq (2 : Fin 6)
    · funext i
      fin_cases i
      · simpa [flat] using congrFun heq (3 : Fin 6)
      · simpa [flat] using congrFun heq (4 : Fin 6)
      · simpa [flat] using congrFun heq (5 : Fin 6)
  have hcover (c : Fin 7 → ℕ) (hc : c ∈ D)
      (v : (Fin 3 → ℕ) × (Fin 3 → ℕ)) (hv : v ∈ cell c) :
      ∃ i : Fin 7, flat v ∈ bands i := by
    obtain ⟨⟨g, hgc, hg⟩, bad, hbc, hbad⟩ := (Finset.mem_filter.mp hc).2
    have hgt := (Finset.mem_filter.mp hgc).1
    have hbt := (Finset.mem_filter.mp hbc).1
    have hvt := (Finset.mem_filter.mp hv).1
    have hgb (i : Fin 7) : b (feature g.1 g.2 i) = b (feature bad.1 bad.2 i) :=
      congrFun ((Finset.mem_filter.mp hgc).2.trans (Finset.mem_filter.mp hbc).2.symm) i
    have hgv (i : Fin 7) : b (feature g.1 g.2 i) = b (feature v.1 v.2 i) :=
      congrFun ((Finset.mem_filter.mp hgc).2.trans (Finset.mem_filter.mp hv).2.symm) i
    have hnear (i : Fin 7) :
        (feature v.1 v.2 i : ℝ) ≤ 2 * (feature g.1 g.2 i : ℝ) := by
      have hge := hends (feature g.1 g.2 i) (hfpos g hgt i)
      have hve := hends (feature v.1 v.2 i) (hfpos v hvt i)
      rw [← hgv i] at hve
      calc
        _ ≤ (if b (feature g.1 g.2 i) ≤ L then lo (b (feature g.1 g.2 i))
            else hi (b (feature g.1 g.2 i))) := hve.2.1
        _ ≤ (1 + h) * lo (b (feature g.1 g.2 i)) := hve.2.2
        _ ≤ (1 + h) * (feature g.1 g.2 i : ℝ) :=
          mul_le_mul_of_nonneg_left hge.1 (by linarith only [hh])
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hh1]) (Nat.cast_nonneg _)
    have hfull : (∏ i : Fin 6, flat v i) ≤ U := by
      apply Nat.le_floor
      rw [hprod, Nat.cast_mul]
      have hgupper : ((feature g.1 g.2 0 * feature g.1 g.2 3 : ℕ) : ℝ) ≤ 2 * x :=
        hg.2.2.2.1
      calc
        _ ≤ (2 * (feature g.1 g.2 0 : ℝ)) * (2 * (feature g.1 g.2 3 : ℝ)) :=
          mul_le_mul (hnear 0) (hnear 3) (Nat.cast_nonneg _) (by positivity)
        _ = 4 * ((feature g.1 g.2 0 * feature g.1 g.2 3 : ℕ) : ℝ) := by
          push_cast
          ring
        _ ≤ 4 * (2 * x) := mul_le_mul_of_nonneg_left hgupper (by norm_num)
        _ = 8 * x := by ring
    have hseven := harman_feature_boundary_full_cell_cover l M0 x Bthreshold h hh
      L b lo hi hlow hsingleton horder hdiameter hends
      (feature g.1 g.2) (feature bad.1 bad.2) (feature v.1 v.2)
      (hfpos g hgt) (hfpos bad hbt) (hfpos v hvt) hgb hgv hg hbad
    rcases hseven with hp | hp | hp | hp | hp | hp | hp
    · refine ⟨0, Finset.mem_filter.mpr ⟨hflat v hvt, hfull,
      hah v.1 (Finset.mem_product.mp hvt).1, ?_, ?_⟩⟩
      · simpa [flat, feature, min_comm] using hp.1
      · simpa [flat, feature, max_comm, min_comm] using hp.2
    · refine ⟨1, Finset.mem_filter.mpr ⟨hflat v hvt, hfull, ?_⟩⟩
      simpa only [hprodlong] using hp
    · refine ⟨2, Finset.mem_filter.mpr ⟨hflat v hvt, hfull, ?_⟩⟩
      simpa only [hprod] using hp
    · refine ⟨3, Finset.mem_filter.mpr ⟨hflat v hvt, hfull, ?_⟩⟩
      simpa only [hprod] using hp
    · have hp' : L < min (flat v named) (flat v 3) ∧
          ((max (flat v named) (flat v 3) : ℕ) : ℝ) ≤
            (1 + h) * ((min (flat v named) (flat v 3) : ℕ) : ℝ) := by
        simpa only [hfnamed, hfs] using hp
      have hn1 : 1 < flat v named := hL.trans_lt (hp'.1.trans_le (min_le_left _ _))
      have hs1 : 1 < flat v 3 := hL.trans_lt (hp'.1.trans_le (min_le_right _ _))
      have hnalt : flat v named = 1 ∨ (flat v named).Prime := by
        rw [hflatnamed]
        exact hanamed v.1 (Finset.mem_product.mp hvt).1
      have hsalt : flat v 3 = 1 ∨ (flat v 3).Prime :=
        hbnamed v.2 (Finset.mem_product.mp hvt).2
      have hnprime := hnalt.resolve_left (ne_of_gt hn1)
      have hsprime := hsalt.resolve_left (ne_of_gt hs1)
      have hmax : max 1 ((flat v 3).primeFactors.sup id) = flat v 3 := by
        simp [hsprime.primeFactors, max_eq_right hsprime.one_le]
      refine ⟨4, Finset.mem_filter.mpr ⟨hflat v hvt, hfull, hn1, ?_, ?_⟩⟩
      · simpa only [hnprime.minFac_eq, hmax] using hp'.1
      · simpa only [hnprime.minFac_eq, hmax, Nat.cast_max, Nat.cast_min] using hp'.2
    · refine ⟨5, Finset.mem_filter.mpr ⟨hflat v hvt, hfull, ?_⟩⟩
      simpa only [hprodname] using hp
    · refine ⟨6, Finset.mem_filter.mpr ⟨hflat v hvt, hfull, ?_⟩⟩
      simpa only [hprodname] using hp
  have hw (v : (Fin 3 → ℕ) × (Fin 3 → ℕ)) (_ : v ∈ T) :
      |(ArithmeticFunction.moebius (v.1 2) : ℝ) *
        (ArithmeticFunction.moebius (v.2 1) : ℝ)| ≤ 1 := by
    have ha : |(ArithmeticFunction.moebius (v.1 2) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := v.1 2)
    have hb : |(ArithmeticFunction.moebius (v.2 1) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := v.2 1)
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul ha hb (abs_nonneg _) zero_le_one
  clear hprime hproduct
  have hm := harman_mixed_cell_mass_le_sum_band_card T key
    (fun v => Good (feature v.1 v.2))
    (fun v => (ArithmeticFunction.moebius (v.1 2) : ℝ) *
      (ArithmeticFunction.moebius (v.2 1) : ℝ)) flat bands hw hinj hcover
  calc
    _ ≤ ∑ i : Fin 7, ((bands i).card : ℝ) := hm
    _ ≤ ∑ _i : Fin 7, K * x / (Real.log x) ^ R :=
      Finset.sum_le_sum fun i _ => hcards i
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

#print axioms sifted_long_active_feature_cell_log_saving_of_bilinear
#print axioms harman_feature_boundary_full_cell_cover
#print axioms harman_long_mixed_cell_mass_le

end PrimeGap182Analytic.Harman

end
