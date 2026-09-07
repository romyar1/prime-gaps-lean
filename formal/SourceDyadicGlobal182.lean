import SourceDyadicDeltaZero182
import HarmanAnalyticInterfaces182

/-! The actual triply-dense convolution estimate follows from a uniform
dyadic delta-zero estimate on the full required scale interval. The
proof performs rough-modulus extraction, coefficient bookkeeping,
ordinary BV, mean terms, and the final finite dispersion sum. Adapted
from the Apache-2.0 public source at the generator's pinned hash. -/

noncomputable section
open scoped BigOperators Topology ContDiff
open Filter Asymptotics PrimeGap186
open PrimeGap182Analytic.Harman
namespace PrimeGap182Audit
set_option maxHeartbeats 2000000

theorem sourceBilinearEstimate_three_of_dyadic
    («ω» δ σ ω' δ' ε : ℝ)
    (hω : 0 < «ω») (hδ : 0 < δ) (hσ : 0 < σ) (hσlt : σ < 1 / 4)
    (hωw : «ω» < ω') (hδw : δ < δ')
    (hεδ : δ + ε ≤ δ') (hωsmall : ω' < 1 / 4)
    (hε : 0 < ε) (hεbound : ε < 1 / 24)
    (hsource : SourceDyadicDeltaZeroEstimate ω' δ' ε (1 / 2 - σ) (1 / 2)) :
    SourceBilinearEstimate 3 «ω» δ σ := by
  intro ι M N α β c C W X₀ k s hc hCscale hW hX₀ hscale hsupport hcoeff hSW
  classical
  have hdyadic_bin_count (x θ : ℝ) (Q : ℕ) (hx : Real.exp 1 ≤ x)
      (hθ : 0 ≤ θ) (hQ : Q ≤ ⌊x ^ θ⌋₊) :
      ((Nat.log 2 Q + 1 : ℕ) : ℝ) ≤
        (1 + θ / Real.log 2) * Real.log x := by
    have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
    have hlogx : 1 ≤ Real.log x := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hx
    have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hQreal : (Q : ℝ) ≤ x ^ θ :=
      (show (Q : ℝ) ≤ (⌊x ^ θ⌋₊ : ℝ) by exact_mod_cast hQ).trans
        (Nat.floor_le (Real.rpow_nonneg hxpos.le θ))
    have hlogbound : (Nat.log 2 Q : ℝ) * Real.log 2 ≤ θ * Real.log x := by
      by_cases hQzero : Q = 0
      · simpa only [hQzero, Nat.log_zero_right, Nat.cast_zero, zero_mul] using
          mul_nonneg hθ (zero_le_one.trans hlogx)
      · have hpow : (2 : ℝ) ^ Nat.log 2 Q ≤ x ^ θ :=
          (show (2 : ℝ) ^ Nat.log 2 Q ≤ (Q : ℝ) by
            exact_mod_cast Nat.pow_log_le_self 2 hQzero).trans hQreal
        have h := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpow
        simpa only [Real.log_pow, Real.log_rpow hxpos] using h
    have hquot : (Nat.log 2 Q : ℝ) ≤ θ * Real.log x / Real.log 2 :=
      (le_div_iff₀ hlogtwo).2 hlogbound
    calc
      ((Nat.log 2 Q + 1 : ℕ) : ℝ) = (Nat.log 2 Q : ℝ) + 1 := by norm_num
      _ ≤ θ * Real.log x / Real.log 2 + Real.log x := add_le_add hquot hlogx
      _ = (1 + θ / Real.log 2) * Real.log x := by ring
  have hpair_dyadic_cover (S : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) (U V : ℕ)
      (hS : ∀ p ∈ S, 0 < p.1 ∧ p.1 ≤ U ∧ 0 < p.2 ∧ p.2 ≤ V)
      (hw : ∀ p ∈ S, 0 ≤ w p) :
      (∑ p ∈ S, w p) ≤
        ∑ j ∈ Finset.Icc 0 (Nat.log 2 U),
          ∑ k ∈ Finset.Icc 0 (Nat.log 2 V),
            ∑ p ∈ S.filter (fun p =>
              2 ^ j ≤ p.1 ∧ p.1 ≤ 2 * 2 ^ j ∧
              2 ^ k ≤ p.2 ∧ p.2 ≤ 2 * 2 ^ k), w p := by
    have hmap : ∀ p ∈ S, (Nat.log 2 p.1, Nat.log 2 p.2) ∈
        (Finset.Icc 0 (Nat.log 2 U)) ×ˢ (Finset.Icc 0 (Nat.log 2 V)) := by
      intro p hp
      exact Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.log_mono_right (b := 2) (hS p hp).2.1⟩,
          Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.log_mono_right (b := 2) (hS p hp).2.2.2⟩⟩
    calc
      (∑ p ∈ S, w p) = ∑ j ∈ Finset.Icc 0 (Nat.log 2 U),
          ∑ k ∈ Finset.Icc 0 (Nat.log 2 V),
            ∑ p ∈ S.filter (fun p => Nat.log 2 p.1 = j ∧ Nat.log 2 p.2 = k), w p := by
        simpa only [Finset.sum_product, Prod.mk.injEq] using
          (Finset.sum_fiberwise_of_maps_to hmap w).symm
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro k _
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨hpS, hj, hk⟩ := Finset.mem_filter.mp hp
          refine Finset.mem_filter.mpr ⟨hpS, ?_, ?_, ?_, ?_⟩
          · simpa only [hj] using Nat.pow_log_le_self 2 (hS p hpS).1.ne'
          · simpa only [hj, pow_succ, Nat.mul_comm] using
              (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p.1).le
          · simpa only [hk] using Nat.pow_log_le_self 2 (hS p hpS).2.2.1.ne'
          · simpa only [hk, pow_succ, Nat.mul_comm] using
              (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p.2).le
        · intro p hp _
          exact hw p (Finset.mem_filter.mp hp).1
  have hprime_product_pos (P : Finset ℕ) (hP : ∀ t ∈ P, Nat.Prime t) :
      0 < ∏ t ∈ P, t :=
    Finset.prod_pos (fun t ht => (hP t ht).pos)
  have hrough_data (Y Z : Set.Ici (1 : ℝ)) (B cutoff D U V : ℕ)
      (T : ℝ) (P : Finset ℕ) (hP : ∀ t ∈ P, Nat.Prime t)
      (p : ℕ × ℕ) (hp : p ∈ roughTripleFactorPairs Y Z B cutoff D U V T P) :
      0 < p.1 ∧ 0 < p.2 ∧ Squarefree (p.1 * p.2) ∧
        p.1 * p.2 ∣ (∏ t ∈ P, t) ∧ D ≤ p.1 * p.2 ∧ p.1 * p.2 ≤ 2 * D ∧
        (smallPrimePart B (p.1 * p.2) : ℝ) ≤ (Z : ℝ) ∧
        T / (Y : ℝ) ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ T * (Z : ℝ) ∧
        Nonempty (DenseDivisibilityWitness
          (inflatedScale Y Z) 1 p.1) ∧
        Nonempty (DenseDivisibilityWitness
          (inflatedScale Y Z) 1 p.2) ∧
        (∀ t ∈ p.1.primeFactors, B < t) := by
    classical
    obtain ⟨hrect, hsource, hsmall, hrough, hlo, hhi, hdense₁, hdense₂⟩ :=
      Finset.mem_filter.mp hp
    obtain ⟨htriple, hDlo, hDhi⟩ := Finset.mem_filter.mp hsource
    obtain ⟨_, hprodDiv, _⟩ := Finset.mem_filter.mp htriple
    have hsfP : Squarefree (∏ t ∈ P, t) := by
      apply Finset.squarefree_prod_of_pairwise_isCoprime
      · intro s hs t ht hst
        exact Nat.coprime_iff_isRelPrime.mp
          ((Nat.coprime_primes (hP s hs) (hP t ht)).mpr hst)
      · intro t ht
        exact (hP t ht).squarefree
    refine ⟨(Finset.mem_Ioc.mp (Finset.mem_product.mp hrect).1).1,
      (Finset.mem_Ioc.mp (Finset.mem_product.mp hrect).2).1,
      hsfP.squarefree_of_dvd hprodDiv, hprodDiv, hDlo, hDhi, hsmall,
      hlo, hhi, hdense₁, hdense₂, ?_⟩
    intro t ht
    have hPrough : ∀ s ∈ P.filter (fun s => B < s), Nat.Prime s :=
      fun s hs => hP s (Finset.mem_filter.mp hs).1
    have ht' : t ∈ P.filter (fun s => B < s) := by
      rw [← Nat.primeFactors_prod hPrough]
      exact Nat.primeFactors_mono hrough
        (hprime_product_pos (P.filter (fun s => B < s)) hPrough).ne' ht
    exact (Finset.mem_filter.mp ht').2
  have hprimitive_average_le (G : ℕ) (hG : 0 < G) (F : ℕ → ℝ) (E : ℝ)
      (hF : ∀ b ∈ primitiveResidues G, F b ≤ E) :
      (∑ b ∈ primitiveResidues G, F b) / (G.totient : ℝ) ≤ E := by
    have hcard : (primitiveResidues G).card = G.totient := by
      unfold primitiveResidues
      rw [Nat.totient_eq_card_coprime]
      congr 1
      ext b
      simp only [Finset.mem_filter, Nat.coprime_comm]
    have hphi : (G.totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr hG).ne'
    calc
      (∑ b ∈ primitiveResidues G, F b) / (G.totient : ℝ) ≤
          (∑ b ∈ primitiveResidues G, E) / (G.totient : ℝ) :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum hF) (Nat.cast_nonneg _)
      _ = E := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        exact mul_div_cancel_left₀ E hphi
  have hselect_pairs (Y Z : Set.Ici (1 : ℝ)) (B cutoff : ℕ)
      (T : ℝ) (P : Finset ℕ) (hP : ∀ t ∈ P, Nat.Prime t) (hT : 1 ≤ T)
      (E : Finset ℕ)
      (hE : ∀ n ∈ E, n ∈ tripleSourceModuli Y cutoff P ∧ T ≤ (n : ℝ) ∧
        (smallPrimePart B n : ℝ) ≤ (Z : ℝ)) :
      ∃ S : Finset (ℕ × ℕ),
        (∀ F : ℕ → ℝ, (∑ n ∈ E, F n) = ∑ p ∈ S, F (p.1 * p.2)) ∧
        ∀ p ∈ S, 0 < p.1 ∧ 0 < p.2 ∧ Squarefree (p.1 * p.2) ∧
          p.1 * p.2 ∈ E ∧ p.1 * p.2 ∣ (∏ t ∈ P, t) ∧
          T / (Y : ℝ) ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ T * (Z : ℝ) ∧
          Nonempty (DenseDivisibilityWitness
            (inflatedScale Y Z) 1 p.1) ∧
          Nonempty (DenseDivisibilityWitness
            (inflatedScale Y Z) 1 p.2) ∧
          (∀ t ∈ p.1.primeFactors, B < t) := by
    classical
    let U : ℕ := ⌈2 * (cutoff : ℝ) * (Y : ℝ) / T⌉₊
    let V : ℕ := ⌈T * (Z : ℝ)⌉₊
    have hTpos : 0 < T := zero_lt_one.trans_le hT
    have hYpos : 0 < (Y : ℝ) := zero_lt_one.trans_le Y.property
    have hV : T * (Z : ℝ) ≤ (V : ℝ) := Nat.le_ceil _
    have hex : ∀ n : ℕ, ∃ p : ℕ × ℕ, n ∈ E →
        p ∈ roughTripleFactorPairs Y Z B cutoff n U V T P ∧ p.1 * p.2 = n := by
      intro n
      by_cases hn : n ∈ E
      · obtain ⟨hsource, hTn, hsmall⟩ := hE n hn
        have hncut : n ≤ cutoff :=
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hsource).1).2
        have hncutR : (n : ℝ) ≤ (cutoff : ℝ) := by exact_mod_cast hncut
        have hU : 2 * (n : ℝ) * (Y : ℝ) / T ≤ (U : ℝ) := by
          calc
            2 * (n : ℝ) * (Y : ℝ) / T ≤
                2 * (cutoff : ℝ) * (Y : ℝ) / T :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hncutR (by norm_num)) hYpos.le) hTpos.le
            _ ≤ (U : ℝ) := Nat.le_ceil _
        have hdyadic : n ∈ dyadicTripleSourceModuli Y cutoff n P :=
          Finset.mem_filter.mpr ⟨hsource, le_rfl, by omega⟩
        obtain ⟨p, hp, hprod⟩ :=
          exists_roughTripleFactorPair Y Z B cutoff n U V T P hP hT hTn hU hV
            hdyadic hsmall
        exact ⟨p, fun _ => ⟨hp, hprod⟩⟩
      · exact ⟨(0, 0), fun h => (hn h).elim⟩
    choose pick hpick using hex
    have hinj : Set.InjOn pick E := by
      intro n hn m hm hnm
      exact (hpick n hn).2.symm.trans
        ((congrArg (fun p : ℕ × ℕ => p.1 * p.2) hnm).trans (hpick m hm).2)
    refine ⟨E.image pick, ?_, ?_⟩
    · intro F
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro n hn
      rw [(hpick n hn).2]
    · intro p hp
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hp, hprod⟩ := hpick n hn
      obtain ⟨hpos₁, hpos₂, hsf, hdiv, _, _, _, hlo, hhi, hdense₁, hdense₂,
        hrough⟩ := hrough_data Y Z B cutoff n U V T P hP (pick n) hp
      refine ⟨hpos₁, hpos₂, hsf, ?_, hdiv, hlo, hhi, hdense₁, hdense₂, hrough⟩
      simpa only [hprod] using hn
  have hω' : 0 < ω' := hω.trans hωw
  have hδ' : 0 < δ' := hδ.trans hδw
  have hσgap : 0 < 1 / 2 - σ := by linarith only [hσ, hσlt]
  let θ : ℝ := 1 / 2 + 2 * «ω»
  have hθpos : 0 < θ := by dsimp only [θ]; linarith only [hω]
  have hθlt : θ < 1 := by dsimp only [θ]; linarith only [hωw, hωsmall]
  have hCpos : 0 < C := zero_lt_one.trans_le hCscale
  let C' : ℝ := max 4 (max C W)
  let c' : ℝ := min c 1
  have hC'4 : 4 ≤ C' := le_max_left _ _
  have hC'C : C ≤ C' := (le_max_left C W).trans (le_max_right _ _)
  have hC'W : W ≤ C' := (le_max_right C W).trans (le_max_right _ _)
  have hC' : 1 ≤ C' := by linarith only [hC'4]
  have hc' : 0 < c' := lt_min hc zero_lt_one
  have hc'c : c' ≤ c := min_le_left _ _
  have hc'C' : c' ≤ C' := (min_le_right _ _).trans hC'
  have hCevent : ∀ᶠ x : ℝ in Filter.atTop, C ≤ x ^ (1 / 4 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually
      (Filter.eventually_ge_atTop C)
  obtain ⟨XC, hXC⟩ := Filter.eventually_atTop.mp hCevent
  let Xbase : ℝ := max X₀ XC
  have hXbase₀ : X₀ ≤ Xbase := le_max_left _ _
  have hXbase : Real.exp 1 ≤ Xbase := hX₀.trans hXbase₀
  have hbalanced : ∀ x : ℝ, Xbase ≤ x → ∀ i : ι,
      x / C ≤ M x i * N x i ∧ M x i * N x i ≤ C * x ∧
      x ^ (1 / 8 : ℝ) ≤ M x i ∧ x ^ (1 / 8 : ℝ) ≤ N x i := by
    intro x hx i
    have hx₀ : X₀ ≤ x := hXbase₀.trans hx
    have hxexp : Real.exp 1 ≤ x := hX₀.trans hx₀
    have hxpos : 0 < x := (Real.exp_pos 1).trans_le hxexp
    have hx1 : 1 ≤ x :=
      (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans hxexp
    obtain ⟨hMNlo, hMNhi, hNlo, hNhi⟩ := hscale x hx₀ i
    have hNpos : 0 < N x i := (Real.rpow_pos_of_pos hxpos _).trans_le hNlo
    have hMpos : 0 < M x i :=
      pos_of_mul_pos_left ((div_pos hxpos hCpos).trans_le hMNlo) hNpos.le
    have hCp : C ≤ x ^ (1 / 4 : ℝ) := hXC x ((le_max_right _ _).trans hx)
    have hMquarter : x ^ (1 / 4 : ℝ) ≤ M x i := by
      refine le_of_mul_le_mul_right ?_ (mul_pos hCpos hNpos)
      calc
        x ^ (1 / 4 : ℝ) * (C * N x i) ≤
            x ^ (1 / 4 : ℝ) * (x ^ (1 / 4 : ℝ) * x ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hCp hNhi hNpos.le (Real.rpow_nonneg hxpos.le _))
            (Real.rpow_nonneg hxpos.le _)
        _ = x := by
          rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
          norm_num
        _ ≤ M x i * (C * N x i) := by
          have hm := (div_le_iff₀ hCpos).mp hMNlo
          nlinarith only [hm]
    refine ⟨hMNlo, hMNhi, ?_, ?_⟩
    · exact (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)).trans hMquarter
    · exact (Real.rpow_le_rpow_of_exponent_le hx1
        (by linarith only [hσlt] : (1 / 8 : ℝ) ≤ 1 / 2 - σ)).trans hNlo
  have hsupportBase := fun x (hx : Xbase ≤ x) => hsupport x (hXbase₀.trans hx)
  have hcoeffBase := fun x (hx : Xbase ≤ x) => hcoeff x (hXbase₀.trans hx)
  have hSWbase : ∀ A : ℝ, 0 < A →
      ∃ KSW XSW : ℝ, 0 < KSW ∧ Xbase ≤ XSW ∧
        ∀ x : ℝ, XSW ≤ x → ∀ i : ι,
        ∀ q r a : ℕ, 0 < q → 0 < r → Nat.Coprime a q →
          ‖fullDiscrepancy ((β x i).filter (fun n : ℕ => Nat.Coprime n r)) q a‖ ≤
            KSW * ((q * r).divisors.card : ℝ) ^ s * N x i / (Real.log x) ^ A := by
    intro A hA
    obtain ⟨KSW, XSW, hKSW, _, hSW'⟩ := hSW A hA
    exact ⟨KSW, max Xbase XSW, hKSW, le_max_left _ _,
      fun x hx => hSW' x ((le_max_right _ _).trans hx)⟩
  intro A hA
  obtain ⟨B, KBV, XBV, hBpos, hKBV, hXBV, hBV⟩ :=
    balanced_bv_masked_uniform_log_saving M N α β c C W (1 / 8) Xbase k s
      hc hCscale hW (by norm_num) hXbase hbalanced hsupportBase hcoeffBase hSWbase A hA
  obtain ⟨KM, XM, hKM, hXM, hMean⟩ :=
    balanced_bv_meanTerm_uniform_log_saving M N α β c C W (1 / 8) Xbase k s
      hc hCscale hW (by norm_num) hXbase hbalanced hsupportBase hcoeffBase hSWbase
      θ (1 / 2 - 2 * ε) hθpos.le (by linarith only [hε]) A hA
  obtain ⟨KE, XE, hKE, hXE, hExceptional⟩ :=
    exceptional_smallPrimePart_fullDiscrepancy_log_saving
      θ hθpos hθlt (2 * k + 1) 0 (2 * k : ℕ) (C ^ 3)
      (one_le_pow₀ hCscale) A hA
  obtain ⟨XL, _hXL, hLow⟩ :=
    hsource C' c' C' c' C' hC' hc' hc'C' hc' hc'C'
      k k k k (A + 2) 1 (by linarith only [hA]) zero_lt_one
  have hZevent : ∀ᶠ x : ℝ in Filter.atTop,
      Real.exp ((Real.log x) ^ (2 / 3 : ℝ)) ≤ x ^ ε := by
    simpa only [Real.rpow_zero, one_mul] using
      small_prime_density_scale_absorption 0 ε hε
  have hLogevent : ∀ᶠ x : ℝ in Filter.atTop,
      ‖(Real.log x) ^ B‖ ≤ ‖x ^ ε‖ := by
    simpa only [one_mul] using
      (isLittleO_log_rpow_rpow_atTop B hε).bound (by norm_num : (0 : ℝ) < 1)
  obtain ⟨XZ, hXZ⟩ := Filter.eventually_atTop.mp hZevent
  obtain ⟨XP, hXP⟩ := Filter.eventually_atTop.mp hLogevent
  let X : ℝ := max XBV (max XM (max XE (max XL (max XZ XP))))
  let Dθ : ℝ := 1 + θ / Real.log 2
  have hDθ : 0 < Dθ := by
    dsimp only [Dθ]
    exact add_pos zero_lt_one (div_pos hθpos (Real.log_pos (by norm_num)))
  let K : ℝ := KBV + KE * W ^ 2 + KM + C * Dθ ^ 2
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, X, hK, hXbase₀.trans (hXBV.trans (le_max_left _ _)), ?_⟩
  intro x hx i I hI a ha
  have hthresholds : XBV ≤ x ∧ XM ≤ x ∧ XE ≤ x ∧ XL ≤ x ∧ XZ ≤ x ∧ XP ≤ x := by
    simpa only [X, max_le_iff] using hx
  obtain ⟨hxBV, hxM, hxE, hxL, hxZ, hxP⟩ := hthresholds
  have hxbase : Xbase ≤ x := hXBV.trans hxBV
  have hx₀ : X₀ ≤ x := hXbase₀.trans hxbase
  have hxexp : Real.exp 1 ≤ x := hX₀.trans hx₀
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hxexp
  have hx1 : 1 ≤ x :=
    (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans hxexp
  have hlog1 : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hxexp
  have hlogpos : 0 < Real.log x := zero_lt_one.trans_le hlog1
  obtain ⟨hMNlo, hMNhi, hNlo, hNhi⟩ := hscale x hx₀ i
  have hNpos : 0 < N x i := (Real.rpow_pos_of_pos hxpos _).trans_le hNlo
  have hMpos : 0 < M x i :=
    pos_of_mul_pos_left ((div_pos hxpos hCpos).trans_le hMNlo) hNpos.le
  have hMNpos : 0 < M x i * N x i := mul_pos hMpos hNpos
  let f : ℕ →₀ ℂ := finiteConvolution (α x i) (β x i)
  let Y : Set.Ici (1 : ℝ) :=
    ⟨max 1 (x ^ δ), le_max_left (1 : ℝ) (x ^ δ)⟩
  let Z : Set.Ici (1 : ℝ) :=
    ⟨Real.exp ((Real.log x) ^ (2 / 3 : ℝ)),
      Real.one_le_exp_iff.mpr (Real.rpow_nonneg hlogpos.le _)⟩
  let cutoff : ℕ := ⌊x ^ θ⌋₊
  let cutoffSmall : ℕ := ⌊x ^ (1 / 2 - ε)⌋₊
  let Brough : ℕ := ⌊Real.exp ((Real.log x) ^ (1 / 3 : ℝ))⌋₊
  let S₀ : Finset ℕ := tripleSourceModuli Y cutoff I
  let E : Finset ℕ := S₀.filter fun q =>
    cutoffSmall < q ∧ (smallPrimePart Brough q : ℝ) ≤ (Z : ℝ)
  let T : ℝ := x ^ (-3 * ε) * N x i
  have hY : (Y : ℝ) = x ^ δ := max_eq_right
    (Real.one_le_rpow hx1 hδ.le)
  have hZ : (Z : ℝ) ≤ x ^ ε := hXZ x hxZ
  have hYworking : (inflatedScale Y Z : ℝ) ≤ max 1 (x ^ δ') := by
    change (Y : ℝ) * (Z : ℝ) ≤ max 1 (x ^ δ')
    calc
      (Y : ℝ) * (Z : ℝ) ≤ x ^ δ * x ^ ε := by
        rw [hY]
        exact mul_le_mul_of_nonneg_left hZ (Real.rpow_nonneg hxpos.le _)
      _ = x ^ (δ + ε) := (Real.rpow_add hxpos _ _).symm
      _ ≤ x ^ δ' := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith only [hεδ, hε])
      _ ≤ max 1 (x ^ δ') := le_max_right _ _
  have hT : 1 ≤ T := by
    calc
      1 ≤ x ^ (-3 * ε + (1 / 2 - σ)) :=
        Real.one_le_rpow hx1 (by linarith only [hεbound, hσlt])
      _ = x ^ (-3 * ε) * x ^ (1 / 2 - σ) := Real.rpow_add hxpos _ _
      _ ≤ T := mul_le_mul_of_nonneg_left hNlo (Real.rpow_nonneg hxpos.le _)
  have hTsmall : T ≤ x ^ (1 / 2 - ε) := by
    calc
      T ≤ x ^ (-3 * ε) * x ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hNhi (Real.rpow_nonneg hxpos.le _)
      _ = x ^ (-3 * ε + 1 / 2) := (Real.rpow_add hxpos _ _).symm
      _ ≤ x ^ (1 / 2 - ε) := Real.rpow_le_rpow_of_exponent_le hx1
        (by linarith only [hε])
  have hTZ : T * (Z : ℝ) ≤ x ^ (-2 * ε) * N x i := by
    calc
      T * (Z : ℝ) ≤ (x ^ (-3 * ε) * N x i) * x ^ ε :=
        mul_le_mul_of_nonneg_left hZ (zero_le_one.trans hT)
      _ = x ^ (-2 * ε) * N x i := by
        rw [mul_right_comm, ← Real.rpow_add hxpos,
          show -3 * ε + ε = -2 * ε by ring]
  have hS₀data (q : ℕ) (hq : q ∈ S₀) :
      0 < q ∧ q ≤ cutoff ∧ q ∣ ∏ p ∈ I, p := by
    obtain ⟨hinterval, hdiv, _⟩ := Finset.mem_filter.mp hq
    exact ⟨(Finset.mem_Icc.mp hinterval).1,
      (Finset.mem_Icc.mp hinterval).2, hdiv⟩
  have hS₀subset : S₀ ⊆ Finset.Icc 1 ⌊x ^ θ⌋₊ := by
    intro q hq
    exact Finset.mem_Icc.mpr ⟨(hS₀data q hq).1, (hS₀data q hq).2.1⟩
  have hS₀primitive (q : ℕ) (hq : q ∈ S₀) : Nat.Coprime a q :=
    ha.of_dvd_right (hS₀data q hq).2.2
  have hlogB : (Real.log x) ^ B ≤ x ^ ε := by
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hlogpos.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le _)] using hXP x hxP
  have hsmallcut : x ^ (1 / 2 - ε) ≤ Real.sqrt x / (Real.log x) ^ B := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hlogpos B)).mpr
    calc
      x ^ (1 / 2 - ε) * (Real.log x) ^ B ≤ x ^ (1 / 2 - ε) * x ^ ε :=
        mul_le_mul_of_nonneg_left hlogB (Real.rpow_nonneg hxpos.le _)
      _ = x ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hxpos]
        congr 1
        ring
      _ = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
  let U : ℕ := ⌊Real.sqrt x / (Real.log x) ^ B⌋₊
  have hsmallU : cutoffSmall ≤ U := Nat.floor_mono hsmallcut
  let F (q : ℕ) : ℝ := ⨆ b : (ZMod q)ˣ, ‖fullDiscrepancy f q (b : ZMod q).val‖
  have hFnonneg (q : ℕ) (hq : 0 < q) : 0 ≤ F q := by
    let : NeZero q := ⟨hq.ne'⟩
    have hb : BddAbove (Set.range fun b : (ZMod q)ˣ =>
        ‖fullDiscrepancy f q (b : ZMod q).val‖) := (Set.finite_range _).bddAbove
    exact (norm_nonneg _).trans (le_ciSup hb (1 : (ZMod q)ˣ))
  have hFbound (q : ℕ) (hq : q ∈ S₀) : ‖fullDiscrepancy f q a‖ ≤ F q := by
    let : NeZero q := ⟨(hS₀data q hq).1.ne'⟩
    have hb : BddAbove (Set.range fun b : (ZMod q)ˣ =>
        ‖fullDiscrepancy f q (b : ZMod q).val‖) := (Set.finite_range _).bddAbove
    have heq : ‖fullDiscrepancy f q
        (ZMod.unitOfCoprime a (hS₀primitive q hq) : ZMod q).val‖ =
          ‖fullDiscrepancy f q a‖ := by
      simp only [ZMod.coe_unitOfCoprime, ZMod.val_natCast, fullDiscrepancy,
        progressionMass, Nat.mod_mod]
    exact heq.symm.trans_le (le_ciSup hb (ZMod.unitOfCoprime a (hS₀primitive q hq)))
  have hfilterOne : f.filter (fun n : ℕ => Nat.Coprime n 1) = f := by
    ext n
    simp only [Finsupp.filter_apply]
    exact ite_eq_left (Nat.coprime_one_right n)
  have hBVone : (∑ q ∈ Finset.Ioc 0 U, F q) ≤ KBV * x / (Real.log x) ^ A := by
    have hb := hBV x hxBV i 1 zero_lt_one
    change (∑ q ∈ Finset.Ioc 0 U,
      ⨆ b : (ZMod q)ˣ, ‖fullDiscrepancy
        (f.filter (fun n : ℕ => Nat.Coprime n 1)) q (b : ZMod q).val‖) ≤ _ at hb
    rw [hfilterOne] at hb
    simpa only [Nat.divisors_one, Finset.card_singleton, Nat.cast_one,
      one_pow, mul_one, F] using hb
  have hsmallBound :
      (∑ q ∈ S₀.filter (fun q => q ≤ cutoffSmall), ‖fullDiscrepancy f q a‖) ≤
        KBV * x / (Real.log x) ^ A := by
    calc
      (∑ q ∈ S₀.filter (fun q => q ≤ cutoffSmall), ‖fullDiscrepancy f q a‖) ≤
          ∑ q ∈ S₀.filter (fun q => q ≤ cutoffSmall), F q :=
        Finset.sum_le_sum fun q hq => hFbound q (Finset.mem_filter.mp hq).1
      _ ≤ ∑ q ∈ Finset.Ioc 0 U, F q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          obtain ⟨hqS, hqcut⟩ := Finset.mem_filter.mp hq
          exact Finset.mem_Ioc.mpr ⟨(hS₀data q hqS).1, hqcut.trans hsmallU⟩
        · intro q hq _
          exact hFnonneg q (Finset.mem_Ioc.mp hq).1
      _ ≤ KBV * x / (Real.log x) ^ A := hBVone
  obtain ⟨hfSupport, hfCoeff⟩ := finiteConvolution_support_and_divisor_bound
    (α x i) (β x i) x (M x i) (N x i) c C W k
      hx1 hMpos hNpos hc hCscale hW hMNhi
      (hsupport x hx₀ i).1 (hsupport x hx₀ i).2
      (fun n _ => (hcoeff x hx₀ i n).1) (fun n _ => (hcoeff x hx₀ i n).2)
  have hExceptionalBound :
      (∑ q ∈ S₀.filter (fun q => (Z : ℝ) < (smallPrimePart Brough q : ℝ)),
        ‖fullDiscrepancy f q a‖) ≤ KE * W ^ 2 * x / (Real.log x) ^ A := by
    have hcoefE : ∀ n ∈ f.support,
        ‖f n‖ ≤ W ^ 2 * (n.divisors.card : ℝ) ^ (2 * k + 1) *
          (Real.log x) ^ ((2 * k : ℕ) : ℝ) := by
      intro n _
      simpa only [Real.rpow_natCast, f] using hfCoeff n
    have he := hExceptional x hxE (W ^ 2) (sq_nonneg W) S₀ hS₀subset
      (fun _ => a) hS₀primitive f hfSupport hcoefE
    simpa only [pow_zero, one_mul, Brough, Z] using he
  have hEdata (n : ℕ) (hn : n ∈ E) :
      n ∈ tripleSourceModuli Y cutoff I ∧ T ≤ (n : ℝ) ∧
        (smallPrimePart Brough n : ℝ) ≤ (Z : ℝ) := by
    obtain ⟨hnS, hnlarge, hnsmall⟩ := Finset.mem_filter.mp hn
    exact ⟨hnS, hTsmall.trans (Nat.lt_of_floor_lt hnlarge).le, hnsmall⟩
  obtain ⟨S, hSsum, hS⟩ := hselect_pairs Y Z Brough cutoff T I hI hT E hEdata
  have hSpair (p : ℕ × ℕ) (hp : p ∈ S) :
      0 < p.1 ∧ 0 < p.2 ∧ p.1 ≤ cutoff ∧ p.2 ≤ cutoff ∧
        Nat.Coprime p.1 p.2 ∧ Nat.Coprime a (p.1 * p.2) := by
    obtain ⟨hq, hr, hsf, hpE, _, _, _, _, _, _⟩ := hS p hp
    have hpS : p.1 * p.2 ∈ S₀ := (Finset.mem_filter.mp hpE).1
    have hcut := (hS₀data _ hpS).2.1
    exact ⟨hq, hr, (Nat.le_mul_of_pos_right _ hr).trans hcut,
      (Nat.le_mul_of_pos_left _ hq).trans hcut,
      Nat.coprime_of_squarefree_mul hsf, hS₀primitive _ hpS⟩
  have hSmean (p : ℕ × ℕ) (hp : p ∈ S) :
      0 < p.1 ∧ p.1 ≤ ⌊x ^ θ⌋₊ ∧
        0 < p.2 ∧ p.2 ≤ ⌊x ^ (1 / 2 - 2 * ε)⌋₊ ∧ Nat.Coprime p.1 p.2 := by
    obtain ⟨hq, hr, hqcut, _, hcop, _⟩ := hSpair p hp
    refine ⟨hq, hqcut, hr, ?_, hcop⟩
    apply (Nat.le_floor_iff (Real.rpow_nonneg hxpos.le _)).mpr
    calc
      (p.2 : ℝ) ≤ T * (Z : ℝ) := (hS p hp).2.2.2.2.2.2.1
      _ ≤ x ^ (-2 * ε) * N x i := hTZ
      _ ≤ x ^ (-2 * ε) * x ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hNhi (Real.rpow_nonneg hxpos.le _)
      _ = x ^ (1 / 2 - 2 * ε) := by
        rw [← Real.rpow_add hxpos]
        congr 1
        ring
  have hMeanBound : (∑ p ∈ S, ‖meanTerm f p.1 p.2 a‖) ≤
      KM * x / (Real.log x) ^ A :=
    hMean x hxM i S hSmean a (fun p hp => (hSpair p hp).2.2.2.2.2)
  let γ : ℝ := Real.log (N x i) / Real.log x
  have hNγ : N x i = x ^ γ := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr hNpos)
      (Set.mem_Ioi.mpr (Real.rpow_pos_of_pos hxpos γ))
    rw [Real.log_rpow hxpos]
    dsimp only [γ]
    field_simp
  have hγlo : 1 / 2 - σ ≤ γ := by
    apply (le_div_iff₀ hlogpos).mpr
    have hn := Real.log_le_log (Real.rpow_pos_of_pos hxpos _) hNlo
    rwa [Real.log_rpow hxpos] at hn
  have hγhi : γ ≤ 1 / 2 := by
    apply (div_le_iff₀ hlogpos).mpr
    have hn := Real.log_le_log hNpos hNhi
    rwa [Real.log_rpow hxpos] at hn
  have hMNlo' : x / C' ≤ M x i * N x i :=
    (div_le_div_of_nonneg_left hxpos.le hCpos hC'C).trans hMNlo
  have hMNhi' : M x i * N x i ≤ C' * x :=
    hMNhi.trans (mul_le_mul_of_nonneg_right hC'C hxpos.le)
  have hαOpen : ∀ n ∈ (α x i).support,
      c' * M x i ≤ (n : ℝ) ∧ (n : ℝ) ≤ C' * M x i ∧
      ‖α x i n‖ ≤ C' * (n.divisors.card : ℝ) ^ k * (Real.log x) ^ (k : ℝ) := by
    intro n hn
    obtain ⟨hnlo, hnhi⟩ := (hsupport x hx₀ i).1 n hn
    refine ⟨(mul_le_mul_of_nonneg_right hc'c hMpos.le).trans hnlo,
      hnhi.trans (mul_le_mul_of_nonneg_right hC'C hMpos.le), ?_⟩
    rw [Real.rpow_natCast]
    exact (hcoeff x hx₀ i n).1.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC'W (pow_nonneg (Nat.cast_nonneg _) _))
        (pow_nonneg hlogpos.le _))
  have hβOpen : ∀ n ∈ (β x i).support,
      c' * N x i ≤ (n : ℝ) ∧ (n : ℝ) ≤ C' * N x i ∧
      ‖β x i n‖ ≤ C' * (n.divisors.card : ℝ) ^ k * (Real.log x) ^ (k : ℝ) := by
    intro n hn
    obtain ⟨hnlo, hnhi⟩ := (hsupport x hx₀ i).2 n hn
    refine ⟨(mul_le_mul_of_nonneg_right hc'c hNpos.le).trans hnlo,
      hnhi.trans (mul_le_mul_of_nonneg_right hC'C hNpos.le), ?_⟩
    rw [Real.rpow_natCast]
    exact (hcoeff x hx₀ i n).2.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC'W (pow_nonneg (Nat.cast_nonneg _) _))
        (pow_nonneg hlogpos.le _))
  let G : ℕ := ∏ p ∈ I, p
  have hG : 0 < G := hprime_product_pos I hI
  have hDeltaBound (b : ℕ) (hb : b ∈ primitiveResidues G) :
      (∑ p ∈ S, ‖deltaZero f p.1 p.2 a a b‖) ≤
        C * Dθ ^ 2 * x / (Real.log x) ^ A := by
    have hbG : Nat.Coprime b G := (Finset.mem_filter.mp hb).2
    have habG : Nat.Coprime (a * a * b) G := (ha.mul_left ha).mul_left hbG
    let J : Finset ℕ := Finset.Icc 0 (Nat.log 2 cutoff)
    let E₀ : ℝ := (M x i * N x i) * (Real.log x) ^ (-(A + 2))
    have hE₀ : 0 ≤ E₀ := mul_nonneg hMNpos.le (Real.rpow_nonneg hlogpos.le _)
    have hBand (j k' : ℕ) :
        (∑ p ∈ S.filter (fun p =>
            2 ^ j ≤ p.1 ∧ p.1 ≤ 2 * 2 ^ j ∧
            2 ^ k' ≤ p.2 ∧ p.2 ≤ 2 * 2 ^ k'),
          ‖deltaZero f p.1 p.2 a a b‖) ≤ E₀ := by
      let Q : ℝ := (2 ^ j : ℕ)
      let R : ℝ := (2 ^ k' : ℕ)
      let S' : Finset (ℕ × ℕ) := S.filter fun p =>
        2 ^ j ≤ p.1 ∧ p.1 ≤ 2 * 2 ^ j ∧
        2 ^ k' ≤ p.2 ∧ p.2 ≤ 2 * 2 ^ k'
      have hQ : 0 < Q := Nat.cast_pos.mpr (pow_pos (by norm_num) _)
      have hR : 0 < R := Nat.cast_pos.mpr (pow_pos (by norm_num) _)
      by_cases hS' : S' = ∅
      · change (∑ p ∈ S', ‖deltaZero f p.1 p.2 a a b‖) ≤ E₀
        simpa only [hS', Finset.sum_empty] using hE₀
      obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hS'
      obtain ⟨hpS, hqloN, hqhiN, hrloN, hrhiN⟩ := Finset.mem_filter.mp hp
      obtain ⟨hqpos, hrpos, hsf, hpE, hpdiv, hrloT, hrhiT, hdq, hdr, hrough⟩ :=
        hS p hpS
      have hqlo : Q ≤ (p.1 : ℝ) := by dsimp only [Q]; exact_mod_cast hqloN
      have hqhi : (p.1 : ℝ) ≤ 2 * Q := by dsimp only [Q]; exact_mod_cast hqhiN
      have hrlo : R ≤ (p.2 : ℝ) := by dsimp only [R]; exact_mod_cast hrloN
      have hrhi : (p.2 : ℝ) ≤ 2 * R := by dsimp only [R]; exact_mod_cast hrhiN
      have hqp : (0 : ℝ) ≤ p.1 := Nat.cast_nonneg _
      have hrp : (0 : ℝ) ≤ p.2 := Nat.cast_nonneg _
      have hprodlo : R * Q ≤ (p.1 : ℝ) * p.2 := by
        simpa only [mul_comm] using mul_le_mul hqlo hrlo hR.le hqp
      have hprodhi : (p.1 : ℝ) * p.2 ≤ 4 * (R * Q) := by
        have hm := mul_le_mul hqhi hrhi hrp (by positivity : 0 ≤ 2 * Q)
        nlinarith only [hm]
      obtain ⟨hpSource, hpLarge, _⟩ := Finset.mem_filter.mp hpE
      have hlarge : x ^ (1 / 2 - ε) < (p.1 : ℝ) * p.2 := by
        exact_mod_cast Nat.lt_of_floor_lt hpLarge
      have hupper : (p.1 : ℝ) * p.2 ≤ x ^ θ := by
        have hh : ((p.1 * p.2 : ℕ) : ℝ) ≤ (cutoff : ℝ) :=
          Nat.cast_le.mpr (hS₀data _ hpSource).2.1
        have hpcast : (p.1 : ℝ) * p.2 ≤ (cutoff : ℝ) := by
          simpa only [Nat.cast_mul] using hh
        exact hpcast.trans (Nat.floor_le (Real.rpow_nonneg hxpos.le _))
      have hRQlo : x ^ (1 / 2 - ε) ≤ C' * R * Q := by
        have hc := mul_le_mul_of_nonneg_right hC'4 (mul_nonneg hR.le hQ.le)
        nlinarith only [hlarge, hprodhi, hc]
      have hRQhi : R * Q ≤ C' * x ^ (1 / 2 + 2 * ω' + ε) := by
        calc
          R * Q ≤ x ^ θ := hprodlo.trans hupper
          _ ≤ x ^ (1 / 2 + 2 * ω' + ε) :=
            Real.rpow_le_rpow_of_exponent_le hx1
              (by dsimp only [θ]; linarith only [hωw, hε])
          _ ≤ C' * x ^ (1 / 2 + 2 * ω' + ε) :=
            le_mul_of_one_le_left (Real.rpow_nonneg hxpos.le _) hC'
      have hRhi : R ≤ C' * x ^ (-2 * ε) * N x i := by
        calc
          R ≤ (p.2 : ℝ) := hrlo
          _ ≤ T * (Z : ℝ) := hrhiT
          _ ≤ x ^ (-2 * ε) * N x i := hTZ
          _ ≤ C' * x ^ (-2 * ε) * N x i :=
            mul_le_mul_of_nonneg_right
              (le_mul_of_one_le_left (Real.rpow_nonneg hxpos.le (-2 * ε)) hC')
              hNpos.le
      have hNfromR : N x i ≤ C' * x ^ (δ' + 4 * ε) * R := by
        have hYpos : 0 < (Y : ℝ) := zero_lt_one.trans_le Y.property
        have ht := (div_le_iff₀ hYpos).mp hrloT
        have hNr : N x i ≤ x ^ (δ + 3 * ε) * (p.2 : ℝ) := by
          calc
            N x i = x ^ (3 * ε) * T := by
              dsimp only [T]
              rw [← mul_assoc, ← Real.rpow_add hxpos]
              rw [show 3 * ε + -3 * ε = 0 by ring, Real.rpow_zero, one_mul]
            _ ≤ x ^ (3 * ε) * ((p.2 : ℝ) * (Y : ℝ)) :=
              mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hxpos.le _)
            _ = x ^ (δ + 3 * ε) * (p.2 : ℝ) := by
              rw [hY]
              calc
                x ^ (3 * ε) * ((p.2 : ℝ) * x ^ δ) =
                    (x ^ (3 * ε) * x ^ δ) * (p.2 : ℝ) := by ring
                _ = x ^ (δ + 3 * ε) * (p.2 : ℝ) := by
                  rw [← Real.rpow_add hxpos,
                    show 3 * ε + δ = δ + 3 * ε by ring]
        calc
          N x i ≤ x ^ (δ + 3 * ε) * (p.2 : ℝ) := hNr
          _ ≤ x ^ (δ + 3 * ε) * (2 * R) :=
            mul_le_mul_of_nonneg_left hrhi (Real.rpow_nonneg hxpos.le _)
          _ ≤ x ^ (δ' + 4 * ε) * (2 * R) :=
            mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith only [hδw, hε]))
              (by positivity)
          _ ≤ C' * x ^ (δ' + 4 * ε) * R := by
            calc
              x ^ (δ' + 4 * ε) * (2 * R) = (2 * x ^ (δ' + 4 * ε)) * R := by ring
              _ ≤ (C' * x ^ (δ' + 4 * ε)) * R :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right
                    (by linarith only [hC'4] : (2 : ℝ) ≤ C')
                    (Real.rpow_nonneg hxpos.le (δ' + 4 * ε))) hR.le
      have hSource : ∀ t ∈ S',
          0 < t.1 ∧ 0 < t.2 ∧ Squarefree (t.1 * t.2) ∧
          Q ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) ≤ 2 * Q ∧
          R ≤ (t.2 : ℝ) ∧ (t.2 : ℝ) ≤ 2 * R ∧
          Nonempty (DenseDivisibilityWitness
            ⟨max 1 (x ^ δ'), le_max_left (1 : ℝ) (x ^ δ')⟩ 1 t.1) ∧
          Nonempty (DenseDivisibilityWitness
            ⟨max 1 (x ^ δ'), le_max_left (1 : ℝ) (x ^ δ')⟩ 1 t.2) ∧
          (∀ u ∈ t.1.primeFactors,
            Real.exp ((Real.log x) ^ (1 / 3 : ℝ)) < (u : ℝ)) := by
        intro t ht
        obtain ⟨htS, htqlo, htqhi, htrlo, htrhi⟩ := Finset.mem_filter.mp ht
        obtain ⟨htq, htr, htsf, _, _, _, _, htdq, htdr, htrough⟩ := hS t htS
        refine ⟨htq, htr, htsf, ?_, ?_, ?_, ?_,
          denseDivisibility_mono_scale hYworking htdq,
          denseDivisibility_mono_scale hYworking htdr, ?_⟩
        · dsimp only [Q]
          exact_mod_cast htqlo
        · dsimp only [Q]
          exact_mod_cast htqhi
        · dsimp only [R]
          exact_mod_cast htrlo
        · dsimp only [R]
          exact_mod_cast htrhi
        · intro u hu
          exact Nat.lt_of_floor_lt (htrough u hu)
      have hPrimitive : ∀ t ∈ S', Nat.Coprime (a * a * b) (t.1 * t.2) := by
        intro t ht
        exact habG.of_dvd_right (hS t (Finset.mem_filter.mp ht).1).2.2.2.2.1
      simpa only [one_mul, f, S', E₀] using
        hLow x hxL (M x i) (N x i) R Q γ hMpos hNpos hR hQ
          hMNlo' hMNhi' hNγ hγlo hγhi
          hNfromR hRhi hRQlo hRQhi (α x i) (β x i) hαOpen hβOpen S' hSource
          a a b hPrimitive
    have hcover := hpair_dyadic_cover S
      (fun p => ‖deltaZero f p.1 p.2 a a b‖) cutoff cutoff
      (fun p hp => ⟨(hSpair p hp).1, (hSpair p hp).2.2.1,
        (hSpair p hp).2.1, (hSpair p hp).2.2.2.1⟩)
      (fun _ _ => norm_nonneg _)
    have hcard : (J.card : ℝ) ≤ Dθ * Real.log x :=
      by simpa only [J, Nat.card_Icc, Nat.sub_zero, Dθ] using
        hdyadic_bin_count x θ cutoff hxexp hθpos.le le_rfl
    calc
      (∑ p ∈ S, ‖deltaZero f p.1 p.2 a a b‖) ≤
          ∑ j ∈ J, ∑ k' ∈ J,
            ∑ p ∈ S.filter (fun p =>
              2 ^ j ≤ p.1 ∧ p.1 ≤ 2 * 2 ^ j ∧
              2 ^ k' ≤ p.2 ∧ p.2 ≤ 2 * 2 ^ k'),
              ‖deltaZero f p.1 p.2 a a b‖ := hcover
      _ ≤ ∑ _j ∈ J, ∑ _k ∈ J, E₀ :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k' _ => hBand j k'
      _ = (J.card : ℝ) ^ 2 * E₀ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ (Dθ * Real.log x) ^ 2 * E₀ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) hE₀
      _ ≤ (Dθ * Real.log x) ^ 2 * ((C * x) * (Real.log x) ^ (-(A + 2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hMNhi (Real.rpow_nonneg hlogpos.le _))
          (sq_nonneg _)
      _ = C * Dθ ^ 2 * x / (Real.log x) ^ A := by
        rw [Real.rpow_neg hlogpos.le, Real.rpow_add hlogpos, Real.rpow_two]
        field_simp
  have hDispersionBound : (∑ p ∈ S, ‖dispersionTerm f p.1 p.2 a‖) ≤
      C * Dθ ^ 2 * x / (Real.log x) ^ A := by
    apply (sum_norm_dispersion_le_global_average f hG S ?_ a).trans
      (hprimitive_average_le G hG
        (fun b => ∑ p ∈ S, ‖deltaZero f p.1 p.2 a a b‖)
        (C * Dθ ^ 2 * x / (Real.log x) ^ A) hDeltaBound)
    intro p hp
    exact ⟨(hSpair p hp).2.2.2.2.1,
      (dvd_mul_right p.1 p.2).trans (hS p hp).2.2.2.2.1⟩
  have hGoodBound : (∑ q ∈ E, ‖fullDiscrepancy f q a‖) ≤
      (C * Dθ ^ 2 + KM) * x / (Real.log x) ^ A := by
    rw [hSsum]
    calc
      (∑ p ∈ S, ‖fullDiscrepancy f (p.1 * p.2) a‖) ≤
          ∑ p ∈ S, (‖dispersionTerm f p.1 p.2 a‖ + ‖meanTerm f p.1 p.2 a‖) := by
        apply Finset.sum_le_sum
        intro p _
        rw [fullDiscrepancy_eq_dispersion_add_mean]
        exact norm_add_le _ _
      _ = (∑ p ∈ S, ‖dispersionTerm f p.1 p.2 a‖) +
          ∑ p ∈ S, ‖meanTerm f p.1 p.2 a‖ := Finset.sum_add_distrib
      _ ≤ C * Dθ ^ 2 * x / (Real.log x) ^ A + KM * x / (Real.log x) ^ A :=
        add_le_add hDispersionBound hMeanBound
      _ = (C * Dθ ^ 2 + KM) * x / (Real.log x) ^ A := by ring
  have hSplit : (∑ q ∈ S₀, ‖fullDiscrepancy f q a‖) ≤
      (∑ q ∈ S₀.filter (fun q => q ≤ cutoffSmall), ‖fullDiscrepancy f q a‖) +
      (∑ q ∈ S₀.filter (fun q => (Z : ℝ) < (smallPrimePart Brough q : ℝ)),
        ‖fullDiscrepancy f q a‖) +
      ∑ q ∈ E, ‖fullDiscrepancy f q a‖ := by
    dsimp only [E]
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro q _
    by_cases hsmall : q ≤ cutoffSmall
    · by_cases hbad : (Z : ℝ) < (smallPrimePart Brough q : ℝ)
      · simp only [hsmall, hbad, not_lt_of_ge hsmall, false_and,
          ite_true, ite_false, add_zero]
        exact le_add_of_nonneg_right (norm_nonneg _)
      · simp only [hsmall, hbad, not_lt_of_ge hsmall, false_and,
          ite_true, ite_false, add_zero, le_refl]
    · have hlarge : cutoffSmall < q := lt_of_not_ge hsmall
      by_cases hbad : (Z : ℝ) < (smallPrimePart Brough q : ℝ)
      · simp only [hsmall, hbad, hlarge, not_le_of_gt hbad, and_false,
          ite_true, ite_false, zero_add, add_zero, le_refl]
      · have hgood : (smallPrimePart Brough q : ℝ) ≤ (Z : ℝ) := le_of_not_gt hbad
        simp only [hsmall, hbad, hlarge, hgood, and_self,
          ite_true, ite_false, zero_add, le_refl]
  change (∑ q ∈ S₀, ‖fullDiscrepancy f q a‖) ≤ K * x / (Real.log x) ^ A
  calc
    (∑ q ∈ S₀, ‖fullDiscrepancy f q a‖) ≤
        (∑ q ∈ S₀.filter (fun q => q ≤ cutoffSmall), ‖fullDiscrepancy f q a‖) +
        (∑ q ∈ S₀.filter (fun q => (Z : ℝ) < (smallPrimePart Brough q : ℝ)),
          ‖fullDiscrepancy f q a‖) +
        ∑ q ∈ E, ‖fullDiscrepancy f q a‖ := hSplit
    _ ≤ KBV * x / (Real.log x) ^ A + KE * W ^ 2 * x / (Real.log x) ^ A +
        (C * Dθ ^ 2 + KM) * x / (Real.log x) ^ A :=
      add_le_add (add_le_add hsmallBound hExceptionalBound) hGoodBound
    _ = K * x / (Real.log x) ^ A := by dsimp only [K]; ring

#print axioms sourceBilinearEstimate_three_of_dyadic
end PrimeGap182Audit
