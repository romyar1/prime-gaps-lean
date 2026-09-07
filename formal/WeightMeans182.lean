import SourceOrdinaryMoments182

/-! Actual shifted means of the prime indicator, sharp minorant, and sharp
defect.  The finite shift changes at most twice the shift many terms.
No progression estimate is assumed in these mean theorems. -/

noncomputable section
open MeasureTheory Filter PrimeGap186
open scoped BigOperators Topology

namespace PrimeGap182Analytic

def selbergWeight182 (w : Fin 3) (x : ℝ) (n : ℕ) : ℝ :=
  ![primeIndicator n, sharpMinorant x (41361 / 100000) n,
    sharpDefect x (41361 / 100000) n] w

def selbergWeightMean182 (w : Fin 3) : ℝ :=
  ![1, 1 - SharpMean.sharpMass, SharpMean.sharpMass] w

theorem selbergWeight182_abs_le (w : Fin 3) (x : ℝ) (n : ℕ) :
    |selbergWeight182 w x n| ≤ 25 := by
  classical
  fin_cases w <;> dsimp [selbergWeight182, primeIndicator,
    sharpMinorant, sharpDefect] <;> split_ifs <;> norm_num

theorem shifted_Icc_sum_sub_abs_le (a b h : ℕ) (f : ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hf : ∀ n, |f n| ≤ C) :
    |(∑ n ∈ Finset.Icc a b, f (n + h)) - ∑ n ∈ Finset.Icc a b, f n| ≤
      2 * (h : ℝ) * C := by
  classical
  let S := Finset.Icc a b
  let T := Finset.Icc (a + h) (b + h)
  have hshift : (∑ n ∈ Finset.Icc a b, f (n + h)) = ∑ n ∈ T, f n := by
    dsimp only [T]
    rw [← Finset.map_add_right_Icc a b h, Finset.sum_map]
    rfl
  have hTS : T \ S ⊆ Finset.Ioc b (b + h) := by
    intro n hn
    simp only [T, S, Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc] at hn ⊢
    omega
  have hST : S \ T ⊆ Finset.Ico a (a + h) := by
    intro n hn
    simp only [T, S, Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ico] at hn ⊢
    omega
  have hsum (U : Finset ℕ) (hcard : U.card ≤ h) : |∑ n ∈ U, f n| ≤ (h : ℝ) * C := by
    calc
      _ ≤ ∑ n ∈ U, |f n| := Finset.abs_sum_le_sum_abs f U
      _ ≤ ∑ n ∈ U, C := Finset.sum_le_sum (fun n _ => hf n)
      _ = (U.card : ℝ) * C := by simp
      _ ≤ (h : ℝ) * C := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hC
  have hsumTS := hsum (T \ S) (by simpa using Finset.card_le_card hTS)
  have hsumST := hsum (S \ T) (by simpa using Finset.card_le_card hST)
  rw [hshift]
  change |(∑ n ∈ T, f n) - ∑ n ∈ S, f n| ≤ _
  rw [← Finset.sum_sdiff_sub_sum_sdiff (s₁ := S) (s₂ := T) (f := f)]
  calc
    _ ≤ |∑ n ∈ T \ S, f n| + |∑ n ∈ S \ T, f n| := abs_sub _ _
    _ ≤ (h : ℝ) * C + (h : ℝ) * C := add_le_add hsumTS hsumST
    _ = _ := by ring

theorem bounded_fixed_shift_mean (f : ℝ → ℕ → ℝ) (C L : ℝ)
    (hC : 0 ≤ C) (hf : ∀ x n, |f x n| ≤ C)
    (hmean : Tendsto (fun x : ℝ => Real.log x / x *
      ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊, f x n) atTop (nhds L)) (h : ℕ) :
    Tendsto (fun x : ℝ => Real.log x / x *
      ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊, f x (n + h)) atTop (nhds L) := by
  let E (x : ℝ) := Real.log x / x *
    ((∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊, f x (n + h)) -
      ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊, f x n)
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have herr : Tendsto (fun x : ℝ => (2 * (h : ℝ) * C) * (Real.log x / x))
      atTop (nhds 0) := by simpa only [mul_zero] using hlog.const_mul (2 * (h : ℝ) * C)
  have hE : Tendsto E atTop (nhds 0) := by
    apply squeeze_zero_norm' _ herr
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hL : 0 ≤ Real.log x / x :=
      div_nonneg (Real.log_nonneg hx.le) (zero_lt_one.trans hx).le
    have hh := mul_le_mul_of_nonneg_left
      (shifted_Icc_sum_sub_abs_le ⌈x⌉₊ ⌊2 * x⌋₊ h (f x) C hC (hf x)) hL
    simpa only [E, Real.norm_eq_abs, abs_mul, abs_of_nonneg hL, mul_comm] using hh
  convert hE.add hmean using 1
  · funext x
    dsimp only [E]
    ring
  · simp only [zero_add]

theorem selbergWeight182_mean (w : Fin 3) :
    Tendsto (fun x : ℝ => Real.log x / x *
      ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊, selbergWeight182 w x n)
      atTop (nhds (selbergWeightMean182 w)) := by
  classical
  fin_cases w
  · change Tendsto (fun x : ℝ => Real.log x / x *
      ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊, if n.Prime then (1 : ℝ) else 0) atTop (nhds 1)
    simpa only [Finset.sum_boole] using closed_dyadic_prime_count_tendsto
  · exact SharpMean.sharpMinorant_signed_mean
  · exact SharpMean.sharpDefect_mass_tendsto

theorem selbergWeight182_shifted_mean (w : Fin 3) (h : ℕ) :
    Tendsto (fun x : ℝ => Real.log x / x *
      ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊, selbergWeight182 w x (n + h))
      atTop (nhds (selbergWeightMean182 w)) :=
  bounded_fixed_shift_mean (selbergWeight182 w) 25 (selbergWeightMean182 w)
    (by norm_num) (selbergWeight182_abs_le w) (selbergWeight182_mean w) h

#print axioms selbergWeight182_abs_le
#print axioms shifted_Icc_sum_sub_abs_le
#print axioms selbergWeight182_shifted_mean

end PrimeGap182Analytic
