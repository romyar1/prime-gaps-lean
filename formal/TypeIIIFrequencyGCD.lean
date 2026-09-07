import TypeIIIFrequencyDecay

/-!
# Actual all-width frequency gcd averaging

The frequency width K is any positive real number. Arithmetic divisor restrictions are
imposed on the actual integer frequency. No lower bound K ≥ 1 is used.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The nonzero decay envelope restricted to the actual multiples of d. -/
def frequencyDivisorDecay (d : ℕ) (K A : ℝ) (c : ℤ) : ℝ :=
  if (d : ℤ) ∣ c then integerFrequencyDecay K⁻¹ A c else 0

theorem frequencyDivisorDecay_nonneg (d : ℕ) {K : ℝ} (hK : 0 < K) (A : ℝ) (c : ℤ) :
    0 ≤ frequencyDivisorDecay d K A c := by
  unfold frequencyDivisorDecay
  split_ifs
  · exact integerFrequencyDecay_nonneg (inv_nonneg.mpr hK.le) A c
  · exact le_rfl

theorem frequencyDivisorDecay_mul (d : ℕ) (hd : 0 < d) (K A : ℝ) (c : ℤ) :
    frequencyDivisorDecay d K A ((d : ℤ) * c) =
      integerFrequencyDecay ((d : ℝ) / K) A c := by
  have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  simp only [frequencyDivisorDecay, dvd_mul_right, ite_true, integerFrequencyDecay,
    mul_eq_zero, hd', false_or, Int.cast_mul, Int.cast_natCast, abs_mul,
    abs_of_nonneg hd0, positiveFrequencyDecay]
  congr 2
  ring

/-- Exact multiple reindexing and the integral test yield the required bound on any
finite set of frequencies, including widths less than one. -/
theorem sum_frequencyDivisorDecay_le (F : Finset ℤ) (d : ℕ) (hd : 0 < d)
    {K A : ℝ} (hK : 0 < K) (hA : 1 < A) :
    (∑ c ∈ F, frequencyDivisorDecay d K A c) ≤
      2 * K / ((d : ℝ) * (A - 1)) := by
  have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hinj : Function.Injective (fun c : ℤ => (d : ℤ) * c) :=
    mul_right_injective₀ hd'
  let S := F.preimage (fun c : ℤ => (d : ℤ) * c) hinj.injOn
  have heq : (∑ c ∈ F, frequencyDivisorDecay d K A c) =
      ∑ c ∈ S, integerFrequencyDecay ((d : ℝ) / K) A c := by
    rw [← Finset.sum_preimage (fun c : ℤ => (d : ℤ) * c) F hinj.injOn
      (frequencyDivisorDecay d K A)]
    · apply Finset.sum_congr rfl
      intro c hc
      exact frequencyDivisorDecay_mul d hd K A c
    · intro c hc hnot
      unfold frequencyDivisorDecay
      apply ite_eq_right
      intro hdiv
      obtain ⟨b, hb⟩ := hdiv
      exact hnot ⟨b, hb.symm⟩
  have hs := integerFrequencyDecay_tsum (show 0 < (d : ℝ) / K by positivity) hA
  rw [heq]
  calc
    _ ≤ ∑' c : ℤ, integerFrequencyDecay ((d : ℝ) / K) A c :=
      hs.1.sum_le_tsum S (fun c hc => integerFrequencyDecay_nonneg (by positivity) A c)
    _ ≤ 2 / (((d : ℝ) / K) * (A - 1)) := hs.2
    _ = _ := by field_simp

/-- The positive arithmetic majorant uses all actual divisors of the frequency gcd. -/
theorem gcd_rpow_le_divisor_majorant (w : ℕ) (hw : 0 < w) (c : ℤ) (b : ℝ) :
    (Int.gcd c (w : ℤ) : ℝ) ^ b ≤
      ∑ d ∈ w.divisors, if (d : ℤ) ∣ c then (d : ℝ) ^ b else 0 := by
  let g := Int.gcd c (w : ℤ)
  have hgpos : 0 < g := by
    dsimp only [g]
    rw [Int.gcd_def, Int.natAbs_natCast]
    exact Nat.gcd_pos_of_pos_right _ hw
  have hgdw : g ∣ w := by
    dsimp only [g]
    rw [Int.gcd_def, Int.natAbs_natCast]
    exact Nat.gcd_dvd_right _ _
  have hgdc : (g : ℤ) ∣ c := by
    exact Int.gcd_dvd_left _ _
  have hmem : g ∈ w.divisors := Nat.mem_divisors.mpr ⟨hgdw, hw.ne'⟩
  calc
    _ = (if (g : ℤ) ∣ c then (g : ℝ) ^ b else 0) := by rw [ite_eq_left hgdc]
    _ ≤ _ := Finset.single_le_sum (f := fun d : ℕ => if (d : ℤ) ∣ c then (d : ℝ) ^ b else 0)
      (fun d hd => by split_ifs <;> positivity) hmem

/-- The normalized nonzero frequency weight with its actual gcd. -/
def frequencyGCDWeight (w : ℕ) (K A b : ℝ) (c : ℤ) : ℝ :=
  integerFrequencyDecay K⁻¹ A c / K * (Int.gcd c (w : ℤ) : ℝ) ^ b

theorem frequencyGCDWeight_nonneg (w : ℕ) {K : ℝ} (hK : 0 < K) (A b : ℝ) (c : ℤ) :
    0 ≤ frequencyGCDWeight w K A b c :=
  mul_nonneg (div_nonneg (integerFrequencyDecay_nonneg (inv_nonneg.mpr hK.le) A c) hK.le)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The exact all-width divisor majorant on every finite frequency set. -/
theorem sum_frequencyGCDWeight_le (F : Finset ℤ) (w : ℕ) (hw : 0 < w)
    {K A : ℝ} (hK : 0 < K) (hA : 1 < A) (b : ℝ) :
    (∑ c ∈ F, frequencyGCDWeight w K A b c) ≤
      2 / (A - 1) * ∑ d ∈ w.divisors, (d : ℝ) ^ (b - 1) := by
  have hmajor (c : ℤ) : frequencyGCDWeight w K A b c ≤
      ∑ d ∈ w.divisors, ((d : ℝ) ^ b / K) * frequencyDivisorDecay d K A c := by
    have hh := mul_le_mul_of_nonneg_left (gcd_rpow_le_divisor_majorant w hw c b)
      (div_nonneg (integerFrequencyDecay_nonneg (inv_nonneg.mpr hK.le) A c) hK.le)
    apply hh.trans_eq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    unfold frequencyDivisorDecay
    split_ifs <;> ring
  calc
    _ ≤ ∑ c ∈ F, ∑ d ∈ w.divisors, ((d : ℝ) ^ b / K) * frequencyDivisorDecay d K A c :=
      Finset.sum_le_sum (fun c hc => hmajor c)
    _ = ∑ d ∈ w.divisors, ((d : ℝ) ^ b / K) * ∑ c ∈ F, frequencyDivisorDecay d K A c := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ d ∈ w.divisors, ((d : ℝ) ^ b / K) * (2 * K / ((d : ℝ) * (A - 1))) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
      exact mul_le_mul_of_nonneg_left (sum_frequencyDivisorDecay_le F d hdpos hK hA)
        (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) b) hK.le)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
      rw [Real.rpow_sub hdpos, Real.rpow_one]
      field_simp

/-- Actual summability and the all-width gcd bound over every nonzero integer frequency. -/
theorem frequencyGCDWeight_tsum (w : ℕ) (hw : 0 < w)
    {K A : ℝ} (hK : 0 < K) (hA : 1 < A) (b : ℝ) :
    Summable (frequencyGCDWeight w K A b) ∧
      (∑' c : ℤ, frequencyGCDWeight w K A b c) ≤
        2 / (A - 1) * ∑ d ∈ w.divisors, (d : ℝ) ^ (b - 1) := by
  have hn : 0 ≤ frequencyGCDWeight w K A b := frequencyGCDWeight_nonneg w hK A b
  have hb := fun F => sum_frequencyGCDWeight_le F w hw hK hA b
  exact ⟨summable_of_sum_le hn hb, Real.tsum_le_of_sum_le hn hb⟩

/-- For the three residual exponents in the paper, every divisor contributes at most one. -/
theorem divisor_rpow_sum_le_card (w : ℕ) {b : ℝ} (hb : b ≤ 1) :
    (∑ d ∈ w.divisors, (d : ℝ) ^ (b - 1)) ≤ w.divisors.card := by
  calc
    _ ≤ ∑ _d ∈ w.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast Nat.pos_of_mem_divisors hd
      · linarith
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- A uniform subpower bound in the modulus, with no restriction on the positive width. -/
theorem exists_frequencyGCDWeight_subpower {A b ε : ℝ}
    (hA : 1 < A) (hb : b ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : ℕ), 0 < w → ∀ K : ℝ, 0 < K →
      (∑' c : ℤ, frequencyGCDWeight w K A b c) ≤ C * (w : ℝ) ^ ε := by
  obtain ⟨D, hD, hbound⟩ := PrimeGap186.exists_card_divisors_bound hε
  refine ⟨2 / (A - 1) * D, by positivity, ?_⟩
  intro w hw K hK
  calc
    _ ≤ 2 / (A - 1) * ∑ d ∈ w.divisors, (d : ℝ) ^ (b - 1) :=
      (frequencyGCDWeight_tsum w hw hK hA b).2
    _ ≤ 2 / (A - 1) * w.divisors.card :=
      mul_le_mul_of_nonneg_left (divisor_rpow_sum_le_card w hb) (by positivity)
    _ ≤ 2 / (A - 1) * (D * (w : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (hbound w hw.ne') (by positivity)
    _ = _ := by ring

#print axioms sum_frequencyDivisorDecay_le
#print axioms gcd_rpow_le_divisor_majorant
#print axioms sum_frequencyGCDWeight_le
#print axioms frequencyGCDWeight_tsum
#print axioms exists_frequencyGCDWeight_subpower

end

end PrimeGap182.TypeIII
