import TypeIIIIntegerKernel

/-! Subpower absorption for the explicit local-mask, divisor, and logarithmic constants. -/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

/-- Distinct prime factors in an actual CRT family inject into the prime factors of its product. -/
theorem card_prime_family_le_primeFactors
    {ι : Type*} [Fintype ι] (q : ι → ℕ) [∀ i, Fact (q i).Prime]
    [NeZero (∏ i, q i)] (hcp : Pairwise (fun i j => (q i).Coprime (q j))) :
    Fintype.card ι ≤ (∏ i, q i).primeFactors.card := by
  have hmem (i : ι) : q i ∈ (∏ j, q j).primeFactors := by
    exact Nat.mem_primeFactors.mpr ⟨Fact.out, Finset.dvd_prod_of_mem q (Finset.mem_univ i), NeZero.ne _⟩
  let f (i : ι) : ↥(∏ j, q j).primeFactors := ⟨q i, hmem i⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have hq : q i = q j := congrArg Subtype.val hij
    by_contra hne
    have hc := hcp hne
    dsimp only at hc
    rw [hq, Nat.coprime_self] at hc
    exact (Fact.out : (q j).Prime).ne_one hc
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

/-- The local mask constants are bounded by a fixed base to the actual prime-factor count. -/
theorem family_maskConstant_le_primeFactor_power
    {ι : Type*} [Fintype ι] (q : ι → ℕ) [∀ i, Fact (q i).Prime]
    [NeZero (∏ i, q i)] (hcp : Pairwise (fun i j => (q i).Coprime (q j)))
    {C : ℝ} (hC : 0 ≤ C) (D : ℕ) :
    C ^ Fintype.card ι * maskComplexity D (Fintype.card ι) ≤
      (max 1 (C * (5 * ((max D 1 : ℕ) : ℝ) ^ 2))) ^ (∏ i, q i).primeFactors.card := by
  unfold maskComplexity
  rw [← mul_pow]
  apply (pow_le_pow_left₀ (by positivity) (le_max_right _ _) (Fintype.card ι)).trans
  exact pow_le_pow_right₀ (le_max_left _ _) (card_prime_family_le_primeFactors q hcp)

/-- The square of `1+log s` is uniformly bounded by every positive power of s. -/
theorem exists_logSquare_subpower {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℕ, s ≠ 0 →
      (1 + Real.log (s : ℝ)) ^ 2 ≤ K * (s : ℝ) ^ ε := by
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨(1 + 1 / δ) ^ 2, by positivity, ?_⟩
  intro s hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hs
  have hs0 : 0 ≤ (s : ℝ) := Nat.cast_nonneg s
  have hsp : 1 ≤ (s : ℝ) ^ δ := Real.one_le_rpow hs1 hδ.le
  have hlog := Real.log_natCast_le_rpow_div s hδ
  have hadd : 1 + Real.log (s : ℝ) ≤ (1 + 1 / δ) * (s : ℝ) ^ δ := by
    calc
      _ ≤ (s : ℝ) ^ δ + (s : ℝ) ^ δ / δ := add_le_add hsp hlog
      _ = _ := by ring
  calc
    _ ≤ ((1 + 1 / δ) * (s : ℝ) ^ δ) ^ 2 :=
      pow_le_pow_left₀ (by linarith [Real.log_nonneg hs1]) hadd 2
    _ = (1 + 1 / δ) ^ 2 * (s : ℝ) ^ (δ * 2) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hs0]
      norm_num
    _ = _ := by congr 2; dsimp [δ]; ring

/-- All explicit non-polynomial factors in the matrix fourth moment are subpower. -/
theorem exists_primeFactor_divisor_log_subpower
    {a ε : ℝ} (ha : 1 ≤ a) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℕ, s ≠ 0 →
      a ^ s.primeFactors.card * 64 * (s.divisors.card : ℝ) ^ 2 *
        (1 + Real.log (s : ℝ)) ^ 2 ≤ K * (s : ℝ) ^ ε := by
  have he : 0 < ε / 3 := by positivity
  obtain ⟨K₁, hK₁, h₁⟩ := PrimeGap186.exists_primeFactors_power_bound ha he
  obtain ⟨K₂, hK₂, h₂⟩ := PrimeGap186.exists_divisorPower_bound 2 he
  obtain ⟨K₃, hK₃, h₃⟩ := exists_logSquare_subpower he
  refine ⟨64 * K₁ * K₂ * K₃, by positivity, ?_⟩
  intro s hs
  calc
    _ = 64 * (a ^ s.primeFactors.card * (s.divisors.card : ℝ) ^ 2 *
        (1 + Real.log (s : ℝ)) ^ 2) := by ring
    _ ≤ 64 * ((K₁ * (s : ℝ) ^ (ε / 3)) * (K₂ * (s : ℝ) ^ (ε / 3)) *
        (K₃ * (s : ℝ) ^ (ε / 3))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul
      · exact mul_le_mul (h₁ s hs) (h₂ s hs) (by positivity) (by positivity)
      · exact h₃ s hs
      · positivity
      · positivity
    _ = (64 * K₁ * K₂ * K₃) * (s : ℝ) ^ ε := by
      have hsp : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs
      calc
        _ = (64 * K₁ * K₂ * K₃) *
            (((s : ℝ) ^ (ε / 3) * (s : ℝ) ^ (ε / 3)) * (s : ℝ) ^ (ε / 3)) := by ring
        _ = _ := by rw [← Real.rpow_add hsp, ← Real.rpow_add hsp]; congr 2; ring

#print axioms card_prime_family_le_primeFactors
#print axioms family_maskConstant_le_primeFactor_power
#print axioms exists_logSquare_subpower
#print axioms exists_primeFactor_divisor_log_subpower

end

end PrimeGap182.TypeIII
