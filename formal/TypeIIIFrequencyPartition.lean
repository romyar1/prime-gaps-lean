import TypeIIISharedMatrix

/-! The actual prime partition is exactly the gcd of the integer frequency and modulus. -/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] familyProductNeZero

theorem gcd_finset_prod_of_pairwise {ι : Type*} [DecidableEq ι] (q : ι → ℕ)
    (hcp : Pairwise (fun i j => (q i).Coprime (q j))) (S : Finset ι) (k : ℕ) :
    Nat.gcd k (∏ i ∈ S, q i) = ∏ i ∈ S, Nat.gcd k (q i) := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Nat.gcd_one_right]
  | @insert i S hi ih =>
    have hcop : (q i).Coprime (∏ j ∈ S, q j) :=
      Nat.Coprime.prod_right (fun j hj => hcp (fun hij => hi (hij ▸ hj)))
    rw [Finset.prod_insert hi, Nat.Coprime.gcd_mul k hcop, ih, Finset.prod_insert hi]

theorem gcd_natAbs_prime_eq (p : ℕ) [Fact p.Prime] (c : ℤ) :
    Nat.gcd c.natAbs p = if (c : ZMod p) = 0 then p else 1 := by
  by_cases h : (c : ZMod p) = 0
  · rw [ite_eq_left h, Nat.gcd_comm]
    exact Nat.gcd_eq_left_iff_dvd.mpr
      (Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp h))
  · rw [ite_eq_right h]
    apply Nat.Coprime.gcd_eq_one
    apply Nat.Coprime.symm
    apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    intro hd
    exact h ((ZMod.intCast_zmod_eq_zero_iff_dvd c p).mpr (Int.natCast_dvd.mpr hd))

/-- The product of exactly those prime factors where the frequency vanishes is the gcd. -/
theorem zeroFrequency_product_eq_gcd {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, Fact (q i).Prime]
    (hcp : Pairwise (fun i j => (q i).Coprime (q j))) (c : ℤ) :
    (∏ i : ZeroFrequencyPrime q c, q i.1) = Int.gcd c ((∏ i, q i : ℕ) : ℤ) := by
  rw [Int.gcd_def, Int.natAbs_natCast, gcd_finset_prod_of_pairwise q hcp Finset.univ]
  simp only [gcd_natAbs_prime_eq]
  rw [← Finset.prod_filter]
  exact (Finset.prod_subtype (Finset.univ.filter (fun i => (c : ZMod (q i)) = 0))
    (fun i => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) q).symm

theorem frequency_partition_product {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, Fact (q i).Prime] (c : ℤ) :
    (∏ i : ZeroFrequencyPrime q c, q i.1) *
      (∏ i : NonzeroFrequencyPrime q c, q i.1) = ∏ i, q i :=
  Fintype.prod_subtype_mul_prod_subtype (fun i => (c : ZMod (q i)) = 0) q

theorem nonzeroFrequency_product_eq_div_gcd {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, Fact (q i).Prime]
    (hcp : Pairwise (fun i j => (q i).Coprime (q j))) (c : ℤ) :
    (∏ i : NonzeroFrequencyPrime q c, q i.1) =
      (∏ i, q i) / Int.gcd c ((∏ i, q i : ℕ) : ℤ) := by
  rw [← zeroFrequency_product_eq_gcd q hcp c]
  exact (Nat.div_eq_of_eq_mul_right
    (NeZero.pos (∏ i : ZeroFrequencyPrime q c, q i.1))
    (frequency_partition_product q c).symm).symm

/-- All matching costs beyond the explicit gcd are absorbed uniformly into a power of the
original modulus; the remaining kernel contributes the complementary modulus power. -/
theorem exists_frequency_partition_subpower {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ι : Type} [Fintype ι] (q : ι → ℕ) [∀ i, Fact (q i).Prime],
      Pairwise (fun i j => (q i).Coprime (q j)) → ∀ c : ℤ,
      (4 : ℝ) ^ Fintype.card (ZeroFrequencyPrime q c) *
        ((∏ i : ZeroFrequencyPrime q c, q i.1 : ℕ) : ℝ) *
        ((∏ i : NonzeroFrequencyPrime q c, q i.1 : ℕ) : ℝ) ^ ε ≤
      K * ((∏ i, q i : ℕ) : ℝ) ^ ε * (Int.gcd c ((∏ i, q i : ℕ) : ℤ) : ℝ) := by
  obtain ⟨K, hK, hbound⟩ :=
    PrimeGap186.exists_primeFactors_power_bound (show (1 : ℝ) ≤ 4 by norm_num) hε
  refine ⟨K, hK, ?_⟩
  intro ι _ q _ hcp c
  have hcp' : Pairwise (fun i j : ZeroFrequencyPrime q c => (q i.1).Coprime (q j.1)) :=
    fun _ _ hij => hcp (fun heq => hij (Subtype.ext heq))
  have hh : (4 : ℝ) ^ Fintype.card (ZeroFrequencyPrime q c) ≤
      K * ((∏ i : ZeroFrequencyPrime q c, q i.1 : ℕ) : ℝ) ^ ε :=
    (pow_le_pow_right₀ (by norm_num)
      (card_prime_family_le_primeFactors (fun i : ZeroFrequencyPrime q c => q i.1) hcp')).trans
      (hbound _ (NeZero.ne _))
  have hp := frequency_partition_product q c
  have hp' : ((∏ i : ZeroFrequencyPrime q c, q i.1 : ℕ) : ℝ) *
      ((∏ i : NonzeroFrequencyPrime q c, q i.1 : ℕ) : ℝ) = ((∏ i, q i : ℕ) : ℝ) := by
    exact_mod_cast hp
  calc
    _ ≤ (K * ((∏ i : ZeroFrequencyPrime q c, q i.1 : ℕ) : ℝ) ^ ε) *
        ((∏ i : ZeroFrequencyPrime q c, q i.1 : ℕ) : ℝ) *
        ((∏ i : NonzeroFrequencyPrime q c, q i.1 : ℕ) : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (by positivity)) (by positivity)
    _ = _ := by
      rw [← zeroFrequency_product_eq_gcd q hcp c, ← hp',
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      ring

#print axioms zeroFrequency_product_eq_gcd
#print axioms frequency_partition_product
#print axioms nonzeroFrequency_product_eq_div_gcd
#print axioms exists_frequency_partition_subpower

end

end PrimeGap182.TypeIII
