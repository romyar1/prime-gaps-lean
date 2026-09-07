import TypeIIIZeroOffDiagonal
import TypeIIISubpower

/-! Subpower bounds for the actual finite losses in the zero-frequency branch. -/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem natCast_finset_sup_le {ι : Type*} (S : Finset ι) (f : ι → ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hf : ∀ i ∈ S, (f i : ℝ) ≤ B) : ((S.sup f : ℕ) : ℝ) ≤ B := by
  induction S using Finset.induction_on with
  | empty => simpa using hB
  | @insert i S hi ih =>
    rw [Finset.sup_insert, Nat.cast_max]
    exact max_le (hf i (Finset.mem_insert_self i S))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem cubicDifference_abs_le {M R u v m n : ℕ}
    (hu : u ≤ 2 * R) (hv : v ≤ 2 * R) (hm : m ≤ M) (hn : n ≤ M) :
    ((cubicDifference u v m n).natAbs : ℝ) ≤ (M : ℝ) * (2 * (R : ℝ)) ^ 3 := by
  have hleft : (m : ℝ) * (u : ℝ) ^ 3 ≤ (M : ℝ) * (2 * (R : ℝ)) ^ 3 := by
    exact mul_le_mul (Nat.cast_le.mpr hm)
      (pow_le_pow_left₀ (Nat.cast_nonneg u) (by exact_mod_cast hu) 3)
      (pow_nonneg (Nat.cast_nonneg u) 3) (Nat.cast_nonneg M)
  have hright : (n : ℝ) * (v : ℝ) ^ 3 ≤ (M : ℝ) * (2 * (R : ℝ)) ^ 3 := by
    exact mul_le_mul (Nat.cast_le.mpr hn)
      (pow_le_pow_left₀ (Nat.cast_nonneg v) (by exact_mod_cast hv) 3)
      (pow_nonneg (Nat.cast_nonneg v) 3) (Nat.cast_nonneg M)
  rw [Nat.cast_natAbs, Int.cast_abs]
  simp only [cubicDifference, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  apply abs_le.mpr
  constructor
  · nlinarith [show (0 : ℝ) ≤ (m : ℝ) * (u : ℝ) ^ 3 by positivity]
  · nlinarith [show (0 : ℝ) ≤ (n : ℝ) * (v : ℝ) ^ 3 by positivity]

/-- The maximum divisor count is taken over actual polynomially bounded integers. -/
theorem exists_cubicDivisorBound_subpower {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ M R : ℕ,
      (cubicDivisorBound M R : ℝ) ≤ K * (1 + (M : ℝ) * (2 * (R : ℝ)) ^ 3) ^ ε := by
  obtain ⟨K, hK, hb⟩ := PrimeGap186.exists_divisorPower_bound 1 hε
  refine ⟨K, hK, ?_⟩
  intro M R
  unfold cubicDivisorBound
  apply natCast_finset_sup_le _ _ _ (by positivity)
  intro uv_mn huv_mn
  obtain ⟨huv, hmn⟩ := Finset.mem_product.mp huv_mn
  obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
  obtain ⟨hm, hn⟩ := Finset.mem_product.mp hmn
  let z := cubicDifference uv_mn.1.1 uv_mn.1.2 uv_mn.2.1 uv_mn.2.2
  by_cases hz : z = 0
  · simp only [show cubicDifference uv_mn.1.1 uv_mn.1.2 uv_mn.2.1 uv_mn.2.2 = 0 from hz,
      Int.natAbs_zero, Nat.divisors_zero, Finset.card_empty, Nat.cast_zero]
    positivity
  · have hz' : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
    have hdiv := hb z.natAbs hz'
    rw [pow_one] at hdiv
    apply hdiv.trans
    apply mul_le_mul_of_nonneg_left _ hK.le
    apply Real.rpow_le_rpow (Nat.cast_nonneg z.natAbs) _ hε.le
    have hh := cubicDifference_abs_le (Finset.mem_Icc.mp hu).2 (Finset.mem_Icc.mp hv).2
      (Finset.mem_Icc.mp hm).2 (Finset.mem_Icc.mp hn).2
    exact hh.trans (by linarith)

/-- A common prime-count loss is proved uniformly over every relevant positive s,g. -/
theorem exists_zeroFrequency_prime_loss {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ S R : ℕ, ∀ s ∈ Finset.Icc 1 S, ∀ g ∈ Finset.Icc 1 (2 * R),
      (2 : ℝ) ^ (s * g).primeFactors.card ≤ K * (1 + 2 * (S : ℝ) * (R : ℝ)) ^ ε := by
  obtain ⟨K, hK, hb⟩ := PrimeGap186.exists_primeFactors_power_bound (show (1 : ℝ) ≤ 2 by norm_num) hε
  refine ⟨K, hK, ?_⟩
  intro S R s hs g hg
  have hsg : s * g ≠ 0 := (mul_pos (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hg).1).ne'
  apply (hb (s * g) hsg).trans
  apply mul_le_mul_of_nonneg_left _ hK.le
  apply Real.rpow_le_rpow (Nat.cast_nonneg (s * g)) _ hε.le
  have hh : s * g ≤ S * (2 * R) := Nat.mul_le_mul (Finset.mem_Icc.mp hs).2 (Finset.mem_Icc.mp hg).2
  have hh' : ((s * g : ℕ) : ℝ) ≤ (S : ℝ) * (2 * (R : ℝ)) := by exact_mod_cast hh
  nlinarith

#print axioms exists_cubicDivisorBound_subpower
#print axioms exists_zeroFrequency_prime_loss

end

end PrimeGap182.TypeIII
