import TypeIIIResidualRanges

/-!
# Exact positive cubic fibers in the zero-frequency branch

Coprimality forces the concrete parametrization m=v³k and n=u³k. The finite count and
weighted residual-range bounds are proved for the actual solution set.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem coprime_cubic_solution (u v m n : ℕ) (hv : 0 < v) (huv : u.Coprime v)
    (he : m * u ^ 3 = n * v ^ 3) :
    ∃ k : ℕ, m = v ^ 3 * k ∧ n = u ^ 3 * k := by
  have hd : v ^ 3 ∣ m := (huv.symm.pow 3 3).dvd_of_dvd_mul_right
    (show v ^ 3 ∣ m * u ^ 3 by rw [he]; exact dvd_mul_left _ _)
  obtain ⟨k, hk⟩ := hd
  refine ⟨k, hk, ?_⟩
  apply mul_right_cancel₀ (pow_ne_zero 3 hv.ne')
  calc
    n * v ^ 3 = m * u ^ 3 := he.symm
    _ = (u ^ 3 * k) * v ^ 3 := by rw [hk]; ring

def cubicDiagonalPairs (M u v : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter (fun mn => mn.1 * u ^ 3 = mn.2 * v ^ 3)

theorem cubicDiagonalPairs_card_le_div (M u v : ℕ) (hv : 0 < v) (huv : u.Coprime v) :
    (cubicDiagonalPairs M u v).card ≤ M / v ^ 3 := by
  let S := (Finset.Icc 1 M).filter (fun m => v ^ 3 ∣ m)
  have hmap : (cubicDiagonalPairs M u v).card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (fun mn : ℕ × ℕ => mn.1)
    · intro mn hmn
      obtain ⟨hmem, he⟩ := Finset.mem_filter.mp hmn
      obtain ⟨k, hk, _⟩ := coprime_cubic_solution u v mn.1 mn.2 hv huv he
      exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hmem).1, ⟨k, hk⟩⟩
    · intro mn hmn ij hij hsame
      change mn.1 = ij.1 at hsame
      apply Prod.ext hsame
      apply mul_right_cancel₀ (pow_ne_zero 3 hv.ne')
      have hm := (Finset.mem_filter.mp hmn).2
      have hi := (Finset.mem_filter.mp hij).2
      rw [← hm, ← hi, hsame]
  have hc : S.card = M / v ^ 3 := by
    have hh := PrimeGap186.sum_pos_multiples M (v ^ 3) (pow_pos hv 3) (fun _ : ℕ => (1 : ℕ))
    simpa only [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc,
      Nat.add_sub_cancel] using hh
  exact hmap.trans_eq hc

theorem cubicDiagonalPairs_card_le_real (M u v : ℕ) (hv : 0 < v) (huv : u.Coprime v) :
    ((cubicDiagonalPairs M u v).card : ℝ) ≤ (M : ℝ) / (v : ℝ) ^ 3 := by
  apply (le_div_iff₀ (pow_pos (Nat.cast_pos.mpr hv) 3)).2
  have hh := (Nat.mul_le_mul_right (v ^ 3) (cubicDiagonalPairs_card_le_div M u v hv huv)).trans
    (Nat.div_mul_le_self M (v ^ 3))
  exact_mod_cast hh

theorem cubicDiagonalPairs_residual_card_le {M R g u v : ℕ}
    (hR : 0 < R) (hv : v ∈ residualRange R g) (huv : u.Coprime v) :
    ((cubicDiagonalPairs M u v).card : ℝ) ≤ (M : ℝ) * ((g : ℝ) / (R : ℝ)) ^ 3 := by
  calc
    _ ≤ (M : ℝ) / (v : ℝ) ^ 3 :=
      cubicDiagonalPairs_card_le_real M u v (residualRange_spec hv).1 huv
    _ = (M : ℝ) * ((v : ℝ)⁻¹) ^ 3 := by rw [div_eq_mul_inv, inv_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (residualRange_inv_le hR hv) 3) (Nat.cast_nonneg M)

def cubicDiagonalMass (M R g : ℕ) : ℝ :=
  ∑ u ∈ residualRange R g, ∑ v ∈ residualRange R g,
    if u.Coprime v then ((cubicDiagonalPairs M u v).card : ℝ) *
      ((u : ℝ)⁻¹ ^ 2) * ((v : ℝ)⁻¹ ^ 2) else 0

theorem cubicDiagonalMass_nonneg (M R g : ℕ) : 0 ≤ cubicDiagonalMass M R g := by
  unfold cubicDiagonalMass
  positivity

theorem cubicDiagonalMass_le (M R g : ℕ) (hR : 0 < R) (hg : 0 < g) :
    cubicDiagonalMass M R g ≤ 4 * (M : ℝ) * (g : ℝ) ^ 5 / (R : ℝ) ^ 5 := by
  have hR' : (0 : ℝ) < R := Nat.cast_pos.mpr hR
  calc
    _ ≤ ∑ u ∈ residualRange R g, ∑ v ∈ residualRange R g,
        ((M : ℝ) * ((g : ℝ) / (R : ℝ)) ^ 3) *
          (((u : ℝ)⁻¹ ^ 2) * ((v : ℝ)⁻¹ ^ 2)) := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro v hv
      by_cases hc : u.Coprime v
      · rw [ite_eq_left hc]
        have hh := mul_le_mul_of_nonneg_right (cubicDiagonalPairs_residual_card_le (M := M) hR hv hc)
          (mul_nonneg (sq_nonneg ((u : ℝ)⁻¹)) (sq_nonneg ((v : ℝ)⁻¹)))
        simpa only [mul_assoc] using hh
      · rw [ite_eq_right hc]
        positivity
    _ = ((M : ℝ) * ((g : ℝ) / (R : ℝ)) ^ 3) *
        (∑ u ∈ residualRange R g, ∑ v ∈ residualRange R g,
          (((u : ℝ)⁻¹ ^ 2) * ((v : ℝ)⁻¹ ^ 2))) := by simp only [Finset.mul_sum]
    _ ≤ ((M : ℝ) * ((g : ℝ) / (R : ℝ)) ^ 3) *
        (4 * (g : ℝ) ^ 2 / (R : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (residualRange_pair_inv_sq_sum_le hR hg) (by positivity)
    _ = _ := by ring

theorem sum_Icc_nat_pow_le (G k : ℕ) :
    (∑ g ∈ Finset.Icc 1 G, (g : ℝ) ^ k) ≤ (G : ℝ) ^ (k + 1) := by
  calc
    _ ≤ ∑ _g ∈ Finset.Icc 1 G, (G : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro g hg
      exact pow_le_pow_left₀ (Nat.cast_nonneg g) (Nat.cast_le.mpr (Finset.mem_Icc.mp hg).2) k
    _ = _ := by simp [Nat.card_Icc, pow_succ, mul_comm]

/-- Summing all gcd values gives the required linear dependence on the residual scale. -/
theorem cubicDiagonalMass_g_sum_le (M R : ℕ) (hR : 0 < R) :
    (∑ g ∈ Finset.Icc 1 (2 * R), cubicDiagonalMass M R g) ≤ 256 * (M : ℝ) * (R : ℝ) := by
  have hR' : (0 : ℝ) < R := Nat.cast_pos.mpr hR
  calc
    _ ≤ ∑ g ∈ Finset.Icc 1 (2 * R), 4 * (M : ℝ) * (g : ℝ) ^ 5 / (R : ℝ) ^ 5 :=
      Finset.sum_le_sum (fun g hg => cubicDiagonalMass_le M R g hR (Finset.mem_Icc.mp hg).1)
    _ = (4 * (M : ℝ) / (R : ℝ) ^ 5) * ∑ g ∈ Finset.Icc 1 (2 * R), (g : ℝ) ^ 5 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ ≤ (4 * (M : ℝ) / (R : ℝ) ^ 5) * (((2 * R : ℕ) : ℝ) ^ 6) :=
      mul_le_mul_of_nonneg_left (sum_Icc_nat_pow_le (2 * R) 5) (by positivity)
    _ = _ := by
      push_cast
      field_simp
      ring

/-- The complete positive central diagonal weight has the paper's M S² R scale. -/
theorem zeroFrequency_diagonal_weight_sum_le (M R S : ℕ) (hR : 0 < R) :
    (∑ g ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 S,
      (s : ℝ) * cubicDiagonalMass M R g) ≤ 256 * (M : ℝ) * (S : ℝ) ^ 2 * (R : ℝ) := by
  have hs : (∑ s ∈ Finset.Icc 1 S, (s : ℝ)) ≤ (S : ℝ) ^ 2 := by
    simpa only [pow_one] using sum_Icc_nat_pow_le S 1
  calc
    _ = (∑ s ∈ Finset.Icc 1 S, (s : ℝ)) *
        (∑ g ∈ Finset.Icc 1 (2 * R), cubicDiagonalMass M R g) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ ≤ (S : ℝ) ^ 2 * (256 * (M : ℝ) * (R : ℝ)) :=
      mul_le_mul hs (cubicDiagonalMass_g_sum_le M R hR)
        (Finset.sum_nonneg (fun g _ => cubicDiagonalMass_nonneg M R g)) (sq_nonneg _)
    _ = _ := by ring

#print axioms coprime_cubic_solution
#print axioms cubicDiagonalPairs_card_le_div
#print axioms zeroFrequency_diagonal_weight_sum_le

end

end PrimeGap182.TypeIII
