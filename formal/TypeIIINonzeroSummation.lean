import TypeIIIDyadicBlock
import TypeIIICubicFibers

/-!
# Summing the three nonzero-frequency scales

The gcd exponents are derived from the actual dyadic scale, then their convergent
series are used uniformly. This is the scalar summation step; the signed G₂ support
reindexing is a separate finite-sum obligation.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem shared_scale_monomial {R s g : ℝ} (hR : 0 < R) (hs : 0 < s) (hg : 0 < g)
    (b d : ℝ) :
    s * (R / g) ^ b * (s * g) ^ d = R ^ b * s ^ (1 + d) * g ^ (d - b) := by
  rw [Real.div_rpow hR.le hg.le, Real.mul_rpow hs.le hg.le,
    Real.rpow_add hs, Real.rpow_one, Real.rpow_sub hg]
  ring

/-- The three summable gcd exponents are exactly −5/2, −7/4, and −21/8. -/
theorem nonzero_sg_expansion {M R s g : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hs : 0 < s) (hg : 0 < g) :
    s * dyadicNonzeroScale M (R / g) (s * g) =
      (M ^ (7 / 4 : ℝ) * R ^ 3 * s ^ (3 / 2 : ℝ)) * g ^ (-(5 / 2 : ℝ)) +
      (M ^ 2 * R ^ (5 / 2 : ℝ) * s ^ (7 / 4 : ℝ)) * g ^ (-(7 / 4 : ℝ)) +
      (M ^ 2 * R ^ 3 * s ^ (11 / 8 : ℝ)) * g ^ (-(21 / 8 : ℝ)) := by
  have hMpow : M * M ^ (3 / 4 : ℝ) = M ^ (7 / 4 : ℝ) := by
    rw [show (7 / 4 : ℝ) = 1 + 3 / 4 by norm_num, Real.rpow_add hM, Real.rpow_one]
  have hrpow : (R / g) ^ 3 / (R / g) ^ (1 / 2 : ℝ) = (R / g) ^ (5 / 2 : ℝ) := by
    rw [show (5 / 2 : ℝ) = 3 - 1 / 2 by norm_num, Real.rpow_sub (div_pos hR hg)]
    norm_num
  have h₁ := shared_scale_monomial hR hs hg 3 (1 / 2)
  have h₂ := shared_scale_monomial hR hs hg (5 / 2) (3 / 4)
  have h₃ := shared_scale_monomial hR hs hg 3 (3 / 8)
  norm_num at h₁ h₂ h₃
  calc
    _ = M ^ (7 / 4 : ℝ) * (s * (R / g) ^ 3 * (s * g) ^ (1 / 2 : ℝ)) +
        M ^ 2 * (s * (R / g) ^ (5 / 2 : ℝ) * (s * g) ^ (3 / 4 : ℝ)) +
        M ^ 2 * (s * (R / g) ^ 3 * (s * g) ^ (3 / 8 : ℝ)) := by
      rw [← hMpow, ← hrpow]
      unfold dyadicNonzeroScale matrixThreeScale
      ring
    _ = _ := by rw [h₁, h₂, h₃]; ring

theorem sum_Icc_nonneg_rpow_le (S : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    (∑ s ∈ Finset.Icc 1 S, (s : ℝ) ^ b) ≤ (S : ℝ) ^ (b + 1) := by
  by_cases hS : S = 0
  · subst S
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), Finset.sum_empty,
      Nat.cast_zero]
    positivity
  · have hS' : (0 : ℝ) < S := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hS)
    calc
      _ ≤ ∑ _s ∈ Finset.Icc 1 S, (S : ℝ) ^ b := by
        apply Finset.sum_le_sum
        intro s hs
        exact Real.rpow_le_rpow (Nat.cast_nonneg s) (Nat.cast_le.mpr (Finset.mem_Icc.mp hs).2) hb
      _ = (S : ℝ) * (S : ℝ) ^ b := by simp
      _ = _ := by rw [Real.rpow_add hS', Real.rpow_one]; ring

def nonzeroSGScale (M R S : ℝ) : ℝ :=
  M ^ (7 / 4 : ℝ) * R ^ 3 * S ^ (5 / 2 : ℝ) +
  M ^ 2 * R ^ (5 / 2 : ℝ) * S ^ (11 / 4 : ℝ) +
  M ^ 2 * R ^ 3 * S ^ (19 / 8 : ℝ)

/-- The gcd sum has an absolute constant; the positive shared-factor sum gives precisely
the three nonzero scales before setting R=Q/S. -/
theorem exists_nonzero_sg_sum_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (M R : ℝ), 0 < M → 0 < R → ∀ (S G : ℕ),
      (∑ s ∈ Finset.Icc 1 S, ∑ g ∈ Finset.Icc 1 G,
        (s : ℝ) * dyadicNonzeroScale M (R / (g : ℝ)) ((s : ℝ) * (g : ℝ))) ≤
          K * nonzeroSGScale M R S := by
  let A : ℝ := ∑' g : ℕ, (g : ℝ) ^ (-(5 / 2 : ℝ))
  let B : ℝ := ∑' g : ℕ, (g : ℝ) ^ (-(7 / 4 : ℝ))
  let C : ℝ := ∑' g : ℕ, (g : ℝ) ^ (-(21 / 8 : ℝ))
  have hA : 0 ≤ A := tsum_nonneg (fun g => Real.rpow_nonneg (Nat.cast_nonneg g) _)
  have hB : 0 ≤ B := tsum_nonneg (fun g => Real.rpow_nonneg (Nat.cast_nonneg g) _)
  have hC : 0 ≤ C := tsum_nonneg (fun g => Real.rpow_nonneg (Nat.cast_nonneg g) _)
  let K := 1 + A + B + C
  have hK : 0 < K := by dsimp only [K]; linarith
  have hKA : A ≤ K := by dsimp only [K]; linarith
  have hKB : B ≤ K := by dsimp only [K]; linarith
  have hKC : C ≤ K := by dsimp only [K]; linarith
  have hsA : Summable (fun g : ℕ => (g : ℝ) ^ (-(5 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hsB : Summable (fun g : ℕ => (g : ℝ) ^ (-(7 / 4 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hsC : Summable (fun g : ℕ => (g : ℝ) ^ (-(21 / 8 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro M R hM hR S G
  have hgA : (∑ g ∈ Finset.Icc 1 G, (g : ℝ) ^ (-(5 / 2 : ℝ))) ≤ K :=
    (hsA.sum_le_tsum _ (fun g _ => Real.rpow_nonneg (Nat.cast_nonneg g) _)).trans hKA
  have hgB : (∑ g ∈ Finset.Icc 1 G, (g : ℝ) ^ (-(7 / 4 : ℝ))) ≤ K :=
    (hsB.sum_le_tsum _ (fun g _ => Real.rpow_nonneg (Nat.cast_nonneg g) _)).trans hKB
  have hgC : (∑ g ∈ Finset.Icc 1 G, (g : ℝ) ^ (-(21 / 8 : ℝ))) ≤ K :=
    (hsC.sum_le_tsum _ (fun g _ => Real.rpow_nonneg (Nat.cast_nonneg g) _)).trans hKC
  have hpoint (s : ℕ) (hs : s ∈ Finset.Icc 1 S) :
      (∑ g ∈ Finset.Icc 1 G,
        (s : ℝ) * dyadicNonzeroScale M (R / (g : ℝ)) ((s : ℝ) * (g : ℝ))) ≤
        K * ((M ^ (7 / 4 : ℝ) * R ^ 3) * (s : ℝ) ^ (3 / 2 : ℝ) +
          (M ^ 2 * R ^ (5 / 2 : ℝ)) * (s : ℝ) ^ (7 / 4 : ℝ) +
          (M ^ 2 * R ^ 3) * (s : ℝ) ^ (11 / 8 : ℝ)) := by
    have heq := Finset.sum_congr rfl (fun g (hg : g ∈ Finset.Icc 1 G) =>
      nonzero_sg_expansion hM hR (Nat.cast_pos.mpr (Finset.mem_Icc.mp hs).1)
        (Nat.cast_pos.mpr (Finset.mem_Icc.mp hg).1))
    rw [heq]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    calc
      _ ≤ ((M ^ (7 / 4 : ℝ) * R ^ 3) * (s : ℝ) ^ (3 / 2 : ℝ)) * K +
          ((M ^ 2 * R ^ (5 / 2 : ℝ)) * (s : ℝ) ^ (7 / 4 : ℝ)) * K +
          ((M ^ 2 * R ^ 3) * (s : ℝ) ^ (11 / 8 : ℝ)) * K := by
        exact add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hgA (by positivity))
          (mul_le_mul_of_nonneg_left hgB (by positivity)))
          (mul_le_mul_of_nonneg_left hgC (by positivity))
      _ = _ := by ring
  calc
    _ ≤ ∑ s ∈ Finset.Icc 1 S,
        K * ((M ^ (7 / 4 : ℝ) * R ^ 3) * (s : ℝ) ^ (3 / 2 : ℝ) +
          (M ^ 2 * R ^ (5 / 2 : ℝ)) * (s : ℝ) ^ (7 / 4 : ℝ) +
          (M ^ 2 * R ^ 3) * (s : ℝ) ^ (11 / 8 : ℝ)) := Finset.sum_le_sum hpoint
    _ = K * ((M ^ (7 / 4 : ℝ) * R ^ 3) * (∑ s ∈ Finset.Icc 1 S, (s : ℝ) ^ (3 / 2 : ℝ)) +
        (M ^ 2 * R ^ (5 / 2 : ℝ)) * (∑ s ∈ Finset.Icc 1 S, (s : ℝ) ^ (7 / 4 : ℝ)) +
        (M ^ 2 * R ^ 3) * (∑ s ∈ Finset.Icc 1 S, (s : ℝ) ^ (11 / 8 : ℝ))) := by
      simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    _ ≤ K * nonzeroSGScale M R S := by
      apply mul_le_mul_of_nonneg_left _ hK.le
      unfold nonzeroSGScale
      apply add_le_add
      · apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa only [show (3 / 2 : ℝ) + 1 = 5 / 2 by norm_num] using
            sum_Icc_nonneg_rpow_le S (show (0 : ℝ) ≤ 3 / 2 by norm_num)
        · apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa only [show (7 / 4 : ℝ) + 1 = 11 / 4 by norm_num] using
            sum_Icc_nonneg_rpow_le S (show (0 : ℝ) ≤ 7 / 4 by norm_num)
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [show (11 / 8 : ℝ) + 1 = 19 / 8 by norm_num] using
          sum_Icc_nonneg_rpow_le S (show (0 : ℝ) ≤ 11 / 8 by norm_num)

def paperNonzeroScale (M Q S : ℝ) : ℝ :=
  M ^ (7 / 4 : ℝ) * Q ^ 3 * S ^ (-(1 / 2 : ℝ)) +
  M ^ 2 * Q ^ (5 / 2 : ℝ) * S ^ (1 / 4 : ℝ) +
  M ^ 2 * Q ^ 3 * S ^ (-(5 / 8 : ℝ))

theorem quotient_rpow_mul_rpow {Q S : ℝ} (hQ : 0 < Q) (hS : 0 < S) (b c : ℝ) :
    (Q / S) ^ b * S ^ c = Q ^ b * S ^ (c - b) := by
  rw [Real.div_rpow hQ.le hS.le, Real.rpow_sub hS]
  ring

/-- The final three powers in equation (T₂,nonzero) follow by the actual R=Q/S substitution. -/
theorem nonzeroSGScale_at_ratio (M : ℝ) {Q S : ℝ} (hQ : 0 < Q) (hS : 0 < S) :
    nonzeroSGScale M (Q / S) S = paperNonzeroScale M Q S := by
  have h₁ := quotient_rpow_mul_rpow hQ hS 3 (5 / 2)
  have h₂ := quotient_rpow_mul_rpow hQ hS (5 / 2) (11 / 4)
  have h₃ := quotient_rpow_mul_rpow hQ hS 3 (19 / 8)
  norm_num at h₁ h₂ h₃
  calc
    _ = M ^ (7 / 4 : ℝ) * ((Q / S) ^ 3 * S ^ (5 / 2 : ℝ)) +
        M ^ 2 * ((Q / S) ^ (5 / 2 : ℝ) * S ^ (11 / 4 : ℝ)) +
        M ^ 2 * ((Q / S) ^ 3 * S ^ (19 / 8 : ℝ)) := by unfold nonzeroSGScale; ring
    _ = _ := by rw [h₁, h₂, h₃]; unfold paperNonzeroScale; ring

#print axioms nonzero_sg_expansion
#print axioms exists_nonzero_sg_sum_bound
#print axioms nonzeroSGScale_at_ratio

end

end PrimeGap182.TypeIII
