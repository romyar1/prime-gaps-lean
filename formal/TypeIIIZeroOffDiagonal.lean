import TypeIIICubicFibers

/-!
# The positive off-diagonal zero-frequency sum

The divisor count is the maximum over the actual finite cubic differences. The s-sum
is performed only after u,v,m,n have been fixed, as required by the signed completion
argument. No large-divisor remainder is introduced.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

def cubicDifference (u v m n : ℕ) : ℤ := (m : ℤ) * (u : ℤ) ^ 3 - (n : ℤ) * (v : ℤ) ^ 3

def cubicDivisorBound (M R : ℕ) : ℕ :=
  ((Finset.Icc 1 (2 * R) ×ˢ Finset.Icc 1 (2 * R)) ×ˢ
    (Finset.Icc 1 M ×ˢ Finset.Icc 1 M)).sup
      (fun uv_mn => (cubicDifference uv_mn.1.1 uv_mn.1.2 uv_mn.2.1 uv_mn.2.2).natAbs.divisors.card)

theorem cubicDifference_divisors_le {M R g u v m n : ℕ}
    (hu : u ∈ residualRange R g) (hv : v ∈ residualRange R g)
    (hm : m ∈ Finset.Icc 1 M) (hn : n ∈ Finset.Icc 1 M) :
    (cubicDifference u v m n).natAbs.divisors.card ≤ cubicDivisorBound M R := by
  unfold cubicDivisorBound
  apply Finset.le_sup (b := ((u, v), (m, n)))
    (f := fun uv_mn : (ℕ × ℕ) × (ℕ × ℕ) =>
      (cubicDifference uv_mn.1.1 uv_mn.1.2 uv_mn.2.1 uv_mn.2.2).natAbs.divisors.card)
  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨(residualRange_spec hu).1, residualRange_upper hu⟩,
      Finset.mem_Icc.mpr ⟨(residualRange_spec hv).1, residualRange_upper hv⟩⟩,
    Finset.mem_product.mpr ⟨hm, hn⟩⟩

def zeroOffDiagonalMass (M R S g : ℕ) : ℝ :=
  ∑ u ∈ residualRange R g, ∑ v ∈ residualRange R g,
    ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
      if cubicDifference u v m n ≠ 0 then
        ((g : ℝ)⁻¹ * ((u : ℝ)⁻¹ ^ 2) * ((v : ℝ)⁻¹ ^ 2)) *
          ∑ s ∈ Finset.Icc 1 S,
            (Int.gcd (cubicDifference u v m n) ((s * g : ℕ) : ℤ) : ℝ)
      else 0

theorem zeroOffDiagonalMass_nonneg (M R S g : ℕ) : 0 ≤ zeroOffDiagonalMass M R S g := by
  unfold zeroOffDiagonalMass
  positivity

theorem zeroOffDiagonalMass_le (M R S g : ℕ) (hR : 0 < R) (hg : 0 < g) :
    zeroOffDiagonalMass M R S g ≤
      4 * (S : ℝ) * (cubicDivisorBound M R : ℝ) * (M : ℝ) ^ 2 *
        (g : ℝ) ^ 2 / (R : ℝ) ^ 2 := by
  have hg' : (0 : ℝ) < g := Nat.cast_pos.mpr hg
  let B : ℝ := (S : ℝ) * (cubicDivisorBound M R : ℝ)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hpoint (u : ℕ) (hu : u ∈ residualRange R g) (v : ℕ) (hv : v ∈ residualRange R g)
      (m : ℕ) (hm : m ∈ Finset.Icc 1 M) (n : ℕ) (hn : n ∈ Finset.Icc 1 M) :
      (if cubicDifference u v m n ≠ 0 then
        ((g : ℝ)⁻¹ * ((u : ℝ)⁻¹ ^ 2) * ((v : ℝ)⁻¹ ^ 2)) *
          ∑ s ∈ Finset.Icc 1 S,
            (Int.gcd (cubicDifference u v m n) ((s * g : ℕ) : ℤ) : ℝ)
        else 0) ≤ B * (((u : ℝ)⁻¹ ^ 2) * ((v : ℝ)⁻¹ ^ 2)) := by
    by_cases hD : cubicDifference u v m n ≠ 0
    · rw [ite_eq_left hD]
      have hb := zeroFrequency_offDiagonal_s_sum S g hg (cubicDifference u v m n) hD
      have hτ : ((cubicDifference u v m n).natAbs.divisors.card : ℝ) ≤ cubicDivisorBound M R :=
        Nat.cast_le.mpr (cubicDifference_divisors_le hu hv hm hn)
      have hs : (∑ s ∈ Finset.Icc 1 S,
          (Int.gcd (cubicDifference u v m n) ((s * g : ℕ) : ℤ) : ℝ)) ≤ (g : ℝ) * B := by
        apply hb.trans
        dsimp only [B]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hτ
          (mul_nonneg (Nat.cast_nonneg g) (Nat.cast_nonneg S))
      calc
        _ ≤ ((g : ℝ)⁻¹ * ((u : ℝ)⁻¹ ^ 2) * ((v : ℝ)⁻¹ ^ 2)) * ((g : ℝ) * B) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
        _ = _ := by field_simp
    · rw [ite_eq_right hD]
      positivity
  calc
    _ ≤ ∑ u ∈ residualRange R g, ∑ v ∈ residualRange R g,
        ∑ _m ∈ Finset.Icc 1 M, ∑ _n ∈ Finset.Icc 1 M,
          B * (((u : ℝ)⁻¹ ^ 2) * ((v : ℝ)⁻¹ ^ 2)) :=
      Finset.sum_le_sum (fun u hu => Finset.sum_le_sum (fun v hv =>
        Finset.sum_le_sum (fun m hm => Finset.sum_le_sum (fun n hn => hpoint u hu v hv m hm n hn))))
    _ = (B * (M : ℝ) ^ 2) *
        (∑ u ∈ residualRange R g, ∑ v ∈ residualRange R g,
          (((u : ℝ)⁻¹ ^ 2) * ((v : ℝ)⁻¹ ^ 2))) := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ ≤ (B * (M : ℝ) ^ 2) * (4 * (g : ℝ) ^ 2 / (R : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (residualRange_pair_inv_sq_sum_le hR hg) (by positivity)
    _ = _ := by dsimp only [B]; ring

/-- Summing every possible gcd value gives the paper's M² S R off-diagonal scale. -/
theorem zeroFrequency_offDiagonal_weight_sum_le (M R S : ℕ) (hR : 0 < R) :
    (∑ g ∈ Finset.Icc 1 (2 * R), zeroOffDiagonalMass M R S g) ≤
      32 * (S : ℝ) * (cubicDivisorBound M R : ℝ) * (M : ℝ) ^ 2 * (R : ℝ) := by
  have hR' : (0 : ℝ) < R := Nat.cast_pos.mpr hR
  let B : ℝ := 4 * (S : ℝ) * (cubicDivisorBound M R : ℝ) * (M : ℝ) ^ 2 / (R : ℝ) ^ 2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  calc
    _ ≤ ∑ g ∈ Finset.Icc 1 (2 * R), B * (g : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro g hg
      apply (zeroOffDiagonalMass_le M R S g hR (Finset.mem_Icc.mp hg).1).trans_eq
      dsimp only [B]
      ring
    _ = B * ∑ g ∈ Finset.Icc 1 (2 * R), (g : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ B * (((2 * R : ℕ) : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left (sum_Icc_nat_pow_le (2 * R) 2) hB
    _ = _ := by
      dsimp only [B]
      push_cast
      field_simp
      ring

#print axioms cubicDifference_divisors_le
#print axioms zeroFrequency_offDiagonal_weight_sum_le

end

end PrimeGap182.TypeIII
