import TypeIIIZeroOffDiagonal

/-! The full cubic gcd weight is split and summed, retaining the coprime diagonal. -/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

theorem cubicDifference_eq_zero_iff (u v m n : ℕ) :
    cubicDifference u v m n = 0 ↔ m * u ^ 3 = n * v ^ 3 := by
  unfold cubicDifference
  rw [sub_eq_zero]
  exact_mod_cast (Iff.rfl : m * u ^ 3 = n * v ^ 3 ↔ m * u ^ 3 = n * v ^ 3)

theorem cubicDiagonalPairs_card_eq_sum (M u v : ℕ) :
    ((cubicDiagonalPairs M u v).card : ℝ) =
      ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
        if cubicDifference u v m n = 0 then (1 : ℝ) else 0 := by
  simp only [cubicDifference_eq_zero_iff]
  rw [show ((cubicDiagonalPairs M u v).card : ℝ) =
    ∑ _mn ∈ cubicDiagonalPairs M u v, (1 : ℝ) by simp]
  simp only [cubicDiagonalPairs, Finset.sum_filter, Finset.sum_product]

def cubicGcdPairMass (M u v s g : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
    ((g : ℝ)⁻¹ * ((u : ℝ)⁻¹ ^ 2) * ((v : ℝ)⁻¹ ^ 2)) *
      (Int.gcd (cubicDifference u v m n) ((s * g : ℕ) : ℤ) : ℝ)

def cubicOffDiagonalPairMass (M u v s g : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
    if cubicDifference u v m n ≠ 0 then
      ((g : ℝ)⁻¹ * ((u : ℝ)⁻¹ ^ 2) * ((v : ℝ)⁻¹ ^ 2)) *
        (Int.gcd (cubicDifference u v m n) ((s * g : ℕ) : ℤ) : ℝ)
    else 0

theorem cubicGcdPairMass_eq (M u v s g : ℕ) (hg : 0 < g) :
    cubicGcdPairMass M u v s g =
      (s : ℝ) * ((cubicDiagonalPairs M u v).card : ℝ) *
        ((u : ℝ)⁻¹ ^ 2) * ((v : ℝ)⁻¹ ^ 2) + cubicOffDiagonalPairMass M u v s g := by
  rw [cubicDiagonalPairs_card_eq_sum]
  simp only [cubicGcdPairMass, cubicOffDiagonalPairMass, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  by_cases hD : cubicDifference u v m n = 0
  · simp [hD]
    have hg' : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hg)
    field_simp
  · simp only [hD, ite_eq_right, ne_eq, not_false_eq_true, ite_eq_left, mul_zero, zero_mul,
      zero_add]

def cubicGcdMass (M R s g : ℕ) : ℝ :=
  ∑ u ∈ residualRange R g, ∑ v ∈ residualRange R g,
    if u.Coprime v then cubicGcdPairMass M u v s g else 0

theorem cubicGcdMass_nonneg (M R s g : ℕ) : 0 ≤ cubicGcdMass M R s g := by
  unfold cubicGcdMass cubicGcdPairMass
  positivity

theorem cubicGcdMass_le (M R s g : ℕ) (hg : 0 < g) :
    cubicGcdMass M R s g ≤ (s : ℝ) * cubicDiagonalMass M R g +
      ∑ u ∈ residualRange R g, ∑ v ∈ residualRange R g,
        cubicOffDiagonalPairMass M u v s g := by
  calc
    _ ≤ ∑ u ∈ residualRange R g, ∑ v ∈ residualRange R g,
        ((s : ℝ) * (if u.Coprime v then ((cubicDiagonalPairs M u v).card : ℝ) *
          ((u : ℝ)⁻¹ ^ 2) * ((v : ℝ)⁻¹ ^ 2) else 0) +
            cubicOffDiagonalPairMass M u v s g) := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro v _
      by_cases huv : u.Coprime v
      · simp only [ite_eq_left huv]
        apply le_of_eq
        rw [cubicGcdPairMass_eq M u v s g hg]
        ring
      · simp only [ite_eq_right huv, mul_zero, zero_add]
        unfold cubicOffDiagonalPairMass
        positivity
    _ = _ := by simp only [Finset.sum_add_distrib, cubicDiagonalMass, Finset.mul_sum]

theorem cubicOffDiagonalPairMass_s_sum (M R S g : ℕ) :
    (∑ s ∈ Finset.Icc 1 S, ∑ u ∈ residualRange R g, ∑ v ∈ residualRange R g,
      cubicOffDiagonalPairMass M u v s g) = zeroOffDiagonalMass M R S g := by
  unfold cubicOffDiagonalPairMass zeroOffDiagonalMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hD : cubicDifference u v m n ≠ 0
  · simp only [ite_eq_left hD, Finset.mul_sum]
  · simp only [ite_eq_right hD, Finset.sum_const_zero]

/-- Both zero-frequency branches together, before the harmless prime-count factor. -/
theorem cubicGcdMass_total_le (M R S : ℕ) (hR : 0 < R) :
    (∑ s ∈ Finset.Icc 1 S, ∑ g ∈ Finset.Icc 1 (2 * R), cubicGcdMass M R s g) ≤
      256 * (M : ℝ) * (S : ℝ) ^ 2 * (R : ℝ) +
        32 * (S : ℝ) * (cubicDivisorBound M R : ℝ) * (M : ℝ) ^ 2 * (R : ℝ) := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ g ∈ Finset.Icc 1 (2 * R),
        ((∑ s ∈ Finset.Icc 1 S, (s : ℝ) * cubicDiagonalMass M R g) +
          zeroOffDiagonalMass M R S g) := by
      apply Finset.sum_le_sum
      intro g hg
      calc
        _ ≤ ∑ s ∈ Finset.Icc 1 S, ((s : ℝ) * cubicDiagonalMass M R g +
            ∑ u ∈ residualRange R g, ∑ v ∈ residualRange R g,
              cubicOffDiagonalPairMass M u v s g) :=
          Finset.sum_le_sum (fun s _ => cubicGcdMass_le M R s g (Finset.mem_Icc.mp hg).1)
        _ = _ := by rw [Finset.sum_add_distrib, cubicOffDiagonalPairMass_s_sum]
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      exact add_le_add (zeroFrequency_diagonal_weight_sum_le M R S hR)
        (zeroFrequency_offDiagonal_weight_sum_le M R S hR)

#print axioms cubicGcdPairMass_eq
#print axioms cubicGcdMass_total_le

end

end PrimeGap182.TypeIII
