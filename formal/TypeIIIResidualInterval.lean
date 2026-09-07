import TypeIIIResidualRanges
import TypeIIIDyadicBlock

/-! Exact interval coordinates for the residual modulus range R ≤ gu ≤ 2R. -/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def residualStart (R g : ℕ) : ℕ+ := ⟨(R - 1) / g + 1, Nat.zero_lt_succ _⟩

def residualLength (R g : ℕ) : ℕ := 2 * R / g + 1 - (residualStart R g : ℕ)

theorem residualRange_eq_Icc (R g : ℕ) (hR : 0 < R) (hg : 0 < g) :
    residualRange R g = Finset.Icc (residualStart R g : ℕ) (2 * R / g) := by
  ext u
  simp only [residualRange, Finset.mem_filter, Finset.mem_Icc]
  change ((1 ≤ u ∧ u ≤ 2 * R / g) ∧ R ≤ g * u) ↔
    ((R - 1) / g + 1 ≤ u ∧ u ≤ 2 * R / g)
  have he₀ : (R - 1) / g < u ↔ R - 1 < u * g := Nat.div_lt_iff_lt_mul hg
  have he : (R - 1) / g < u ↔ R - 1 < g * u := by
    simpa only [mul_comm] using he₀
  constructor
  · rintro ⟨⟨_, hupper⟩, hlower⟩
    exact ⟨Nat.succ_le_iff.mpr (he.mpr ((Nat.sub_lt hR (by norm_num : (0 : ℕ) < 1)).trans_le hlower)),
      hupper⟩
  · rintro ⟨hlower, hupper⟩
    refine ⟨⟨(Nat.succ_le_succ (Nat.zero_le _)).trans hlower, hupper⟩, ?_⟩
    calc
      R = (R - 1) + 1 := (Nat.sub_add_cancel hR).symm
      _ ≤ g * u := Nat.succ_le_iff.mpr (he.mp (Nat.lt_of_succ_le hlower))

theorem residualLength_le (R g : ℕ) : residualLength R g ≤ 2 * R / g := by
  unfold residualLength
  have hh : 1 ≤ (residualStart R g : ℕ) := (residualStart R g).pos
  exact (Nat.sub_le_sub_left hh _).trans_eq (Nat.add_sub_cancel _ _)

theorem residualStart_add_mem (R g x : ℕ) (hR : 0 < R) (hg : 0 < g)
    (hx : x ∈ Finset.range (residualLength R g)) :
    (residualStart R g : ℕ) + x ∈ residualRange R g := by
  rw [residualRange_eq_Icc R g hR hg]
  have hh := Finset.mem_range.mp hx
  dsimp only [residualLength] at hh
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

/-- An actual finite sum over residual moduli equals the indicated integer interval sum. -/
theorem sum_residualRange_eq_sum_range {E : Type*} [AddCommMonoid E]
    (R g : ℕ) (hR : 0 < R) (hg : 0 < g) (f : ℕ → E) :
    (∑ u ∈ residualRange R g, f u) =
      ∑ x ∈ Finset.range (residualLength R g), f ((residualStart R g : ℕ) + x) := by
  rw [residualRange_eq_Icc R g hR hg]
  symm
  apply Finset.sum_bij (fun x _ => (residualStart R g : ℕ) + x)
  · intro x hx
    have hh := Finset.mem_range.mp hx
    dsimp only [residualLength] at hh
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro x _ y _ hxy
    exact Nat.add_left_cancel hxy
  · intro u hu
    refine ⟨u - (residualStart R g : ℕ), ?_, ?_⟩
    · obtain ⟨hu₁, hu₂⟩ := Finset.mem_Icc.mp hu
      apply Finset.mem_range.mpr
      dsimp only [residualLength]
      omega
    · exact Nat.add_sub_of_le (Finset.mem_Icc.mp hu).1
  · intro x _
    rfl

theorem residualRange_real_bounds {R g u : ℕ} (hg : 0 < g) (hu : u ∈ residualRange R g) :
    (R : ℝ) / (g : ℝ) ≤ u ∧ (u : ℝ) ≤ 2 * (R : ℝ) / (g : ℝ) := by
  have hg' : (0 : ℝ) < g := Nat.cast_pos.mpr hg
  have hm := residualRange_spec hu
  constructor
  · apply (div_le_iff₀ hg').2
    exact_mod_cast (show R ≤ u * g by simpa [mul_comm] using hm.2.1)
  · apply (le_div_iff₀ hg').2
    exact_mod_cast ((Nat.mul_le_mul_right g hm.2.2).trans (Nat.div_mul_le_self (2 * R) g))

theorem residualLength_real_le {R g : ℕ} (hg : 0 < g) :
    (residualLength R g : ℝ) ≤ 2 * (R : ℝ) / (g : ℝ) := by
  apply (le_div_iff₀ (Nat.cast_pos.mpr hg)).2
  exact_mod_cast ((Nat.mul_le_mul_right g (residualLength_le R g)).trans
    (Nat.div_mul_le_self (2 * R) g))

theorem residualInterval_upper_scale {R g : ℕ} (hg : 0 < g)
    (hN : 0 < residualLength R g) :
    (residualStart R g : ℝ) + (residualLength R g : ℝ) ≤ 4 * ((R : ℝ) / (g : ℝ)) := by
  have hU := (residualStart R g).pos
  have hNU : (residualStart R g : ℕ) + residualLength R g = 2 * R / g + 1 := by
    dsimp only [residualLength] at *
    omega
  have hfloor : 1 ≤ 2 * R / g := by
    dsimp only [residualLength] at hN
    omega
  have hgr : g ≤ 2 * R := by
    have := (Nat.le_div_iff_mul_le hg).mp hfloor
    simpa only [one_mul] using this
  have hgr' : (g : ℝ) ≤ 2 * (R : ℝ) := by exact_mod_cast hgr
  have hcast : (residualStart R g : ℝ) + (residualLength R g : ℝ) =
      ((2 * R / g : ℕ) : ℝ) + 1 := by exact_mod_cast hNU
  have hfloor' : ((2 * R / g : ℕ) : ℝ) * (g : ℝ) ≤ 2 * (R : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self (2 * R) g
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (Nat.cast_pos.mpr hg)).2
  rw [hcast]
  nlinarith

/-- The outer-average factor is increasing, despite the reciprocal square root in its
middle summand. This is used with the actual residual interval length. -/
theorem outer_matrix_scale_expand {M R w : ℝ} (hR : 0 < R) :
    R ^ 2 * matrixThreeScale M R w =
      (M ^ (3 / 4 : ℝ) * w ^ (1 / 2 : ℝ)) * R ^ 2 +
      (M * w ^ (3 / 4 : ℝ)) * R ^ (3 / 2 : ℝ) +
      (M * w ^ (3 / 8 : ℝ)) * R ^ 2 := by
  have he : R ^ 2 / R ^ (1 / 2 : ℝ) = R ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 2 - 1 / 2 by norm_num, Real.rpow_sub hR]
    norm_num
  rw [← he]
  unfold matrixThreeScale
  ring

theorem outer_matrix_scale_comparison {M N R w : ℝ}
    (hM : 0 ≤ M) (hw : 0 ≤ w) (hN : 0 < N) (hR : 0 < R) (hNR : N ≤ 2 * R) :
    N ^ 2 * matrixThreeScale M N w ≤ 4 * (R ^ 2 * matrixThreeScale M R w) := by
  rw [outer_matrix_scale_expand hN, outer_matrix_scale_expand hR]
  have hsquare : N ^ 2 ≤ 4 * R ^ 2 := by nlinarith [sq_nonneg (2 * R - N)]
  have hthree : N ^ (3 / 2 : ℝ) ≤ 4 * R ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ (2 * R) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow hN.le hNR (by norm_num)
      _ = (2 : ℝ) ^ (3 / 2 : ℝ) * R ^ (3 / 2 : ℝ) := Real.mul_rpow (by norm_num) hR.le
      _ ≤ (2 : ℝ) ^ (2 : ℝ) * R ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num : (3 / 2 : ℝ) ≤ 2))
          (Real.rpow_nonneg hR.le _)
      _ = _ := by norm_num
  calc
    _ ≤ (M ^ (3 / 4 : ℝ) * w ^ (1 / 2 : ℝ)) * (4 * R ^ 2) +
        (M * w ^ (3 / 4 : ℝ)) * (4 * R ^ (3 / 2 : ℝ)) +
        (M * w ^ (3 / 8 : ℝ)) * (4 * R ^ 2) := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hsquare (by positivity))
        (mul_le_mul_of_nonneg_left hthree (by positivity)))
        (mul_le_mul_of_nonneg_left hsquare (by positivity))
    _ = _ := by ring

#print axioms sum_residualRange_eq_sum_range
#print axioms residualRange_real_bounds
#print axioms outer_matrix_scale_comparison

end

end PrimeGap182.TypeIII
