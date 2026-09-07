import IncidenceFareyCounting

/-!
# Actual Farey residue collisions and gcd row sums

No numerator is assumed to be a unit. The denominators can have either
sign, provided their absolute values lie in the specified dyadic band.
-/

noncomputable section

namespace PrimeGap182Audit

open scoped BigOperators

def incidenceFareyResidue (q : ℕ) (B a k : ℤ) : ZMod q :=
  ((k + B : ℤ) : ZMod q) * (a : ZMod q)⁻¹

theorem incidenceUnitRatio_eq_iff {q : ℕ} (a b x y : ZMod q)
    (ha : IsUnit a) (hb : IsUnit b) :
    x * a⁻¹ = y * b⁻¹ ↔ b * x = a * y := by
  have hl : (a * b) * (x * a⁻¹) = b * x := by
    calc
      _ = (a * a⁻¹) * (b * x) := by ring
      _ = _ := by rw [ZMod.mul_inv_of_unit a ha, one_mul]
  have hr : (a * b) * (y * b⁻¹) = a * y := by
    calc
      _ = (b * b⁻¹) * (a * y) := by ring
      _ = _ := by rw [ZMod.mul_inv_of_unit b hb, one_mul]
  calc
    x * a⁻¹ = y * b⁻¹ ↔ (a * b) * (x * a⁻¹) = (a * b) * (y * b⁻¹) :=
      (ha.mul hb).mul_right_inj.symm
    _ ↔ b * x = a * y := by rw [hl, hr]

theorem incidenceFarey_collision_iff (q : ℕ) (B a b k l : ℤ)
    (ha : IsUnit (a : ZMod q)) (hb : IsUnit (b : ZMod q)) :
    incidenceFareyResidue q B a k = incidenceFareyResidue q B b l ↔
      Int.ModEq (q : ℤ) (b * k - a * l) (B * (a - b)) := by
  rw [incidenceFareyResidue, incidenceFareyResidue,
    incidenceUnitRatio_eq_iff _ _ _ _ ha hb, ← ZMod.intCast_eq_intCast_iff]
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_add]
  constructor <;> intro h <;> linear_combination h

theorem incidenceFarey_pair_card_le (I J : Finset ℤ) (q : ℕ) (hq : 0 < q)
    (B a b : ℤ) (ha : a ≠ 0)
    (hau : IsUnit (a : ZMod q)) (hbu : IsUnit (b : ZMod q))
    (U V c₁ c₂ : ℝ) (hU : 0 < U) (hV : 0 ≤ V)
    (haU : U ≤ |(a : ℝ)|) (ha2U : |(a : ℝ)| ≤ 2 * U)
    (hb2U : |(b : ℝ)| ≤ 2 * U)
    (hI : ∀ k ∈ I, |(k : ℝ) - c₁| ≤ V)
    (hJ : ∀ l ∈ J, |(l : ℝ) - c₂| ≤ V) :
    ((((I ×ˢ J).filter (fun z =>
        incidenceFareyResidue q B a z.1 = incidenceFareyResidue q B b z.2)).card) : ℝ) ≤
      (1 + 8 * U * V / (q : ℝ)) * (1 + 2 * V * (Int.gcd a b : ℝ) / U) := by
  classical
  have h := incidenceDeterminant_mod_card_le
    ((I ×ˢ J).filter (fun z =>
      incidenceFareyResidue q B a z.1 = incidenceFareyResidue q B b z.2))
    a b (q : ℤ) (B * (a - b)) ha (by exact_mod_cast hq)
    U V c₁ c₂ hU hV haU ha2U hb2U (by
      intro z hz
      exact (incidenceFarey_collision_iff q B a b z.1 z.2 hau hbu).mp
        (Finset.mem_filter.mp hz).2) (by
      intro z hz
      have hzIJ := Finset.mem_product.mp (Finset.mem_filter.mp hz).1
      exact ⟨hI z.1 hzIJ.1, hJ z.2 hzIJ.2⟩)
  simpa only [Int.cast_natCast] using h

theorem incidenceFarey_gcd_row_sum (A : Finset ℤ) (a : ℤ) (ha : a ≠ 0)
    (U : ℝ) (hU : 0 ≤ U)
    (hA : ∀ b ∈ A, b ≠ 0 ∧ |(b : ℝ)| ≤ 2 * U) :
    (∑ b ∈ A, (Int.gcd a b : ℝ)) ≤
      4 * U * (a.natAbs.divisors.card : ℝ) := by
  classical
  let K : ℕ := ⌊2 * U⌋₊
  have hK : (K : ℝ) ≤ 2 * U := Nat.floor_le (by positivity)
  have hJ : ∀ b ∈ A, b ≠ 0 ∧ -(K : ℤ) ≤ b ∧ b ≤ (K : ℤ) := by
    intro b hb
    have habs : (b.natAbs : ℝ) = |(b : ℝ)| := by
      calc
        (b.natAbs : ℝ) = ((b.natAbs : ℤ) : ℝ) := rfl
        _ = ((|b| : ℤ) : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs b)
        _ = |(b : ℝ)| := Int.cast_abs
    have hbK : b.natAbs ≤ K := Nat.le_floor ((habs ▸ (hA b hb).2))
    have hbI : |b| ≤ (K : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hbK
    exact ⟨(hA b hb).1, abs_le.mp hbI⟩
  have hs := PrimeGap186.sourceSmoothFactor_signed_gcd_sum_le a.natAbs K
    (Int.natAbs_pos.mpr ha) A hJ
  have hg (b : ℤ) : Int.gcd b (a.natAbs : ℤ) = Int.gcd a b := by
    simp only [Int.gcd_def, Int.natAbs_natCast, Nat.gcd_comm]
  simp only [hg] at hs
  calc
    _ ≤ 2 * (K : ℝ) * (a.natAbs.divisors.card : ℝ) := hs
    _ ≤ 4 * U * (a.natAbs.divisors.card : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      linarith

#print axioms incidenceUnitRatio_eq_iff
#print axioms incidenceFarey_collision_iff
#print axioms incidenceFarey_pair_card_le
#print axioms incidenceFarey_gcd_row_sum

end PrimeGap182Audit
