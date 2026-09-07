import IncidenceFareyResidues
import IncidenceSchur

/-!
# The actual Farey coefficient estimate

This is the finite version of Lemma 2.3, with the divisor factor explicit.
The proof counts actual congruent pairs and applies the proved finite
Schur estimate. Both signs of the denominators are allowed; no numerator
unit condition is imposed.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators

def incidenceFareyCoefficients {q : ℕ} [NeZero q]
    (A : Finset ℤ) (I : ℤ → Finset ℤ) (B : ℤ)
    (c : ℤ → ℂ) (β : ℤ → ℤ → ℂ) : ZMod q → ℂ := fun b =>
  ∑ a ∈ A, c a * ∑ k ∈ I a,
    if incidenceFareyResidue q B a k = b then β a k else 0

set_option maxHeartbeats 800000 in
theorem incidenceFarey_energy_le {q : ℕ} [NeZero q]
    (A : Finset ℤ) (I : ℤ → Finset ℤ) (B : ℤ)
    (U V τ : ℝ) (hU : 0 < U) (hV : 0 ≤ V)
    (hA : ∀ a ∈ A, U ≤ |(a : ℝ)| ∧ |(a : ℝ)| ≤ 2 * U ∧
      IsUnit (a : ZMod q))
    (hτ : ∀ a ∈ A, (a.natAbs.divisors.card : ℝ) ≤ τ)
    (center : ℤ → ℝ) (hI : ∀ a ∈ A, ∀ k ∈ I a, |(k : ℝ) - center a| ≤ V)
    (c : ℤ → ℂ) (β : ℤ → ℤ → ℂ)
    (hβ : ∀ a ∈ A, ∀ k ∈ I a, ‖β a k‖ ≤ 1) :
    incidenceVectorEnergy (incidenceFareyCoefficients (q := q) A I B c β) ≤
      (1 + 8 * U * V / (q : ℝ)) * ((A.card : ℝ) + 8 * V * τ) *
        ∑ a ∈ A, ‖c a‖ ^ 2 := by
  classical
  let R : Matrix (ZMod q) A ℂ :=
    incidenceFiberMatrix (fun a : A => I a.val)
      (fun a : A => incidenceFareyResidue q B a.val)
      (fun a : A => β a.val)
  let K : ℝ := 1 + 8 * U * V / (q : ℝ)
  let N : Matrix A A ℝ := fun a b => K *
    (1 + (2 * V / U) * (Int.gcd a.val b.val : ℝ))
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hne (a : ℤ) (ha : a ∈ A) : a ≠ 0 := by
    intro hz
    have h := (hA a ha).1
    simp only [hz, Int.cast_zero, abs_zero] at h
    exact hU.not_ge h
  have hN : ∀ a b, 0 ≤ N a b := by
    intro a b
    dsimp only [N]
    positivity
  have hsym : ∀ a b, N a b = N b a := by
    intro a b
    dsimp only [N]
    rw [Int.gcd_comm]
  have hrow (a : A) : ∑ b, N a b ≤ K * ((A.card : ℝ) + 8 * V * τ) := by
    have hg := incidenceFarey_gcd_row_sum A a.val (hne a.val a.property) U hU.le
      (fun b hb => ⟨hne b hb, (hA b hb).2.1⟩)
    have hgτ : (∑ b ∈ A, (Int.gcd a.val b : ℝ)) ≤ 4 * U * τ :=
      hg.trans (mul_le_mul_of_nonneg_left (hτ a.val a.property) (by positivity))
    change (∑ b : A, K * (1 + (2 * V / U) * (Int.gcd a.val b.val : ℝ))) ≤ _
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
      mul_one, ← Finset.mul_sum]
    rw [Finset.sum_coe_sort A (fun b : ℤ => (Int.gcd a.val b : ℝ))]
    apply mul_le_mul_of_nonneg_left _ hK
    apply add_le_add le_rfl
    calc
      _ ≤ (2 * V / U) * (4 * U * τ) :=
        mul_le_mul_of_nonneg_left hgτ (by positivity)
      _ = 8 * V * τ := by field_simp; ring
  have hgram (a b : A) : ‖(Rᴴ * R) a b‖ ≤ N a b := by
    have hg := incidenceFiberMatrix_gram_norm
      (fun a : A => I a.val) (fun a : A => incidenceFareyResidue q B a.val)
      (fun a : A => β a.val) (fun a k hk => hβ a.val a.property k hk) a b
    have hc := incidenceFarey_pair_card_le (I a.val) (I b.val) q hq B a.val b.val
      (hne a.val a.property) (hA a.val a.property).2.2 (hA b.val b.property).2.2
      U V (center a.val) (center b.val) hU hV
      (hA a.val a.property).1 (hA a.val a.property).2.1 (hA b.val b.property).2.1
      (hI a.val a.property) (hI b.val b.property)
    apply hg.trans
    change _ ≤ K * (1 + (2 * V / U) * (Int.gcd a.val b.val : ℝ))
    convert hc using 1
    dsimp only [K, incidenceFiberCollisions]
    ring
  have hresp : R *ᵥ (fun a : A => c a.val) =
      incidenceFareyCoefficients (q := q) A I B c β := by
    funext b
    simp only [Matrix.mulVec, dotProduct, R, incidenceFiberMatrix,
      incidenceFareyCoefficients]
    rw [Finset.sum_coe_sort A (fun a : ℤ =>
      (∑ k ∈ I a, if incidenceFareyResidue q B a k = b then β a k else 0) * c a)]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hb := incidenceEnergy_le_symmetricSchur R N (K * ((A.card : ℝ) + 8 * V * τ))
    hN hsym hrow hgram (fun a : A => c a.val)
  have hcen : incidenceVectorEnergy (fun a : A => c a.val) = ∑ a ∈ A, ‖c a‖ ^ 2 :=
    Finset.sum_coe_sort A (fun a : ℤ => ‖c a‖ ^ 2)
  rw [hresp, hcen] at hb
  simpa only [K] using hb

#print axioms incidenceFarey_energy_le

end PrimeGap182Audit
