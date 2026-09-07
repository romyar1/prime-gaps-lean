import TypeIIISquarefreeCompletion

/-!
# Actual integer indices, the exceptional gcd, and off-diagonal averaging

The repeated local residue factors divide the gcd of the modulus and the integer
discriminant.  The off-diagonal average below excludes the zero difference before using a
divisor estimate; no diagonal term of size equal to the modulus is silently discarded.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem integer_repetition_iff_dvd (p : ℕ) [Fact p.Prime] (m m' n n' : ℤ) :
    ((m : ZMod p) = (m' : ZMod p) ∨ (n : ZMod p) = (n' : ZMod p)) ↔
      (p : ℤ) ∣ (m - m') * (n - n') := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_mul, Int.cast_sub, Int.cast_sub,
    mul_eq_zero, sub_eq_zero, sub_eq_zero]

theorem repeatedResidueFactor_le_gcd
    {ι : Type*} [Fintype ι] (q : ι → ℕ) [∀ i, Fact (q i).Prime]
    [NeZero (∏ i, q i)] (hcp : Pairwise (fun i j => (q i).Coprime (q j)))
    (m m' n n' : ℤ) :
    repeatedResidueFactor q (fun i => (m : ZMod (q i))) (fun i => (m' : ZMod (q i)))
      (fun i => (n : ZMod (q i))) (fun i => (n' : ZMod (q i))) ≤
      Int.gcd ((m - m') * (n - n')) ((∏ i, q i : ℕ) : ℤ) := by
  let r (i : ι) := if (q i : ℤ) ∣ (m - m') * (n - n') then q i else 1
  have hrep : repeatedResidueFactor q (fun i => (m : ZMod (q i)))
      (fun i => (m' : ZMod (q i))) (fun i => (n : ZMod (q i)))
      (fun i => (n' : ZMod (q i))) = ∏ i, r i := by
    unfold repeatedResidueFactor
    simp only [integer_repetition_iff_dvd, r]
  have hrdiv (i : ι) : r i ∣ q i := by
    dsimp only [r]
    split_ifs <;> simp only [dvd_refl, one_dvd]
  have hcp' : Pairwise (fun i j => IsCoprime (r i : ℤ) (r j : ℤ)) := by
    intro i j hij
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    rw [Int.gcd_natCast_natCast]
    exact Nat.Coprime.of_dvd (hrdiv i) (hrdiv j) (hcp hij)
  have hrd (i : ι) : (r i : ℤ) ∣ (m - m') * (n - n') := by
    dsimp only [r]
    split_ifs with hi
    · exact hi
    · exact one_dvd _
  have hprod : ((∏ i, r i : ℕ) : ℤ) ∣ (m - m') * (n - n') := by
    rw [Nat.cast_prod]
    exact Fintype.prod_dvd_of_coprime hcp' hrd
  have hprodS : (∏ i, r i) ∣ ∏ i, q i :=
    Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => hrdiv i)
  have hprodD : (∏ i, r i) ∣ ((m - m') * (n - n')).natAbs :=
    Int.natCast_dvd.mp hprod
  rw [hrep, Int.gcd_def, Int.natAbs_natCast]
  exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (NeZero.pos _))
    (Nat.dvd_gcd hprodD hprodS)

theorem squarefreeCompletionShape_mono_gcd {S G G' : ℝ}
    (hS : 1 ≤ S) (hG : G ≤ G') (Nh Nk : ℕ) :
    squarefreeCompletionShape S G Nh Nk ≤ squarefreeCompletionShape S G' Nh Nk := by
  have hs0 : 0 ≤ S := zero_le_one.trans hS
  have hL : 0 ≤ 1 + Real.log S := add_nonneg zero_le_one (Real.log_nonneg hS)
  unfold squarefreeCompletionShape
  gcongr

/-- The actual signed interval gcd sum after removing the unique zero difference. -/
theorem signed_interval_gcd_offzero_sum (s N : ℕ) (hs : 0 < s) :
    (∑ z ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0,
      (Int.gcd z (s : ℤ) : ℝ)) ≤ 2 * N * (s.divisors.card : ℝ) := by
  have hzero : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    simp only [Finset.mem_Icc, Left.neg_nonpos_iff, Nat.cast_nonneg, and_self]
  have heq := Finset.sum_erase_add (s := Finset.Icc (-(N : ℤ)) (N : ℤ))
    (fun z => (Int.gcd z (s : ℤ) : ℝ)) hzero
  have hb := PrimeGap186.signed_interval_gcd_sum_le s N hs
  simp only [Int.zero_gcd, Int.natAbs_natCast] at heq
  linarith

/-- Square roots of the integer gcd are bounded by that positive integer. -/
theorem sqrt_int_gcd_le (s : ℕ) (hs : 0 < s) (z : ℤ) :
    Real.sqrt (Int.gcd z (s : ℤ) : ℝ) ≤ (Int.gcd z (s : ℤ) : ℝ) := by
  apply Real.sqrt_le_self_iff.mpr
  right
  have hpos : 0 < Int.gcd z (s : ℤ) := by
    rw [Int.gcd_def, Int.natAbs_natCast]
    exact Nat.gcd_pos_of_pos_right _ hs
  exact_mod_cast hpos

/-- Each actual interval row has off-diagonal square-root gcd mass at most `2*N*τ(s)`. -/
theorem interval_row_sqrt_gcd_offdiag
    (s N : ℕ) (hs : 0 < s) (A u : ℤ)
    (hu : u ∈ Finset.Ico A (A + N)) :
    (∑ v ∈ (Finset.Ico A (A + N)).erase u,
      Real.sqrt (Int.gcd (u - v) (s : ℤ) : ℝ)) ≤ 2 * N * (s.divisors.card : ℝ) := by
  have himage : ((Finset.Ico A (A + N)).erase u).image (fun v => u - v) ⊆
      (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0 := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hvu, hv⟩ := Finset.mem_erase.mp hv
    have hu' := Finset.mem_Ico.mp hu
    have hv' := Finset.mem_Ico.mp hv
    apply Finset.mem_erase.mpr
    constructor
    · omega
    · simp only [Finset.mem_Icc]
      omega
  have hinj : Set.InjOn (fun v : ℤ => u - v) ((Finset.Ico A (A + N)).erase u) := by
    intro v hv w hw heq
    dsimp only at heq
    omega
  calc
    _ ≤ ∑ z ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0, (Int.gcd z (s : ℤ) : ℝ) :=
      Finset.sum_le_sum_of_injOn (fun v : ℤ => u - v) hinj himage
        (fun v _ => sqrt_int_gcd_le s hs (u - v)) (fun z _ _ => Nat.cast_nonneg _)
    _ ≤ _ := signed_interval_gcd_offzero_sum s N hs

/-- The off-diagonal square-root gcd average, with repeated interval residues allowed. -/
theorem interval_sqrt_gcd_offdiag
    (s N : ℕ) (hs : 0 < s) (A : ℤ) :
    (∑ u ∈ Finset.Ico A (A + N), ∑ v ∈ (Finset.Ico A (A + N)).erase u,
      Real.sqrt (Int.gcd (u - v) (s : ℤ) : ℝ)) ≤ 2 * (N : ℝ) ^ 2 * s.divisors.card := by
  calc
    _ ≤ ∑ _u ∈ Finset.Ico A (A + N), 2 * (N : ℝ) * s.divisors.card :=
      Finset.sum_le_sum (fun u hu => interval_row_sqrt_gcd_offdiag s N hs A u hu)
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Int.card_Ico, add_sub_cancel_left,
        Int.toNat_natCast]
      ring

/-- Submultiplicativity of the actual gcd weight in the integer discriminant. -/
theorem sqrt_gcd_integer_product_le (s : ℕ) (hs : 0 < s) (a b : ℤ) :
    Real.sqrt (Int.gcd (a * b) (s : ℤ) : ℝ) ≤
      Real.sqrt (Int.gcd a (s : ℤ) : ℝ) * Real.sqrt (Int.gcd b (s : ℤ) : ℝ) := by
  have ha : 0 < Nat.gcd s a.natAbs := Nat.gcd_pos_of_pos_left _ hs
  have hb : 0 < Nat.gcd s b.natAbs := Nat.gcd_pos_of_pos_left _ hs
  have hdiv : Nat.gcd s (a.natAbs * b.natAbs) ∣ Nat.gcd s a.natAbs * Nat.gcd s b.natAbs :=
    gcd_mul_dvd_mul_gcd s a.natAbs b.natAbs
  have hle := Nat.le_of_dvd (Nat.mul_pos ha hb) hdiv
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.sqrt_le_sqrt
  simp only [Int.gcd_def, Int.natAbs_mul, Int.natAbs_natCast, Nat.gcd_comm,
    ← Nat.cast_mul]
  exact_mod_cast hle

/-- The four-index off-diagonal discriminant average needed after the fourth-moment
expansion. Both index intervals may be longer than the modulus. -/
theorem interval_four_index_sqrt_gcd_offdiag
    (s N M : ℕ) (hs : 0 < s) (A B : ℤ) :
    (∑ u ∈ Finset.Ico A (A + N), ∑ v ∈ (Finset.Ico A (A + N)).erase u,
      ∑ a ∈ Finset.Ico B (B + M), ∑ b ∈ (Finset.Ico B (B + M)).erase a,
        Real.sqrt (Int.gcd ((u - v) * (a - b)) (s : ℤ) : ℝ)) ≤
      4 * (N : ℝ) ^ 2 * (M : ℝ) ^ 2 * (s.divisors.card : ℝ) ^ 2 := by
  let U := Finset.Ico A (A + N)
  let V := Finset.Ico B (B + M)
  calc
    _ ≤ ∑ u ∈ U, ∑ v ∈ U.erase u, ∑ a ∈ V, ∑ b ∈ V.erase a,
        Real.sqrt (Int.gcd (u - v) (s : ℤ) : ℝ) *
          Real.sqrt (Int.gcd (a - b) (s : ℤ) : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact sqrt_gcd_integer_product_le s hs (u - v) (a - b)
    _ = (∑ u ∈ U, ∑ v ∈ U.erase u, Real.sqrt (Int.gcd (u - v) (s : ℤ) : ℝ)) *
        (∑ a ∈ V, ∑ b ∈ V.erase a, Real.sqrt (Int.gcd (a - b) (s : ℤ) : ℝ)) := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ (2 * (N : ℝ) ^ 2 * s.divisors.card) *
        (2 * (M : ℝ) ^ 2 * s.divisors.card) := by
      apply mul_le_mul (interval_sqrt_gcd_offdiag s N hs A)
        (interval_sqrt_gcd_offdiag s M hs B)
      · exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _))
      · positivity
    _ = _ := by ring

#print axioms integer_repetition_iff_dvd
#print axioms repeatedResidueFactor_le_gcd
#print axioms signed_interval_gcd_offzero_sum
#print axioms interval_row_sqrt_gcd_offdiag
#print axioms interval_sqrt_gcd_offdiag
#print axioms sqrt_gcd_integer_product_le
#print axioms interval_four_index_sqrt_gcd_offdiag

end

end PrimeGap182.TypeIII
