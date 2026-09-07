import TypeIIISharedMatrix
import TypeIIICoefficientNorms

/-!
# Actual one-sided Fourier coefficient vectors from the signed square

The arithmetic unit restrictions stay in the coefficient vectors. Their Euclidean norms
are bounded by the proved one-sided Fourier estimate. The finite original correlation sum
is then identified with the shared matrix coefficient, with all CRT factors intact.
-/

open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

attribute [local instance] familyProductNeZero

/-- One-sided Fourier coefficients, retaining the original unit restriction at `u*w`. -/
def separatedFourierVector (u w : ℕ) [NeZero u] [NeZero w]
    (a : ℤ) (d : ZMod u) (A : ℤ) (N : ℕ) (α : IntegerIntervalIndex A N → ℂ) :
    EuclideanSpace ℂ (IntegerIntervalIndex A N) :=
  WithLp.toLp 2 (fun m => if IsUnit (m.1 : ZMod (u * w)) then
    α m * singleFourier u ((a : ZMod u) * (m.1 : ZMod u)⁻¹ * ((w : ZMod u)⁻¹) ^ 3) d
    else 0)

theorem card_integerIntervalIndex (A : ℤ) (N : ℕ) :
    Fintype.card (IntegerIntervalIndex A N) = N := by
  simp only [IntegerIntervalIndex, Fintype.card_coe, Int.card_Ico, add_sub_cancel_left,
    Int.toNat_natCast]

/-- The actual masked coefficient vector has the expected Euclidean square-root bound. -/
theorem separatedFourierVector_norm_le (u w : ℕ) [NeZero u] [NeZero w]
    (huw : u.Coprime w) (hsq : Squarefree u) (a : ℤ) (ha : IsUnit (a : ZMod u))
    (d : ZMod u) (A : ℤ) (N : ℕ) (α : IntegerIntervalIndex A N → ℂ)
    {L : ℝ} (hL : 0 ≤ L) (hα : ∀ m, ‖α m‖ ≤ L) :
    ‖separatedFourierVector u w a d A N α‖ ≤
      Real.sqrt (N : ℝ) * (L * (3 : ℝ) ^ u.primeFactors.card * Real.sqrt (u : ℝ)) := by
  let C : ℝ := L * (3 : ℝ) ^ u.primeFactors.card * Real.sqrt (u : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint (m : IntegerIntervalIndex A N) :
      ‖separatedFourierVector u w a d A N α m‖ ≤ C := by
    change ‖if IsUnit (m.1 : ZMod (u * w)) then
      α m * singleFourier u ((a : ZMod u) * (m.1 : ZMod u)⁻¹ * ((w : ZMod u)⁻¹) ^ 3) d
      else 0‖ ≤ C
    by_cases hm : IsUnit (m.1 : ZMod (u * w))
    · rw [ite_eq_left hm, norm_mul]
      have hmu := PrimeGap186.isUnit_intCast_of_dvd u (u * w) (dvd_mul_right u w) m.1 hm
      have harg := (ha.mul (ZMod.isUnit_inv hmu)).mul
        (PrimeGap186.isUnit_inv_cube u w huw.symm)
      have hh := mul_le_mul (hα m) (singleFourier_norm_le u hsq _ d harg)
        (norm_nonneg _) hL
      simpa only [C, mul_assoc] using hh
    · rw [ite_eq_right hm, norm_zero]
      exact hC
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) hC)).mp
  rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  calc
    _ ≤ ∑ _m : IntegerIntervalIndex A N, C ^ 2 :=
      Finset.sum_le_sum (fun m _ => pow_le_pow_left₀ (norm_nonneg _) (hpoint m) 2)
    _ = (N : ℝ) * C ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, card_integerIntervalIndex, nsmul_eq_mul]

/-- The original shared-frequency finite sum, with both original arithmetic guards. -/
def sharedOriginalCoefficientSum (u v w : ℕ) [NeZero u] [NeZero v] [NeZero w]
    (a c A B : ℤ) (N M : ℕ)
    (α : IntegerIntervalIndex A N → ℂ) (β : IntegerIntervalIndex B M → ℂ) : ℂ :=
  ∑ m : IntegerIntervalIndex A N, ∑ n : IntegerIntervalIndex B M,
    if IsUnit (m.1 : ZMod (u * w)) ∧ IsUnit (n.1 : ZMod (v * w)) then
      α m * sharedInverseFourier u v w a m.1 n.1 c * star (β n)
    else 0

/-- Exact finite-sum identification with the genuine shared matrix coefficient. -/
theorem sharedOriginalCoefficientSum_eq_matrix {ι : Type*} [Fintype ι]
    (q : ι → ℕ) [∀ i, Fact (q i).Prime]
    (hcp : Pairwise (fun i j => (q i).Coprime (q j)))
    (u v : ℕ) [NeZero u] [NeZero v] (huv : u.Coprime v)
    (huw : u.Coprime (∏ i, q i)) (hvw : v.Coprime (∏ i, q i))
    (a c A B : ℤ) (ha : IsUnit (a : ZMod (∏ i, q i))) (N M : ℕ)
    (α : IntegerIntervalIndex A N → ℂ) (β : IntegerIntervalIndex B M → ℂ) :
    sharedOriginalCoefficientSum u v (∏ i, q i) a c A B N M α β =
      matrixCoefficientSum (sharedMatchingMatrix q a c A B N M (u : ℤ) (v : ℤ))
        (separatedFourierVector u (∏ i, q i) a
          ((c : ZMod u) * ((v * ∏ i, q i : ℕ) : ZMod u)⁻¹) A N α)
        (separatedFourierVector v (∏ i, q i) a
          (-((c : ZMod v) * ((u * ∏ i, q i : ℕ) : ZMod v)⁻¹)) B M β) := by
  unfold sharedOriginalCoefficientSum matrixCoefficientSum
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  change (if IsUnit (m.1 : ZMod (u * ∏ i, q i)) ∧ IsUnit (n.1 : ZMod (v * ∏ i, q i)) then
      α m * sharedInverseFourier u v (∏ i, q i) a m.1 n.1 c * star (β n) else 0) =
    (if IsUnit (m.1 : ZMod (u * ∏ i, q i)) then
      α m * singleFourier u
        ((a : ZMod u) * (m.1 : ZMod u)⁻¹ * (((∏ i, q i : ℕ) : ZMod u)⁻¹) ^ 3)
        ((c : ZMod u) * ((v * ∏ i, q i : ℕ) : ZMod u)⁻¹) else 0) *
    sharedMatchingMatrix q a c A B N M (u : ℤ) (v : ℤ) m n *
    star (if IsUnit (n.1 : ZMod (v * ∏ i, q i)) then
      β n * singleFourier v
        ((a : ZMod v) * (n.1 : ZMod v)⁻¹ * (((∏ i, q i : ℕ) : ZMod v)⁻¹) ^ 3)
        (-((c : ZMod v) * ((u * ∏ i, q i : ℕ) : ZMod v)⁻¹)) else 0)
  by_cases hm : IsUnit (m.1 : ZMod (u * ∏ i, q i))
  · by_cases hn : IsUnit (n.1 : ZMod (v * ∏ i, q i))
    · rw [ite_eq_left ⟨hm, hn⟩, ite_eq_left hm, ite_eq_left hn,
        sharedInverseFourier_crt u v (∏ i, q i) huv huw hvw a m.1 n.1 c hm hn]
      have hu : IsUnit ((u : ℤ) : ZMod (∏ i, q i)) := by
        simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime u (∏ i, q i)).mpr huw
      have hv : IsUnit ((v : ℤ) : ZMod (∏ i, q i)) := by
        simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime v (∏ i, q i)).mpr hvw
      have hmw := PrimeGap186.isUnit_intCast_of_dvd (∏ i, q i) (u * ∏ i, q i)
        (dvd_mul_left (∏ i, q i) u) m.1 hm
      have hnw := PrimeGap186.isUnit_intCast_of_dvd (∏ i, q i) (v * ∏ i, q i)
        (dvd_mul_left (∏ i, q i) v) n.1 hn
      rw [sharedMatchingMatrix_apply_of_units q hcp a c A B N M u v ha hu hv m n hmw hnw,
        star_mul]
      simp only [Int.cast_natCast, Nat.cast_mul]
      ring
    · simp only [hn, and_false, ite_false, star_zero, mul_zero]
  · simp only [hm, false_and, ite_false, zero_mul]

/-- A uniform subpower version of the actual one-sided vector bound. -/
theorem exists_separatedFourierVector_norm_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u w : ℕ) [NeZero u] [NeZero w],
      u.Coprime w → Squarefree u → ∀ (a : ℤ), IsUnit (a : ZMod u) →
      ∀ (d : ZMod u) (A : ℤ) (N : ℕ) (α : IntegerIntervalIndex A N → ℂ) (L : ℝ),
      0 ≤ L → (∀ m, ‖α m‖ ≤ L) →
      ‖separatedFourierVector u w a d A N α‖ ≤
        C * Real.sqrt (N : ℝ) * L * (u : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hbound⟩ :=
    PrimeGap186.exists_primeFactors_power_bound (show (1 : ℝ) ≤ 3 by norm_num) hε
  refine ⟨C, hC, ?_⟩
  intro u w _ _ huw hsq a ha d A N α L hL hα
  apply (separatedFourierVector_norm_le u w huw hsq a ha d A N α hL hα).trans
  have hu : (0 : ℝ) < u := by exact_mod_cast NeZero.pos u
  calc
    _ = (Real.sqrt (N : ℝ) * L * Real.sqrt (u : ℝ)) * (3 : ℝ) ^ u.primeFactors.card := by ring
    _ ≤ (Real.sqrt (N : ℝ) * L * Real.sqrt (u : ℝ)) * (C * (u : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (hbound u (NeZero.ne u)) (by positivity)
    _ = _ := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.rpow_add hu]
      ring

/-- The product of the actual two coefficient norms is uniformly bounded when both
outer moduli lie below the same positive scale. -/
theorem exists_separatedFourierVector_pair_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u v w : ℕ) [NeZero u] [NeZero v] [NeZero w],
      u.Coprime w → v.Coprime w → Squarefree u → Squarefree v →
      ∀ (a : ℤ), IsUnit (a : ZMod u) → IsUnit (a : ZMod v) →
      ∀ (du : ZMod u) (dv : ZMod v) (A B : ℤ) (M : ℕ)
        (α : IntegerIntervalIndex A M → ℂ) (β : IntegerIntervalIndex B M → ℂ)
        (L₁ L₂ T : ℝ), 0 ≤ L₁ → 0 ≤ L₂ → (u : ℝ) ≤ T → (v : ℝ) ≤ T →
      (∀ m, ‖α m‖ ≤ L₁) → (∀ n, ‖β n‖ ≤ L₂) →
      ‖separatedFourierVector u w a du A M α‖ * ‖separatedFourierVector v w a dv B M β‖ ≤
        C * (M : ℝ) * (L₁ * L₂) * T ^ (1 + ε) := by
  obtain ⟨C, hC, hb⟩ := exists_separatedFourierVector_norm_bound (show 0 < ε / 2 by positivity)
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  intro u v w _ _ _ huw hvw hsu hsv a hau hav du dv A B M α β L₁ L₂ T hL₁ hL₂ hu hv hα hβ
  have hT : 0 < T := lt_of_lt_of_le (by exact_mod_cast NeZero.pos u) hu
  have hu' : (u : ℝ) ^ (1 / 2 + ε / 2) ≤ T ^ (1 / 2 + ε / 2) :=
    Real.rpow_le_rpow (Nat.cast_nonneg u) hu (by positivity)
  have hv' : (v : ℝ) ^ (1 / 2 + ε / 2) ≤ T ^ (1 / 2 + ε / 2) :=
    Real.rpow_le_rpow (Nat.cast_nonneg v) hv (by positivity)
  have hf := (hb u w huw hsu a hau du A M α L₁ hL₁ hα).trans
    (mul_le_mul_of_nonneg_left hu' (by positivity))
  have hg := (hb v w hvw hsv a hav dv B M β L₂ hL₂ hβ).trans
    (mul_le_mul_of_nonneg_left hv' (by positivity))
  calc
    _ ≤ (C * Real.sqrt (M : ℝ) * L₁ * T ^ (1 / 2 + ε / 2)) *
        (C * Real.sqrt (M : ℝ) * L₂ * T ^ (1 / 2 + ε / 2)) :=
      mul_le_mul hf hg (norm_nonneg _) (by positivity)
    _ = C ^ 2 * (Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ)) * (L₁ * L₂) *
        (T ^ (1 / 2 + ε / 2) * T ^ (1 / 2 + ε / 2)) := by ring
    _ = _ := by
      rw [Real.mul_self_sqrt (Nat.cast_nonneg M), ← Real.rpow_add hT]
      congr 2
      ring

#print axioms separatedFourierVector_norm_le
#print axioms sharedOriginalCoefficientSum_eq_matrix
#print axioms exists_separatedFourierVector_norm_bound
#print axioms exists_separatedFourierVector_pair_bound

end

end PrimeGap182.TypeIII
