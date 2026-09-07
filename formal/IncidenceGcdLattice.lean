import IncidenceShearLattice

/-!
# The gcd-weighted sheared Fourier lattice

Every common divisor is retained. The divisor majorant, lattice reindexing,
summability and scale bound are proved, including zero coordinates and q=1.
-/

noncomputable section

namespace PrimeGap182Audit

open scoped BigOperators

def incidenceDivisibleDecay (d : ℕ) (a b τ : ℝ) (z : ℤ × ℤ) : ℝ :=
  if (d : ℤ) ∣ z.1 ∧ (d : ℤ) ∣ z.2 then incidenceShearedNonzeroDecay a b τ z else 0

def incidenceGcdDecay (q : ℕ) (a b τ : ℝ) (z : ℤ × ℤ) : ℝ :=
  incidenceShearedNonzeroDecay a b τ z * Real.sqrt (Nat.gcd q (Int.gcd z.1 z.2) : ℝ)

theorem incidenceDivisibleDecay_summable (d : ℕ) (a b τ : ℝ)
    (ha : 0 < a) (hb : 0 < b) : Summable (incidenceDivisibleDecay d a b τ) := by
  apply Summable.of_nonneg_of_le _ _ (incidenceShearedNonzeroDecay_bounds a b τ ha hb).1
  · intro z
    unfold incidenceDivisibleDecay
    split_ifs <;> first | exact le_rfl | exact incidenceShearedNonzeroDecay_nonneg _ _ _ _
  · intro z
    unfold incidenceDivisibleDecay
    split_ifs <;> first | exact le_rfl | exact incidenceShearedNonzeroDecay_nonneg _ _ _ _

/-- The subset of divisible pairs is actually parametrized by multiplying
both coordinates by d. -/
theorem incidenceDivisibleDecay_tsum (d : ℕ) (hd : 0 < d) (a b τ : ℝ) :
    (∑' z : ℤ × ℤ, incidenceDivisibleDecay d a b τ z) =
      ∑' z : ℤ × ℤ, incidenceShearedNonzeroDecay (a * d) (b * d) τ z := by
  let T (z : ℤ × ℤ) : ℤ × ℤ := ((d : ℤ) * z.1, (d : ℤ) * z.2)
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hi : Function.Injective T := by
    intro z w heq
    exact Prod.ext (mul_left_cancel₀ hdZ (congrArg Prod.fst heq))
      (mul_left_cancel₀ hdZ (congrArg Prod.snd heq))
  have hsupp : Function.support (incidenceDivisibleDecay d a b τ) ⊆ Set.range T := by
    intro z hz
    have hdiv : (d : ℤ) ∣ z.1 ∧ (d : ℤ) ∣ z.2 := by
      by_contra hn
      exact hz (by simp [incidenceDivisibleDecay, hn])
    obtain ⟨h, hh⟩ := hdiv.1
    obtain ⟨ν, hν⟩ := hdiv.2
    exact ⟨(h, ν), Prod.ext hh.symm hν.symm⟩
  have hterm (z : ℤ × ℤ) :
      incidenceDivisibleDecay d a b τ (T z) =
        incidenceShearedNonzeroDecay (a * d) (b * d) τ z := by
    have hT0 : T z = 0 ↔ z = 0 := by
      have hTzero : T 0 = 0 := by simp [T]
      constructor
      · intro heq
        exact hi (heq.trans hTzero.symm)
      · rintro rfl
        simp [T]
    simp only [incidenceDivisibleDecay, T, dvd_mul_right, and_self, ite_true]
    change incidenceShearedNonzeroDecay a b τ (T z) = _
    simp only [incidenceShearedNonzeroDecay, hT0]
    split_ifs
    · rfl
    · dsimp only [T]
      simp only [incidenceDecay, Int.cast_mul, Int.cast_natCast]
      have hlin : (d : ℝ) * (z.1 : ℝ) + τ * ((d : ℝ) * (z.2 : ℝ)) =
          (d : ℝ) * ((z.1 : ℝ) + τ * (z.2 : ℝ)) := by ring
      rw [hlin, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
      ring
  have heq := hi.tsum_eq hsupp
  simpa only [hterm] using heq.symm

theorem incidence_sqrt_gcd_le_divisor_sum (q : ℕ) (hq : 0 < q) (h ν : ℤ) :
    Real.sqrt (Nat.gcd q (Int.gcd h ν) : ℝ) ≤
      ∑ d ∈ q.divisors, if (d : ℤ) ∣ h ∧ (d : ℤ) ∣ ν then Real.sqrt (d : ℝ) else 0 := by
  let g := Nat.gcd q (Int.gcd h ν)
  have hgmem : g ∈ q.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left q _, hq.ne'⟩
  have hgg : (g : ℤ) ∣ (Int.gcd h ν : ℤ) := by
    exact_mod_cast Nat.gcd_dvd_right q (Int.gcd h ν)
  have hgh : (g : ℤ) ∣ h := hgg.trans (Int.gcd_dvd_left h ν)
  have hgν : (g : ℤ) ∣ ν := hgg.trans (Int.gcd_dvd_right h ν)
  have hh := Finset.single_le_sum
    (f := fun d : ℕ => if (d : ℤ) ∣ h ∧ (d : ℤ) ∣ ν then Real.sqrt (d : ℝ) else 0)
    (fun d _ => by split_ifs <;> positivity) hgmem
  have hgcond : (g : ℤ) ∣ h ∧ (g : ℤ) ∣ ν := ⟨hgh, hgν⟩
  rw [ite_eq_left hgcond] at hh
  exact hh

theorem incidenceDivisibleDecay_weighted_bound (d : ℕ) (hd : 0 < d)
    (a b τ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (d : ℝ) * (∑' z : ℤ × ℤ, incidenceDivisibleDecay d a b τ z) ≤
      8 / (a * b) + 4 / b + 2 / a := by
  rw [incidenceDivisibleDecay_tsum d hd]
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsq : Real.sqrt (d : ℝ) ≤ (d : ℝ) := Real.sqrt_le_self_iff.mpr (Or.inr hd1)
  have hi1 : Real.sqrt (d : ℝ) / d ≤ 1 := (div_le_one hdR).mpr hsq
  have hi2 : Real.sqrt (d : ℝ) / (d : ℝ) ^ 2 ≤ 1 :=
    (div_le_one (sq_pos_of_pos hdR)).mpr (hsq.trans (by nlinarith))
  calc
    _ ≤ Real.sqrt (d : ℝ) *
        (8 / ((a * d) * (b * d)) + 4 / (b * d) + 2 / (a * d)) :=
      mul_le_mul_of_nonneg_left
        (incidenceShearedNonzeroDecay_bounds (a * d) (b * d) τ
          (mul_pos ha hdR) (mul_pos hb hdR)).2 (Real.sqrt_nonneg _)
    _ = (8 / (a * b)) * (Real.sqrt (d : ℝ) / (d : ℝ) ^ 2) +
        (4 / b) * (Real.sqrt (d : ℝ) / d) +
        (2 / a) * (Real.sqrt (d : ℝ) / d) := by ring
    _ ≤ (8 / (a * b)) * 1 + (4 / b) * 1 + (2 / a) * 1 := by gcongr
    _ = _ := by ring

/-- The full gcd-weighted lattice bound used by squarefree mode completion. -/
theorem incidenceGcdDecay_bounds (q : ℕ) (hq : 0 < q) (a b τ : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    Summable (incidenceGcdDecay q a b τ) ∧
      (∑' z : ℤ × ℤ, incidenceGcdDecay q a b τ z) ≤
        (q.divisors.card : ℝ) * (8 / (a * b) + 4 / b + 2 / a) := by
  let G (z : ℤ × ℤ) : ℝ :=
    ∑ d ∈ q.divisors, Real.sqrt (d : ℝ) * incidenceDivisibleDecay d a b τ z
  have hsumG : Summable G :=
    summable_sum (fun d _ => (incidenceDivisibleDecay_summable d a b τ ha hb).mul_left _)
  have hnonneg (z : ℤ × ℤ) : 0 ≤ incidenceGcdDecay q a b τ z :=
    mul_nonneg (incidenceShearedNonzeroDecay_nonneg _ _ _ _) (Real.sqrt_nonneg _)
  have hpoint (z : ℤ × ℤ) : incidenceGcdDecay q a b τ z ≤ G z := by
    have h := mul_le_mul_of_nonneg_left
      (incidence_sqrt_gcd_le_divisor_sum q hq z.1 z.2)
      (incidenceShearedNonzeroDecay_nonneg a b τ z)
    calc
      _ ≤ incidenceShearedNonzeroDecay a b τ z *
          ∑ d ∈ q.divisors, if (d : ℤ) ∣ z.1 ∧ (d : ℤ) ∣ z.2 then Real.sqrt (d : ℝ) else 0 := h
      _ = G z := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        unfold incidenceDivisibleDecay
        split_ifs <;> ring
  have hs := Summable.of_nonneg_of_le hnonneg hpoint hsumG
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' z : ℤ × ℤ, G z := hs.tsum_le_tsum hpoint hsumG
    _ = ∑ d ∈ q.divisors, Real.sqrt (d : ℝ) *
        ∑' z : ℤ × ℤ, incidenceDivisibleDecay d a b τ z := by
      rw [Summable.tsum_finsetSum (fun d _ =>
        (incidenceDivisibleDecay_summable d a b τ ha hb).mul_left _)]
      simp only [tsum_mul_left]
    _ ≤ ∑ _d ∈ q.divisors, (8 / (a * b) + 4 / b + 2 / a) := by
      apply Finset.sum_le_sum
      intro d hd
      exact incidenceDivisibleDecay_weighted_bound d (Nat.pos_of_mem_divisors hd) a b τ ha hb
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

#print axioms incidenceDivisibleDecay_tsum
#print axioms incidence_sqrt_gcd_le_divisor_sum
#print axioms incidenceDivisibleDecay_weighted_bound
#print axioms incidenceGcdDecay_bounds

end PrimeGap182Audit
