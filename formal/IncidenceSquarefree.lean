import IncidenceZeroBound

/-!
# All squarefree incidence modes from the local rank-four scalar input

A single unit multiplier on both integer frequencies is retained through the
CRT induction. This makes vanishing at each prime exactly divisibility of
the original two integers, rather than a new arithmetic assumption.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- The finite-field input at each prime, with no asymptotic assertion. -/
def AllIncidenceRankFourBounds : Prop :=
  ∀ p : ℕ, ∀ [Fact p.Prime], IncidenceRankFourBound p

def incidenceFrequencyFactor (p : ℕ) (h ν : ℤ) : ℝ :=
  if (p : ℤ) ∣ h ∧ (p : ℤ) ∣ ν then (p : ℝ) else 1

def incidencePrimeFactorBound (p : ℕ) (h ν : ℤ) : ℝ :=
  8 * (p : ℝ) * Real.sqrt (p : ℝ) * Real.sqrt (incidenceFrequencyFactor p h ν)

theorem incidenceFrequencyFactor_nonneg (p : ℕ) (h ν : ℤ) :
    0 ≤ incidenceFrequencyFactor p h ν := by
  unfold incidenceFrequencyFactor
  split_ifs <;> positivity

theorem incidencePrimeFactorBound_nonneg (p : ℕ) (h ν : ℤ) :
    0 ≤ incidencePrimeFactorBound p h ν := by
  unfold incidencePrimeFactorBound
  positivity

theorem incidenceModeMod_prime_scaled_norm_le {p : ℕ} [Fact p.Prime]
    (hK4 : IncidenceRankFourBound p) (A t : ZMod p) (hA : IsUnit A) (ht : IsUnit t)
    (h ν : ℤ) :
    ‖incidenceModeMod A (t * (h : ZMod p), t * (ν : ZMod p))‖ ≤
      incidencePrimeFactorBound p h ν := by
  rw [incidenceModeMod_eq_prime]
  by_cases hd : (p : ℤ) ∣ h ∧ (p : ℤ) ∣ ν
  · have hh : (h : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd h p).mpr hd.1
    have hν : (ν : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd ν p).mpr hd.2
    simp only [hh, hν, mul_zero]
    calc
      _ ≤ (p : ℝ) ^ 2 := primeIncidenceMode_zero_norm_le A hA.ne_zero
      _ ≤ 8 * (p : ℝ) ^ 2 := by nlinarith [sq_nonneg (p : ℝ)]
      _ = incidencePrimeFactorBound p h ν := by
        simp only [incidencePrimeFactorBound, incidenceFrequencyFactor, ite_eq_left hd]
        rw [mul_assoc (8 * (p : ℝ)), Real.mul_self_sqrt (Nat.cast_nonneg p)]
        ring
  · have hξ : (t * (h : ZMod p), t * (ν : ZMod p)) ≠ 0 := by
      intro heq
      have hh : (h : ZMod p) = 0 :=
        (mul_eq_zero.mp (congrArg Prod.fst heq)).resolve_left ht.ne_zero
      have hν : (ν : ZMod p) = 0 :=
        (mul_eq_zero.mp (congrArg Prod.snd heq)).resolve_left ht.ne_zero
      exact hd ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd h p).mp hh,
        (ZMod.intCast_zmod_eq_zero_iff_dvd ν p).mp hν⟩
    simpa only [incidencePrimeFactorBound, incidenceFrequencyFactor,
      ite_eq_right hd, Real.sqrt_one, mul_one] using
      primeIncidenceMode_norm_le A hA.ne_zero hK4 _ hξ

/-- The exact product of prime bounds, proved on the actual composite modes. -/
theorem incidenceModeMod_squarefree_product_bound (hK4 : AllIncidenceRankFourBounds)
    {q : ℕ} [NeZero q] (hq : Squarefree q) (A t : ZMod q)
    (hA : IsUnit A) (ht : IsUnit t) (h ν : ℤ) :
    ‖incidenceModeMod A (t * (h : ZMod q), t * (ν : ZMod q))‖ ≤
      ∏ p ∈ q.primeFactors, incidencePrimeFactorBound p h ν := by
  have hmain : ∀ q : ℕ, ∀ [NeZero q], Squarefree q →
      ∀ A t : ZMod q, IsUnit A → IsUnit t → ∀ h ν : ℤ,
      ‖incidenceModeMod A (t * (h : ZMod q), t * (ν : ZMod q))‖ ≤
        ∏ p ∈ q.primeFactors, incidencePrimeFactorBound p h ν := by
    refine induction_on_primes ?_ ?_ ?_
    · intro _
      exact False.elim (NeZero.ne 0 rfl)
    · intro _ _ A _ _ _ _ _
      rw [incidenceModeMod_one]
      simp
    · intro p n hp ih _ hpn A t hA ht h ν
      have hn : Squarefree n := hpn.of_mul_right
      let : NeZero n := ⟨hn.ne_zero⟩
      let : Fact p.Prime := ⟨hp⟩
      have hcop : p.Coprime n := Nat.coprime_of_squarefree_mul hpn
      have hAL := incidenceCRTScaledLeft_isUnit hcop A hA
      have hAR := incidenceCRTScaledRight_isUnit hcop A hA
      have htL := incidenceCRTScaledLeft_isUnit hcop t ht
      have htR := incidenceCRTScaledRight_isUnit hcop t ht
      have hcrt := incidenceModeMod_crt_norm_le hcop A (t * (h : ZMod (p * n)), t * (ν : ZMod (p * n)))
      simp only [incidenceCRTScaledLeft_mul_intCast, incidenceCRTScaledRight_mul_intCast] at hcrt
      have hleft := incidenceModeMod_prime_scaled_norm_le (hK4 p)
        (incidenceCRTScaledLeft hcop A) (incidenceCRTScaledLeft hcop t) hAL htL h ν
      have hright := ih hn (incidenceCRTScaledRight hcop A)
        (incidenceCRTScaledRight hcop t) hAR htR h ν
      rw [hcop.primeFactors_mul, Finset.prod_union hcop.disjoint_primeFactors,
        hp.primeFactors, Finset.prod_singleton]
      exact hcrt.trans (mul_le_mul hleft hright (norm_nonneg _)
        (incidencePrimeFactorBound_nonneg p h ν))
  exact hmain q hq A t hA ht h ν

theorem incidenceFrequencyFactor_prod {q : ℕ} (hq : Squarefree q) (h ν : ℤ) :
    (∏ p ∈ q.primeFactors, incidenceFrequencyFactor p h ν) =
      (Nat.gcd q (Int.gcd h ν) : ℝ) := by
  let d := Nat.gcd q (Int.gcd h ν)
  have hd : d ∣ q := Nat.gcd_dvd_left q (Int.gcd h ν)
  have hdsq : Squarefree d := hq.squarefree_of_dvd hd
  have hfilter : q.primeFactors.filter (fun p : ℕ => (p : ℤ) ∣ h ∧ (p : ℤ) ∣ ν) =
      d.primeFactors := by
    rw [← Nat.primeFactors_filter_dvd_of_dvd hq.ne_zero hd]
    apply Finset.filter_congr
    intro p hp
    simp only [d, Int.gcd_def, Int.natCast_dvd, Nat.dvd_gcd_iff,
      Nat.dvd_of_mem_primeFactors hp, true_and]
  simp only [incidenceFrequencyFactor]
  rw [← Finset.prod_filter, hfilter, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hdsq]

theorem incidencePrimeFactorBound_prod {q : ℕ} (hq : Squarefree q) (h ν : ℤ) :
    (∏ p ∈ q.primeFactors, incidencePrimeFactorBound p h ν) =
      (8 : ℝ) ^ q.primeFactors.card * (q : ℝ) * Real.sqrt (q : ℝ) *
        Real.sqrt (Nat.gcd q (Int.gcd h ν) : ℝ) := by
  have hprod : (∏ p ∈ q.primeFactors, (p : ℝ)) = (q : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hq]
  simp only [incidencePrimeFactorBound, Finset.prod_mul_distrib, Finset.prod_const]
  rw [← Real.sqrt_prod _ (fun p _ => Nat.cast_nonneg p),
    ← Real.sqrt_prod _ (fun p _ => incidenceFrequencyFactor_nonneg p h ν),
    hprod, incidenceFrequencyFactor_prod hq]

/-- Explicit squarefree bound before replacing the prime-count factor by q^η. -/
theorem incidenceModeMod_squarefree_norm_le (hK4 : AllIncidenceRankFourBounds)
    {q : ℕ} [NeZero q] (hq : Squarefree q) (A : ZMod q) (hA : IsUnit A)
    (h ν : ℤ) :
    ‖incidenceModeMod A ((h : ZMod q), (ν : ZMod q))‖ ≤
      (8 : ℝ) ^ q.primeFactors.card * (q : ℝ) * Real.sqrt (q : ℝ) *
        Real.sqrt (Nat.gcd q (Int.gcd h ν) : ℝ) := by
  have hb := incidenceModeMod_squarefree_product_bound hK4 hq A 1 hA isUnit_one h ν
  simpa only [one_mul, incidencePrimeFactorBound_prod hq] using hb

#print axioms incidenceModeMod_prime_scaled_norm_le
#print axioms incidenceModeMod_squarefree_product_bound
#print axioms incidenceFrequencyFactor_prod
#print axioms incidencePrimeFactorBound_prod
#print axioms incidenceModeMod_squarefree_norm_le

end PrimeGap182Audit
