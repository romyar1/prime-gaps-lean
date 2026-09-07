import IncidenceFrequencySectors

/-!
# The actual source frequency block and supported quotient

These are the literal frequency-block definitions from the public186
positive Cauchy reduction. Dividing by w₁ preserves the full m-supported
part because w₁ is prime to m. The final quotient is therefore a unit
modulo every divisor of m, without an assumed factorization.
-/

noncomputable section

namespace PrimeGap182Audit

open Classical
open scoped BigOperators

def incidenceFullSupportedPart (m : ℕ) (y : ℤ) : ℕ :=
  ∏ p ∈ m.primeFactors, p ^ y.natAbs.factorization p

def incidenceSourceFrequencyBlock (J : Finset ℤ) (v₁ v₂ m w₁ w₂ : ℕ) (Y : ℤ) :
    Finset (ℤ × ℤ) :=
  ((J.product J).filter (fun h => h.1 * (v₂ : ℤ) ≠ h.2 * (v₁ : ℤ))).filter
    (fun h => (w₁ : ℤ) ∣ incidenceReducedFrequency v₁ v₂ h ∧
      incidenceFullSupportedPart m (incidenceReducedFrequency v₁ v₂ h) = w₂ ∧
      1 ≤ (incidenceReducedFrequency v₁ v₂ h : ℝ) / (Y : ℝ) ∧
      (incidenceReducedFrequency v₁ v₂ h : ℝ) / (Y : ℝ) < 2)

def incidenceQuotientFrequency (w₁ v₁ v₂ : ℕ) (h : ℤ × ℤ) : ℤ :=
  incidenceReducedFrequency v₁ v₂ h / (w₁ : ℤ)

theorem incidenceReducedFrequency_scale (v₁ v₂ : ℕ) (h : ℤ × ℤ) :
    (Nat.gcd v₁ v₂ : ℤ) * incidenceReducedFrequency v₁ v₂ h =
      h.1 * (v₂ : ℤ) - h.2 * (v₁ : ℤ) := by
  have hg₁ : (Nat.gcd v₁ v₂ : ℤ) * ((v₁ / Nat.gcd v₁ v₂ : ℕ) : ℤ) = (v₁ : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_left v₁ v₂)
  have hg₂ : (Nat.gcd v₁ v₂ : ℤ) * ((v₂ / Nat.gcd v₁ v₂ : ℕ) : ℤ) = (v₂ : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_right v₁ v₂)
  unfold incidenceReducedFrequency
  linear_combination h.1 * hg₂ - h.2 * hg₁

theorem incidenceSourceFrequencyBlock_nonzero (J : Finset ℤ) (v₁ v₂ m w₁ w₂ : ℕ)
    (Y : ℤ) (h : ℤ × ℤ) (hh : h ∈ incidenceSourceFrequencyBlock J v₁ v₂ m w₁ w₂ Y) :
    incidenceReducedFrequency v₁ v₂ h ≠ 0 := by
  intro hz
  have hne := (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).2
  have hs := incidenceReducedFrequency_scale v₁ v₂ h
  rw [hz, mul_zero] at hs
  exact hne (sub_eq_zero.mp hs.symm)

theorem incidenceQuotientFrequency_mul (w₁ v₁ v₂ : ℕ) (h : ℤ × ℤ)
    (hd : (w₁ : ℤ) ∣ incidenceReducedFrequency v₁ v₂ h) :
    (w₁ : ℤ) * incidenceQuotientFrequency w₁ v₁ v₂ h =
      incidenceReducedFrequency v₁ v₂ h := Int.mul_ediv_cancel' hd

theorem incidenceFullSupportedPart_quotient (m w : ℕ) (hm : m ≠ 0) (hw : w ≠ 0)
    (hwm : Nat.Coprime w m) (y : ℤ) (hy : y ≠ 0) (hwy : (w : ℤ) ∣ y) :
    let l := y / (w : ℤ)
    let w₂ := incidenceFullSupportedPart m y
    0 < w₂ ∧ (w₂ : ℤ) ∣ l ∧ IsUnit ((l / (w₂ : ℤ) : ℤ) : ZMod m) ∧
      incidenceFullSupportedPart m l = w₂ := by
  intro l w₂
  have hmul : (w : ℤ) * l = y := Int.mul_ediv_cancel' hwy
  have hl : l ≠ 0 := by
    intro hl
    apply hy
    rw [← hmul, hl, mul_zero]
  have hnat : y.natAbs = w * l.natAbs := by
    rw [← hmul, Int.natAbs_mul, Int.natAbs_natCast]
  have hp := PrimeGap186.primeFactors_prod_pow_factorization_dvd_and_coprime_div
    m l.natAbs hm (Int.natAbs_ne_zero.mpr hl)
  have hpart : w₂ = incidenceFullSupportedPart m l := by
    simpa only [w₂, incidenceFullSupportedPart, hnat] using hp.2.2.2.2 w hw hwm
  rw [hpart]
  have hd : (incidenceFullSupportedPart m l : ℤ) ∣ l := Int.natCast_dvd.mpr hp.2.1
  refine ⟨hp.1, hd, ?_, rfl⟩
  rw [incidenceIntegerUnit_iff, Int.natAbs_ediv_of_dvd hd, Int.natAbs_natCast]
  exact hp.2.2.2.1

theorem incidenceSourceFrequencyBlock_quotient (J : Finset ℤ) (v₁ v₂ m w₁ w₂ : ℕ)
    (hm : m ≠ 0) (hw : w₁ ≠ 0) (hwm : Nat.Coprime w₁ m) (Y : ℤ)
    (h : ℤ × ℤ) (hh : h ∈ incidenceSourceFrequencyBlock J v₁ v₂ m w₁ w₂ Y) :
    let l := incidenceQuotientFrequency w₁ v₁ v₂ h
    l ≠ 0 ∧ 0 < w₂ ∧ (w₂ : ℤ) ∣ l ∧ IsUnit ((l / (w₂ : ℤ) : ℤ) : ZMod m) ∧
      incidenceFullSupportedPart m l = w₂ := by
  intro l
  have hd := (Finset.mem_filter.mp hh).2.1
  have hn := incidenceSourceFrequencyBlock_nonzero J v₁ v₂ m w₁ w₂ Y h hh
  have hp := incidenceFullSupportedPart_quotient m w₁ hm hw hwm
    (incidenceReducedFrequency v₁ v₂ h) hn hd
  rw [(Finset.mem_filter.mp hh).2.2.1] at hp
  refine ⟨?_, hp⟩
  intro hl
  have hs := incidenceQuotientFrequency_mul w₁ v₁ v₂ h hd
  change (w₁ : ℤ) * l = _ at hs
  rw [hl, mul_zero] at hs
  exact hn hs.symm

theorem incidenceSourceFrequencyBlock_dyadic (J : Finset ℤ) (v₁ v₂ m w₁ w₂ : ℕ)
    (hw : 0 < w₁) (Y : ℤ) (h : ℤ × ℤ)
    (hh : h ∈ incidenceSourceFrequencyBlock J v₁ v₂ m w₁ w₂ Y) :
    0 < |(Y : ℝ)| / (w₁ : ℝ) ∧
      |(Y : ℝ)| / (w₁ : ℝ) ≤ |(incidenceQuotientFrequency w₁ v₁ v₂ h : ℝ)| ∧
      |(incidenceQuotientFrequency w₁ v₁ v₂ h : ℝ)| ≤ 2 * (|(Y : ℝ)| / (w₁ : ℝ)) := by
  have hband := (Finset.mem_filter.mp hh).2.2.2
  have hY : (Y : ℝ) ≠ 0 := by
    intro hz
    simp only [hz, div_zero] at hband
    linarith [hband.1]
  have hr : |(incidenceReducedFrequency v₁ v₂ h : ℝ)| / |(Y : ℝ)| =
      (incidenceReducedFrequency v₁ v₂ h : ℝ) / (Y : ℝ) := by
    rw [← abs_div, abs_of_nonneg (zero_le_one.trans hband.1)]
  have hYpos : 0 < |(Y : ℝ)| := abs_pos.mpr hY
  have hwR : 0 < (w₁ : ℝ) := by exact_mod_cast hw
  have hlo : |(Y : ℝ)| ≤ |(incidenceReducedFrequency v₁ v₂ h : ℝ)| := by
    nlinarith only [(le_div_iff₀ hYpos).mp (hr.symm ▸ hband.1)]
  have hhi : |(incidenceReducedFrequency v₁ v₂ h : ℝ)| ≤ 2 * |(Y : ℝ)| :=
    ((div_lt_iff₀ hYpos).mp (hr.symm ▸ hband.2)).le
  have hscale : |(incidenceReducedFrequency v₁ v₂ h : ℝ)| =
      (w₁ : ℝ) * |(incidenceQuotientFrequency w₁ v₁ v₂ h : ℝ)| := by
    have hs := congrArg (fun n : ℤ => |(n : ℝ)|)
      (incidenceQuotientFrequency_mul w₁ v₁ v₂ h (Finset.mem_filter.mp hh).2.1)
    simpa only [Int.cast_mul, Int.cast_natCast, abs_mul, abs_of_pos hwR] using hs.symm
  rw [hscale] at hlo hhi
  refine ⟨div_pos hYpos hwR, (div_le_iff₀ hwR).mpr (by nlinarith only [hlo]), ?_⟩
  rw [← mul_div_assoc]
  exact (le_div_iff₀ hwR).mpr (by nlinarith only [hhi])

end PrimeGap182Audit

#print axioms PrimeGap182Audit.incidenceReducedFrequency_scale
#print axioms PrimeGap182Audit.incidenceSourceFrequencyBlock_nonzero
#print axioms PrimeGap182Audit.incidenceQuotientFrequency_mul
#print axioms PrimeGap182Audit.incidenceFullSupportedPart_quotient
#print axioms PrimeGap182Audit.incidenceSourceFrequencyBlock_quotient
#print axioms PrimeGap182Audit.incidenceSourceFrequencyBlock_dyadic
