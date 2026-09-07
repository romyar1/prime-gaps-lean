import IncidenceCirculant

/-!
# The reciprocal rank-three circulant from an explicit rank-four scalar bound

`incidenceKloosterman4Raw` is the actual three-unit parametrization of the
unnormalized rank-four Kloosterman sum. The fourth variable is `c/(u*v*w)`.
`IncidenceRankFourBound` is an explicit local finite-sum hypothesis, not an
axiom. Every Fourier identity and the resulting Euclidean matrix norm bound
is proved from that scalar premise and the existing exact rank-three formula.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {p : ℕ} [Fact p.Prime]

/-- The unnormalized rank-four sum in its three-unit parametrization. -/
def incidenceKloosterman4Raw (c : ZMod p) : ℂ :=
  ∑ u : (ZMod p)ˣ, ∑ v : (ZMod p)ˣ, ∑ w : (ZMod p)ˣ,
    ZMod.stdAddChar ((u : ZMod p) + (v : ZMod p) + (w : ZMod p) +
      c / ((u : ZMod p) * (v : ZMod p) * (w : ZMod p)))

/-- The exact external scalar input: Deligne's rank-four bound at nonzero arguments. -/
def IncidenceRankFourBound (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ c : ZMod p, c ≠ 0 →
    ‖incidenceKloosterman4Raw c‖ ≤ 4 * (p : ℝ) * Real.sqrt (p : ℝ)

/-- The actual kernel of manuscript `L_a`, with the diagonal removed. -/
def incidenceReciprocalKl3Kernel (a d : ZMod p) : ℂ :=
  if d = 0 then 0 else PrimeGap186.normalizedKloosterman3 p (a / d)

/-- At the arguments used by Deligne, the unit parametrization equals the
actual four-variable product-constraint sum. -/
theorem incidenceKloosterman4Raw_eq_hypersurface (c : ZMod p) (hc : c ≠ 0) :
    incidenceKloosterman4Raw c =
      ∑ u : ZMod p, ∑ v : ZMod p, ∑ w : ZMod p, ∑ t : ZMod p,
        if u * v * w * t = c then ZMod.stdAddChar (u + v + w + t) else 0 := by
  have hinner (u v w : ZMod p) :
      (∑ t : ZMod p,
        if u * v * w * t = c then ZMod.stdAddChar (u + v + w + t) else 0) =
        if u * v * w = 0 then 0 else
          ZMod.stdAddChar (u + v + w + c / (u * v * w)) := by
    by_cases hprod : u * v * w = 0
    · simp [hprod, Ne.symm hc]
    · have hcond (t : ZMod p) : u * v * w * t = c ↔ t = c / (u * v * w) := by
        constructor
        · intro ht
          exact (eq_div_iff hprod).mpr (by simpa [mul_comm] using ht)
        · intro ht
          simpa [mul_comm] using (eq_div_iff hprod).mp ht
      simp [hcond, hprod]
  simp_rw [hinner]
  unfold incidenceKloosterman4Raw
  rw [PrimeGap186.sum_units_eq_sum_ite p (fun u : ZMod p =>
    ∑ v : (ZMod p)ˣ, ∑ w : (ZMod p)ˣ,
      ZMod.stdAddChar (u + (v : ZMod p) + (w : ZMod p) +
        c / (u * (v : ZMod p) * (w : ZMod p))))]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u = 0
  · simp [hu]
  rw [ite_eq_left hu, PrimeGap186.sum_units_eq_sum_ite p (fun v : ZMod p =>
    ∑ w : (ZMod p)ˣ, ZMod.stdAddChar (u + v + (w : ZMod p) +
      c / (u * v * (w : ZMod p))))]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v = 0
  · simp [hv]
  rw [ite_eq_left hv, PrimeGap186.sum_units_eq_sum_ite p (fun w : ZMod p =>
    ZMod.stdAddChar (u + v + w + c / (u * v * w)))]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : w = 0 <;> simp [hu, hv, hw]

theorem incidenceKloosterman4Raw_zero : incidenceKloosterman4Raw (0 : ZMod p) = -1 := by
  have hs : (∑ u : (ZMod p)ˣ, ZMod.stdAddChar (u : ZMod p)) = -1 := by
    simpa using PrimeGap186.stdAddChar_sum_units p 1
  simp only [incidenceKloosterman4Raw, zero_div, add_zero, AddChar.map_add_eq_mul]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, hs]
  norm_num

theorem incidenceReciprocalKl3_dft_units (a s : ZMod p) :
    ZMod.dft (incidenceReciprocalKl3Kernel a) s =
      ∑ d : (ZMod p)ˣ, PrimeGap186.normalizedKloosterman3 p (a / (d : ZMod p)) *
        ZMod.stdAddChar (-s * (d : ZMod p)) := by
  rw [PrimeGap186.sum_units_eq_sum_ite p (fun d : ZMod p =>
    PrimeGap186.normalizedKloosterman3 p (a / d) * ZMod.stdAddChar (-s * d)),
    ZMod.dft_apply]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d = 0
  · simp [incidenceReciprocalKl3Kernel, hd]
  · simp [incidenceReciprocalKl3Kernel, hd, smul_eq_mul, mul_comm]

private theorem incidenceReciprocalKl3_unit_term (a s : ZMod p) (d : (ZMod p)ˣ) :
    PrimeGap186.normalizedKloosterman3 p (a / (d : ZMod p)) *
        ZMod.stdAddChar (-s * (d : ZMod p)) =
      (p : ℂ)⁻¹ * ∑ u : (ZMod p)ˣ, ∑ v : (ZMod p)ˣ,
        ZMod.stdAddChar ((u : ZMod p) + (v : ZMod p) +
          a / ((d : ZMod p) * (u : ZMod p) * (v : ZMod p)) - s * (d : ZMod p)) := by
  rw [PrimeGap186.normalizedKloosterman3_eq_doubleUnitSum,
    PrimeGap186.reciprocalProductCompleteSum, mul_assoc]
  congr 1
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [one_mul, div_div]
  ring

/-- The reciprocal argument adds a fourth variable. This is not the baseline's
linear-argument rank-three Fourier identity. -/
theorem incidenceReciprocalKl3_dft_nonzero (a s : ZMod p) (hs : s ≠ 0) :
    ZMod.dft (incidenceReciprocalKl3Kernel a) s =
      (p : ℂ)⁻¹ * incidenceKloosterman4Raw (-a * s) := by
  rw [incidenceReciprocalKl3_dft_units]
  simp_rw [incidenceReciprocalKl3_unit_term, ← Finset.mul_sum]
  congr 1
  unfold incidenceKloosterman4Raw
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  let k : (ZMod p)ˣ := Units.mk0 (-s) (neg_ne_zero.mpr hs)
  refine Fintype.sum_equiv (Equiv.mulLeft k) _ _ ?_
  intro d
  simp only [Equiv.coe_mulLeft, Units.val_mul, k, Units.val_mk0]
  congr 1
  field_simp
  ring

theorem incidenceReciprocalKl3_dft_zero (a : ZMod p) (ha : a ≠ 0) :
    ZMod.dft (incidenceReciprocalKl3Kernel a) 0 = -(p : ℂ)⁻¹ := by
  rw [incidenceReciprocalKl3_dft_units]
  simp_rw [incidenceReciprocalKl3_unit_term, ← Finset.mul_sum]
  simp only [zero_mul, sub_zero]
  have hinner (u v : (ZMod p)ˣ) :
      (∑ d : (ZMod p)ˣ, ZMod.stdAddChar ((u : ZMod p) + (v : ZMod p) +
        a / ((d : ZMod p) * (u : ZMod p) * (v : ZMod p)))) =
        -ZMod.stdAddChar ((u : ZMod p) + (v : ZMod p)) := by
    have hid (d : (ZMod p)ˣ) :
        a / ((d : ZMod p) * (u : ZMod p) * (v : ZMod p)) =
          (a / ((u : ZMod p) * (v : ZMod p))) / (d : ZMod p) := by
      simp only [div_div, mul_comm, mul_left_comm]
    simp_rw [hid, AddChar.map_add_eq_mul, ← Finset.mul_sum]
    rw [PrimeGap186.stdAddChar_sum_units_div]
    have hc : a / ((u : ZMod p) * (v : ZMod p)) ≠ 0 :=
      div_ne_zero ha (mul_ne_zero u.ne_zero v.ne_zero)
    simp [hc]
  have hsum : (∑ d : (ZMod p)ˣ, ∑ u : (ZMod p)ˣ, ∑ v : (ZMod p)ˣ,
      ZMod.stdAddChar ((u : ZMod p) + (v : ZMod p) +
        a / ((d : ZMod p) * (u : ZMod p) * (v : ZMod p)))) = -1 := by
    have hswap : (∑ d : (ZMod p)ˣ, ∑ u : (ZMod p)ˣ, ∑ v : (ZMod p)ˣ,
        ZMod.stdAddChar ((u : ZMod p) + (v : ZMod p) +
          a / ((d : ZMod p) * (u : ZMod p) * (v : ZMod p)))) =
        ∑ u : (ZMod p)ˣ, ∑ v : (ZMod p)ˣ, ∑ d : (ZMod p)ˣ,
          ZMod.stdAddChar ((u : ZMod p) + (v : ZMod p) +
            a / ((d : ZMod p) * (u : ZMod p) * (v : ZMod p))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
    rw [hswap]
    simp_rw [hinner, Finset.sum_neg_distrib, AddChar.map_add_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_mul]
    have hs : (∑ u : (ZMod p)ˣ, ZMod.stdAddChar (u : ZMod p)) = -1 := by
      simpa using PrimeGap186.stdAddChar_sum_units p 1
    rw [hs]
    norm_num
  rw [hsum]
  ring

/-- The actual reciprocal rank-three circulant has the required operator norm
assuming only the stated scalar rank-four finite-sum bound. -/
theorem incidenceReciprocalKl3Circulant_norm_le (a : ZMod p) (ha : a ≠ 0)
    (hK4 : IncidenceRankFourBound p) :
    ‖Matrix.circulant (incidenceReciprocalKl3Kernel a)‖ ≤ 4 * Real.sqrt (p : ℝ) := by
  apply incidenceCirculant_norm_le _ _ (by positivity)
  intro s
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  by_cases hs : s = 0
  · subst s
    rw [incidenceReciprocalKl3_dft_zero a ha, norm_neg, norm_inv, Complex.norm_natCast]
    have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
    have hi : (p : ℝ)⁻¹ ≤ 1 := by simpa only [one_div] using (div_le_one hp).mpr hp1
    have hsq : 1 ≤ Real.sqrt (p : ℝ) := Real.one_le_sqrt.mpr hp1
    linarith
  · rw [incidenceReciprocalKl3_dft_nonzero a s hs, norm_mul, norm_inv, Complex.norm_natCast]
    calc
      _ ≤ (p : ℝ)⁻¹ * (4 * (p : ℝ) * Real.sqrt (p : ℝ)) :=
        mul_le_mul_of_nonneg_left (hK4 _ (mul_ne_zero (neg_ne_zero.mpr ha) hs))
          (inv_nonneg.mpr hp.le)
      _ = 4 * Real.sqrt (p : ℝ) := by field_simp

#print axioms incidenceKloosterman4Raw_eq_hypersurface
#print axioms incidenceKloosterman4Raw_zero
#print axioms incidenceReciprocalKl3_dft_nonzero
#print axioms incidenceReciprocalKl3_dft_zero
#print axioms incidenceReciprocalKl3Circulant_norm_le

end PrimeGap182Audit
