import TypeIIIZeroSchur

/-!
# The actual shared local frequency and its matrix parameter

The same residue `c` is used for every outer pair `(u,v)`. At a nonzero local frequency,
the kernel parameter depends only on `a,c` and the complementary factor `t`; at zero
frequency the equality condition is exactly the cubic matching relation.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- Reindexing the actual unit sum normalizes any nonzero additive frequency to one. -/
theorem correlation_normalize_frequency (A B c : ZMod p) (hc : c ≠ 0) :
    correlation p A B c = correlation p (A / c) (B / c) 1 := by
  let F (x : ZMod p) := kl3 p ((A / c) * x) * star (kl3 p ((B / c) * x)) *
    ZMod.stdAddChar x
  have hA (x : ZMod p) : (A / c) * (c * x) = A * x := by field_simp
  have hB (x : ZMod p) : (B / c) * (c * x) = B * x := by field_simp
  calc
    _ = ∑ h : (ZMod p)ˣ, F (c * (h : ZMod p)) := by
      simp only [correlation, F, hA, hB]
    _ = ∑ h : (ZMod p)ˣ, F (h : ZMod p) :=
      PrimeGap186.sum_units_mul p F c (isUnit_iff_ne_zero.mpr hc)
    _ = _ := by simp only [correlation, F, one_mul]

/-- The nonzero shared CRT factor is the actual matrix kernel with a parameter independent
of the two outer variables. Here `t` is the complementary factor `w/p` reduced modulo p. -/
theorem shared_correlation_eq_kernel (a c t m n u v : ZMod p)
    (hc : c ≠ 0) (ht : t ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    correlation p (a / (m * u ^ 3 * t ^ 3)) (a / (n * v ^ 3 * t ^ 3))
      (c / (u * v * t)) =
      kernel p (a / c * (t⁻¹) ^ 2) m n u v := by
  rw [correlation_normalize_frequency p _ _ _
    (div_ne_zero hc (mul_ne_zero (mul_ne_zero hu hv) ht)), kernel,
    ite_eq_right (not_or.mpr ⟨hu, hv⟩)]
  congr 1 <;> field_simp

/-- The equivalent local expression after the CRT inverse cubes have been absorbed by
reindexing the shared unit sum. -/
theorem shared_normalized_correlation_eq_kernel (a c t m n u v : ZMod p)
    (hc : c ≠ 0) (ht : t ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    correlation p (a / (m * u ^ 3)) (a / (n * v ^ 3)) (c * t ^ 2 / (u * v)) =
      kernel p (a / c * (t⁻¹) ^ 2) m n u v := by
  rw [correlation_normalize_frequency p _ _ _
    (div_ne_zero (mul_ne_zero hc (pow_ne_zero _ ht)) (mul_ne_zero hu hv)), kernel,
    ite_eq_right (not_or.mpr ⟨hu, hv⟩)]
  congr 1 <;> field_simp

/-- Equality of the two local arguments is the exact cubic matching relation. -/
theorem shared_correlation_arguments_eq_iff (a t m n u v : ZMod p)
    (ha : a ≠ 0) (ht : t ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    a / (m * u ^ 3 * t ^ 3) = a / (n * v ^ 3 * t ^ 3) ↔
      m * u ^ 3 = n * v ^ 3 := by
  have hdm : m * u ^ 3 * t ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hm (pow_ne_zero _ hu)) (pow_ne_zero _ ht)
  have hdn : n * v ^ 3 * t ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hn (pow_ne_zero _ hv)) (pow_ne_zero _ ht)
  rw [div_eq_div_iff hdm hdn]
  constructor
  · intro h
    exact (mul_right_cancel₀ (pow_ne_zero 3 ht) (mul_left_cancel₀ ha h)).symm
  · intro h
    rw [h]

/-- The shared zero-frequency factor, including the full lower-order correction. -/
theorem shared_correlation_zero (a t m n u v : ZMod p)
    (ha : a ≠ 0) (ht : t ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    correlation p (a / (m * u ^ 3 * t ^ 3)) (a / (n * v ^ 3 * t ^ 3)) 0 =
      (if m * u ^ 3 = n * v ^ 3 then (p : ℂ) else 0) -
        (zeroCorrelationCorrection p : ℂ) := by
  rw [correlation_zero p _ _
    (div_ne_zero ha (mul_ne_zero (mul_ne_zero hm (pow_ne_zero _ hu)) (pow_ne_zero _ ht)))
    (div_ne_zero ha (mul_ne_zero (mul_ne_zero hn (pow_ne_zero _ hv)) (pow_ne_zero _ ht)))]
  simp only [shared_correlation_arguments_eq_iff p a t m n u v ha ht hm hn hu hv,
    zeroCorrelationCorrection, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_pow]
  ring

#print axioms correlation_normalize_frequency
#print axioms shared_correlation_eq_kernel
#print axioms shared_normalized_correlation_eq_kernel
#print axioms shared_correlation_arguments_eq_iff
#print axioms shared_correlation_zero

end

end PrimeGap182.TypeIII
