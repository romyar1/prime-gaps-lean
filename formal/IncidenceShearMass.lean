import IncidenceSchwartzSummability

/-!
# Full lattice mass under an arbitrary real shear

This is the unrestricted mass bound, separate from the nonzero-mode bound.
Real centers and the shear enter only the centers of the one-dimensional
sums and do not affect the constants.
-/

noncomputable section

namespace PrimeGap182Audit

open scoped BigOperators

theorem incidenceShearedDecay_nonneg (a b τ α β : ℝ) (z : ℤ × ℤ) :
    0 ≤ incidenceShearedDecay a b τ α β z :=
  mul_nonneg (incidenceDecay_nonneg _ _) (incidenceDecay_nonneg _ _)

set_option maxHeartbeats 600000 in
theorem incidenceShearedDecay_mass_le (a b τ α β : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∑' z : ℤ × ℤ, incidenceShearedDecay a b τ α β z) ≤
      (2 + 4 / a) * (2 + 4 / b) := by
  let F := incidenceShearedDecay a b τ α β
  have hs := incidenceShearedDecay_summable a b τ α β ha hb
  have hrow (ν : ℤ) : (∑' h : ℤ, F (h, ν)) ≤
      (2 + 4 / a) * incidenceDecay b ((ν : ℝ) + β) := by
    have hm := (incidenceDecay_shift_bounds a (α + τ * ((ν : ℝ) + β)) ha).2
    simpa only [F, incidenceShearedDecay, add_assoc, tsum_mul_right] using
      mul_le_mul_of_nonneg_right hm (incidenceDecay_nonneg _ _)
  calc
    _ = ∑' ν : ℤ, ∑' h : ℤ, F (h, ν) :=
      hs.tsum_prod.trans (hs.tsum_comm (f := fun h ν => F (h, ν))).symm
    _ ≤ ∑' ν : ℤ, (2 + 4 / a) * incidenceDecay b ((ν : ℝ) + β) :=
      hs.prod_symm.prod.tsum_le_tsum hrow
        ((incidenceDecay_shift_bounds b β hb).1.mul_left (2 + 4 / a))
    _ = (2 + 4 / a) * ∑' ν : ℤ, incidenceDecay b ((ν : ℝ) + β) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (incidenceDecay_shift_bounds b β hb).2 (by positivity)

#print axioms incidenceShearedDecay_mass_le

end PrimeGap182Audit
