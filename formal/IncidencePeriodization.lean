import IncidencePeriodicPoisson
import IncidenceSquarefreeCompletion

/-!
# Actual periodization of integer-lattice weights

The complete residue weight is a convergent sum over every integer lift.
Its mass is exactly the unrestricted lattice mass. The incidence kernel's
unit mask stays in the matrix, not in this weight.
-/

noncomputable section

namespace PrimeGap182Audit

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {q : ℕ} [NeZero q]

def incidencePeriodize {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (w : ℤ × ℤ → M) (r : ZMod q × ZMod q) : M :=
  ∑' z : (incidenceIntegerResidue q ⁻¹' {r}), w z.val

theorem incidencePeriodize_complex_sum (w : ℤ × ℤ → ℂ)
    (hw : Summable (fun z => ‖w z‖)) (f : ZMod q × ZMod q → ℂ) :
    (∑ r, incidencePeriodize w r * f r) =
      ∑' z : ℤ × ℤ, w z * f (incidenceIntegerResidue q z) := by
  have hs := (incidencePeriodicMul_norm_summable w hw f).of_norm
  have h := (hs.hasSum.tsum_fiberwise (incidenceIntegerResidue q)).tsum_eq
  calc
    _ = ∑ r : ZMod q × ZMod q,
        ∑' z : (incidenceIntegerResidue q ⁻¹' {r}),
          w z.val * f (incidenceIntegerResidue q z.val) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [incidencePeriodize, ← tsum_mul_right]
      apply tsum_congr
      intro z
      have hz := z.property
      change incidenceIntegerResidue q z.val = r at hz
      rw [hz]
    _ = _ := by simpa only [tsum_fintype] using h

omit [NeZero q] in
theorem incidencePeriodize_ofReal (w : ℤ × ℤ → ℝ) (r : ZMod q × ZMod q) :
    incidencePeriodize (fun z => (w z : ℂ)) r = (incidencePeriodize w r : ℝ) := by
  simp only [incidencePeriodize, Complex.ofReal_tsum]

theorem incidencePeriodize_real_sum (w : ℤ × ℤ → ℝ) (hw : Summable w)
    (f : ZMod q × ZMod q → ℝ) :
    (∑ r, incidencePeriodize w r * f r) =
      ∑' z : ℤ × ℤ, w z * f (incidenceIntegerResidue q z) := by
  have hwc : Summable (fun z => ‖(w z : ℂ)‖) := by
    simpa only [Complex.norm_real] using hw.norm
  have h := incidencePeriodize_complex_sum (fun z => (w z : ℂ)) hwc
    (fun r => (f r : ℂ))
  apply Complex.ofReal_injective
  simpa only [incidencePeriodize_ofReal, Complex.ofReal_sum, Complex.ofReal_tsum,
    Complex.ofReal_mul] using h

/-- Exact unrestricted mass, with no unit-row restriction. -/
theorem incidencePeriodize_mass (w : ℤ × ℤ → ℝ) (hw : Summable w) :
    (∑ r : ZMod q × ZMod q, incidencePeriodize w r) = ∑' z, w z := by
  simpa only [mul_one] using incidencePeriodize_real_sum w hw (fun _ => 1)

omit [NeZero q] in
theorem incidencePeriodize_nonneg (w : ℤ × ℤ → ℝ) (hw : ∀ z, 0 ≤ w z)
    (r : ZMod q × ZMod q) : 0 ≤ incidencePeriodize w r :=
  tsum_nonneg (fun z => hw z.val)

/-- The joint DFT of the periodization is the actual modulated lattice sum. -/
theorem incidencePeriodize_dft (w : ℤ × ℤ → ℂ)
    (hw : Summable (fun z => ‖w z‖)) (ξ : ZMod q × ZMod q) :
    incidenceJointDFT (incidencePeriodize w) ξ =
      ∑' z : ℤ × ℤ, w z * incidenceJointChar ξ (-incidenceIntegerResidue q z) := by
  exact incidencePeriodize_complex_sum w hw (fun r => incidenceJointChar ξ (-r))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem incidencePeriodize_energy (R : Matrix (ZMod q × ZMod q) ι ℂ)
    (w : ℤ × ℤ → ℝ) (hw : Summable w) (c : ι → ℂ) :
    incidenceRowEnergy R (incidencePeriodize w) c =
      ∑' z : ℤ × ℤ, w z * ‖(R *ᵥ c) (incidenceIntegerResidue q z)‖ ^ 2 :=
  incidencePeriodize_real_sum w hw (fun r => ‖(R *ᵥ c) r‖ ^ 2)

/-- The squarefree incidence estimate for every actual nonnegative summable
integer-lattice weight, with its full lattice mass retained at coefficient one. -/
theorem incidenceLatticeEnergy_squarefree_le (hK4 : AllIncidenceRankFourBounds)
    (hq : Squarefree q) (A : ZMod q) (hA : IsUnit A)
    (w : ℤ × ℤ → ℝ) (hw : Summable w) (hw0 : ∀ z, 0 ≤ w z)
    (c : ZMod q → ℂ) :
    (∑' z : ℤ × ℤ, w z *
      ‖(incidenceMatrixMod A *ᵥ c) (incidenceIntegerResidue q z)‖ ^ 2) ≤
      ((∑' z, w z) + ((q : ℝ) ^ 2)⁻¹ *
        ∑ ξ ∈ Finset.univ.erase 0,
          ‖∑' z : ℤ × ℤ, (w z : ℂ) *
            incidenceJointChar ξ (-incidenceIntegerResidue q z)‖ *
            ((8 : ℝ) ^ q.primeFactors.card * (q : ℝ) * Real.sqrt (q : ℝ) *
              Real.sqrt (incidenceFrequencyGCD ξ : ℝ))) * incidenceVectorEnergy c := by
  have h := incidenceRowEnergy_squarefree_le hK4 hq A hA (incidencePeriodize w)
    (incidencePeriodize_nonneg w hw0) c
  rw [incidencePeriodize_energy _ w hw c, incidencePeriodize_mass w hw] at h
  have hwc : Summable (fun z => ‖(w z : ℂ)‖) := by
    simpa only [Complex.norm_real] using hw.norm
  have hd (ξ : ZMod q × ZMod q) :
      incidenceJointDFT (fun r => ((incidencePeriodize w r : ℝ) : ℂ)) ξ =
        ∑' z : ℤ × ℤ, (w z : ℂ) * incidenceJointChar ξ (-incidenceIntegerResidue q z) := by
    have heq : incidencePeriodize (fun z => (w z : ℂ)) =
        (fun r : ZMod q × ZMod q => ((incidencePeriodize w r : ℝ) : ℂ)) := by
      funext r
      exact incidencePeriodize_ofReal w r
    rw [← heq]
    exact incidencePeriodize_dft (fun z => (w z : ℂ)) hwc ξ
  simpa only [hd] using h

#print axioms incidencePeriodize_complex_sum
#print axioms incidencePeriodize_real_sum
#print axioms incidencePeriodize_mass
#print axioms incidencePeriodize_dft
#print axioms incidencePeriodize_energy
#print axioms incidenceLatticeEnergy_squarefree_le

end PrimeGap182Audit
