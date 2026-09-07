import TypeIIIBoundary
import TypeIIIGeometricAssembly

/-!
# From finite Frobenius spectra to the Type III trace envelopes

This file proves the elementary numerical consequences of the trace and weight
formalism. A `FrobeniusBlock` records eigenvalues with algebraic multiplicity.
It is data, not an assertion that a particular arithmetic sum has an etale
realization. A `SurfaceStalk` records the three possible ordinary cohomology
degrees -2, -1, and 0 of a perverse complex on a smooth surface. Its trace uses
the alternating signs, before any estimate is made.

The external geometric obligations are supplied separately: the actual trace
identity, the eigenvalue bounds, dimension bounds, and support restrictions.
No norm bound for a Fourier sum is postulated by this module.
-/

noncomputable section
open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

/-- Eigenvalues of a finite-dimensional Frobenius operator, counted with
algebraic multiplicity. Diagonalizability is not required. -/
structure FrobeniusBlock where
  dimension : ℕ
  eigenvalue : Fin dimension → ℂ

namespace FrobeniusBlock

def trace (V : FrobeniusBlock) : ℂ := ∑ i, V.eigenvalue i

theorem norm_trace_le (V : FrobeniusBlock) (L : ℝ)
    (hV : ∀ i, ‖V.eigenvalue i‖ ≤ L) : ‖V.trace‖ ≤ V.dimension * L := by
  calc
    _ ≤ ∑ _i : Fin V.dimension, L := norm_sum_le_of_le _ fun i _ => hV i
    _ = _ := by simp

theorem trace_eq_zero_of_dimension_eq_zero (V : FrobeniusBlock)
    (hV : V.dimension = 0) : V.trace = 0 := by
  rcases V with ⟨d, e⟩
  change d = 0 at hV
  subst d
  simp [trace]

theorem norm_trace_le_of_dimension_le (V : FrobeniusBlock) (B : ℕ) (L : ℝ)
    (hB : V.dimension ≤ B) (hL : 0 ≤ L)
    (hV : ∀ i, ‖V.eigenvalue i‖ ≤ L) : ‖V.trace‖ ≤ B * L :=
  (V.norm_trace_le L hV).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hB) hL)

end FrobeniusBlock

/-- Ordinary stalk cohomology in degrees -2, -1, and 0. An application must
first establish that all other degrees vanish. -/
structure SurfaceStalk where
  minusTwo : FrobeniusBlock
  minusOne : FrobeniusBlock
  zero : FrobeniusBlock

namespace SurfaceStalk

def trace (V : SurfaceStalk) : ℂ :=
  V.minusTwo.trace - V.minusOne.trace + V.zero.trace

def dimensionsLe (V : SurfaceStalk) (B : ℕ) : Prop :=
  V.minusTwo.dimension ≤ B ∧ V.minusOne.dimension ≤ B ∧ V.zero.dimension ≤ B

/-- The eigenvalue part of the weight convention. The arguments are the
actual bounds at each ordinary cohomology degree. -/
def eigenvaluesLe (V : SurfaceStalk) (L₂ L₁ L₀ : ℝ) : Prop :=
  (∀ i, ‖V.minusTwo.eigenvalue i‖ ≤ L₂) ∧
  (∀ i, ‖V.minusOne.eigenvalue i‖ ≤ L₁) ∧
  (∀ i, ‖V.zero.eigenvalue i‖ ≤ L₀)

theorem norm_trace_le (V : SurfaceStalk) (B : ℕ) (L₂ L₁ L₀ : ℝ)
    (hB : V.dimensionsLe B) (h₂ : 0 ≤ L₂) (h₁ : 0 ≤ L₁) (h₀ : 0 ≤ L₀)
    (hV : V.eigenvaluesLe L₂ L₁ L₀) :
    ‖V.trace‖ ≤ B * L₂ + B * L₁ + B * L₀ := by
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (norm_sub_le _ _).trans (add_le_add
      (V.minusTwo.norm_trace_le_of_dimension_le B L₂ hB.1 h₂ hV.1)
      (V.minusOne.norm_trace_le_of_dimension_le B L₁ hB.2.1 h₁ hV.2.1))
  · exact V.zero.norm_trace_le_of_dimension_le B L₀ hB.2.2 h₀ hV.2.2

/-- Support restrictions remove the corresponding ordinary-cohomology
traces exactly, before the triangle inequality. -/
theorem norm_trace_le_with_support (V : SurfaceStalk) (B : ℕ)
    (L₂ L₁ L₀ : ℝ) (badCurve badPoint : Prop) [Decidable badCurve]
    [Decidable badPoint] (hB : V.dimensionsLe B)
    (h₂ : 0 ≤ L₂) (h₁ : 0 ≤ L₁) (h₀ : 0 ≤ L₀)
    (hV : V.eigenvaluesLe L₂ L₁ L₀)
    (hcurve : ¬badCurve → V.minusOne.dimension = 0)
    (hpoint : ¬badPoint → V.zero.dimension = 0) :
    ‖V.trace‖ ≤ B * L₂ + (if badCurve then B * L₁ else 0) +
      (if badPoint then B * L₀ else 0) := by
  have hminus : ‖V.minusOne.trace‖ ≤ if badCurve then B * L₁ else 0 := by
    by_cases hc : badCurve
    · simpa only [ite_eq_left hc] using
        V.minusOne.norm_trace_le_of_dimension_le B L₁ hB.2.1 h₁ hV.2.1
    · rw [ite_eq_right hc, V.minusOne.trace_eq_zero_of_dimension_eq_zero (hcurve hc)]
      simp
  have hzero : ‖V.zero.trace‖ ≤ if badPoint then B * L₀ else 0 := by
    by_cases hp : badPoint
    · simpa only [ite_eq_left hp] using
        V.zero.norm_trace_le_of_dimension_le B L₀ hB.2.2 h₀ hV.2.2
    · rw [ite_eq_right hp, V.zero.trace_eq_zero_of_dimension_eq_zero (hpoint hp)]
      simp
  exact (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
    (add_le_add (V.minusTwo.norm_trace_le_of_dimension_le B L₂ hB.1 h₂ hV.1)
      hminus)) hzero)

/-- Weight at most eight, with degree zero supported at the origin and
degree -1 on a specified curve, gives the required repeated-index shape. -/
theorem fourier_trace_norm_le (V : SurfaceStalk) (p B : ℕ)
    (badCurve badPoint : Prop) [Decidable badCurve] [Decidable badPoint]
    (hB : V.dimensionsLe B)
    (hV : V.eigenvaluesLe ((p : ℝ) ^ 3) ((p : ℝ) ^ 3 * Real.sqrt p)
      ((p : ℝ) ^ 4))
    (hcurve : ¬badCurve → V.minusOne.dimension = 0)
    (hpoint : ¬badPoint → V.zero.dimension = 0) :
    ‖V.trace‖ ≤ B * (p : ℝ) ^ 3 *
      (1 + Real.sqrt p * (if badCurve then 1 else 0) +
        (p : ℝ) * if badPoint then 1 else 0) := by
  apply (V.norm_trace_le_with_support B _ _ _ badCurve badPoint hB
    (by positivity) (by positivity) (by positivity) hV hcurve hpoint).trans_eq
  split_ifs <;> ring

/-- Full-support intermediate extensions have no degree-zero stalk and
only finitely supported degree -1 stalks. This lemma proves the numerical
consequence of those separately supplied geometric conclusions. -/
theorem fourier_trace_norm_le_finite (V : SurfaceStalk) (p B : ℕ)
    (bad : Prop) [Decidable bad] (hB : V.dimensionsLe B)
    (hV : V.eigenvaluesLe ((p : ℝ) ^ 3) ((p : ℝ) ^ 3 * Real.sqrt p)
      ((p : ℝ) ^ 4))
    (hbad : ¬bad → V.minusOne.dimension = 0) (hzero : V.zero.dimension = 0) :
    ‖V.trace‖ ≤ B * (p : ℝ) ^ 3 *
      (1 + Real.sqrt p * if bad then 1 else 0) := by
  simpa only [ite_false, mul_zero, add_zero] using
    V.fourier_trace_norm_le p B bad False hB hV hbad (fun _ => hzero)

/-- Before Fourier transform the weight is at most six. The finite
degree -1 support must be kept when estimating the physical boundary. -/
theorem physical_trace_norm_le (V : SurfaceStalk) (p B : ℕ)
    (bad : Prop) [Decidable bad] (hB : V.dimensionsLe B)
    (hV : V.eigenvaluesLe ((p : ℝ) ^ 2) ((p : ℝ) ^ 2 * Real.sqrt p)
      ((p : ℝ) ^ 3))
    (hbad : ¬bad → V.minusOne.dimension = 0) (hzero : V.zero.dimension = 0) :
    ‖V.trace‖ ≤ B * (p : ℝ) ^ 2 +
      if bad then B * (p : ℝ) ^ 2 * Real.sqrt p else 0 := by
  have h := V.norm_trace_le_with_support B _ _ _ bad False hB
    (by positivity) (by positivity) (by positivity) hV hbad (fun _ => hzero)
  simpa only [ite_false, add_zero, mul_assoc] using h

end SurfaceStalk

#print axioms FrobeniusBlock
#print axioms FrobeniusBlock.mk
#print axioms FrobeniusBlock.dimension
#print axioms FrobeniusBlock.eigenvalue
#print axioms FrobeniusBlock.trace
#print axioms FrobeniusBlock.norm_trace_le
#print axioms FrobeniusBlock.trace_eq_zero_of_dimension_eq_zero
#print axioms FrobeniusBlock.norm_trace_le_of_dimension_le
#print axioms SurfaceStalk
#print axioms SurfaceStalk.mk
#print axioms SurfaceStalk.minusTwo
#print axioms SurfaceStalk.minusOne
#print axioms SurfaceStalk.zero
#print axioms SurfaceStalk.trace
#print axioms SurfaceStalk.dimensionsLe
#print axioms SurfaceStalk.eigenvaluesLe
#print axioms SurfaceStalk.norm_trace_le
#print axioms SurfaceStalk.norm_trace_le_with_support
#print axioms SurfaceStalk.fourier_trace_norm_le
#print axioms SurfaceStalk.fourier_trace_norm_le_finite
#print axioms SurfaceStalk.physical_trace_norm_le

end PrimeGap182.TypeIII
