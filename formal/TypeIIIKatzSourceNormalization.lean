import TypeIIICanonicalInputTrace

/-!
# Katz's raw trace and the exact normalized source sums

Katz, GKM, Theorem 4.1.1(2), gives the product-constrained unit sum,
with sign (-1)^(n-1), for geometric Frobenius over every finite extension.
For n=3 the Tate twist (1) divides that trace by the extension cardinality.
The finite-sum reindexing below is checked over an arbitrary finite field.
It then supplies the exact source trace used by the canonical input recipe.

The published raw trace, AS trace, and general Tate/pullback trace laws
remain explicit premises about the SAME source objects. No sheaf category,
coefficient embedding, or compatible source family is constructed here.
Kloosterman traces are required only on units; no trace at zero is imposed.
Reference: https://web.math.princeton.edu/~nmk/Katz-GKM.pdf,
Theorem 4.1.1(2), section 4.3, and section 11.0.1.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped BigOperators Classical

namespace PrimeGap182.TypeIII.KatzSourceNormalization

universe u v w

section FiniteSums

variable {K : Type u} [Field K] [Fintype K] (ψ : AddChar K ℂ)

/-- The unnormalized unit sum in Katz's rank-three trace formula. -/
def rawKl3 (t : Kˣ) : ℂ :=
  ∑ u : Kˣ, ∑ v : Kˣ, ∑ w : Kˣ,
    if u * v * w = t then ψ ((u : K) + (v : K) + (w : K)) else 0

/-- Solving the product constraint removes exactly the third unit variable.
This identity requires neither a sheaf theorem nor character nontriviality. -/
theorem rawKl3_eq_double_sum (t : Kˣ) :
    rawKl3 ψ t =
      ∑ u : Kˣ, ∑ v : Kˣ,
        ψ ((u : K) + (v : K) + (t : K) / ((u : K) * (v : K))) := by
  have hcond (u v w : Kˣ) : u * v * w = t ↔ w = (u * v)⁻¹ * t := by
    constructor
    · intro h
      calc
        w = (u * v)⁻¹ * ((u * v) * w) := (inv_mul_cancel_left (u * v) w).symm
        _ = (u * v)⁻¹ * t := by rw [h]
    · intro h
      rw [h, ← mul_assoc]
      simp
  unfold rawKl3
  simp_rw [hcond]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  simp [Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_comm]

variable {Line : Type v} (lineTrace : Line → K → ℂ)
  (twistOne : Line → Line) (raw : Line)

/-- The rank-three sign is positive and twist (1) gives exactly `kl3`.
The two hypotheses are a published raw trace formula and a general twist law. -/
theorem normalized_kl_trace
    (hraw : ∀ z : Kˣ, lineTrace raw (z : K) = (-1 : ℂ) ^ (3 - 1) * rawKl3 ψ z)
    (htwist : ∀ A z, lineTrace (twistOne A) z =
      (Fintype.card K : ℂ)⁻¹ * lineTrace A z)
    (z : Kˣ) :
    lineTrace (twistOne raw) (z : K) = FiniteFieldSums.kl3 ψ (z : K) := by
  rw [htwist, hraw, rawKl3_eq_double_sum]
  norm_num [FiniteFieldSums.kl3]

end FiniteSums

open StartingSourceMaps StartingSourceComplexity CanonicalCurveInput
open PublishedPhysicalConstruction CanonicalInputTrace

variable (p : ℕ) [Fact p.Prime]
  {L : Type} [Field L] [Fintype L] [Algebra (ZMod p) L]
  {Input : Type u} {Point : Type v} {Line : Type w} {D : CurveData Input Point}
  (F : PullbackData (ZMod p) Line Input) (G : LineGeometry Line)
  (R : ScalarPullbackRules F G D) (twistOne : Line → Line) (raw as : Line)
  (hkl : Kl3Properties G (twistOne raw)) (has : ASProperties G as)
  (T : CurveTraceData D L) (lineTrace : Line → L → ℂ) (lambda xi : Lˣ)
  (Q : PullbackTraceRules F T lineTrace lambda xi)

include Q in
/-- Over every finite extension of the prime field, the raw Katz and AS
formulas supply all three original family traces through the proved maps.
No completed normalized-Kloosterman or correlation trace is an input. -/
theorem canonicalTraceData_of_katz
    (hraw : ∀ z : Lˣ, lineTrace raw (z : L) =
      (-1 : ℂ) ^ (3 - 1) * rawKl3 (FiniteFieldSums.traceAddChar p L) z)
    (htwist : ∀ A z, lineTrace (twistOne A) z =
      (Fintype.card L : ℂ)⁻¹ * lineTrace A z)
    (hasTrace : ∀ z : L, lineTrace as z =
      ZMod.stdAddChar (Algebra.trace (ZMod p) L z)) :
    KloostermanTraceData D L (canonicalInput F G R (twistOne raw) as hkl has) T
      (FiniteFieldSums.traceAddChar p L) lambda xi := by
  apply canonicalTraceData F G R (twistOne raw) as hkl has T lineTrace lambda xi Q
    (FiniteFieldSums.traceAddChar p L)
  · exact normalized_kl_trace (FiniteFieldSums.traceAddChar p L) lineTrace twistOne raw hraw htwist
  · exact hasTrace

end PrimeGap182.TypeIII.KatzSourceNormalization

#print axioms PrimeGap182.TypeIII.KatzSourceNormalization.rawKl3_eq_double_sum
#print axioms PrimeGap182.TypeIII.KatzSourceNormalization.normalized_kl_trace
#print axioms PrimeGap182.TypeIII.KatzSourceNormalization.canonicalTraceData_of_katz
