import TypeIIICurveFibers
import TypeIIIBaselineBridge
import TypeIIISmallPrimes

/-!
# Quantitative physical-boundary estimates for the actual Type III sums

This module proves the finite-field point count and Fourier boundary estimate
needed when returning from a geometric intermediate extension to the original
four-cycle. It does not assume or prove the local Fourier proposition.
-/

noncomputable section
open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

theorem boundedVerticalFibers_card_le
    (s : ℕ) [NeZero s] (D : ℕ) (E : Finset (ZMod s × ZMod s))
    (hE : BoundedVerticalFibers s D E) : E.card ≤ 2 * D * s := by
  classical
  obtain ⟨V, hV, hfib⟩ := hE
  have hcard : E.card =
      ∑ h : ZMod s, (Finset.univ.filter (fun k : ZMod s => (h, k) ∈ E)).card := by
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [← Fintype.sum_prod_type (fun z : ZMod s × ZMod s =>
      if z ∈ E then (1 : ℕ) else 0)]
    simp
  have hbound (h : ZMod s) :
      (Finset.univ.filter (fun k : ZMod s => (h, k) ∈ E)).card ≤
        D + if h ∈ V then s else 0 := by
    by_cases hh : h ∈ V
    · rw [ite_eq_left hh]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
    · rw [ite_eq_right hh, add_zero]
      exact hfib h hh
  calc
    E.card = _ := hcard
    _ ≤ ∑ h : ZMod s, (D + if h ∈ V then s else 0) :=
      Finset.sum_le_sum (fun h _ => hbound h)
    _ = s * D + V.card * s := by simp [Finset.sum_add_distrib]
    _ ≤ s * D + D * s := Nat.add_le_add_left (Nat.mul_le_mul_right s hV) _
    _ = 2 * D * s := by ring

/-- A geometric plane polynomial of bounded degree has `O(D*p)` actual
prime-field zeros, even when its coefficients lie in the algebraic closure. -/
theorem curveZeroSet_card_le
    (p : ℕ) [Fact p.Prime] (D : ℕ)
    (P : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p)))
    (hP : P ≠ 0) (hD : P.totalDegree ≤ D) :
    (curveZeroSet p P).card ≤ 2 * D * p :=
  boundedVerticalFibers_card_le p D (curveZeroSet p P)
    (curveZeroSet_boundedVerticalFibers p D P hP hD)

/-- Restriction to a finite physical open set, extended by zero. -/
def physicalRestriction (s : ℕ) [NeZero s]
    (U : Finset (ZMod s × ZMod s)) (F : ZMod s → ZMod s → ℂ)
    (x y : ZMod s) : ℂ :=
  if (x, y) ∈ U then F x y else 0

/-- The Fourier sum of the omitted physical points. -/
def physicalBoundaryFourier (s : ℕ) [NeZero s]
    (E : Finset (ZMod s × ZMod s)) (F : ZMod s → ZMod s → ℂ)
    (h k : ZMod s) : ℂ :=
  ∑ z ∈ E, F z.1 z.2 * ZMod.stdAddChar (h * z.1 + k * z.2)

theorem physicalBoundaryFourier_norm_le
    (s : ℕ) [NeZero s] (E : Finset (ZMod s × ZMod s))
    (F : ZMod s → ZMod s → ℂ) (L : ℝ)
    (hF : ∀ z ∈ E, ‖F z.1 z.2‖ ≤ L) (h k : ZMod s) :
    ‖physicalBoundaryFourier s E F h k‖ ≤ (E.card : ℝ) * L := by
  unfold physicalBoundaryFourier
  calc
    _ ≤ ∑ _z ∈ E, L := by
      apply norm_sum_le_of_le
      intro z hz
      simpa only [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one] using hF z hz
    _ = _ := by simp

/-- A finite set of larger boundary stalks contributes its cardinality, rather
than the cardinality of the whole boundary. This is the distinction required
by the surface intermediate-extension estimate. -/
theorem physicalBoundaryFourier_norm_le_sparse
    (s : ℕ) [NeZero s] (E Z : Finset (ZMod s × ZMod s))
    (F : ZMod s → ZMod s → ℂ) (L₀ L₁ : ℝ) (hL₁ : 0 ≤ L₁)
    (hF : ∀ z ∈ E, ‖F z.1 z.2‖ ≤ L₀ + if z ∈ Z then L₁ else 0)
    (h k : ZMod s) :
    ‖physicalBoundaryFourier s E F h k‖ ≤
      (E.card : ℝ) * L₀ + (Z.card : ℝ) * L₁ := by
  classical
  have hcard : ((E ∩ Z).card : ℝ) ≤ (Z.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : E ∩ Z ⊆ Z)
  unfold physicalBoundaryFourier
  calc
    _ ≤ ∑ z ∈ E, (L₀ + if z ∈ Z then L₁ else 0) := by
      apply norm_sum_le_of_le
      intro z hz
      simpa only [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one] using hF z hz
    _ = (E.card : ℝ) * L₀ + ((E ∩ Z).card : ℝ) * L₁ := by
      simp [Finset.sum_add_distrib]
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_right hcard hL₁) _

/-- The aggregate `O(p³)` estimate remains valid when finitely many boundary
stalks have the larger `O(p^(5/2))` bound. All trace estimates are explicit
premises; no sheaf-theoretic weight theorem is assumed by definition. -/
theorem physicalBoundaryFourier_norm_le_surface_weights
    (p : ℕ) [Fact p.Prime] (D R : ℕ)
    (E Z : Finset (ZMod p × ZMod p))
    (hE : E.card ≤ 2 * D * p) (hZ : Z.card ≤ R)
    (F : ZMod p → ZMod p → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ z ∈ E, ‖F z.1 z.2‖ ≤ B * (p : ℝ) ^ 2 +
      if z ∈ Z then B * (p : ℝ) ^ 2 * Real.sqrt p else 0)
    (h k : ZMod p) :
    ‖physicalBoundaryFourier p E F h k‖ ≤
      B * (2 * (D : ℝ) + R) * (p : ℝ) ^ 3 := by
  have hcE : (E.card : ℝ) ≤ 2 * D * p := by exact_mod_cast hE
  have hcZ : (Z.card : ℝ) ≤ R := by exact_mod_cast hZ
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (NeZero.one_le : 1 ≤ p)
  have hsqrt : Real.sqrt (p : ℝ) ≤ p := Real.sqrt_le_self_iff.mpr (Or.inr hp)
  calc
    _ ≤ (E.card : ℝ) * (B * (p : ℝ) ^ 2) +
        (Z.card : ℝ) * (B * (p : ℝ) ^ 2 * Real.sqrt p) :=
      physicalBoundaryFourier_norm_le_sparse p E Z F _ _ (by positivity) hF h k
    _ ≤ (2 * (D : ℝ) * p) * (B * (p : ℝ) ^ 2) +
        (R : ℝ) * (B * (p : ℝ) ^ 2 * Real.sqrt p) :=
      add_le_add (mul_le_mul_of_nonneg_right hcE (by positivity))
        (mul_le_mul_of_nonneg_right hcZ (by positivity))
    _ ≤ (2 * (D : ℝ) * p) * (B * (p : ℝ) ^ 2) +
        (R : ℝ) * (B * (p : ℝ) ^ 2 * p) := by
      gcongr
    _ = _ := by ring

/-- Exact restoration of the omitted physical boundary; all Fourier phases
and the zero extension agree with the local proposition's conventions. -/
theorem fourier₂_eq_restriction_add_boundary
    (s : ℕ) [NeZero s] (U : Finset (ZMod s × ZMod s))
    (F : ZMod s → ZMod s → ℂ) (h k : ZMod s) :
    fourier₂ s F h k =
      fourier₂ s (physicalRestriction s U F) h k +
        physicalBoundaryFourier s (Finset.univ \ U) F h k := by
  classical
  unfold fourier₂ physicalBoundaryFourier
  rw [← Fintype.sum_prod_type (fun z : ZMod s × ZMod s =>
    F z.1 z.2 * ZMod.stdAddChar (h * z.1 + k * z.2))]
  rw [← Fintype.sum_prod_type (fun z : ZMod s × ZMod s =>
    physicalRestriction s U F z.1 z.2 * ZMod.stdAddChar (h * z.1 + k * z.2))]
  have hU : (∑ z : ZMod s × ZMod s,
      physicalRestriction s U F z.1 z.2 * ZMod.stdAddChar (h * z.1 + k * z.2)) =
      ∑ z ∈ U, F z.1 z.2 * ZMod.stdAddChar (h * z.1 + k * z.2) := by
    simp only [physicalRestriction, ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    simp
  rw [hU]
  simpa only [add_comm] using
    (Finset.sum_sdiff
      (f := fun z : ZMod s × ZMod s =>
        F z.1 z.2 * ZMod.stdAddChar (h * z.1 + k * z.2))
      (Finset.subset_univ U)).symm

theorem raw_fourCycle_physicalBoundary_norm_le
    (hbase : BaselineLocalInputs) (p : ℕ) [Fact p.Prime]
    (D : ℕ) (E : Finset (ZMod p × ZMod p)) (hE : E.card ≤ 2 * D * p)
    (α m m' n n' : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0)
    (hn : n ≠ 0) (hn' : n' ≠ 0) (h k : ZMod p) :
    ‖physicalBoundaryFourier p E (fourCycle p α m m' n n') h k‖ ≤
      13122 * (D : ℝ) * (p : ℝ) ^ 3 := by
  have hcard : (E.card : ℝ) ≤ 2 * D * p := by exact_mod_cast hE
  calc
    _ ≤ (E.card : ℝ) * (6561 * (p : ℝ) ^ 2) :=
      physicalBoundaryFourier_norm_le p E _ _
        (fun z _ => fourCycle_norm_le_baseline_inputs hbase p α m m' n n' z.1 z.2
          hα hm hm' hn hn') h k
    _ ≤ (2 * (D : ℝ) * p) * (6561 * (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-- The exact original four-cycle has a uniform `O(D*p^3)` Fourier error
when a geometric zero set of degree at most `D` is removed. The only
finite-field inputs here are the two established baseline estimates. -/
theorem raw_fourCycle_polynomialBoundary_norm_le
    (hbase : BaselineLocalInputs) (p : ℕ) [Fact p.Prime] (D : ℕ)
    (P : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p)))
    (hP : P ≠ 0) (hD : P.totalDegree ≤ D)
    (α m m' n n' : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0)
    (hn : n ≠ 0) (hn' : n' ≠ 0) (h k : ZMod p) :
    ‖physicalBoundaryFourier p (curveZeroSet p P) (fourCycle p α m m' n n') h k‖ ≤
      13122 * (D : ℝ) * (p : ℝ) ^ 3 :=
  raw_fourCycle_physicalBoundary_norm_le hbase p D (curveZeroSet p P)
    (curveZeroSet_card_le p D P hP hD) α m m' n n' hα hm hm' hn hn' h k

#print axioms boundedVerticalFibers_card_le
#print axioms curveZeroSet_card_le
#print axioms physicalBoundaryFourier_norm_le
#print axioms physicalBoundaryFourier_norm_le_sparse
#print axioms physicalBoundaryFourier_norm_le_surface_weights
#print axioms fourier₂_eq_restriction_add_boundary
#print axioms raw_fourCycle_physicalBoundary_norm_le
#print axioms raw_fourCycle_polynomialBoundary_norm_le

end PrimeGap182.TypeIII
