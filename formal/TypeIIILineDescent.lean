import TypeIIIConstantField

/-!
# Constant ratios and translated lines

This file checks the algebraic line step in the Type III curve-exclusion
argument. Rational functions, algebraic closures, automorphisms and affine
lines are actual Mathlib objects. No geometric finite-orbit assertion is
made here.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open Polynomial
open scoped Classical Affine

set_option maxHeartbeats 1000000

variable {k : Type*} [Field k]

/-- The actual linear form `v₀ + v₁ z` in the rational-function field. -/
def lineDescentLinearForm (v : Fin 2 → k) : RatFunc k :=
  RatFunc.C (v 0) + RatFunc.C (v 1) * RatFunc.X

theorem lineDescentLinearForm_eq_algebraMap (v : Fin 2 → k) :
    lineDescentLinearForm v =
      algebraMap k[X] (RatFunc k) (C (v 0) + C (v 1) * X) := by
  simp [lineDescentLinearForm]

theorem lineDescentLinearForm_injective :
    Function.Injective (lineDescentLinearForm (k := k)) := by
  intro u v h
  rw [lineDescentLinearForm_eq_algebraMap,
    lineDescentLinearForm_eq_algebraMap] at h
  have hp := RatFunc.algebraMap_injective k h
  ext i
  fin_cases i
  · simpa using congrArg (fun p : k[X] => p.coeff 0) hp
  · simpa using congrArg (fun p : k[X] => p.coeff 1) hp

theorem lineDescentLinearForm_ne_zero (v : Fin 2 → k) (hv : v ≠ 0) :
    lineDescentLinearForm v ≠ 0 := by
  intro h
  apply hv
  apply lineDescentLinearForm_injective
  simpa [lineDescentLinearForm] using h

theorem lineDescentLinearForm_smul (a : k) (v : Fin 2 → k) :
    lineDescentLinearForm (a • v) = RatFunc.C a * lineDescentLinearForm v := by
  simp [lineDescentLinearForm, mul_add, mul_assoc]

/-- The actual rational function `(u₀ + u₁ z)/(v₀ + v₁ z)`. -/
def lineDescentRatio (u v : Fin 2 → k) : RatFunc k :=
  lineDescentLinearForm u / lineDescentLinearForm v

theorem lineDescentRatio_eq_constant_iff (u v : Fin 2 → k) (hv : v ≠ 0) (a : k) :
    lineDescentRatio u v = RatFunc.C a ↔ u = a • v := by
  rw [lineDescentRatio, div_eq_iff (lineDescentLinearForm_ne_zero v hv),
    ← lineDescentLinearForm_smul, lineDescentLinearForm_injective.eq_iff]

/-- The determinant of the two actual coefficient vectors. -/
def lineDescentDeterminant (u v : Fin 2 → k) : k := u 0 * v 1 - u 1 * v 0

theorem lineDescentDeterminant_eq_zero_iff (u v : Fin 2 → k) (hv : v ≠ 0) :
    lineDescentDeterminant u v = 0 ↔ ∃ a : k, u = a • v := by
  constructor
  · intro h
    have hc : u 0 * v 1 = u 1 * v 0 := sub_eq_zero.mp h
    by_cases hv0 : v 0 = 0
    · have hv1 : v 1 ≠ 0 := by
        intro h1
        apply hv
        ext i
        fin_cases i <;> simp [hv0, h1]
      have hu0 : u 0 = 0 := (mul_eq_zero.mp (by simpa [hv0] using hc)).resolve_right hv1
      refine ⟨u 1 / v 1, ?_⟩
      ext i
      fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, hu0, hv0, hv1]
    · refine ⟨u 0 / v 0, ?_⟩
      ext i
      fin_cases i
      · simp [Pi.smul_apply, smul_eq_mul, hv0]
      · change u 1 = u 0 / v 0 * v 1
        rw [div_mul_eq_mul_div]
        exact (eq_div_iff hv0).mpr hc.symm
  · rintro ⟨a, rfl⟩
    simp only [lineDescentDeterminant, Pi.smul_apply, smul_eq_mul]
    ring

/-- Constancy is precisely the vanishing determinant criterion, over every
field and in every characteristic. -/
theorem lineDescentRatio_constant_iff (u v : Fin 2 → k) (hv : v ≠ 0) :
    (∃ a : k, lineDescentRatio u v = RatFunc.C a) ↔
      lineDescentDeterminant u v = 0 := by
  simp_rw [lineDescentRatio_eq_constant_iff u v hv]
  exact (lineDescentDeterminant_eq_zero_iff u v hv).symm

/-- The image of the same rational function in its actual algebraic closure. -/
def lineDescentRatioClosure (u v : Fin 2 → k) : AlgebraicClosure (RatFunc k) :=
  algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) (lineDescentRatio u v)

theorem lineDescentRatioClosure_eq_constant_iff (u v : Fin 2 → k)
    (hv : v ≠ 0) (a : k) :
    lineDescentRatioClosure u v = algebraMap k (AlgebraicClosure (RatFunc k)) a ↔
      u = a • v := by
  rw [lineDescentRatioClosure,
    IsScalarTower.algebraMap_apply k (RatFunc k) (AlgebraicClosure (RatFunc k)),
    (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))).injective.eq_iff,
    RatFunc.algebraMap_eq_C]
  exact lineDescentRatio_eq_constant_iff u v hv a

theorem lineDescentRatioClosure_constant_iff (u v : Fin 2 → k) (hv : v ≠ 0) :
    (∃ a : k, algebraMap k (AlgebraicClosure (RatFunc k)) a =
      lineDescentRatioClosure u v) ↔ lineDescentDeterminant u v = 0 := by
  constructor
  · rintro ⟨a, ha⟩
    exact (lineDescentDeterminant_eq_zero_iff u v hv).mpr
      ⟨a, (lineDescentRatioClosure_eq_constant_iff u v hv a).mp ha.symm⟩
  · intro hdet
    obtain ⟨a, ha⟩ := (lineDescentDeterminant_eq_zero_iff u v hv).mp hdet
    exact ⟨a, ((lineDescentRatioClosure_eq_constant_iff u v hv a).mpr ha).symm⟩

/-- The actual translated affine line with base point `u` and direction `v`. -/
def lineDescentAffineLine (u v : Fin 2 → k) : AffineSubspace k (Fin 2 → k) :=
  affineSpan k {u, u + v}

theorem mem_lineDescentAffineLine_iff (u v x : Fin 2 → k) :
    x ∈ lineDescentAffineLine u v ↔ ∃ t : k, u + t • v = x := by
  rw [lineDescentAffineLine, mem_affineSpan_pair_iff_exists_lineMap_eq]
  simp only [AffineMap.lineMap_apply_module', add_sub_cancel_left, add_comm]

theorem zero_mem_lineDescentAffineLine_iff (u v : Fin 2 → k) :
    (0 : Fin 2 → k) ∈ lineDescentAffineLine u v ↔ ∃ a : k, u = a • v := by
  rw [mem_lineDescentAffineLine_iff]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨-t, ?_⟩
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left ht
  · rintro ⟨a, rfl⟩
    exact ⟨-a, by simp⟩

theorem zero_mem_lineDescentAffineLine_of_det_zero (u v : Fin 2 → k)
    (hv : v ≠ 0) (hdet : lineDescentDeterminant u v = 0) :
    (0 : Fin 2 → k) ∈ lineDescentAffineLine u v :=
  (zero_mem_lineDescentAffineLine_iff u v).mpr
    ((lineDescentDeterminant_eq_zero_iff u v hv).mp hdet)

/-- Finite orbit under the actual constant-field automorphism group forces
the line to have zero intercept determinant. Algebraic closure of the base
is the hypothesis used in the manuscript; no characteristic is excluded. -/
theorem lineDescentDeterminant_eq_zero_of_finite_orbit [IsAlgClosed k]
    (u v : Fin 2 → k) (hv : v ≠ 0)
    (hfinite : (Set.range (fun σ : AlgebraicClosure (RatFunc k) ≃ₐ[k]
      AlgebraicClosure (RatFunc k) => σ (lineDescentRatioClosure u v))).Finite) :
    lineDescentDeterminant u v = 0 := by
  apply (lineDescentRatioClosure_constant_iff u v hv).mp
  exact (rationalAlgebraicClosure_finite_orbit_iff k (lineDescentRatioClosure u v)).mp hfinite

theorem zero_mem_lineDescentAffineLine_of_finite_orbit [IsAlgClosed k]
    (u v : Fin 2 → k) (hv : v ≠ 0)
    (hfinite : (Set.range (fun σ : AlgebraicClosure (RatFunc k) ≃ₐ[k]
      AlgebraicClosure (RatFunc k) => σ (lineDescentRatioClosure u v))).Finite) :
    (0 : Fin 2 → k) ∈ lineDescentAffineLine u v :=
  zero_mem_lineDescentAffineLine_of_det_zero u v hv
    (lineDescentDeterminant_eq_zero_of_finite_orbit u v hv hfinite)

theorem lineDescent_exists_parameter_of_finite_orbit [IsAlgClosed k]
    (u v : Fin 2 → k) (hv : v ≠ 0)
    (hfinite : (Set.range (fun σ : AlgebraicClosure (RatFunc k) ≃ₐ[k]
      AlgebraicClosure (RatFunc k) => σ (lineDescentRatioClosure u v))).Finite) :
    ∃ t : k, u + t • v = 0 :=
  (mem_lineDescentAffineLine_iff u v 0).mp
    (zero_mem_lineDescentAffineLine_of_finite_orbit u v hv hfinite)

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.lineDescentRatio_constant_iff
#print axioms PrimeGap182.TypeIII.lineDescentRatioClosure_constant_iff
#print axioms PrimeGap182.TypeIII.lineDescentDeterminant_eq_zero_of_finite_orbit
#print axioms PrimeGap182.TypeIII.zero_mem_lineDescentAffineLine_of_finite_orbit
#print axioms PrimeGap182.TypeIII.lineDescent_exists_parameter_of_finite_orbit
