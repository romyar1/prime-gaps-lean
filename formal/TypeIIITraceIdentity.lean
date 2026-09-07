import TypeIIIExactSpectrum
import TypeIIIRepeatedAlgebra
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Finite.Basic

/-!
# Exact origin reduction for the actual Type III transform

At the origin the scalar toric transform is an integer determined by a
cubic fiber.  Its nontrivial fibers have at most three elements, giving a
uniform `2p + 1` bound away from the zero coefficient pair.  Substitution in
the exact four-cycle formula retains the full, explicit rectangle spectrum.
No estimate for that remaining spectrum, or realization by a sheaf, is
asserted here.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The actual unit cubic fiber appearing in radial summation at the origin. -/
def toricOriginCubicFiber (A B : ZMod p) : Finset (ZMod p)ˣ :=
  Finset.univ.filter (fun z => A * (z : ZMod p) ^ 3 + B = 0)

/-- The full scalar toric sum at the origin, including its zero-coefficient
case, is exactly a cubic-fiber count. -/
theorem toricPhaseFourier_origin (A B : ZMod p) :
    toricPhaseFourier p A B 0 0 =
      (p : ℂ) * (toricOriginCubicFiber p A B).card - ((p : ℂ) - 1) := by
  rw [toricPhaseFourier_radial]
  simp only [zero_mul, add_zero, ite_true]
  have he (z : (ZMod p)ˣ) :
      A * (z : ZMod p) + B / (z : ZMod p) ^ 2 = 0 ↔
        A * (z : ZMod p) ^ 3 + B = 0 := by
    have hz : (z : ZMod p) ^ 2 ≠ 0 := pow_ne_zero _ (Units.ne_zero z)
    have hs : A * (z : ZMod p) + B / (z : ZMod p) ^ 2 =
        (A * (z : ZMod p) ^ 3 + B) / (z : ZMod p) ^ 2 := by
      field_simp
    rw [hs, div_eq_zero_iff, or_iff_left hz]
  simp_rw [he]
  have hi (z : (ZMod p)ˣ) :
      (if A * (z : ZMod p) ^ 3 + B = 0 then (p : ℂ) - 1 else -1) =
        (if A * (z : ZMod p) ^ 3 + B = 0 then (p : ℂ) else 0) - 1 := by
    split_ifs <;> ring
  simp_rw [hi]
  rw [Finset.sum_sub_distrib, ← Finset.sum_filter]
  simp only [toricOriginCubicFiber, Finset.sum_const, Finset.card_univ,
    ZMod.card_units, nsmul_eq_mul, mul_one]
  rw [Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one]
  ring

/-- No cubic fiber has more than three points when at least one coefficient
is nonzero.  This includes both coefficient axes. -/
theorem toricOriginCubicFiber_card_le_three (A B : ZMod p)
    (hAB : A ≠ 0 ∨ B ≠ 0) : (toricOriginCubicFiber p A B).card ≤ 3 := by
  classical
  by_cases hA : A = 0
  · have hB : B ≠ 0 := hAB.resolve_left (not_not.mpr hA)
    simp [toricOriginCubicFiber, hA, hB]
  · let P : Polynomial (ZMod p) := Polynomial.X ^ 3 - Polynomial.C (-B / A)
    have hP : P ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by decide) _
    have hinj : (toricOriginCubicFiber p A B).card ≤ P.roots.toFinset.card := by
      apply Finset.card_le_card_of_injOn (f := fun z : (ZMod p)ˣ => (z : ZMod p))
      · intro z hz
        change (z : ZMod p) ∈ P.roots.toFinset
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
        change z ∈ toricOriginCubicFiber p A B at hz
        have hz' := (Finset.mem_filter.mp hz).2
        simp only [P, Polynomial.IsRoot, Polynomial.eval_sub,
          Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
        apply sub_eq_zero.mpr
        apply (eq_div_iff hA).mpr
        linear_combination hz'
      · intro a _ b _ hab
        exact Units.ext hab
    exact hinj.trans ((Multiset.toFinset_card_le _).trans
      (Polynomial.card_roots_X_pow_sub_C (by decide : 0 < 3) _))

/-- At nonzero coefficient pairs the complete radial cancellation leaves
at most `2p + 1`, without any finite-field character-sum bound as a premise. -/
theorem toricPhaseFourier_origin_norm_le (A B : ZMod p)
    (hAB : A ≠ 0 ∨ B ≠ 0) :
    ‖toricPhaseFourier p A B 0 0‖ ≤ 2 * (p : ℝ) + 1 := by
  have hcard : ((toricOriginCubicFiber p A B).card : ℝ) ≤ 3 := by
    exact_mod_cast toricOriginCubicFiber_card_le_three p A B hAB
  have hcard0 : 0 ≤ ((toricOriginCubicFiber p A B).card : ℝ) := by positivity
  have hp : 0 ≤ (p : ℝ) := by positivity
  rw [toricPhaseFourier_origin]
  have he : (p : ℂ) * (toricOriginCubicFiber p A B).card - ((p : ℂ) - 1) =
      (((p : ℝ) * (toricOriginCubicFiber p A B).card - ((p : ℝ) - 1) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor
  · nlinarith [mul_nonneg hp hcard0]
  · nlinarith [mul_le_mul_of_nonneg_left hcard hp]

/-- The exceptional coefficient pair contributes its exact torus cardinality. -/
theorem toricPhaseFourier_origin_zero_coefficients :
    toricPhaseFourier p 0 0 0 0 = ((p : ℂ) - 1) ^ 2 := by
  rw [toricPhaseFourier_origin]
  simp only [toricOriginCubicFiber, zero_mul, zero_add, Finset.filter_true,
    Finset.card_univ, ZMod.card_units]
  rw [Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one]
  ring

/-- When cubing is a permutation of the unit group, every fiber with two
nonzero coefficients has exactly one point. -/
theorem toricOriginCubicFiber_card_eq_one (h3 : (p - 1).Coprime 3)
    (A B : ZMod p) (hA : A ≠ 0) (hB : B ≠ 0) :
    (toricOriginCubicFiber p A B).card = 1 := by
  classical
  have hc : Function.Bijective (fun z : (ZMod p)ˣ => z ^ 3) := by
    apply Nat.Coprime.pow_left_bijective
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units] using h3
  let u : (ZMod p)ˣ := Units.mk0 (-B / A) (div_ne_zero (neg_ne_zero.mpr hB) hA)
  obtain ⟨z, hz⟩ := hc.surjective u
  have hzv : (z : ZMod p) ^ 3 = -B / A := by
    simpa only [Units.val_pow_eq_pow_val, u, Units.val_mk0] using congrArg Units.val hz
  apply Finset.card_eq_one.mpr
  refine ⟨z, Finset.ext fun w => ?_⟩
  simp only [toricOriginCubicFiber, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_singleton]
  constructor
  · intro hw
    apply hc.injective
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val]
    rw [hzv]
    apply (eq_div_iff hA).mpr
    linear_combination hw
  · intro hw
    subst w
    rw [hzv]
    field_simp
    ring

/-- For unit coefficients and bijective cubing the scalar origin sum is
exactly one, despite having `(p - 1)²` unit summands. -/
theorem toricPhaseFourier_origin_eq_one (h3 : (p - 1).Coprime 3)
    (A B : ZMod p) (hA : A ≠ 0) (hB : B ≠ 0) :
    toricPhaseFourier p A B 0 0 = 1 := by
  rw [toricPhaseFourier_origin, toricOriginCubicFiber_card_eq_one p h3 A B hA hB]
  push_cast
  ring

/-- Exact cubic-weighted spectrum of the actual four-cycle at the origin.
The rectangle spectrum on the right is explicitly defined by rank-two
Kloosterman sums and finite convolutions, with no estimate assumed. -/
theorem exact_fourCycle_fourier_origin (α m m' n n' : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    fourier₂ p (fourCycle p α m m' n n') 0 0 =
      ((p : ℂ) ^ 2)⁻¹ * ∑ a : ZMod p, ∑ b : ZMod p,
        exactRectangleSpectrum p α m m' n n' a b *
          ((p : ℂ) * (toricOriginCubicFiber p (-a) (-b)).card - ((p : ℂ) - 1)) := by
  rw [exact_fourCycle_fourier_explicit p α m m' n n' 0 0 hα hm hm' hn hn']
  simp_rw [toricPhaseFourier_origin]

/-- The zero coefficient pair is displayed separately from the remaining
cubic-weighted rectangle spectrum.  It cannot be included in the scalar
`2p + 1` bound. -/
theorem exact_fourCycle_fourier_origin_split (α m m' n n' : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    fourier₂ p (fourCycle p α m m' n n') 0 0 =
      ((p : ℂ) ^ 2)⁻¹ *
        (exactRectangleSpectrum p α m m' n n' 0 0 * ((p : ℂ) - 1) ^ 2 +
          ∑ ab ∈ (Finset.univ.erase ((0 : ZMod p), (0 : ZMod p))),
            exactRectangleSpectrum p α m m' n n' ab.1 ab.2 *
              ((p : ℂ) * (toricOriginCubicFiber p (-ab.1) (-ab.2)).card -
                ((p : ℂ) - 1))) := by
  classical
  rw [exact_fourCycle_fourier_explicit p α m m' n n' 0 0 hα hm hm' hn hn']
  have hpairs :
      (∑ a : ZMod p, ∑ b : ZMod p,
        exactRectangleSpectrum p α m m' n n' a b * toricPhaseFourier p (-a) (-b) 0 0) =
      ∑ ab : ZMod p × ZMod p,
        exactRectangleSpectrum p α m m' n n' ab.1 ab.2 *
          toricPhaseFourier p (-ab.1) (-ab.2) 0 0 := by
    rw [Fintype.sum_prod_type]
  rw [hpairs]
  have hs := Finset.sum_erase_add
    (s := (Finset.univ : Finset (ZMod p × ZMod p)))
    (f := fun ab : ZMod p × ZMod p =>
      exactRectangleSpectrum p α m m' n n' ab.1 ab.2 *
        toricPhaseFourier p (-ab.1) (-ab.2) 0 0)
    (a := (0, 0)) (Finset.mem_univ _)
  rw [← hs]
  simp only [neg_zero, toricPhaseFourier_origin_zero_coefficients]
  simp_rw [toricPhaseFourier_origin]
  rw [add_comm]

/-- The determinant-three monomial map on the actual unit pairs. -/
def exactUnitTorusMap (xy : (ZMod p)ˣ × (ZMod p)ˣ) : (ZMod p)ˣ × (ZMod p)ˣ :=
  (xy.2 / xy.1 ^ 2, xy.1 / xy.2 ^ 2)

/-- The nonlinear torus map is a permutation whenever cubing is a
permutation of the unit group. -/
theorem exactUnitTorusMap_bijective (h3 : (p - 1).Coprime 3) :
    Function.Bijective (exactUnitTorusMap p) := by
  have hc : Function.Injective (fun z : (ZMod p)ˣ => z ^ 3) := by
    apply (Nat.Coprime.pow_left_bijective (G := (ZMod p)ˣ) ?_).injective
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units] using h3
  have hrec (x y : (ZMod p)ˣ) : ((y / x ^ 2) ^ 2 * (x / y ^ 2))⁻¹ = x ^ 3 := by
    apply Units.ext
    simp only [Units.val_inv_eq_inv_val, Units.val_mul,
      Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
    field_simp
  apply Finite.injective_iff_bijective.mp
  intro xy uv he
  have h₁ : xy.2 / xy.1 ^ 2 = uv.2 / uv.1 ^ 2 := congrArg Prod.fst he
  have h₂ : xy.1 / xy.2 ^ 2 = uv.1 / uv.2 ^ 2 := congrArg Prod.snd he
  apply Prod.ext
  · apply hc
    change xy.1 ^ 3 = uv.1 ^ 3
    rw [← hrec xy.1 xy.2, ← hrec uv.1 uv.2, h₁, h₂]
  · apply hc
    change xy.2 ^ 3 = uv.2 ^ 3
    rw [← hrec xy.2 xy.1, ← hrec uv.2 uv.1, h₁, h₂]

/-- When cubing is bijective, the origin of the actual nonlinear pullback
is exactly the sum of its original function over the unit torus. -/
theorem exact_torus_pullback_origin_of_coprime (h3 : (p - 1).Coprime 3)
    (f : ZMod p → ZMod p → ℂ) :
    fourier₂ p (exactTorusPullback p f) 0 0 =
      ∑ u : (ZMod p)ˣ, ∑ v : (ZMod p)ˣ, f (u : ZMod p) (v : ZMod p) := by
  classical
  have hu : fourier₂ p (exactTorusPullback p f) 0 0 =
      ∑ x : (ZMod p)ˣ, ∑ y : (ZMod p)ˣ,
        f ((y : ZMod p) / (x : ZMod p) ^ 2)
          ((x : ZMod p) / (y : ZMod p) ^ 2) := by
    simp only [fourier₂, exactTorusPullback, zero_mul, add_zero,
      AddChar.map_zero_eq_one, mul_one]
    rw [PrimeGap186.sum_units_eq_sum_ite p (fun x : ZMod p =>
      ∑ y : (ZMod p)ˣ,
        f ((y : ZMod p) / x ^ 2) (x / (y : ZMod p) ^ 2))]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x = 0
    · simp [hx]
    · rw [ite_eq_left hx, PrimeGap186.sum_units_eq_sum_ite p (fun y : ZMod p =>
        f (y / x ^ 2) (x / y ^ 2))]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y = 0 <;> simp [hx, hy]
  rw [hu]
  let e : ((ZMod p)ˣ × (ZMod p)ˣ) ≃ ((ZMod p)ˣ × (ZMod p)ˣ) :=
    Equiv.ofBijective (exactUnitTorusMap p) (exactUnitTorusMap_bijective p h3)
  have he := Fintype.sum_equiv e
    (fun xy : (ZMod p)ˣ × (ZMod p)ˣ =>
      f ((xy.2 : ZMod p) / (xy.1 : ZMod p) ^ 2)
        ((xy.1 : ZMod p) / (xy.2 : ZMod p) ^ 2))
    (fun uv : (ZMod p)ˣ × (ZMod p)ˣ => f (uv.1 : ZMod p) (uv.2 : ZMod p))
    (by
      intro xy
      simp only [e, Equiv.ofBijective_apply, exactUnitTorusMap,
        Units.val_div_eq_div_val, Units.val_pow_eq_pow_val])
  simpa only [Fintype.sum_prod_type] using he

/-- For primes with bijective cubing, the actual origin coefficient is the
unpulled unit-rectangle sum.  In particular, the nonlinear substitution
does not by itself supply cancellation for this coefficient. -/
theorem exact_fourCycle_fourier_origin_of_coprime (h3 : (p - 1).Coprime 3)
    (α m m' n n' : ZMod p) :
    fourier₂ p (fourCycle p α m m' n n') 0 0 =
      ∑ u : (ZMod p)ˣ, ∑ v : (ZMod p)ˣ,
        exactCorrelationRectangle p α m m' n n' (u : ZMod p) (v : ZMod p) := by
  rw [exact_fourCycle_eq_pullback, exact_torus_pullback_origin_of_coprime p h3]

#print axioms toricPhaseFourier_origin
#print axioms toricOriginCubicFiber_card_le_three
#print axioms toricPhaseFourier_origin_norm_le
#print axioms toricPhaseFourier_origin_zero_coefficients
#print axioms toricOriginCubicFiber_card_eq_one
#print axioms toricPhaseFourier_origin_eq_one
#print axioms exact_fourCycle_fourier_origin
#print axioms exact_fourCycle_fourier_origin_split
#print axioms exactUnitTorusMap_bijective
#print axioms exact_torus_pullback_origin_of_coprime
#print axioms exact_fourCycle_fourier_origin_of_coprime

end

end PrimeGap182.TypeIII
