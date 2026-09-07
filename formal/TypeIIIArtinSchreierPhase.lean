import Mathlib

/-!
# Pole-one Artin–Schreier classes in the completed Laurent-series field

All series below are actual `LaurentSeries k`, i.e. Hahn series with integer
exponents, equipped with Mathlib's additive order valuation. No rational-function
restriction is imposed on the possible Artin–Schreier primitive.

This file proves a field-theoretic obstruction. It does not construct an ℓ-adic
sheaf or identify the characters of the Type III correlation.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open HahnSeries

set_option maxHeartbeats 1000000

variable {k : Type*} [Field k]

/-- The actual additive valuation on the Laurent-series field, with value `⊤`
at zero and the least nonzero exponent otherwise. -/
abbrev laurentOrder (k : Type*) [Field k] :
    AddValuation (LaurentSeries k) (WithTop ℤ) := HahnSeries.addVal ℤ k

/-- The literal Laurent-series fraction `c/T`, with `T = single 1 1`. -/
def laurentPoleOne (c : k) : LaurentSeries k :=
  HahnSeries.C c / HahnSeries.single (1 : ℤ) 1

@[simp] theorem laurentPoleOne_eq_single (c : k) :
    laurentPoleOne c = HahnSeries.single (-1 : ℤ) c := by
  simp only [laurentPoleOne, HahnSeries.C_apply, HahnSeries.single_div_single,
    zero_sub, div_one]

@[simp] theorem laurentPoleOne_zero : laurentPoleOne (0 : k) = 0 := by
  simp only [laurentPoleOne_eq_single, HahnSeries.single_eq_zero]

theorem laurentPoleOne_sub (c d : k) :
    laurentPoleOne (c - d) = laurentPoleOne c - laurentPoleOne d := by
  simp only [laurentPoleOne, map_sub, sub_div]

theorem laurentOrder_poleOne (c : k) (hc : c ≠ 0) :
    laurentOrder k (laurentPoleOne c) = ((-1 : ℤ) : WithTop ℤ) := by
  rw [laurentPoleOne_eq_single, HahnSeries.addVal_apply, HahnSeries.orderTop_single hc]

/-- The valuation-ring part stays in the valuation ring under `f ↦ f^n-f`. -/
theorem laurentOrder_pow_sub_nonnegative (n : ℕ) (f : LaurentSeries k)
    (hf : 0 ≤ laurentOrder k f) : 0 ≤ laurentOrder k (f ^ n - f) := by
  apply AddValuation.map_le_sub
  · rw [AddValuation.map_pow]
    exact nsmul_nonneg hf n
  · exact hf

/-- For a series with a pole, raising it to any integer power greater than one
strictly lowers its additive valuation. -/
theorem laurentOrder_pow_lt (n : ℕ) (hn : 1 < n) (f : LaurentSeries k)
    (hf : laurentOrder k f < 0) : laurentOrder k (f ^ n) < laurentOrder k f := by
  have hf0 : f ≠ 0 := by
    intro hz
    simp only [hz, laurentOrder, HahnSeries.addVal_apply, HahnSeries.orderTop_zero,
      not_top_lt] at hf
  have ho : f.order < 0 := by
    have h := hf
    rw [HahnSeries.addVal_apply_of_ne hf0, ← WithTop.coe_zero, WithTop.coe_lt_coe] at h
    exact h
  rw [HahnSeries.addVal_apply_of_ne (pow_ne_zero n hf0),
    HahnSeries.addVal_apply_of_ne hf0, WithTop.coe_lt_coe,
    HahnSeries.order_pow, nsmul_eq_mul]
  have hn' : (1 : ℤ) < n := by exact_mod_cast hn
  simpa only [one_mul] using mul_lt_mul_of_neg_right hn' ho

/-- Exact valuation of the difference: its two summands have distinct orders,
so their leading terms cannot cancel. This holds in any characteristic. -/
theorem laurentOrder_pow_sub_of_negative (n : ℕ) (hn : 1 < n) (f : LaurentSeries k)
    (hf : laurentOrder k f < 0) :
    laurentOrder k (f ^ n - f) = n • laurentOrder k f := by
  rw [AddValuation.map_sub_eq_of_lt_left _ (laurentOrder_pow_lt n hn f hf),
    AddValuation.map_pow]

/-- Every negative valuation of `f^n-f` is `n` times a negative integer. -/
theorem laurentOrder_pow_sub_negative_multiple (n : ℕ) (hn : 1 < n)
    (f : LaurentSeries k) (hf : laurentOrder k (f ^ n - f) < 0) :
    ∃ a : ℤ, a < 0 ∧
      laurentOrder k (f ^ n - f) = (((n : ℤ) * a : ℤ) : WithTop ℤ) := by
  have ho : laurentOrder k f < 0 := by
    by_contra h
    exact (not_lt_of_ge (laurentOrder_pow_sub_nonnegative n f (le_of_not_gt h))) hf
  have hf0 : f ≠ 0 := by
    intro hz
    simp only [hz, laurentOrder, HahnSeries.addVal_apply, HahnSeries.orderTop_zero,
      not_top_lt] at ho
  refine ⟨f.order, ?_, ?_⟩
  · have h := ho
    rw [HahnSeries.addVal_apply_of_ne hf0, ← WithTop.coe_zero, WithTop.coe_lt_coe] at h
    exact h
  · rw [laurentOrder_pow_sub_of_negative n hn f ho, HahnSeries.addVal_apply_of_ne hf0]
    simp only [← WithTop.coe_nsmul, nsmul_eq_mul]

/-- No Laurent series, including any infinite series in the completed field,
can be a primitive of a nonzero pole-one phase under `f ↦ f^n-f`, for `n>1`. -/
theorem laurentPoleOne_ne_pow_sub (n : ℕ) (hn : 1 < n) (c : k) (hc : c ≠ 0)
    (f : LaurentSeries k) : laurentPoleOne c ≠ f ^ n - f := by
  intro heq
  have hneg : laurentOrder k (f ^ n - f) < 0 := by
    rw [← heq, laurentOrder_poleOne c hc]
    exact WithTop.coe_lt_coe.mpr (by norm_num : (-1 : ℤ) < 0)
  obtain ⟨a, ha, hval⟩ := laurentOrder_pow_sub_negative_multiple n hn f hneg
  have he := congrArg (laurentOrder k) heq
  rw [laurentOrder_poleOne c hc, hval, WithTop.coe_eq_coe] at he
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  have hmul : (n : ℤ) * a ≤ 2 * a := mul_le_mul_of_nonpos_right hn' ha.le
  omega

/-- Distinct pole-one coefficients are distinct modulo every `f^n-f` image. -/
theorem laurentPoleOne_sub_ne_pow_sub (n : ℕ) (hn : 1 < n) (c d : k) (hcd : c ≠ d)
    (f : LaurentSeries k) : laurentPoleOne c - laurentPoleOne d ≠ f ^ n - f := by
  rw [← laurentPoleOne_sub]
  exact laurentPoleOne_ne_pow_sub n hn (c - d) (sub_ne_zero.mpr hcd) f

section PrimeCharacteristic

variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The actual additive Artin–Schreier map on the Laurent-series field. Its
additivity is obtained from the Frobenius homomorphism in characteristic p. -/
def laurentArtinSchreierMap : LaurentSeries k →+ LaurentSeries k := by
  letI : CharP (LaurentSeries k) p := charP_of_injective_ringHom
    (show Function.Injective (HahnSeries.C : k →+* LaurentSeries k) from
      HahnSeries.C_injective) p
  exact (frobenius (LaurentSeries k) p).toAddMonoidHom - AddMonoidHom.id _

@[simp] theorem laurentArtinSchreierMap_apply (f : LaurentSeries k) :
    laurentArtinSchreierMap p f = f ^ p - f := rfl

/-- Coefficients are mapped into the genuine additive quotient by the image
of the Artin–Schreier homomorphism. -/
def laurentPoleOneClass (c : k) :
    LaurentSeries k ⧸ (laurentArtinSchreierMap (k := k) p).range :=
  QuotientAddGroup.mk (laurentPoleOne c)

/-- Distinct coefficients define distinct Artin–Schreier classes even after
allowing all Laurent series as possible coboundaries. -/
theorem laurentPoleOneClass_injective : Function.Injective (laurentPoleOneClass (k := k) p) := by
  intro c d hcd
  by_contra hne
  have hmem : laurentPoleOne c - laurentPoleOne d ∈
      (laurentArtinSchreierMap (k := k) p).range :=
    QuotientAddGroup.eq_iff_sub_mem.mp hcd
  obtain ⟨f, hf⟩ := hmem
  exact (laurentPoleOne_sub_ne_pow_sub p (Fact.out : p.Prime).one_lt c d hne f)
    (by simpa only [laurentArtinSchreierMap_apply] using hf.symm)

theorem laurentPoleOneClass_eq_iff (c d : k) :
    laurentPoleOneClass p c = laurentPoleOneClass p d ↔ c = d :=
  (laurentPoleOneClass_injective p).eq_iff

@[simp] theorem laurentPoleOneClass_zero : laurentPoleOneClass p (0 : k) = 0 := by
  simp only [laurentPoleOneClass, laurentPoleOne_zero, QuotientAddGroup.mk_zero]

theorem laurentPoleOneClass_ne_zero (c : k) (hc : c ≠ 0) :
    laurentPoleOneClass p c ≠ 0 := by
  rw [← laurentPoleOneClass_zero (k := k) p]
  exact (laurentPoleOneClass_injective p).ne hc

/-- The prime-characteristic obstruction stated directly as a nonexistence
of a Laurent-series primitive. -/
theorem laurentPoleOne_not_artinSchreier (c : k) (hc : c ≠ 0) :
    ¬ ∃ f : LaurentSeries k, laurentPoleOne c = laurentArtinSchreierMap p f := by
  rintro ⟨f, hf⟩
  exact laurentPoleOne_ne_pow_sub p (Fact.out : p.Prime).one_lt c hc f hf

end PrimeCharacteristic

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.laurentOrder_pow_sub_of_negative
#print axioms PrimeGap182.TypeIII.laurentOrder_pow_sub_negative_multiple
#print axioms PrimeGap182.TypeIII.laurentPoleOne_ne_pow_sub
#print axioms PrimeGap182.TypeIII.laurentPoleOne_sub_ne_pow_sub

#print axioms PrimeGap182.TypeIII.laurentPoleOneClass_injective
#print axioms PrimeGap182.TypeIII.laurentPoleOneClass_ne_zero
#print axioms PrimeGap182.TypeIII.laurentPoleOne_not_artinSchreier
