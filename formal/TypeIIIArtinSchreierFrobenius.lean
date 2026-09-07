import TypeIIIFiniteFieldCovariance

/-!
# Actual Artin--Schreier fibers and their Frobenius action

The geometric fiber consists of roots of `z^p - z = f`. Translation by the
prime field makes any nonempty fiber a torsor. Over a finite field, the
arithmetic Frobenius on these roots is translation by the field trace of
`f`. This fixes the sign needed when geometric Frobenius acts on functions
on the fiber: its induced action precomposes with arithmetic Frobenius.
-/

noncomputable section

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

/-- The telescoping identity behind the Artin--Schreier Frobenius action. -/
theorem artinSchreier_frobenius_telescoping (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [CharP R p] (z : R) (d : ℕ) :
    z ^ (p ^ d) - z = ∑ i ∈ Finset.range d, (z ^ p - z) ^ (p ^ i) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Finset.sum_range_succ, ← ih, sub_pow_char_pow, ← pow_mul, pow_succ']
      ring

/-- The roots of the literal Artin--Schreier equation in an extension field. -/
abbrev ArtinSchreierFiber (p : ℕ) (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]
    (f : K) := {z : Ω // z ^ p - z = algebraMap K Ω f}

section Fibers

variable (p : ℕ) [Fact p.Prime]
variable (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]
variable [CharP Ω p] [Algebra (ZMod p) Ω] (f : K)

/-- Translation of an actual root by a prime-field element. -/
def artinSchreierFiberTranslate (a : ZMod p) (z : ArtinSchreierFiber p K Ω f) :
    ArtinSchreierFiber p K Ω f :=
  ⟨(z : Ω) + algebraMap (ZMod p) Ω a, by
    have ha : (algebraMap (ZMod p) Ω a) ^ p = algebraMap (ZMod p) Ω a := by
      rw [← map_pow, ZMod.pow_card]
    rw [add_pow_char, ha]
    convert z.property using 1
    ring⟩

@[simp] theorem artinSchreierFiberTranslate_val (a : ZMod p)
    (z : ArtinSchreierFiber p K Ω f) :
    (artinSchreierFiberTranslate p K Ω f a z : Ω) =
      (z : Ω) + algebraMap (ZMod p) Ω a := rfl

@[simp] theorem artinSchreierFiberTranslate_zero (z : ArtinSchreierFiber p K Ω f) :
    artinSchreierFiberTranslate p K Ω f 0 z = z := by
  apply Subtype.ext
  simp only [artinSchreierFiberTranslate_val, map_zero, add_zero]

theorem artinSchreierFiberTranslate_add (a b : ZMod p)
    (z : ArtinSchreierFiber p K Ω f) :
    artinSchreierFiberTranslate p K Ω f (a + b) z =
      artinSchreierFiberTranslate p K Ω f a (artinSchreierFiberTranslate p K Ω f b z) := by
  apply Subtype.ext
  simp only [artinSchreierFiberTranslate_val, map_add]
  ring

/-- Translation is an actual permutation of the fiber. -/
def artinSchreierFiberTranslateEquiv (a : ZMod p) :
    ArtinSchreierFiber p K Ω f ≃ ArtinSchreierFiber p K Ω f where
  toFun := artinSchreierFiberTranslate p K Ω f a
  invFun := artinSchreierFiberTranslate p K Ω f (-a)
  left_inv z := by
    rw [← artinSchreierFiberTranslate_add, neg_add_cancel, artinSchreierFiberTranslate_zero]
  right_inv z := by
    rw [← artinSchreierFiberTranslate_add, add_neg_cancel, artinSchreierFiberTranslate_zero]

@[simp] theorem artinSchreierFiberTranslateEquiv_apply (a : ZMod p)
    (z : ArtinSchreierFiber p K Ω f) :
    artinSchreierFiberTranslateEquiv p K Ω f a z =
      artinSchreierFiberTranslate p K Ω f a z := rfl

theorem artinSchreierFiberTranslate_injective (z : ArtinSchreierFiber p K Ω f) :
    Function.Injective (fun a => artinSchreierFiberTranslate p K Ω f a z) := by
  intro a b hab
  have h := congrArg (fun z : ArtinSchreierFiber p K Ω f => (z : Ω)) hab
  simp only [artinSchreierFiberTranslate_val] at h
  exact (algebraMap (ZMod p) Ω).injective (add_left_cancel h)

/-- The difference of two roots is in the prime field, proving transitivity. -/
theorem artinSchreierFiberTranslate_surjective (z₀ : ArtinSchreierFiber p K Ω f) :
    Function.Surjective (fun a => artinSchreierFiberTranslate p K Ω f a z₀) := by
  intro z
  have hpw : ((z : Ω) - (z₀ : Ω)) ^ p = (z : Ω) - (z₀ : Ω) := by
    rw [sub_pow_char]
    linear_combination z.property - z₀.property
  have hb : (z : Ω) - (z₀ : Ω) ∈ (⊥ : Subfield Ω) :=
    (Subfield.mem_bot_iff_pow_eq_self Ω p).mpr hpw
  rw [← ZMod.fieldRange_castHom_eq_bot p] at hb
  obtain ⟨a, ha⟩ := RingHom.mem_fieldRange.mp hb
  have hmap : ZMod.castHom (dvd_refl p) Ω = algebraMap (ZMod p) Ω := Subsingleton.elim _ _
  rw [hmap] at ha
  refine ⟨a, Subtype.ext ?_⟩
  simp only [artinSchreierFiberTranslate_val]
  linear_combination ha

/-- A chosen root identifies the actual geometric fiber with the prime field. -/
def artinSchreierFiberEquiv (z₀ : ArtinSchreierFiber p K Ω f) :
    ZMod p ≃ ArtinSchreierFiber p K Ω f :=
  Equiv.ofBijective (fun a => artinSchreierFiberTranslate p K Ω f a z₀)
    ⟨artinSchreierFiberTranslate_injective p K Ω f z₀,
      artinSchreierFiberTranslate_surjective p K Ω f z₀⟩

@[simp] theorem artinSchreierFiberEquiv_apply (z₀ : ArtinSchreierFiber p K Ω f)
    (a : ZMod p) : artinSchreierFiberEquiv p K Ω f z₀ a =
      artinSchreierFiberTranslate p K Ω f a z₀ := rfl

theorem artinSchreierFiberCoordinate_translate (z₀ z : ArtinSchreierFiber p K Ω f)
    (a : ZMod p) :
    (artinSchreierFiberEquiv p K Ω f z₀).symm (artinSchreierFiberTranslate p K Ω f a z) =
      a + (artinSchreierFiberEquiv p K Ω f z₀).symm z := by
  apply (artinSchreierFiberEquiv p K Ω f z₀).injective
  rw [Equiv.apply_symm_apply, artinSchreierFiberEquiv_apply, artinSchreierFiberTranslate_add]
  congr 1
  exact ((artinSchreierFiberEquiv p K Ω f z₀).apply_symm_apply z).symm

end Fibers

section FiniteFieldFrobenius

variable (p : ℕ) [Fact p.Prime]
variable (K Ω : Type*) [Field K] [Fintype K] [Field Ω]
variable [Algebra (ZMod p) K] [CharP Ω p] [Algebra K Ω] [Algebra (ZMod p) Ω]
variable [IsScalarTower (ZMod p) K Ω]

/-- Arithmetic Frobenius minus identity on an actual root is the field trace. -/
theorem artinSchreier_pow_card_sub (f : K) (z : Ω)
    (hz : z ^ p - z = algebraMap K Ω f) :
    z ^ Fintype.card K - z = algebraMap (ZMod p) Ω (Algebra.trace (ZMod p) K f) := by
  have hcard : Fintype.card K = p ^ Module.finrank (ZMod p) K := by
    simpa only [ZMod.card] using (Module.card_eq_pow_finrank (K := ZMod p) (V := K))
  rw [hcard, artinSchreier_frobenius_telescoping, hz]
  simp_rw [← map_pow]
  rw [← map_sum, ← FiniteFieldSums.trace_eq_sum_prime_powers p K f,
    IsScalarTower.algebraMap_apply (ZMod p) K Ω]

/-- Arithmetic Frobenius on the actual roots, written as the proved trace
translation. Its power-map identification is given by the next theorem. -/
def artinSchreierArithmeticFrobenius (f : K) :
    ArtinSchreierFiber p K Ω f ≃ ArtinSchreierFiber p K Ω f :=
  artinSchreierFiberTranslateEquiv p K Ω f (Algebra.trace (ZMod p) K f)

omit [Fintype K] [IsScalarTower (ZMod p) K Ω] in
@[simp] theorem artinSchreierArithmeticFrobenius_eq_translate (f : K)
    (z : ArtinSchreierFiber p K Ω f) :
    artinSchreierArithmeticFrobenius p K Ω f z =
      artinSchreierFiberTranslate p K Ω f (Algebra.trace (ZMod p) K f) z := rfl

theorem artinSchreierArithmeticFrobenius_val (f : K)
    (z : ArtinSchreierFiber p K Ω f) :
    (artinSchreierArithmeticFrobenius p K Ω f z : Ω) = (z : Ω) ^ Fintype.card K := by
  simp only [artinSchreierArithmeticFrobenius_eq_translate, artinSchreierFiberTranslate_val]
  linear_combination -(artinSchreier_pow_card_sub p K Ω f (z : Ω) z.property)

end FiniteFieldFrobenius

#print axioms artinSchreier_frobenius_telescoping
#print axioms ArtinSchreierFiber
#print axioms artinSchreierFiberTranslate
#print axioms artinSchreierFiberTranslate_val
#print axioms artinSchreierFiberTranslate_zero
#print axioms artinSchreierFiberTranslate_add
#print axioms artinSchreierFiberTranslateEquiv
#print axioms artinSchreierFiberTranslateEquiv_apply
#print axioms artinSchreierFiberTranslate_injective
#print axioms artinSchreierFiberTranslate_surjective
#print axioms artinSchreierFiberEquiv
#print axioms artinSchreierFiberEquiv_apply
#print axioms artinSchreierFiberCoordinate_translate
#print axioms artinSchreier_pow_card_sub
#print axioms artinSchreierArithmeticFrobenius
#print axioms artinSchreierArithmeticFrobenius_eq_translate
#print axioms artinSchreierArithmeticFrobenius_val

end PrimeGap182.TypeIII
