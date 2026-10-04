import TypeIIIPublishedTypeIII
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Algebraic coefficient automorphisms

Construct a coefficient-field automorphism with the required action on
the finite additive character. This is an algebraic field automorphism;
no continuity for the usual complex topology is asserted.
-/

noncomputable section

namespace PrimeGap182.TypeIII.CoefficientAutomorphism

/-- An automorphism of a subfield extends to an algebraically closed
overfield, using a transcendence basis and uniqueness of algebraic closure. -/
theorem exists_extension {K L : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] (e : K ≃+* K) :
    ∃ σ : L ≃+* L, ∀ x : K, σ (algebraMap K L x) = algebraMap K L (e x) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis (fun x : s => (x : L)) hs
  let a := hs.1.aevalEquiv
  let b : Algebra.adjoin K (Set.range (fun x : s => (x : L))) ≃+*
      Algebra.adjoin K (Set.range (fun x : s => (x : L))) :=
    a.symm.toRingEquiv.trans ((MvPolynomial.mapEquiv s e).trans a.toRingEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv L L b, ?_⟩
  intro x
  have hb : b (algebraMap K _ x) = algebraMap K _ (e x) := by
    change a (MvPolynomial.map e (a.symm (algebraMap K _ x))) = _
    rw [a.symm.commutes]
    change a (MvPolynomial.map e (MvPolynomial.C x)) = _
    rw [MvPolynomial.map_C]
    exact a.commutes (e x)
  rw [IsScalarTower.algebraMap_apply K (Algebra.adjoin K (Set.range (fun x : s => (x : L)))) L,
    IsAlgClosure.equivOfEquiv_algebraMap, hb,
    ← IsScalarTower.algebraMap_apply]

/-- The character value at one is a primitive root, directly from
injectivity of the standard additive character on ZMod. -/
theorem stdAddChar_one_primitive (p : ℕ) [Fact p.Prime] :
    IsPrimitiveRoot (ZMod.stdAddChar (1 : ZMod p)) p where
  pow_eq_one := by
    rw [← AddChar.map_nsmul_eq_pow]
    simp
  dvd_of_pow_eq_one n hn := by
    apply (ZMod.natCast_eq_zero_iff n p).mp
    apply ZMod.injective_stdAddChar
    simpa only [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_one,
      AddChar.map_zero_eq_one] using hn

/-- Choose an extension of the supplied coefficient automorphism, so
its action on every coefficient is retained, not merely its root action. -/
def extension (K L : Type*) [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] (e : K ≃+* K) : L ≃+* L :=
  (exists_extension (L := L) e).choose

theorem extension_spec (K L : Type*) [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] (e : K ≃+* K) (x : K) :
    extension K L e (algebraMap K L x) = algebraMap K L (e x) :=
  (exists_extension (L := L) e).choose_spec x

/-- All character values are powers of the value at one. -/
theorem map_stdAddChar_of_one (p : ℕ) [Fact p.Prime] (σ : ℂ ≃+* ℂ)
    (hσ : σ (ZMod.stdAddChar (1 : ZMod p)) = ZMod.stdAddChar (1 : ZMod p) ^ 2)
    (t : ZMod p) : σ (ZMod.stdAddChar t) = ZMod.stdAddChar (2 * t) := by
  have ht : ZMod.stdAddChar t = ZMod.stdAddChar (1 : ZMod p) ^ t.val := by
    simpa only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val] using
      (ZMod.stdAddChar (N := p)).map_nsmul_eq_pow t.val 1
  have htwo : ZMod.stdAddChar (2 * t) = ZMod.stdAddChar t ^ 2 := by
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using
      (ZMod.stdAddChar (N := p)).map_nsmul_eq_pow 2 t
  rw [ht, map_pow, hσ, htwo, ht]
  simp only [← pow_mul, Nat.mul_comm]

/-- A coefficient automorphism with the required root action gives the
same character action after extending the entire coefficient embedding. -/
theorem extension_doubling_spec (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [Algebra K ℂ] (τ : K ≃+* K) (ζ : K)
    (hζ : algebraMap K ℂ ζ = ZMod.stdAddChar (1 : ZMod p)) (hτ : τ ζ = ζ ^ 2)
    (t : ZMod p) :
    extension K ℂ τ (ZMod.stdAddChar t) = ZMod.stdAddChar (2 * t) := by
  apply map_stdAddChar_of_one p (extension K ℂ τ) _ t
  rw [← hζ, extension_spec, hτ, map_pow]

/-- Cyclotomic conjugacy first gives the automorphism on algebraic
numbers; the preceding extension theorem realizes it on the same ℂ. -/
theorem exists_square_primitive_root (p : ℕ) [Fact p.Prime] (hp : 3 < p)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ p) :
    ∃ σ : ℂ ≃+* ℂ, σ ζ = ζ ^ 2 := by
  let A := algebraicClosure ℚ ℂ
  let : IsAlgClosure ℚ A := algebraicClosure.isAlgClosure ℚ ℂ
  let z : A := ⟨ζ, mem_algebraicClosure_iff.mpr
    (((hζ.isIntegral (Fact.out : p.Prime).pos).tower_top (A := ℚ)).isAlgebraic)⟩
  have hz : IsPrimitiveRoot z p :=
    (show IsPrimitiveRoot (algebraMap A ℂ z) p from hζ).of_map_of_injective
      (algebraMap A ℂ).injective
  have hc : Nat.Coprime 2 p :=
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega))).symm
  have hirr := Polynomial.cyclotomic.irreducible_rat (Fact.out : p.Prime).pos
  have hconj : IsConjRoot ℚ (z ^ 2) z := isConjRoot_def.mpr
    (((hz.pow_of_coprime 2 hc).minpoly_eq_cyclotomic_of_irreducible hirr).symm.trans
      (hz.minpoly_eq_cyclotomic_of_irreducible hirr))
  obtain ⟨e, he⟩ := hconj.exists_algEquiv
  obtain ⟨σ, hσ⟩ := exists_extension (L := ℂ) e.toRingEquiv
  refine ⟨σ, ?_⟩
  have h := hσ z
  change σ ζ = algebraMap A ℂ (e z) at h
  simpa only [he, map_pow, IntermediateField.algebraMap_apply] using h

/-- The precise coefficient action required by the Type III covariance
argument exists for every prime greater than three. -/
theorem exists_doubling (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    ∃ σ : ℂ ≃+* ℂ, ∀ t : ZMod p,
      σ (ZMod.stdAddChar t) = ZMod.stdAddChar (2 * t) := by
  obtain ⟨σ, hσ⟩ := exists_square_primitive_root p hp _ (stdAddChar_one_primitive p)
  exact ⟨σ, map_stdAddChar_of_one p σ hσ⟩

/-- A fixed choice for the exact coefficient action, depending only on
the prime and its cutoff proof. No extra existence premise is required. -/
def doubling (p : ℕ) [Fact p.Prime] (hp : 3 < p) : ℂ ≃+* ℂ :=
  (exists_doubling p hp).choose

theorem doubling_spec (p : ℕ) [Fact p.Prime] (hp : 3 < p) (t : ZMod p) :
    doubling p hp (ZMod.stdAddChar t) = ZMod.stdAddChar (2 * t) :=
  (exists_doubling p hp).choose_spec t

end PrimeGap182.TypeIII.CoefficientAutomorphism

#print axioms PrimeGap182.TypeIII.CoefficientAutomorphism.exists_extension
#print axioms PrimeGap182.TypeIII.CoefficientAutomorphism.stdAddChar_one_primitive
#print axioms PrimeGap182.TypeIII.CoefficientAutomorphism.exists_square_primitive_root
#print axioms PrimeGap182.TypeIII.CoefficientAutomorphism.exists_doubling
#print axioms PrimeGap182.TypeIII.CoefficientAutomorphism.doubling
#print axioms PrimeGap182.TypeIII.CoefficientAutomorphism.doubling_spec
#print axioms PrimeGap182.TypeIII.CoefficientAutomorphism.extension
#print axioms PrimeGap182.TypeIII.CoefficientAutomorphism.extension_spec
#print axioms PrimeGap182.TypeIII.CoefficientAutomorphism.map_stdAddChar_of_one
#print axioms PrimeGap182.TypeIII.CoefficientAutomorphism.extension_doubling_spec
