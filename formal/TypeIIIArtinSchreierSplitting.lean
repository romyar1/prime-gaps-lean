import TypeIIIArtinSchreierCover
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.Quotient

/-!
# Splitting the actual Artin--Schreier algebra over a ring

If `z^p-z=f` in a commutative characteristic-`p` ring `S`, the literal
quotient `S[X]/(X^p-X-f)` is isomorphic as an `S`-algebra to `ZMod p → S`.
The component indexed by `a` evaluates `X` at `z+a`.  The factorization
over the prime field is transported to `S`; the differences of distinct
prime-field scalars are units even when `S` has zero divisors.  The
Chinese remainder theorem therefore applies to the actual factor ideals.
-/

noncomputable section

open Polynomial
open scoped BigOperators Classical Function

namespace PrimeGap182.TypeIII

variable (p : ℕ) [Fact p.Prime] (S : Type*) [CommRing S] [CharP S p]

/-- The prime-field factorization remains a polynomial identity over any
commutative ring of characteristic `p`. -/
theorem artinSchreierPolynomial_zero_factorization :
    artinSchreierPolynomial p (0 : S) =
      ∏ a : ZMod p, (X - C (ZMod.castHom (dvd_refl p) S a)) := by
  have hroots : (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val := by
    simpa only [ZMod.card] using FiniteField.roots_X_pow_card_sub_X (ZMod p)
  have hmonic : (X ^ p - X : (ZMod p)[X]).Monic := by
    simpa only [artinSchreierPolynomial, map_zero, sub_zero] using
      artinSchreierPolynomial_monic p (0 : ZMod p)
  have hcard : (X ^ p - X : (ZMod p)[X]).roots.card =
      (X ^ p - X : (ZMod p)[X]).natDegree := by
    rw [hroots, ← Finset.card_def, Finset.card_univ, ZMod.card,
      FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) (Fact.out : p.Prime).one_lt]
  have hprod : (∏ a : ZMod p, (X - C a)) = (X ^ p - X : (ZMod p)[X]) := by
    simpa only [hroots, Finset.prod] using
      prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
  have hm := congrArg (Polynomial.map (ZMod.castHom (dvd_refl p) S)) hprod
  simpa only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, artinSchreierPolynomial, map_zero, sub_zero] using hm.symm

/-- A chosen actual root translates the prime-field factorization. -/
theorem artinSchreierPolynomial_root_factorization (f z : S) (hz : z ^ p - z = f) :
    artinSchreierPolynomial p f =
      ∏ a : ZMod p, (X - C (z + ZMod.castHom (dvd_refl p) S a)) := by
  have hcomp : (artinSchreierPolynomial p (0 : S)).comp (X - C z) =
      artinSchreierPolynomial p f := by
    simp only [artinSchreierPolynomial, map_zero, sub_zero, sub_comp, X_pow_comp, X_comp,
      sub_pow_char, ← map_pow]
    rw [← hz, map_sub]
    ring
  rw [← hcomp, artinSchreierPolynomial_zero_factorization, prod_comp]
  apply Finset.prod_congr rfl
  intro a _
  rw [sub_comp, X_comp, C_comp, map_add]
  ring

/-- The actual principal ideal of the linear factor with root `z+a`. -/
def artinSchreierRootFactorIdeal (z : S) (a : ZMod p) : Ideal S[X] :=
  Ideal.span {X - C (z + ZMod.castHom (dvd_refl p) S a)}

/-- Distinct prime-field scalars have unit differences in `S`, so the
linear-factor ideals are pairwise coprime without a domain hypothesis. -/
theorem artinSchreierRootFactorIdeal_pairwise_isCoprime (z : S) :
    Pairwise (IsCoprime on artinSchreierRootFactorIdeal p S z) := by
  intro a b hab
  change IsCoprime
    (Ideal.span ({X - C (z + ZMod.castHom (dvd_refl p) S a)} : Set S[X]))
    (Ideal.span ({X - C (z + ZMod.castHom (dvd_refl p) S b)} : Set S[X]))
  rw [Ideal.isCoprime_span_singleton_iff]
  apply isCoprime_X_sub_C_of_isUnit_sub
  have hu : IsUnit (ZMod.castHom (dvd_refl p) S (a - b)) :=
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hab)).map (ZMod.castHom (dvd_refl p) S)
  convert hu using 1
  rw [map_sub]
  ring

/-- The defining ideal is the intersection of the pairwise coprime
linear-factor ideals. -/
theorem artinSchreierPolynomial_span_eq_iInf (f z : S) (hz : z ^ p - z = f) :
    Ideal.span {artinSchreierPolynomial p f} =
      ⨅ a : ZMod p, artinSchreierRootFactorIdeal p S z a := by
  rw [artinSchreierPolynomial_root_factorization p S f z hz,
    ← Ideal.prod_span_singleton]
  change (∏ a : ZMod p, artinSchreierRootFactorIdeal p S z a) = _
  simpa only [Finset.mem_univ, iInf_true] using
    Ideal.prod_eq_iInf_of_pairwise_isCoprime
      (s := Finset.univ) (J := artinSchreierRootFactorIdeal p S z)
      (fun a _ b _ hab => artinSchreierRootFactorIdeal_pairwise_isCoprime p S z hab)

/-- The actual Chinese remainder isomorphism, followed by evaluation in
each linear-factor quotient. -/
def artinSchreierCover_splitRingEquiv (f z : S) (hz : z ^ p - z = f) :
    ArtinSchreierCover p S f ≃+* (ZMod p → S) :=
  ((Ideal.quotEquivOfEq (artinSchreierPolynomial_span_eq_iInf p S f z hz)).trans
    (Ideal.quotientInfRingEquivPiQuotient (artinSchreierRootFactorIdeal p S z)
      (artinSchreierRootFactorIdeal_pairwise_isCoprime p S z))).trans
    (RingEquiv.piCongrRight fun a =>
      (quotientSpanXSubCAlgEquiv (z + ZMod.castHom (dvd_refl p) S a)).toRingEquiv)

/-- Each CRT component evaluates a polynomial representative at `z+a`. -/
@[simp] theorem artinSchreierCover_splitRingEquiv_mk
    (f z : S) (hz : z ^ p - z = f) (q : S[X]) (a : ZMod p) :
    artinSchreierCover_splitRingEquiv p S f z hz
        (AdjoinRoot.mk (artinSchreierPolynomial p f) q) a =
      q.eval (z + ZMod.castHom (dvd_refl p) S a) := rfl

/-- Given an actual root in a commutative characteristic-`p` ring, the
Artin--Schreier quotient is the product of `p` copies of that ring. -/
def artinSchreierCover_splitEquiv (f z : S) (hz : z ^ p - z = f) :
    ArtinSchreierCover p S f ≃ₐ[S] (ZMod p → S) where
  __ := artinSchreierCover_splitRingEquiv p S f z hz
  commutes' s := by
    funext a
    change artinSchreierCover_splitRingEquiv p S f z hz
      (AdjoinRoot.mk (artinSchreierPolynomial p f) (C s)) a = s
    rw [artinSchreierCover_splitRingEquiv_mk, eval_C]

/-- The algebra isomorphism is the same explicit evaluation map. -/
@[simp] theorem artinSchreierCover_splitEquiv_mk
    (f z : S) (hz : z ^ p - z = f) (q : S[X]) (a : ZMod p) :
    artinSchreierCover_splitEquiv p S f z hz
        (AdjoinRoot.mk (artinSchreierPolynomial p f) q) a =
      q.eval (z + ZMod.castHom (dvd_refl p) S a) :=
  artinSchreierCover_splitRingEquiv_mk p S f z hz q a

/-- The generator is sent to the function `a ↦ z+a`. -/
@[simp] theorem artinSchreierCover_splitEquiv_root
    (f z : S) (hz : z ^ p - z = f) (a : ZMod p) :
    artinSchreierCover_splitEquiv p S f z hz (artinSchreierRoot p f) a =
      z + ZMod.castHom (dvd_refl p) S a := by
  change artinSchreierCover_splitEquiv p S f z hz
    (AdjoinRoot.mk (artinSchreierPolynomial p f) X) a = _
  rw [artinSchreierCover_splitEquiv_mk, eval_X]

/-- In particular the zero-parameter Artin--Schreier cover splits without
any chosen-root hypothesis. -/
def artinSchreierCover_zeroSplitEquiv :
    ArtinSchreierCover p S 0 ≃ₐ[S] (ZMod p → S) :=
  artinSchreierCover_splitEquiv p S 0 0
    (by rw [zero_pow (Fact.out : p.Prime).ne_zero, sub_self])

@[simp] theorem artinSchreierCover_zeroSplitEquiv_root (a : ZMod p) :
    artinSchreierCover_zeroSplitEquiv p S (artinSchreierRoot p (0 : S)) a =
      ZMod.castHom (dvd_refl p) S a := by
  simp only [artinSchreierCover_zeroSplitEquiv, artinSchreierCover_splitEquiv_root, zero_add]

/-- The same zero-parameter splitting with the polynomial written
literally as `X^p-X`. -/
def artinSchreierZero_adjoinRootEquiv :
    AdjoinRoot (X ^ p - X : S[X]) ≃ₐ[S] (ZMod p → S) := by
  refine (Ideal.quotientEquivAlgOfEq S ?_).trans (artinSchreierCover_zeroSplitEquiv p S)
  simp only [artinSchreierPolynomial, C_0, sub_zero]

#print axioms artinSchreierPolynomial_zero_factorization
#print axioms artinSchreierPolynomial_root_factorization
#print axioms artinSchreierRootFactorIdeal
#print axioms artinSchreierRootFactorIdeal_pairwise_isCoprime
#print axioms artinSchreierPolynomial_span_eq_iInf
#print axioms artinSchreierCover_splitRingEquiv
#print axioms artinSchreierCover_splitRingEquiv_mk
#print axioms artinSchreierCover_splitEquiv
#print axioms artinSchreierCover_splitEquiv_mk
#print axioms artinSchreierCover_splitEquiv_root
#print axioms artinSchreierCover_zeroSplitEquiv
#print axioms artinSchreierCover_zeroSplitEquiv_root
#print axioms artinSchreierZero_adjoinRootEquiv

end PrimeGap182.TypeIII
