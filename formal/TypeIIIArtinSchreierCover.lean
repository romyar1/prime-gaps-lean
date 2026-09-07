import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The actual finite étale Artin--Schreier algebra

For a commutative ring `R` of prime characteristic `p` and `f : R`, the
algebra here is the literal quotient `R[X]/(X^p-X-f)`.  Monicity supplies
the basis `1, x, ..., x^(p-1)`.  The derivative is `-1`, giving an explicit
standard étale presentation with localization polynomial `1`.  Its
canonical algebra isomorphism with the finite quotient proves étaleness
of the actual quotient, without assuming any geometric property.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open Polynomial
open scoped Classical

section Definitions

variable (p : ℕ) {R : Type*} [CommRing R]

/-- The literal Artin--Schreier polynomial. -/
def artinSchreierPolynomial (f : R) : R[X] := X ^ p - X - C f

/-- The actual finite quotient algebra, not an abstract covering interface. -/
abbrev ArtinSchreierCover (R : Type*) [CommRing R] (f : R) :=
  AdjoinRoot (artinSchreierPolynomial p f)

/-- The distinguished image of the polynomial variable in the quotient. -/
def artinSchreierRoot (f : R) : ArtinSchreierCover p R f :=
  AdjoinRoot.root (artinSchreierPolynomial p f)

/-- A direct identification with the displayed polynomial quotient. -/
def artinSchreierCover_quotientEquiv (f : R) :
    ArtinSchreierCover p R f ≃ₐ[R] R[X] ⧸ Ideal.span {X ^ p - X - C f} :=
  AlgEquiv.refl

/-- The distinguished root satisfies the defining equation exactly. -/
theorem artinSchreierRoot_relation (f : R) :
    artinSchreierRoot p f ^ p - artinSchreierRoot p f =
      algebraMap R (ArtinSchreierCover p R f) f := by
  have h : aeval (artinSchreierRoot p f) (artinSchreierPolynomial p f) = 0 := by
    simp only [artinSchreierRoot, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  simpa only [artinSchreierPolynomial, map_sub, map_pow, aeval_X, aeval_C,
    sub_eq_zero] using h

end Definitions

section PrimeCharacteristic

variable (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]

include p in
/-- Exact prime characteristic makes the coefficient ring nontrivial. -/
theorem artinSchreierBase_nontrivial : Nontrivial R :=
  CharP.nontrivial_of_char_ne_one (R := R) (Fact.out : p.Prime).ne_one

/-- The polynomial is monic over every commutative characteristic-`p` ring. -/
theorem artinSchreierPolynomial_monic (f : R) : (artinSchreierPolynomial p f).Monic := by
  let : Nontrivial R := artinSchreierBase_nontrivial p
  rw [artinSchreierPolynomial, sub_sub]
  apply monic_X_pow_sub
  rw [degree_X_add_C]
  exact_mod_cast (Fact.out : p.Prime).one_lt

/-- Its degree is exactly the prime `p`, including for non-domain rings. -/
theorem artinSchreierPolynomial_natDegree (f : R) :
    (artinSchreierPolynomial p f).natDegree = p := by
  let : Nontrivial R := artinSchreierBase_nontrivial p
  rw [artinSchreierPolynomial, sub_sub,
    natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
  rw [natDegree_X_add_C, natDegree_X_pow]
  exact (Fact.out : p.Prime).one_lt

omit [Fact p.Prime] in
/-- The actual formal derivative is the unit `-1`. -/
theorem artinSchreierPolynomial_derivative (f : R) :
    (artinSchreierPolynomial p f).derivative = -1 := by
  simp only [artinSchreierPolynomial, derivative_sub, derivative_X_pow,
    CharP.cast_eq_zero, map_zero, zero_mul, derivative_X, derivative_C, zero_sub, sub_zero]

/-- The monomial basis of the actual quotient, explicitly indexed by `Fin p`. -/
def artinSchreierCover_basis (f : R) :
    Module.Basis (Fin p) R (ArtinSchreierCover p R f) :=
  (AdjoinRoot.powerBasis' (artinSchreierPolynomial_monic p f)).basis.reindex
    (finCongr (artinSchreierPolynomial_natDegree p f))

/-- The basis is concretely `1, x, ..., x^(p-1)`. -/
theorem artinSchreierCover_basis_apply (f : R) (i : Fin p) :
    artinSchreierCover_basis p f i = artinSchreierRoot p f ^ (i : ℕ) := by
  rw [artinSchreierCover_basis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

/-- Freeness is obtained from the displayed basis. -/
theorem artinSchreierCover_free (f : R) : Module.Free R (ArtinSchreierCover p R f) :=
  Module.Free.of_basis (artinSchreierCover_basis p f)

/-- Finiteness is obtained from the same finite basis. -/
theorem artinSchreierCover_finite (f : R) : Module.Finite R (ArtinSchreierCover p R f) :=
  Module.Finite.of_basis (artinSchreierCover_basis p f)

/-- The exact free rank is `p`. -/
theorem artinSchreierCover_finrank (f : R) :
    Module.finrank R (ArtinSchreierCover p R f) = p := by
  let : Nontrivial R := artinSchreierBase_nontrivial p
  simpa only [Fintype.card_fin] using
    Module.finrank_eq_card_basis (artinSchreierCover_basis p f)

/-- The standard étale pair has localization polynomial `1`, and its
derivative Bézout identity is `(-1)*(-1) + f*0 = 1^0`. -/
def artinSchreierCover_standardEtalePair (f : R) : StandardEtalePair R where
  f := artinSchreierPolynomial p f
  monic_f := artinSchreierPolynomial_monic p f
  g := 1
  cond := ⟨-1, 0, 0, by rw [artinSchreierPolynomial_derivative]; simp⟩

/-- The standard étale presentation is canonically the finite polynomial
quotient itself: localizing away from `1` adds no new elements. -/
def artinSchreierCover_standardEtaleEquiv (f : R) :
    (artinSchreierCover_standardEtalePair p f).Ring ≃ₐ[R] ArtinSchreierCover p R f := by
  let P := artinSchreierCover_standardEtalePair p f
  have hroot : P.HasMap (artinSchreierRoot p f) := by
    constructor
    · change aeval (AdjoinRoot.root (artinSchreierPolynomial p f))
        (artinSchreierPolynomial p f) = 0
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    · change IsUnit (aeval (artinSchreierRoot p f) (1 : R[X]))
      simp only [map_one, isUnit_one]
  let toCover : P.Ring →ₐ[R] ArtinSchreierCover p R f := P.lift _ hroot
  let toStandard : ArtinSchreierCover p R f →ₐ[R] P.Ring :=
    AdjoinRoot.liftAlgHom (artinSchreierPolynomial p f) (Algebra.ofId R P.Ring)
      P.X P.hasMap_X.1
  have hforward : toCover P.X = artinSchreierRoot p f := P.lift_X _ hroot
  have hbackward : toStandard (artinSchreierRoot p f) = P.X :=
    AdjoinRoot.liftAlgHom_root (artinSchreierPolynomial p f)
      (Algebra.ofId R P.Ring) P.X P.hasMap_X.1
  refine AlgEquiv.ofAlgHom toCover toStandard ?_ ?_
  · apply AdjoinRoot.algHom_ext
    change toCover (toStandard (artinSchreierRoot p f)) = artinSchreierRoot p f
    rw [hbackward, hforward]
  · apply P.hom_ext
    change toStandard (toCover P.X) = P.X
    rw [hforward, hbackward]

/-- The actual finite quotient has an explicitly constructed standard
étale presentation. -/
theorem artinSchreierCover_isStandardEtale (f : R) :
    Algebra.IsStandardEtale R (ArtinSchreierCover p R f) :=
  Algebra.IsStandardEtale.of_equiv (artinSchreierCover_standardEtaleEquiv p f)

/-- The actual algebra `R[X]/(X^p-X-f)` is étale, proved from its derivative
and finite polynomial presentation. -/
theorem artinSchreierCover_etale (f : R) :
    Algebra.Etale R (ArtinSchreierCover p R f) :=
  Algebra.Etale.of_equiv (artinSchreierCover_standardEtaleEquiv p f)

/-- The construction is finite free of rank `p` and étale. -/
theorem artinSchreierCover_finite_free_etale (f : R) :
    Module.Finite R (ArtinSchreierCover p R f) ∧
      Module.Free R (ArtinSchreierCover p R f) ∧
      Module.finrank R (ArtinSchreierCover p R f) = p ∧
      Algebra.Etale R (ArtinSchreierCover p R f) :=
  ⟨artinSchreierCover_finite p f, artinSchreierCover_free p f,
    artinSchreierCover_finrank p f, artinSchreierCover_etale p f⟩

/-- Translation by a prime-field scalar preserves the defining polynomial. -/
theorem artinSchreierPolynomial_comp_translation (f : R) (a : ZMod p) :
    (artinSchreierPolynomial p f).comp (X + C (ZMod.castHom (dvd_refl p) R a)) =
      artinSchreierPolynomial p f := by
  have ha : (ZMod.castHom (dvd_refl p) R a) ^ p = ZMod.castHom (dvd_refl p) R a := by
    simp only [ZMod.castHom_apply, ZMod.cast_eq_val]
    exact map_natCast (frobenius R p) a.val
  rw [artinSchreierPolynomial, sub_comp, sub_comp, X_pow_comp, X_comp, C_comp,
    add_pow_char, ← map_pow, ha]
  ring

/-- The translated distinguished root is a root in the actual quotient. -/
theorem artinSchreierRoot_translation_aeval (f : R) (a : ZMod p) :
    aeval (artinSchreierRoot p f +
      algebraMap R (ArtinSchreierCover p R f) (ZMod.castHom (dvd_refl p) R a))
      (artinSchreierPolynomial p f) = 0 := by
  calc
    _ = aeval (artinSchreierRoot p f)
        ((artinSchreierPolynomial p f).comp (X + C (ZMod.castHom (dvd_refl p) R a))) := by
      rw [aeval_comp, map_add, aeval_X, aeval_C]
    _ = aeval (artinSchreierRoot p f) (artinSchreierPolynomial p f) :=
      congrArg (aeval (artinSchreierRoot p f)) (artinSchreierPolynomial_comp_translation p f a)
    _ = 0 := by simp only [artinSchreierRoot, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

/-- The quotient algebra homomorphism sending `x` to `x+a`. -/
def artinSchreierCover_translationHom (f : R) (a : ZMod p) :
    ArtinSchreierCover p R f →ₐ[R] ArtinSchreierCover p R f :=
  AdjoinRoot.liftAlgHom (artinSchreierPolynomial p f)
    (Algebra.ofId R (ArtinSchreierCover p R f))
    (artinSchreierRoot p f +
      algebraMap R (ArtinSchreierCover p R f) (ZMod.castHom (dvd_refl p) R a))
    (artinSchreierRoot_translation_aeval p f a)

/-- The action on the distinguished generator is exactly translation. -/
@[simp] theorem artinSchreierCover_translationHom_root (f : R) (a : ZMod p) :
    artinSchreierCover_translationHom p f a (artinSchreierRoot p f) =
      artinSchreierRoot p f +
        algebraMap R (ArtinSchreierCover p R f) (ZMod.castHom (dvd_refl p) R a) :=
  AdjoinRoot.liftAlgHom_root (artinSchreierPolynomial p f)
    (Algebra.ofId R (ArtinSchreierCover p R f)) _
    (artinSchreierRoot_translation_aeval p f a)

/-- The quotient translations satisfy the additive composition law. -/
theorem artinSchreierCover_translationHom_add (f : R) (a b : ZMod p) :
    (artinSchreierCover_translationHom p f a).comp
        (artinSchreierCover_translationHom p f b) =
      artinSchreierCover_translationHom p f (a + b) := by
  apply AdjoinRoot.algHom_ext
  change artinSchreierCover_translationHom p f a
      (artinSchreierCover_translationHom p f b (artinSchreierRoot p f)) =
    artinSchreierCover_translationHom p f (a + b) (artinSchreierRoot p f)
  simp only [artinSchreierCover_translationHom_root, map_add, AlgHom.commutes, add_assoc]

/-- Translation by zero is the identity on the quotient. -/
@[simp] theorem artinSchreierCover_translationHom_zero (f : R) :
    artinSchreierCover_translationHom p f 0 = AlgHom.id R (ArtinSchreierCover p R f) := by
  apply AdjoinRoot.algHom_ext
  change artinSchreierCover_translationHom p f 0 (artinSchreierRoot p f) =
    artinSchreierRoot p f
  simp only [artinSchreierCover_translationHom_root, map_zero, add_zero]

/-- The actual algebra automorphism `x ↦ x+a`, with inverse `x ↦ x-a`. -/
def artinSchreierCover_translation (f : R) (a : ZMod p) :
    ArtinSchreierCover p R f ≃ₐ[R] ArtinSchreierCover p R f :=
  AlgEquiv.ofAlgHom (artinSchreierCover_translationHom p f a)
    (artinSchreierCover_translationHom p f (-a))
    (by rw [artinSchreierCover_translationHom_add, add_neg_cancel,
      artinSchreierCover_translationHom_zero])
    (by rw [artinSchreierCover_translationHom_add, neg_add_cancel,
      artinSchreierCover_translationHom_zero])

/-- The automorphism has the advertised value on the quotient generator. -/
@[simp] theorem artinSchreierCover_translation_root (f : R) (a : ZMod p) :
    artinSchreierCover_translation p f a (artinSchreierRoot p f) =
      artinSchreierRoot p f +
        algebraMap R (ArtinSchreierCover p R f) (ZMod.castHom (dvd_refl p) R a) :=
  artinSchreierCover_translationHom_root p f a

end PrimeCharacteristic

#print axioms artinSchreierPolynomial
#print axioms ArtinSchreierCover
#print axioms artinSchreierRoot
#print axioms artinSchreierCover_quotientEquiv
#print axioms artinSchreierRoot_relation
#print axioms artinSchreierBase_nontrivial
#print axioms artinSchreierPolynomial_monic
#print axioms artinSchreierPolynomial_natDegree
#print axioms artinSchreierPolynomial_derivative
#print axioms artinSchreierCover_basis
#print axioms artinSchreierCover_basis_apply
#print axioms artinSchreierCover_free
#print axioms artinSchreierCover_finite
#print axioms artinSchreierCover_finrank
#print axioms artinSchreierCover_standardEtalePair
#print axioms artinSchreierCover_standardEtaleEquiv
#print axioms artinSchreierCover_isStandardEtale
#print axioms artinSchreierCover_etale
#print axioms artinSchreierCover_finite_free_etale
#print axioms artinSchreierPolynomial_comp_translation
#print axioms artinSchreierRoot_translation_aeval
#print axioms artinSchreierCover_translationHom
#print axioms artinSchreierCover_translationHom_root
#print axioms artinSchreierCover_translationHom_add
#print axioms artinSchreierCover_translationHom_zero
#print axioms artinSchreierCover_translation
#print axioms artinSchreierCover_translation_root

end PrimeGap182.TypeIII
