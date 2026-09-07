import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Finite torsion coefficient levels with compatible characters

The level n coefficient ring is the actual quotient
  (ZMod (ℓ^(n+1)))[X] / (cyclotomic p).
For distinct primes p and ℓ, it is a nontrivial finite ring, free of
rank p-1 over its displayed base ring. The image of X is a primitive
p-th root of unity and p is invertible.

Reduction of the base modulus induces actual homomorphisms of these
quotients. They preserve the distinguished roots and additive characters
and compose as a coefficient tower. These are finite coefficient rings;
no ℓ-adic cohomology or weight statement is asserted.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open Polynomial

/-- The finite base at level n starts at modulus ℓ, when n=0. -/
abbrev TorsionCoefficientBase (ell n : ℕ) := ZMod (ell ^ (n + 1))

/-- The actual cyclotomic quotient at level n. -/
abbrev TorsionCoefficientRing (p ell n : ℕ) :=
  AdjoinRoot (cyclotomic p (TorsionCoefficientBase ell n))

/-- The distinguished image of the variable in the actual quotient. -/
def torsionCoefficientRoot (p ell n : ℕ) : TorsionCoefficientRing p ell n :=
  AdjoinRoot.root (cyclotomic p (TorsionCoefficientBase ell n))

/-- Every base modulus in the tower is greater than one. -/
theorem torsionCoefficientModulus_one_lt (ell n : ℕ) [Fact ell.Prime] :
    1 < ell ^ (n + 1) :=
  one_lt_pow' (Fact.out : ell.Prime).one_lt (Nat.succ_ne_zero n)

instance torsionCoefficientBase_nontrivial (ell n : ℕ) [Fact ell.Prime] :
    Nontrivial (TorsionCoefficientBase ell n) :=
  ZMod.nontrivial_iff.mpr (ne_of_gt (torsionCoefficientModulus_one_lt ell n))

/-- The defining polynomial has its usual positive degree over the
nontrivial finite base, including when that base has zero divisors. -/
theorem torsionCoefficientPolynomial_natDegree (p ell n : ℕ)
    [Fact p.Prime] [Fact ell.Prime] :
    (cyclotomic p (TorsionCoefficientBase ell n)).natDegree = p - 1 := by
  rw [natDegree_cyclotomic, Nat.totient_prime (Fact.out : p.Prime)]

/-- The actual quotient has the displayed monomial basis. -/
def torsionCoefficientBasis (p ell n : ℕ) [Fact p.Prime] [Fact ell.Prime] :
    Module.Basis (Fin (p - 1)) (TorsionCoefficientBase ell n)
      (TorsionCoefficientRing p ell n) :=
  (AdjoinRoot.powerBasis' (cyclotomic.monic p (TorsionCoefficientBase ell n))).basis.reindex
    (finCongr (torsionCoefficientPolynomial_natDegree p ell n))

theorem torsionCoefficientBasis_apply (p ell n : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (i : Fin (p - 1)) :
    torsionCoefficientBasis p ell n i = torsionCoefficientRoot p ell n ^ (i : ℕ) := by
  rw [torsionCoefficientBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

instance torsionCoefficientRing_free (p ell n : ℕ) :
    Module.Free (TorsionCoefficientBase ell n) (TorsionCoefficientRing p ell n) :=
  (cyclotomic.monic p (TorsionCoefficientBase ell n)).free_adjoinRoot

instance torsionCoefficientRing_moduleFinite (p ell n : ℕ) :
    Module.Finite (TorsionCoefficientBase ell n) (TorsionCoefficientRing p ell n) :=
  (cyclotomic.monic p (TorsionCoefficientBase ell n)).finite_adjoinRoot

/-- The base injection is proved from monicity and positive degree. -/
theorem torsionCoefficientBase_injective (p ell n : ℕ)
    [Fact p.Prime] [Fact ell.Prime] :
    Function.Injective
      (algebraMap (TorsionCoefficientBase ell n) (TorsionCoefficientRing p ell n)) := by
  apply AdjoinRoot.of.injective_of_monic_of_degree_pos
    (cyclotomic.monic p (TorsionCoefficientBase ell n))
  rw [← natDegree_pos_iff_degree_pos, torsionCoefficientPolynomial_natDegree]
  exact Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt

instance torsionCoefficientRing_nontrivial (p ell n : ℕ)
    [Fact p.Prime] [Fact ell.Prime] : Nontrivial (TorsionCoefficientRing p ell n) :=
  Function.Injective.nontrivial (torsionCoefficientBase_injective p ell n)

/-- The displayed ℓ-power modulus is the exact characteristic. -/
instance torsionCoefficientRing_charP (p ell n : ℕ)
    [Fact p.Prime] [Fact ell.Prime] :
    CharP (TorsionCoefficientRing p ell n) (ell ^ (n + 1)) :=
  charP_of_injective_ringHom (torsionCoefficientBase_injective p ell n) _

/-- Finite generation over the finite base proves actual finiteness. -/
instance torsionCoefficientRing_finite (p ell n : ℕ) [Fact ell.Prime] :
    Finite (TorsionCoefficientRing p ell n) :=
  Module.finite_of_finite (TorsionCoefficientBase ell n)

/-- The free rank of the actual quotient is p-1. -/
theorem torsionCoefficientRing_finrank (p ell n : ℕ)
    [Fact p.Prime] [Fact ell.Prime] :
    Module.finrank (TorsionCoefficientBase ell n) (TorsionCoefficientRing p ell n) =
      p - 1 := by
  simpa only [Fintype.card_fin] using
    Module.finrank_eq_card_basis (torsionCoefficientBasis p ell n)

/-- The finite ring has the exact cardinality supplied by its basis. -/
theorem torsionCoefficientRing_card (p ell n : ℕ)
    [Fact p.Prime] [Fact ell.Prime] :
    Nat.card (TorsionCoefficientRing p ell n) = ell ^ ((n + 1) * (p - 1)) := by
  simpa only [Nat.card_fun, Nat.card_fin, TorsionCoefficientBase, Nat.card_zmod, pow_mul] using
    Nat.card_congr (torsionCoefficientBasis p ell n).equivFun.toEquiv

/-- Coprimality of the two primes makes p a unit in the actual
quotient, without any field or domain structure on the quotient. -/
theorem torsionCoefficient_p_isUnit (p ell n : ℕ)
    [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell) :
    IsUnit (p : TorsionCoefficientRing p ell n) := by
  have hcop : p.Coprime ell :=
    (Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : ell.Prime)).mpr hne
  have hu : IsUnit (p : TorsionCoefficientBase ell n) :=
    (ZMod.isUnit_iff_coprime p (ell ^ (n + 1))).mpr (hcop.pow_right (n + 1))
  simpa only [map_natCast] using
    hu.map (algebraMap (TorsionCoefficientBase ell n) (TorsionCoefficientRing p ell n))

/-- Cyclotomic divisibility proves the p-th power relation in the
literal quotient, without a primitive-root assumption. -/
theorem torsionCoefficientRoot_pow (p ell n : ℕ) :
    torsionCoefficientRoot p ell n ^ p = 1 := by
  have h := (AdjoinRoot.mk_eq_zero
    (f := cyclotomic p (TorsionCoefficientBase ell n))
    (g := X ^ p - 1)).mpr
      (cyclotomic.dvd_X_pow_sub_one p (TorsionCoefficientBase ell n))
  simpa only [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero,
    torsionCoefficientRoot] using h

/-- The root is not one: evaluating its defining polynomial at one
would force the unit p to vanish in a nontrivial ring. -/
theorem torsionCoefficientRoot_ne_one (p ell n : ℕ)
    [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell) :
    torsionCoefficientRoot p ell n ≠ 1 := by
  intro hroot
  have h := AdjoinRoot.eval₂_root (cyclotomic p (TorsionCoefficientBase ell n))
  change eval₂ _ (torsionCoefficientRoot p ell n) _ = 0 at h
  rw [hroot, eval₂_one_cyclotomic_prime] at h
  exact (torsionCoefficient_p_isUnit p ell n hne).ne_zero h

/-- Since p is prime, the nontrivial p-th root has exact order p. -/
theorem torsionCoefficientRoot_isPrimitive (p ell n : ℕ)
    [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell) :
    IsPrimitiveRoot (torsionCoefficientRoot p ell n) p := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp
      (orderOf_dvd_of_pow_eq_one (torsionCoefficientRoot_pow p ell n)) with h | h
  · exact False.elim (torsionCoefficientRoot_ne_one p ell n hne (orderOf_eq_one_iff.mp h))
  · exact h

/-- The additive character is the actual power of the distinguished
cyclotomic root at the canonical integer representative. -/
def torsionCoefficientChar (p ell n : ℕ) [Fact p.Prime] :
    AddChar (ZMod p) (TorsionCoefficientRing p ell n) :=
  AddChar.zmodChar p (torsionCoefficientRoot_pow p ell n)

@[simp] theorem torsionCoefficientChar_apply (p ell n : ℕ) [Fact p.Prime] (a : ZMod p) :
    torsionCoefficientChar p ell n a = torsionCoefficientRoot p ell n ^ a.val := rfl

/-- The constructed additive character is primitive, as a consequence
of the proved root order. -/
theorem torsionCoefficientChar_isPrimitive (p ell n : ℕ)
    [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell) :
    (torsionCoefficientChar p ell n).IsPrimitive :=
  AddChar.zmodChar_primitive_of_primitive_root p
    (torsionCoefficientRoot_isPrimitive p ell n hne)

/-- The actual reduction between the displayed ℓ-power base rings. -/
def torsionCoefficientBaseReduce (ell : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    TorsionCoefficientBase ell n →+* TorsionCoefficientBase ell m :=
  ZMod.castHom (pow_dvd_pow ell (Nat.add_le_add_right hmn 1))
    (TorsionCoefficientBase ell m)

theorem torsionCoefficientBaseReduce_surjective (ell : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    Function.Surjective (torsionCoefficientBaseReduce ell hmn) :=
  ZMod.castHom_surjective _

/-- Reduction of coefficients induces a homomorphism of the actual
cyclotomic quotients, because cyclotomic polynomials commute with ring maps. -/
def torsionCoefficientReduce (p ell : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    TorsionCoefficientRing p ell n →+* TorsionCoefficientRing p ell m :=
  AdjoinRoot.map (torsionCoefficientBaseReduce ell hmn)
    (cyclotomic p (TorsionCoefficientBase ell n))
    (cyclotomic p (TorsionCoefficientBase ell m))
    (by simp only [map_cyclotomic, dvd_refl])

@[simp] theorem torsionCoefficientReduce_root (p ell : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    torsionCoefficientReduce p ell hmn (torsionCoefficientRoot p ell n) =
      torsionCoefficientRoot p ell m := by
  simp only [torsionCoefficientReduce, torsionCoefficientRoot, AdjoinRoot.map_root]

/-- Reduction agrees with the actual coefficient reduction on the base. -/
theorem torsionCoefficientReduce_algebraMap (p ell : ℕ) {m n : ℕ} (hmn : m ≤ n)
    (r : TorsionCoefficientBase ell n) :
    torsionCoefficientReduce p ell hmn
        (algebraMap (TorsionCoefficientBase ell n) (TorsionCoefficientRing p ell n) r) =
      algebraMap (TorsionCoefficientBase ell m) (TorsionCoefficientRing p ell m)
        (torsionCoefficientBaseReduce ell hmn r) :=
  AdjoinRoot.map_of _ _ _ _ r

/-- Reduction of a polynomial class is represented by reducing each
of its coefficients. -/
theorem torsionCoefficientReduce_mk (p ell : ℕ) {m n : ℕ} (hmn : m ≤ n)
    (q : Polynomial (TorsionCoefficientBase ell n)) :
    torsionCoefficientReduce p ell hmn
        (AdjoinRoot.mk (cyclotomic p (TorsionCoefficientBase ell n)) q) =
      AdjoinRoot.mk (cyclotomic p (TorsionCoefficientBase ell m))
        (q.map (torsionCoefficientBaseReduce ell hmn)) := by
  have h : (torsionCoefficientReduce p ell hmn).comp
        (AdjoinRoot.mk (cyclotomic p (TorsionCoefficientBase ell n))) =
      (AdjoinRoot.mk (cyclotomic p (TorsionCoefficientBase ell m))).comp
        (Polynomial.mapRingHom (torsionCoefficientBaseReduce ell hmn)) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, AdjoinRoot.mk_C, Polynomial.coe_mapRingHom,
        Polynomial.map_C]
      exact torsionCoefficientReduce_algebraMap p ell hmn r
    · simp only [RingHom.comp_apply, AdjoinRoot.mk_X, Polynomial.coe_mapRingHom,
        Polynomial.map_X]
      exact torsionCoefficientReduce_root p ell hmn
  exact RingHom.congr_fun h q

/-- All transition maps in the coefficient tower are surjective. -/
theorem torsionCoefficientReduce_surjective (p ell : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    Function.Surjective (torsionCoefficientReduce p ell hmn) := by
  intro x
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨r, hr⟩ := Polynomial.map_surjective (torsionCoefficientBaseReduce ell hmn)
    (torsionCoefficientBaseReduce_surjective ell hmn) q
  refine ⟨AdjoinRoot.mk (cyclotomic p (TorsionCoefficientBase ell n)) r, ?_⟩
  rw [torsionCoefficientReduce_mk, hr]

/-- Successive reductions compose to the actual direct reduction. -/
theorem torsionCoefficientReduce_comp (p ell : ℕ) {k m n : ℕ}
    (hkm : k ≤ m) (hmn : m ≤ n) :
    (torsionCoefficientReduce p ell hkm).comp (torsionCoefficientReduce p ell hmn) =
      torsionCoefficientReduce p ell (hkm.trans hmn) := by
  apply AdjoinRoot.ringHom_ext
  · exact Subsingleton.elim _ _
  · simp only [RingHom.comp_apply, torsionCoefficientReduce, AdjoinRoot.map_root]

@[simp] theorem torsionCoefficientReduce_refl (p ell n : ℕ) :
    torsionCoefficientReduce p ell (le_refl n) = RingHom.id (TorsionCoefficientRing p ell n) := by
  apply AdjoinRoot.ringHom_ext
  · exact Subsingleton.elim _ _
  · exact torsionCoefficientReduce_root p ell (le_refl n)

/-- The actual additive characters are compatible with every reduction. -/
@[simp] theorem torsionCoefficientReduce_char (p ell : ℕ) [Fact p.Prime]
    {m n : ℕ} (hmn : m ≤ n) (a : ZMod p) :
    torsionCoefficientReduce p ell hmn (torsionCoefficientChar p ell n a) =
      torsionCoefficientChar p ell m a := by
  simp only [torsionCoefficientChar_apply, map_pow, torsionCoefficientReduce_root]

/-- Compatibility also holds as an equality of bundled additive characters. -/
theorem torsionCoefficientReduce_comp_char (p ell : ℕ) [Fact p.Prime]
    {m n : ℕ} (hmn : m ≤ n) :
    (torsionCoefficientReduce p ell hmn).toMonoidHom.compAddChar
        (torsionCoefficientChar p ell n) = torsionCoefficientChar p ell m := by
  ext a
  exact torsionCoefficientReduce_char p ell hmn a

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.TorsionCoefficientBase
#print axioms PrimeGap182.TypeIII.TorsionCoefficientRing
#print axioms PrimeGap182.TypeIII.torsionCoefficientRoot
#print axioms PrimeGap182.TypeIII.torsionCoefficientModulus_one_lt
#print axioms PrimeGap182.TypeIII.torsionCoefficientBase_nontrivial
#print axioms PrimeGap182.TypeIII.torsionCoefficientPolynomial_natDegree
#print axioms PrimeGap182.TypeIII.torsionCoefficientBasis
#print axioms PrimeGap182.TypeIII.torsionCoefficientBasis_apply
#print axioms PrimeGap182.TypeIII.torsionCoefficientRing_free
#print axioms PrimeGap182.TypeIII.torsionCoefficientRing_moduleFinite
#print axioms PrimeGap182.TypeIII.torsionCoefficientBase_injective
#print axioms PrimeGap182.TypeIII.torsionCoefficientRing_nontrivial
#print axioms PrimeGap182.TypeIII.torsionCoefficientRing_charP
#print axioms PrimeGap182.TypeIII.torsionCoefficientRing_finite
#print axioms PrimeGap182.TypeIII.torsionCoefficientRing_finrank
#print axioms PrimeGap182.TypeIII.torsionCoefficientRing_card
#print axioms PrimeGap182.TypeIII.torsionCoefficient_p_isUnit
#print axioms PrimeGap182.TypeIII.torsionCoefficientRoot_pow
#print axioms PrimeGap182.TypeIII.torsionCoefficientRoot_ne_one
#print axioms PrimeGap182.TypeIII.torsionCoefficientRoot_isPrimitive
#print axioms PrimeGap182.TypeIII.torsionCoefficientChar
#print axioms PrimeGap182.TypeIII.torsionCoefficientChar_apply
#print axioms PrimeGap182.TypeIII.torsionCoefficientChar_isPrimitive
#print axioms PrimeGap182.TypeIII.torsionCoefficientBaseReduce
#print axioms PrimeGap182.TypeIII.torsionCoefficientBaseReduce_surjective
#print axioms PrimeGap182.TypeIII.torsionCoefficientReduce
#print axioms PrimeGap182.TypeIII.torsionCoefficientReduce_root
#print axioms PrimeGap182.TypeIII.torsionCoefficientReduce_algebraMap
#print axioms PrimeGap182.TypeIII.torsionCoefficientReduce_mk
#print axioms PrimeGap182.TypeIII.torsionCoefficientReduce_surjective
#print axioms PrimeGap182.TypeIII.torsionCoefficientReduce_comp
#print axioms PrimeGap182.TypeIII.torsionCoefficientReduce_refl
#print axioms PrimeGap182.TypeIII.torsionCoefficientReduce_char
#print axioms PrimeGap182.TypeIII.torsionCoefficientReduce_comp_char
