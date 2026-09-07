import TypeIIICoprimeIdempotentLifting
import TypeIIIFiniteAlgebraAnnihilator
import TypeIIIFiniteAlgebraJacobson
import TypeIIIHenselianFactorizationLifting
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Idempotents in finite algebras over a henselian local ring

For every finite commutative algebra A over a henselian local ring R,
the original quotient map A -> A / m A is a bijection on idempotents.
The algebra A need not be free, faithful, nonzero, or local.

Given a lift a of a residue idempotent, finite-module Cayley–Hamilton
produces a monic annihilator F of a(a-1) with residue X^N, N > 0.
The actual henselian factorization theorem lifts the coprime factors
X^N and (X-1)^N of F(X(X-1)).  Their evaluations at a have zero product
and an actual Bézout identity, which constructs the desired idempotent.
Uniqueness uses the proved inclusion m A in the Jacobson radical.

No henselianity of A or idempotent-lifting premise is assumed.  This is
an algebraic result and does not assert clopen lifting on a proper
nonaffine scheme.
-/

noncomputable section

universe u v

namespace PrimeGap182.TypeIII.FiniteAlgebraIdempotentLifting

open Polynomial IsLocalRing

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

/-- The actual henselian factorization of F(X(X-1)) has the prescribed
two residue factors, with no hypothesis asserting that lifts exist. -/
theorem exists_coprime_factors {N : ℕ} (F : MonicDegreeEq R N)
    (hF : F.1.map (residue R) = X ^ N) :
    ∃ g h : R[X], g * h = F.1.comp (X * (X - 1)) ∧ IsCoprime g h ∧
      g.map (residue R) = X ^ N ∧ h.map (residue R) = (X - 1) ^ N := by
  have hm : (X * (X - 1) : R[X]).Monic :=
    monic_X.mul (monic_X_sub_C (1 : R))
  have hd : (X * (X - 1) : R[X]).natDegree = 2 := by
    change (X * (X - C (1 : R)) : R[X]).natDegree = 2
    rw [(monic_X : (X : R[X]).Monic).natDegree_mul (monic_X_sub_C (1 : R)),
      natDegree_X, natDegree_X_sub_C]
  have hp : (F.1.comp (X * (X - 1))).Monic :=
    F.monic.comp hm (by rw [hd]; decide)
  have hpd : (F.1.comp (X * (X - 1))).natDegree = N + N := by
    rw [natDegree_comp_eq_of_mul_ne_zero (by simp [F.monic.leadingCoeff, hm.leadingCoeff]),
      F.natDegree, hd, Nat.mul_two]
  let p : MonicDegreeEq R (N + N) := MonicDegreeEq.mk _ hp hpd
  let q₁ : MonicDegreeEq (ResidueField R) N :=
    MonicDegreeEq.mk (X ^ N) (monic_X.pow N) (natDegree_X_pow N)
  let q₂ : MonicDegreeEq (ResidueField R) N :=
    MonicDegreeEq.mk ((X - 1) ^ N) ((monic_X_sub_C (1 : ResidueField R)).pow N)
      (by
        change ((X - C (1 : ResidueField R)) ^ N).natDegree = N
        rw [(monic_X_sub_C (1 : ResidueField R)).natDegree_pow, natDegree_X_sub_C,
          mul_one])
  have hq : q₁.1 * q₂.1 = p.1.map (algebraMap R (ResidueField R)) := by
    change X ^ N * (X - 1) ^ N = (F.1.comp (X * (X - 1))).map (residue R)
    simp [Polynomial.map_comp, hF, mul_pow]
  have hc : IsCoprime q₁.1 q₂.1 := by
    have h : IsCoprime (X : (ResidueField R)[X]) (X - 1) := by
      refine ⟨1, -1, ?_⟩
      ring
    exact h.pow
  let q : HenselianFactorizationLifting.CoprimeFactorization (ResidueField R) N N p :=
    ⟨(q₁, q₂), hq, hc⟩
  refine ⟨(HenselianFactorizationLifting.lift p q).1.1.1,
    (HenselianFactorizationLifting.lift p q).1.2.1,
    HenselianFactorizationLifting.lift_mul p q,
    HenselianFactorizationLifting.lift_isCoprime p q,
    HenselianFactorizationLifting.lift_fst_reduction p q,
    HenselianFactorizationLifting.lift_snd_reduction p q⟩

variable (R) (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A]

/-- Every idempotent of A / m A lifts to an actual idempotent of A. -/
theorem exists_idempotent_lift
    (e : A ⧸ (maximalIdeal R).map (algebraMap R A)) (he : IsIdempotentElem e) :
    ∃ a : A, IsIdempotentElem a ∧
      Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R A)) a = e := by
  let I : Ideal A := (maximalIdeal R).map (algebraMap R A)
  let r : A →+* A ⧸ I := Ideal.Quotient.mk I
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective e
  change (Ideal.Quotient.mk I) a = e at ha
  have hx : a * (a - 1) ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul, map_sub, map_one, ha, mul_sub, he.eq, mul_one, sub_self]
  obtain ⟨N, hN, F, hzero, hmap⟩ :=
    FiniteAlgebraAnnihilator.exists_positive_monicDegreeEq_annihilator
      (maximalIdeal R) (a * (a - 1)) hx
  obtain ⟨g, h, hprod, hcop, hg, hh⟩ := exists_coprime_factors F hmap
  have hprod' : aeval a g * aeval a h = 0 := by
    rw [← aeval_mul, hprod, aeval_comp]
    simpa using hzero
  let : Algebra (ResidueField R) (A ⧸ I) :=
    Ideal.Quotient.algebraQuotientOfLEComap (p := maximalIdeal R) (P := I)
      Ideal.le_comap_map
  have hcoeff : (algebraMap (ResidueField R) (A ⧸ I)).comp (residue R) =
      r.comp (algebraMap R A) :=
    Ideal.quotientMap_comp_mk (f := algebraMap R A) Ideal.le_comap_map
  have hg' : r (aeval a g) = e ^ N := by
    rw [map_aeval_eq_aeval_map hcoeff, hg]
    simpa [r] using congrArg (fun b => b ^ N) ha
  have hh' : r (aeval a h) = (e - 1) ^ N := by
    rw [map_aeval_eq_aeval_map hcoeff, hh]
    simpa [r] using congrArg (fun b => (b - 1) ^ N) ha
  exact CoprimeIdempotentLifting.exists_lift_of_powers r e
    (hcop.map (aeval a).toRingHom) hprod' N hN he hg' hh'

/-- The original idempotent reduction is surjective for finite algebras
over the henselian local base. -/
theorem idempotentReduction_surjective :
    Function.Surjective (HenselianIdempotentLifting.idempotentReduction A
      ((maximalIdeal R).map (algebraMap R A))) := by
  intro e
  obtain ⟨a, ha, hae⟩ := exists_idempotent_lift R A e.1 e.2
  exact ⟨⟨a, ha⟩, Subtype.ext hae⟩

/-- The actual quotient-map reduction is bijective on idempotents. -/
theorem idempotentReduction_bijective :
    Function.Bijective (HenselianIdempotentLifting.idempotentReduction A
      ((maximalIdeal R).map (algebraMap R A))) :=
  ⟨FiniteAlgebraJacobson.idempotentReduction_injective_of_finite R A,
    idempotentReduction_surjective R A⟩

/-- The equivalence packages the original reduction, without changing
either the algebra or its specified residue quotient. -/
def idempotentReductionEquiv :
    {a : A // IsIdempotentElem a} ≃
      {e : A ⧸ (maximalIdeal R).map (algebraMap R A) // IsIdempotentElem e} :=
  Equiv.ofBijective (HenselianIdempotentLifting.idempotentReduction A _)
    (idempotentReduction_bijective R A)

/-- The forward equivalence is the actual quotient-map reduction. -/
theorem idempotentReductionEquiv_apply (a : {a : A // IsIdempotentElem a}) :
    idempotentReductionEquiv R A a = HenselianIdempotentLifting.idempotentReduction A
      ((maximalIdeal R).map (algebraMap R A)) a := rfl

/-- The inverse gives an idempotent with exactly the prescribed residue. -/
theorem idempotentReductionEquiv_symm_spec
    (e : {e : A ⧸ (maximalIdeal R).map (algebraMap R A) // IsIdempotentElem e}) :
    Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R A))
      ((idempotentReductionEquiv R A).symm e).1 = e.1 :=
  congrArg Subtype.val ((idempotentReductionEquiv R A).apply_symm_apply e)

/-- Each idempotent of the original quotient has a unique idempotent lift. -/
theorem existsUnique_idempotent_lift
    (e : A ⧸ (maximalIdeal R).map (algebraMap R A)) (he : IsIdempotentElem e) :
    ∃! a : A, IsIdempotentElem a ∧
      Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R A)) a = e := by
  obtain ⟨a, ha, hae⟩ := exists_idempotent_lift R A e he
  refine ⟨a, ⟨ha, hae⟩, ?_⟩
  intro b hb
  exact congrArg Subtype.val ((idempotentReduction_bijective R A).injective
    (show HenselianIdempotentLifting.idempotentReduction A _ ⟨b, hb.1⟩ =
      HenselianIdempotentLifting.idempotentReduction A _ ⟨a, ha⟩ from
      Subtype.ext (hb.2.trans hae.symm)))

#print axioms exists_coprime_factors
#print axioms exists_idempotent_lift
#print axioms idempotentReduction_surjective
#print axioms idempotentReduction_bijective
#print axioms idempotentReductionEquiv
#print axioms idempotentReductionEquiv_apply
#print axioms idempotentReductionEquiv_symm_spec
#print axioms existsUnique_idempotent_lift

end PrimeGap182.TypeIII.FiniteAlgebraIdempotentLifting
