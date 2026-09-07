import TypeIIIFiniteAlgebraIdempotentLifting
import TypeIIIIntegralAlgebraFiniteDescent

/-!
# Idempotents in integral algebras over a henselian local ring

The original quotient map A -> A / m A is a bijection on idempotents
for every commutative integral algebra over a henselian local ring R.
Finite descent retains both a representative a and the coefficients
witnessing a(a-1) in m A.  The proved finite-algebra lifting theorem
then transports through the actual finite subalgebra inclusion.

The residue condition is expressed in the original ambient quotient,
using the literal extension of the base maximal ideal.  No finiteness,
freeness, nontriviality, localness, or henselianity is assumed for A.
This proves the idempotent statement without asserting a simple-root
lifting theorem for A or proper nonaffine clopen lifting.
-/

noncomputable section

universe u v

namespace PrimeGap182.TypeIII.IntegralAlgebraIdempotentLifting

open IsLocalRing

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  (A : Type v) [CommRing A] [Algebra R A]

/-- A finite subalgebra containing the idempotence relation gives an
idempotent lift with the correct image in the original ambient quotient. -/
theorem exists_lift_from_finite_subalgebra (B : Subalgebra R A) [Module.Finite R B]
    (b : B) (hb : b * (b - 1) ∈ (maximalIdeal R).map (algebraMap R B)) :
    ∃ c : A, IsIdempotentElem c ∧
      Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R A)) c =
        Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R A)) (b : A) := by
  have he : IsIdempotentElem
      (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R B)) b) := by
    have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr hb
    rw [map_mul, map_sub, map_one, mul_sub, mul_one] at hzero
    exact sub_eq_zero.mp hzero
  obtain ⟨c, hc, hcb⟩ := FiniteAlgebraIdempotentLifting.exists_idempotent_lift R B
    (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R B)) b) he
  have hmem : c - b ∈ (maximalIdeal R).map (algebraMap R B) :=
    Ideal.Quotient.eq.mp hcb
  have hmemA : (c : A) - (b : A) ∈ (maximalIdeal R).map (algebraMap R A) := by
    have h := Ideal.mem_map_of_mem B.val.toRingHom hmem
    have hcomp : B.val.toRingHom.comp (algebraMap R B) = algebraMap R A := by
      ext t
      rfl
    rw [Ideal.map_map, hcomp] at h
    exact h
  exact ⟨(c : A), hc.map B.val, Ideal.Quotient.eq.mpr hmemA⟩

variable [Algebra.IsIntegral R A]

/-- Every idempotent in the original residue quotient of an integral
algebra lifts, using its finite coefficient witness and finite lifting. -/
theorem exists_idempotent_lift
    (e : A ⧸ (maximalIdeal R).map (algebraMap R A)) (he : IsIdempotentElem e) :
    ∃ a : A, IsIdempotentElem a ∧
      Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R A)) a = e := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective e
  have hx : a * (a - 1) ∈ (maximalIdeal R).map (algebraMap R A) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul, map_sub, map_one, ha, mul_sub, he.eq, mul_one, sub_self]
  obtain ⟨B, hB, b, hba, hb⟩ :=
    IntegralAlgebraFiniteDescent.exists_finite_subalgebra (maximalIdeal R) a hx
  let : Module.Finite R B := hB
  obtain ⟨c, hc, hcb⟩ := exists_lift_from_finite_subalgebra R A B b hb
  exact ⟨c, hc, by rw [hcb, hba, ha]⟩

/-- The original reduction of idempotents is surjective for every
integral algebra over the henselian local base. -/
theorem idempotentReduction_surjective :
    Function.Surjective (HenselianIdempotentLifting.idempotentReduction A
      ((maximalIdeal R).map (algebraMap R A))) := by
  intro e
  obtain ⟨a, ha, hae⟩ := exists_idempotent_lift R A e.1 e.2
  exact ⟨⟨a, ha⟩, Subtype.ext hae⟩

/-- The same original reduction is bijective; uniqueness is the
integral-algebra Jacobson result, with no additional lifting assumption. -/
theorem idempotentReduction_bijective :
    Function.Bijective (HenselianIdempotentLifting.idempotentReduction A
      ((maximalIdeal R).map (algebraMap R A))) :=
  ⟨FiniteAlgebraJacobson.idempotentReduction_injective R A,
    idempotentReduction_surjective R A⟩

/-- The equivalence has the original quotient reduction as forward map. -/
def idempotentReductionEquiv :
    {a : A // IsIdempotentElem a} ≃
      {e : A ⧸ (maximalIdeal R).map (algebraMap R A) // IsIdempotentElem e} :=
  Equiv.ofBijective (HenselianIdempotentLifting.idempotentReduction A _)
    (idempotentReduction_bijective R A)

/-- The forward equivalence is exactly the existing reduction function. -/
theorem idempotentReductionEquiv_apply (a : {a : A // IsIdempotentElem a}) :
    idempotentReductionEquiv R A a = HenselianIdempotentLifting.idempotentReduction A
      ((maximalIdeal R).map (algebraMap R A)) a := rfl

/-- The inverse has precisely the prescribed residue in A / m A. -/
theorem idempotentReductionEquiv_symm_spec
    (e : {e : A ⧸ (maximalIdeal R).map (algebraMap R A) // IsIdempotentElem e}) :
    Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R A))
      ((idempotentReductionEquiv R A).symm e).1 = e.1 :=
  congrArg Subtype.val ((idempotentReductionEquiv R A).apply_symm_apply e)

/-- Every specified residue idempotent of an integral algebra has a
unique lift under the original quotient homomorphism. -/
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

#print axioms exists_lift_from_finite_subalgebra
#print axioms exists_idempotent_lift
#print axioms idempotentReduction_surjective
#print axioms idempotentReduction_bijective
#print axioms idempotentReductionEquiv
#print axioms idempotentReductionEquiv_apply
#print axioms idempotentReductionEquiv_symm_spec
#print axioms existsUnique_idempotent_lift

end PrimeGap182.TypeIII.IntegralAlgebraIdempotentLifting
