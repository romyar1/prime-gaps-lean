import TypeIIIHenselianIdempotentLifting
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# The base maximal ideal in an integral algebra

For a commutative integral algebra over a local ring, contraction sends
every maximal ideal to the unique maximal ideal of the base.  Consequently
the extension of that base ideal lies in the actual Jacobson radical.

Reduction modulo this extended ideal is therefore injective on idempotents,
using the original quotient map from `HenselianIdempotentLifting`.  These
are uniqueness statements: no henselianity or existence of an idempotent
lift is assumed or concluded.  The algebra may be the zero ring; no
freeness or faithfulness hypothesis is needed.  Finite algebras specialize
the integral result through the proved finite-implies-integral instance.
-/

universe u v

namespace PrimeGap182.TypeIII.FiniteAlgebraJacobson

variable (R : Type u) [CommRing R] [IsLocalRing R]
  (A : Type v) [CommRing A] [Algebra R A]

section Integral

variable [Algebra.IsIntegral R A]

/-- The actual contraction of every maximal ideal is the unique base
maximal ideal. -/
theorem maximalIdeal_comap_eq (M : Ideal A) [M.IsMaximal] :
    M.comap (algebraMap R A) = IsLocalRing.maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) M)

/-- Every maximal ideal contains the extension of the base maximal ideal. -/
theorem maximalIdeal_map_le_maximal (M : Ideal A) [M.IsMaximal] :
    (IsLocalRing.maximalIdeal R).map (algebraMap R A) ≤ M :=
  Ideal.map_le_iff_le_comap.mpr (le_of_eq (maximalIdeal_comap_eq R A M).symm)

/-- The extended base maximal ideal lies in the actual intersection
of the maximal ideals of the integral algebra. -/
theorem maximalIdeal_map_le_jacobson :
    (IsLocalRing.maximalIdeal R).map (algebraMap R A) ≤ Ideal.jacobson ⊥ := by
  apply le_sInf
  rintro M ⟨_, hM⟩
  let : M.IsMaximal := hM
  exact maximalIdeal_map_le_maximal R A M

/-- The original quotient reduction is injective on idempotents without
any henselianity assumption on the algebra. -/
theorem idempotentReduction_injective :
    Function.Injective (HenselianIdempotentLifting.idempotentReduction A
      ((IsLocalRing.maximalIdeal R).map (algebraMap R A))) :=
  HenselianIdempotentLifting.idempotentReduction_injective_of_le_jacobson A _
    (maximalIdeal_map_le_jacobson R A)

end Integral

section Finite

variable [Module.Finite R A]

/-- The Jacobson inclusion for every finite commutative algebra over
the given local ring. -/
theorem maximalIdeal_map_le_jacobson_of_finite :
    (IsLocalRing.maximalIdeal R).map (algebraMap R A) ≤ Ideal.jacobson ⊥ :=
  maximalIdeal_map_le_jacobson R A

/-- The same original idempotent reduction is injective for finite
algebras, including nonfree and zero algebras. -/
theorem idempotentReduction_injective_of_finite :
    Function.Injective (HenselianIdempotentLifting.idempotentReduction A
      ((IsLocalRing.maximalIdeal R).map (algebraMap R A))) :=
  idempotentReduction_injective R A

end Finite

#print axioms maximalIdeal_comap_eq
#print axioms maximalIdeal_map_le_maximal
#print axioms maximalIdeal_map_le_jacobson
#print axioms idempotentReduction_injective
#print axioms maximalIdeal_map_le_jacobson_of_finite
#print axioms idempotentReduction_injective_of_finite

end PrimeGap182.TypeIII.FiniteAlgebraJacobson
