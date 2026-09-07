import TypeIIIFiniteAlgebraClopenLifting
import TypeIIIIntegralAlgebraIdempotentLifting

/-!
# Clopens of integral algebras over a henselian local ring

For a commutative integral algebra A over a henselian local ring R,
inverse image along the original map Spec(A / m A) → Spec(A) is a
bijection and an order isomorphism on clopens.  The inverse agrees with
the actual integral-algebra idempotent lift under the original
idempotent/clopen correspondence.

The generic quotient bridge is applied to the proved bijectivity of
the original idempotent reduction.  No module finiteness, freeness,
nontriviality, locality, or henselianity of A is assumed.  These are
statements about the actual affine spectra and do not assert clopen
lifting on proper nonaffine schemes.
-/

noncomputable section

universe u v

namespace PrimeGap182.TypeIII.IntegralAlgebraClopenLifting

open TopologicalSpace

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  (A : Type v) [CommRing A] [Algebra R A] [Algebra.IsIntegral R A]

/-- The original clopen inverse-image map is bijective for every
integral algebra over the henselian local base. -/
theorem clopenReduction_bijective :
    Function.Bijective (HenselianIdempotentLifting.clopenReduction A
      ((IsLocalRing.maximalIdeal R).map (algebraMap R A))) :=
  FiniteAlgebraClopenLifting.clopenReduction_bijective_of_idempotentReduction_bijective A _
    (IntegralAlgebraIdempotentLifting.idempotentReduction_bijective R A)

/-- The actual inverse-image map on the original clopen types, packaged
as an order isomorphism. -/
def clopenReductionOrderIso :
    Clopens (PrimeSpectrum A) ≃o
      Clopens (PrimeSpectrum (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))) :=
  FiniteAlgebraClopenLifting.clopenReductionOrderIsoOfIdempotentReductionBijective A _
    (IntegralAlgebraIdempotentLifting.idempotentReduction_bijective R A)

/-- The forward map is literally the original clopen reduction. -/
theorem clopenReductionOrderIso_apply (U : Clopens (PrimeSpectrum A)) :
    clopenReductionOrderIso R A U = HenselianIdempotentLifting.clopenReduction A
      ((IsLocalRing.maximalIdeal R).map (algebraMap R A)) U := rfl

/-- Its carrier is the actual preimage under the original quotient
homomorphism's map on prime spectra. -/
theorem clopenReductionOrderIso_coe (U : Clopens (PrimeSpectrum A)) :
    (clopenReductionOrderIso R A U :
        Set (PrimeSpectrum (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)))) =
      PrimeSpectrum.comap
          (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A))) ⁻¹'
        (U : Set (PrimeSpectrum A)) := rfl

/-- The forward map retains the original idempotent/clopen correspondence. -/
theorem clopenReductionOrderIso_idempotent (a : {a : A // IsIdempotentElem a}) :
    clopenReductionOrderIso R A (PrimeSpectrum.isIdempotentElemEquivClopens a) =
      PrimeSpectrum.isIdempotentElemEquivClopens
        (IntegralAlgebraIdempotentLifting.idempotentReductionEquiv R A a) :=
  HenselianIdempotentLifting.clopenReduction_idempotent A _ a

/-- The inverse is a lift for the same original clopen pullback. -/
theorem clopenReductionOrderIso_symm_spec
    (U : Clopens
      (PrimeSpectrum (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)))) :
    HenselianIdempotentLifting.clopenReduction A
        ((IsLocalRing.maximalIdeal R).map (algebraMap R A))
        ((clopenReductionOrderIso R A).symm U) = U :=
  (clopenReductionOrderIso R A).apply_symm_apply U

/-- The inverse is exactly the clopen defined by the actual
integral-algebra idempotent lift. -/
theorem clopenReductionOrderIso_symm_idempotent
    (e : {e : A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A) //
      IsIdempotentElem e}) :
    (clopenReductionOrderIso R A).symm (PrimeSpectrum.isIdempotentElemEquivClopens e) =
      PrimeSpectrum.isIdempotentElemEquivClopens
        ((IntegralAlgebraIdempotentLifting.idempotentReductionEquiv R A).symm e) :=
  FiniteAlgebraClopenLifting.clopenReductionOrderIsoOfIdempotentReductionBijective_symm_idempotent
    A _ (IntegralAlgebraIdempotentLifting.idempotentReduction_bijective R A) e

/-- Each clopen of the actual residue spectrum has a unique lift. -/
theorem existsUnique_clopen_lift
    (U : Clopens
      (PrimeSpectrum (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)))) :
    ∃! V : Clopens (PrimeSpectrum A),
      HenselianIdempotentLifting.clopenReduction A
        ((IsLocalRing.maximalIdeal R).map (algebraMap R A)) V = U := by
  refine ⟨(clopenReductionOrderIso R A).symm U,
    clopenReductionOrderIso_symm_spec R A U, ?_⟩
  intro V hV
  exact (clopenReduction_bijective R A).injective
    (hV.trans (clopenReductionOrderIso_symm_spec R A U).symm)

#print axioms clopenReduction_bijective
#print axioms clopenReductionOrderIso
#print axioms clopenReductionOrderIso_apply
#print axioms clopenReductionOrderIso_coe
#print axioms clopenReductionOrderIso_idempotent
#print axioms clopenReductionOrderIso_symm_spec
#print axioms clopenReductionOrderIso_symm_idempotent
#print axioms existsUnique_clopen_lift

end PrimeGap182.TypeIII.IntegralAlgebraClopenLifting
