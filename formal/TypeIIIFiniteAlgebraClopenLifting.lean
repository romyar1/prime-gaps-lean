import TypeIIIFiniteAlgebraIdempotentLifting

/-!
# Clopens of finite algebras over a henselian local ring

For a finite commutative algebra A over a henselian local ring R, the
original inverse-image map on clopens along Spec(A / m A) → Spec(A) is
bijective and an order isomorphism.  Its inverse agrees with the proved
unique lift of the idempotent defining the given clopen.

A generic bridge first transfers bijectivity of the original idempotent
reduction to the original clopen reduction for an arbitrary quotient.
The finite-algebra endpoints discharge that premise using the actual
finite-algebra lifting theorem.  No henselianity, nontriviality, freeness,
or locality of A is assumed.  This concerns affine spectra; it does not
assert a clopen-lifting theorem for proper nonaffine schemes.
-/

noncomputable section

universe u v

namespace PrimeGap182.TypeIII.FiniteAlgebraClopenLifting

open TopologicalSpace

section Quotient

variable (A : Type v) [CommRing A] (I : Ideal A)
  (h : Function.Bijective (HenselianIdempotentLifting.idempotentReduction A I))

include h in
/-- The original idempotent/clopen correspondence transfers bijectivity
to the original inverse-image map of the quotient spectrum. -/
theorem clopenReduction_bijective_of_idempotentReduction_bijective :
    Function.Bijective (HenselianIdempotentLifting.clopenReduction A I) := by
  constructor
  · intro U V hUV
    obtain ⟨a, rfl⟩ := (PrimeSpectrum.isIdempotentElemEquivClopens (R := A)).surjective U
    obtain ⟨b, rfl⟩ := (PrimeSpectrum.isIdempotentElemEquivClopens (R := A)).surjective V
    rw [HenselianIdempotentLifting.clopenReduction_idempotent,
      HenselianIdempotentLifting.clopenReduction_idempotent] at hUV
    exact congrArg PrimeSpectrum.isIdempotentElemEquivClopens
      (h.injective (PrimeSpectrum.isIdempotentElemEquivClopens.injective hUV))
  · intro U
    obtain ⟨a, rfl⟩ :=
      (PrimeSpectrum.isIdempotentElemEquivClopens (R := A ⧸ I)).surjective U
    obtain ⟨b, rfl⟩ := h.surjective a
    exact ⟨PrimeSpectrum.isIdempotentElemEquivClopens b,
      HenselianIdempotentLifting.clopenReduction_idempotent A I b⟩

/-- The forward function is the original clopen pullback.  Reflection
of order follows from its injectivity and its preservation of intersections. -/
def clopenReductionOrderIsoOfIdempotentReductionBijective :
    Clopens (PrimeSpectrum A) ≃o Clopens (PrimeSpectrum (A ⧸ I)) where
  toEquiv := Equiv.ofBijective (HenselianIdempotentLifting.clopenReduction A I)
    (clopenReduction_bijective_of_idempotentReduction_bijective A I h)
  map_rel_iff' := by
    intro U V
    constructor
    · intro hUV
      apply inf_eq_left.mp
      apply (clopenReduction_bijective_of_idempotentReduction_bijective A I h).injective
      change HenselianIdempotentLifting.clopenReduction A I U ⊓
          HenselianIdempotentLifting.clopenReduction A I V =
        HenselianIdempotentLifting.clopenReduction A I U
      exact inf_eq_left.mpr hUV
    · intro hUV x hx
      exact hUV hx

/-- Packaging the map as an order isomorphism leaves its value unchanged. -/
theorem clopenReductionOrderIsoOfIdempotentReductionBijective_apply
    (U : Clopens (PrimeSpectrum A)) :
    clopenReductionOrderIsoOfIdempotentReductionBijective A I h U =
      HenselianIdempotentLifting.clopenReduction A I U := rfl

/-- The canonical inverse is a lift for the original clopen reduction. -/
theorem clopenReductionOrderIsoOfIdempotentReductionBijective_symm_spec
    (U : Clopens (PrimeSpectrum (A ⧸ I))) :
    HenselianIdempotentLifting.clopenReduction A I
        ((clopenReductionOrderIsoOfIdempotentReductionBijective A I h).symm U) = U :=
  (clopenReductionOrderIsoOfIdempotentReductionBijective A I h).apply_symm_apply U

/-- The inverse clopen is defined by the unique lifted original idempotent. -/
theorem clopenReductionOrderIsoOfIdempotentReductionBijective_symm_idempotent
    (e : {e : A ⧸ I // IsIdempotentElem e}) :
    (clopenReductionOrderIsoOfIdempotentReductionBijective A I h).symm
        (PrimeSpectrum.isIdempotentElemEquivClopens e) =
      PrimeSpectrum.isIdempotentElemEquivClopens
        ((Equiv.ofBijective (HenselianIdempotentLifting.idempotentReduction A I) h).symm e) := by
  apply (clopenReduction_bijective_of_idempotentReduction_bijective A I h).injective
  rw [clopenReductionOrderIsoOfIdempotentReductionBijective_symm_spec,
    HenselianIdempotentLifting.clopenReduction_idempotent]
  exact (congrArg PrimeSpectrum.isIdempotentElemEquivClopens
    (Equiv.apply_symm_apply
      (Equiv.ofBijective (HenselianIdempotentLifting.idempotentReduction A I) h) e)).symm

end Quotient

section Finite

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A]

/-- Actual clopen inverse image is bijective for a finite algebra over
the henselian local base; henselianity of A is not an input. -/
theorem clopenReduction_bijective :
    Function.Bijective (HenselianIdempotentLifting.clopenReduction A
      ((IsLocalRing.maximalIdeal R).map (algebraMap R A))) :=
  clopenReduction_bijective_of_idempotentReduction_bijective A _
    (FiniteAlgebraIdempotentLifting.idempotentReduction_bijective R A)

/-- The actual clopen pullback for Spec(A / m A) → Spec(A), as an order
isomorphism on the original clopen types. -/
def clopenReductionOrderIso :
    Clopens (PrimeSpectrum A) ≃o
      Clopens (PrimeSpectrum (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))) :=
  clopenReductionOrderIsoOfIdempotentReductionBijective A _
    (FiniteAlgebraIdempotentLifting.idempotentReduction_bijective R A)

/-- Its forward function is literally the existing clopen reduction. -/
theorem clopenReductionOrderIso_apply (U : Clopens (PrimeSpectrum A)) :
    clopenReductionOrderIso R A U = HenselianIdempotentLifting.clopenReduction A
      ((IsLocalRing.maximalIdeal R).map (algebraMap R A)) U := rfl

/-- Its carrier is the actual inverse image under the quotient spectrum map. -/
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
        (FiniteAlgebraIdempotentLifting.idempotentReductionEquiv R A a) :=
  HenselianIdempotentLifting.clopenReduction_idempotent A _ a

/-- The canonical inverse has precisely the prescribed original pullback. -/
theorem clopenReductionOrderIso_symm_spec
    (U : Clopens
      (PrimeSpectrum (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)))) :
    HenselianIdempotentLifting.clopenReduction A
        ((IsLocalRing.maximalIdeal R).map (algebraMap R A))
        ((clopenReductionOrderIso R A).symm U) = U :=
  (clopenReductionOrderIso R A).apply_symm_apply U

/-- The inverse agrees with the actual finite-algebra idempotent lift. -/
theorem clopenReductionOrderIso_symm_idempotent
    (e : {e : A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A) //
      IsIdempotentElem e}) :
    (clopenReductionOrderIso R A).symm (PrimeSpectrum.isIdempotentElemEquivClopens e) =
      PrimeSpectrum.isIdempotentElemEquivClopens
        ((FiniteAlgebraIdempotentLifting.idempotentReductionEquiv R A).symm e) :=
  clopenReductionOrderIsoOfIdempotentReductionBijective_symm_idempotent A _
    (FiniteAlgebraIdempotentLifting.idempotentReduction_bijective R A) e

/-- Every clopen of the actual residue spectrum has a unique clopen lift. -/
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

end Finite

#print axioms clopenReduction_bijective_of_idempotentReduction_bijective
#print axioms clopenReductionOrderIsoOfIdempotentReductionBijective
#print axioms clopenReductionOrderIsoOfIdempotentReductionBijective_apply
#print axioms clopenReductionOrderIsoOfIdempotentReductionBijective_symm_spec
#print axioms clopenReductionOrderIsoOfIdempotentReductionBijective_symm_idempotent
#print axioms clopenReduction_bijective
#print axioms clopenReductionOrderIso
#print axioms clopenReductionOrderIso_apply
#print axioms clopenReductionOrderIso_coe
#print axioms clopenReductionOrderIso_idempotent
#print axioms clopenReductionOrderIso_symm_spec
#print axioms clopenReductionOrderIso_symm_idempotent
#print axioms existsUnique_clopen_lift

end PrimeGap182.TypeIII.FiniteAlgebraClopenLifting
