import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Etale.StandardEtale

/-!
# Unique lifting of residue points of standard étale algebras

For an actual standard étale pair over a henselian local ring, every
algebra homomorphism to the residue field lifts uniquely to an algebra
homomorphism to the original ring.  Existence uses the simple-root
form of Hensel's lemma, followed by the actual universal map from the
standard étale algebra.  Invertibility of the localizing polynomial
is proved from its nonzero residue value.

Uniqueness already holds over a local ring: the defining roots have
the same residue and invertible derivative, so they agree.  The
result concerns standard étale algebras; no arbitrary étale section
or proper base-change theorem is assumed.
-/

noncomputable section

universe u v

namespace PrimeGap182.TypeIII.HenselianEtaleSections

open Polynomial IsLocalRing

variable {R : Type u} [CommRing R]

section Local

variable [IsLocalRing R]

/-- The actual reduction of an R-valued algebra homomorphism to the residue field. -/
def residueReduction {A : Type v} [CommRing A] [Algebra R A]
    (φ : A →ₐ[R] R) : A →ₐ[R] ResidueField R :=
  (Algebra.ofId R (ResidueField R)).comp φ

/-- Reduction is literally residue-field reduction on every value. -/
theorem residueReduction_apply {A : Type v} [CommRing A] [Algebra R A]
    (φ : A →ₐ[R] R) (a : A) : residueReduction φ a = residue R (φ a) := rfl

/-- Two admissible roots of a standard étale pair with the same
residue agree, using the actual invertibility of the derivative. -/
theorem hasMap_eq_of_residue_eq (P : StandardEtalePair R) {a b : R}
    (ha : P.HasMap a) (hb : P.HasMap b) (hab : residue R a = residue R b) : a = b := by
  apply IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
    (f := P.f) (a := a) (b := b)
  · simpa only [coe_aeval_eq_eval] using ha.1
  · simpa only [coe_aeval_eq_eval] using hb.1
  · intro hu
    have hzero : residue R (a - b) = 0 := by rw [map_sub, hab, sub_self]
    exact ((residue_ne_zero_iff_isUnit (a - b)).2 hu) hzero
  · simpa only [coe_aeval_eq_eval] using
      (StandardEtalePair.HasMap.isUnit_derivative_f (P := P) ha)

/-- Actual reduction is injective on homomorphisms from the given
standard étale algebra, even without a henselian assumption. -/
theorem pairReduction_injective (P : StandardEtalePair R) :
    Function.Injective (residueReduction (R := R) (A := P.Ring)) := by
  intro φ ψ h
  apply P.hom_ext
  apply hasMap_eq_of_residue_eq P (P.hasMap_X.map φ) (P.hasMap_X.map ψ)
  exact AlgHom.congr_fun h P.X

/-- Injectivity also holds for an algebra with its actual standard
étale presentation, by evaluation at the presentation's generator. -/
theorem presentationReduction_injective {A : Type v} [CommRing A] [Algebra R A]
    (P : StandardEtalePresentation R A) :
    Function.Injective (residueReduction (R := R) (A := A)) := by
  intro φ ψ h
  apply P.hom_ext
  apply hasMap_eq_of_residue_eq P.P (P.hasMap.map φ) (P.hasMap.map ψ)
  exact AlgHom.congr_fun h P.x

end Local

section Henselian

variable [HenselianLocalRing R]

/-- Hensel's lemma produces an actual admissible root over R with
the given residue root; the localizing polynomial remains a unit. -/
theorem exists_hasMap_lift (P : StandardEtalePair R) (x : ResidueField R)
    (hx : P.HasMap x) : ∃ a : R, P.HasMap a ∧ residue R a = x := by
  have hderiv : IsUnit (aeval x P.f.derivative) :=
    StandardEtalePair.HasMap.isUnit_derivative_f (P := P) hx
  have hH := ((HenselianLocalRing.TFAE R).out 1 2).mp
    (inferInstance : HenselianLocalRing R)
  obtain ⟨a, ha, hres⟩ := hH P.f P.monic_f x hx.1 hderiv.ne_zero
  refine ⟨a, ⟨?_, ?_⟩, hres⟩
  · simpa only [coe_aeval_eq_eval, Polynomial.IsRoot] using ha
  · apply (residue_ne_zero_iff_isUnit (aeval a P.g)).mp
    have hg : residue R (aeval a P.g) = aeval x P.g := by
      calc
        residue R (aeval a P.g) = aeval (residue R a) P.g :=
          (aeval_algHom_apply (Algebra.ofId R (ResidueField R)) a P.g).symm
        _ = aeval x P.g := congrArg (fun z => aeval z P.g) hres
    rw [hg]
    exact hx.2.ne_zero

/-- Every actual residue-field point of the standard étale algebra
lifts to a homomorphism to the original henselian local ring. -/
theorem pairReduction_surjective (P : StandardEtalePair R) :
    Function.Surjective (residueReduction (R := R) (A := P.Ring)) := by
  intro φ
  obtain ⟨a, ha, hres⟩ := exists_hasMap_lift P (φ P.X) (P.hasMap_X.map φ)
  refine ⟨P.lift a ha, ?_⟩
  apply P.hom_ext
  simpa only [residueReduction_apply, StandardEtalePair.lift_X] using hres

/-- Every specified residue-field algebra homomorphism has a unique
lift, with reduction expressed by the actual composition of algebra maps. -/
theorem pair_existsUnique_lift (P : StandardEtalePair R)
    (φ : P.Ring →ₐ[R] ResidueField R) :
    ∃! ψ : P.Ring →ₐ[R] R, (Algebra.ofId R (ResidueField R)).comp ψ = φ := by
  obtain ⟨ψ, hψ⟩ := pairReduction_surjective P φ
  refine ⟨ψ, hψ, ?_⟩
  intro χ hχ
  exact pairReduction_injective P (hχ.trans hψ.symm)

/-- Actual residue reduction is an equivalence of the two sets of algebra homomorphisms. -/
def pairResidueEquiv (P : StandardEtalePair R) :
    (P.Ring →ₐ[R] R) ≃ (P.Ring →ₐ[R] ResidueField R) :=
  Equiv.ofBijective residueReduction ⟨pairReduction_injective P, pairReduction_surjective P⟩

/-- The equivalence has exactly the original residue reduction as its forward function. -/
theorem pairResidueEquiv_apply (P : StandardEtalePair R) (ψ : P.Ring →ₐ[R] R) :
    pairResidueEquiv P ψ = (Algebra.ofId R (ResidueField R)).comp ψ := rfl

/-- Its inverse gives an actual lift with the required original residue-field map. -/
theorem pairResidueEquiv_symm_spec (P : StandardEtalePair R)
    (φ : P.Ring →ₐ[R] ResidueField R) :
    (Algebra.ofId R (ResidueField R)).comp ((pairResidueEquiv P).symm φ) = φ :=
  (pairResidueEquiv P).apply_symm_apply φ

/-- The actual presentation isomorphism transports the constructed
lift to the original algebra, preserving its residue-field homomorphism. -/
theorem presentationReduction_surjective {A : Type v} [CommRing A] [Algebra R A]
    (P : StandardEtalePresentation R A) :
    Function.Surjective (residueReduction (R := R) (A := A)) := by
  intro φ
  obtain ⟨ψ, hψ⟩ := pairReduction_surjective P.P
    (φ.comp P.equivRing.symm.toAlgHom)
  refine ⟨ψ.comp P.equivRing.toAlgHom, ?_⟩
  ext a
  have h := AlgHom.congr_fun hψ (P.equivRing a)
  change residue R (ψ (P.equivRing a)) = φ (P.equivRing.symm (P.equivRing a)) at h
  change residue R (ψ (P.equivRing a)) = φ a
  simpa only [AlgEquiv.symm_apply_apply] using h

/-- For an actual standard étale algebra over a henselian local ring,
residue reduction is bijective; its presentation is supplied by the
existing algebraic property, not by a section hypothesis. -/
theorem standardEtaleReduction_bijective {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.IsStandardEtale R A] :
    Function.Bijective (residueReduction (R := R) (A := A)) := by
  let P : StandardEtalePresentation R A :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  exact ⟨presentationReduction_injective P, presentationReduction_surjective P⟩

/-- Each specified residue-field point of the original standard étale
algebra has a unique lift to the henselian local base ring. -/
theorem standardEtale_existsUnique_lift {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.IsStandardEtale R A] (φ : A →ₐ[R] ResidueField R) :
    ∃! ψ : A →ₐ[R] R, (Algebra.ofId R (ResidueField R)).comp ψ = φ := by
  obtain ⟨ψ, hψ⟩ := standardEtaleReduction_bijective.surjective φ
  refine ⟨ψ, hψ, ?_⟩
  intro χ hχ
  exact standardEtaleReduction_bijective.injective (hχ.trans hψ.symm)

/-- The equivalence for the original algebra has literal residue
reduction as its forward map. -/
def standardEtaleResidueEquiv (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.IsStandardEtale R A] :
    (A →ₐ[R] R) ≃ (A →ₐ[R] ResidueField R) :=
  Equiv.ofBijective residueReduction standardEtaleReduction_bijective

/-- The forward equivalence remains the original composition of algebra maps. -/
theorem standardEtaleResidueEquiv_apply (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.IsStandardEtale R A] (ψ : A →ₐ[R] R) :
    standardEtaleResidueEquiv A ψ = (Algebra.ofId R (ResidueField R)).comp ψ := rfl

/-- The inverse gives the lift of exactly the specified residue-field map. -/
theorem standardEtaleResidueEquiv_symm_spec (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.IsStandardEtale R A] (φ : A →ₐ[R] ResidueField R) :
    (Algebra.ofId R (ResidueField R)).comp ((standardEtaleResidueEquiv A).symm φ) = φ :=
  (standardEtaleResidueEquiv A).apply_symm_apply φ

end Henselian

end PrimeGap182.TypeIII.HenselianEtaleSections

#print axioms PrimeGap182.TypeIII.HenselianEtaleSections.residueReduction
#print axioms PrimeGap182.TypeIII.HenselianEtaleSections.residueReduction_apply
#print axioms PrimeGap182.TypeIII.HenselianEtaleSections.hasMap_eq_of_residue_eq
#print axioms PrimeGap182.TypeIII.HenselianEtaleSections.pairReduction_injective
#print axioms PrimeGap182.TypeIII.HenselianEtaleSections.presentationReduction_injective
#print axioms PrimeGap182.TypeIII.HenselianEtaleSections.exists_hasMap_lift
#print axioms PrimeGap182.TypeIII.HenselianEtaleSections.pairReduction_surjective
#print axioms PrimeGap182.TypeIII.HenselianEtaleSections.pair_existsUnique_lift
#print axioms PrimeGap182.TypeIII.HenselianEtaleSections.pairResidueEquiv
#print axioms PrimeGap182.TypeIII.HenselianEtaleSections.pairResidueEquiv_apply
#print axioms PrimeGap182.TypeIII.HenselianEtaleSections.pairResidueEquiv_symm_spec
#print axioms PrimeGap182.TypeIII.HenselianEtaleSections.presentationReduction_surjective
#print axioms PrimeGap182.TypeIII.HenselianEtaleSections.standardEtaleReduction_bijective
#print axioms PrimeGap182.TypeIII.HenselianEtaleSections.standardEtale_existsUnique_lift
#print axioms PrimeGap182.TypeIII.HenselianEtaleSections.standardEtaleResidueEquiv
#print axioms PrimeGap182.TypeIII.HenselianEtaleSections.standardEtaleResidueEquiv_apply
#print axioms PrimeGap182.TypeIII.HenselianEtaleSections.standardEtaleResidueEquiv_symm_spec
