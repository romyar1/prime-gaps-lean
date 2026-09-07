import TypeIIIHenselianEtaleSections
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Unique lifting of residue points of étale algebras

Let A be an étale algebra over a henselian local ring R.  Actual
composition with R → ResidueField R gives a bijection from R-valued
algebra homomorphisms on A to residue-field-valued ones.

For a specified residue-field homomorphism, the kernel determines
an actual prime of A.  The standard étale neighborhood theorem
provides A[1/g] with nonzero residue value of g.  The residue-field
homomorphism extends to this localization, and the already proved
standard étale lifting theorem gives the lift over R.

Uniqueness holds over every local ring: both proposed lifts send g
to units, so they extend to the same standard étale localization,
where the proved uniqueness theorem applies.  No section, standard
presentation of A, or proper base-change theorem is assumed.
-/

noncomputable section

universe u v

namespace PrimeGap182.TypeIII.HenselianEtaleLifting

open IsLocalRing HenselianEtaleSections

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [Algebra R A] [Algebra.Etale R A]

section Local

variable [IsLocalRing R]

/-- The actual prime kernel of a residue-field point has a standard
étale principal neighborhood on which that point is still defined. -/
theorem exists_standardEtale_neighborhood (φ : A →ₐ[R] ResidueField R) :
    ∃ g : A, φ g ≠ 0 ∧ Algebra.IsStandardEtale R (Localization.Away g) := by
  let Q : Ideal A := RingHom.ker φ.toRingHom
  let : Q.IsPrime := RingHom.ker_isPrime φ.toRingHom
  obtain ⟨g, hg, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) Q
  refine ⟨g, ?_, hstd⟩
  simpa only [Q, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom] using hg

/-- Actual residue reduction is injective on homomorphisms from an
étale algebra over a local ring.  Both homomorphisms extend to the
same standard étale neighborhood of their common residue point. -/
theorem reduction_injective :
    Function.Injective (residueReduction (R := R) (A := A)) := by
  intro ψ χ h
  obtain ⟨g, hg, hstd⟩ := exists_standardEtale_neighborhood (residueReduction ψ)
  let : Algebra.IsStandardEtale R (Localization.Away g) := hstd
  have hψg : IsUnit (ψ g) := (residue_ne_zero_iff_isUnit (ψ g)).mp hg
  have hχg : IsUnit (χ g) := by
    apply (residue_ne_zero_iff_isUnit (χ g)).mp
    change residueReduction χ g ≠ 0
    rw [← h]
    exact hg
  let ψg : Localization.Away g →ₐ[R] R := IsLocalization.Away.liftAlgHom g hψg
  let χg : Localization.Away g →ₐ[R] R := IsLocalization.Away.liftAlgHom g hχg
  have hred : residueReduction ψg = residueReduction χg := by
    apply IsLocalization.algHom_ext (Submonoid.powers g)
    ext a
    change residue R (ψg (algebraMap A (Localization.Away g) a)) =
      residue R (χg (algebraMap A (Localization.Away g) a))
    simpa only [ψg, χg, IsLocalization.Away.coe_liftAlgHom,
      IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, residueReduction_apply] using AlgHom.congr_fun h a
  let P : StandardEtalePresentation R (Localization.Away g) :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  have heq : ψg = χg := presentationReduction_injective P hred
  ext a
  simpa only [ψg, χg, IsLocalization.Away.coe_liftAlgHom,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
      AlgHom.congr_fun heq (algebraMap A (Localization.Away g) a)

end Local

section Henselian

variable [HenselianLocalRing R]

/-- Every residue-field point extends to its actual standard étale
localization, lifts there, and restricts to a lift on the original algebra. -/
theorem reduction_surjective :
    Function.Surjective (residueReduction (R := R) (A := A)) := by
  intro φ
  obtain ⟨g, hg, hstd⟩ := exists_standardEtale_neighborhood φ
  let : Algebra.IsStandardEtale R (Localization.Away g) := hstd
  let φg : Localization.Away g →ₐ[R] ResidueField R :=
    IsLocalization.Away.liftAlgHom g (isUnit_iff_ne_zero.mpr hg)
  obtain ⟨ψ, hψ⟩ := standardEtaleReduction_bijective.surjective φg
  refine ⟨ψ.comp (Algebra.algHom R A (Localization.Away g)), ?_⟩
  ext a
  have h := AlgHom.congr_fun hψ (algebraMap A (Localization.Away g) a)
  change residue R (ψ (algebraMap A (Localization.Away g) a)) =
    φg (algebraMap A (Localization.Away g) a) at h
  change residue R (ψ (algebraMap A (Localization.Away g) a)) = φ a
  simpa only [φg, IsLocalization.Away.coe_liftAlgHom,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h

/-- Actual residue reduction is bijective for every étale algebra
over a henselian local ring. -/
theorem reduction_bijective :
    Function.Bijective (residueReduction (R := R) (A := A)) :=
  ⟨reduction_injective, reduction_surjective⟩

/-- Each specified residue-field algebra homomorphism has a unique
lift to R, with reduction expressed by the original algebra-map composition. -/
theorem existsUnique_lift (φ : A →ₐ[R] ResidueField R) :
    ∃! ψ : A →ₐ[R] R, (Algebra.ofId R (ResidueField R)).comp ψ = φ := by
  obtain ⟨ψ, hψ⟩ := reduction_surjective φ
  refine ⟨ψ, hψ, ?_⟩
  intro χ hχ
  exact reduction_injective (hχ.trans hψ.symm)

/-- The actual equivalence induced by residue reduction on the original étale algebra. -/
def residueEquiv (A : Type v) [CommRing A] [Algebra R A] [Algebra.Etale R A] :
    (A →ₐ[R] R) ≃ (A →ₐ[R] ResidueField R) :=
  Equiv.ofBijective residueReduction reduction_bijective

/-- The equivalence's forward map is exactly actual residue composition. -/
theorem residueEquiv_apply (ψ : A →ₐ[R] R) :
    residueEquiv A ψ = (Algebra.ofId R (ResidueField R)).comp ψ := rfl

/-- The inverse recovers a lift of exactly the prescribed residue-field point. -/
theorem residueEquiv_symm_spec (φ : A →ₐ[R] ResidueField R) :
    (Algebra.ofId R (ResidueField R)).comp ((residueEquiv A).symm φ) = φ :=
  (residueEquiv A).apply_symm_apply φ

end Henselian

end PrimeGap182.TypeIII.HenselianEtaleLifting

#print axioms PrimeGap182.TypeIII.HenselianEtaleLifting.exists_standardEtale_neighborhood
#print axioms PrimeGap182.TypeIII.HenselianEtaleLifting.reduction_injective
#print axioms PrimeGap182.TypeIII.HenselianEtaleLifting.reduction_surjective
#print axioms PrimeGap182.TypeIII.HenselianEtaleLifting.reduction_bijective
#print axioms PrimeGap182.TypeIII.HenselianEtaleLifting.existsUnique_lift
#print axioms PrimeGap182.TypeIII.HenselianEtaleLifting.residueEquiv
#print axioms PrimeGap182.TypeIII.HenselianEtaleLifting.residueEquiv_apply
#print axioms PrimeGap182.TypeIII.HenselianEtaleLifting.residueEquiv_symm_spec
