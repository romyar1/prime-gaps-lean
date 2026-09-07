import TypeIIIArtinSchreierBockstein
import TypeIIIKloostermanTorsionDerivedTower
import TypeIIIRightDerivedLongExact

/-!
# The original compactified Kloosterman Bockstein sequence

The proved short exact sequence of actual character sheaves is extended
by the original exact j! and passed through the original right derived
proper projection. This gives a long exact sequence with multiplication
by ell^(n+1), the original finite reduction map, and the canonical derived
connecting map.

The source terms here are ordinary derived images of the discrete
limit-coefficient sheaf. The torsion terms are the original common-ring
derived tower. No assertion identifies these ordinary source terms with
adic cohomology or commutes derived image with an inverse limit.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  AlgebraicGeometry Opposite

attribute [local instance] kloostermanPhaseRing_charP HasDerivedCategory.standard

variable (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell)

/-- The ordinary compactified derived image of the actual discrete
limit-coefficient character sheaf. -/
def kloostermanLimitDerivedImage (d : ℕ) :
    Sheaf (Spec (.of (Polynomial (ZMod p)))).smallEtaleTopology
      (ModuleCat.{0} (TorsionCoefficientLimit p ell)) :=
  (kloostermanCompactifiedDerivedImage p (TorsionCoefficientLimit p ell) d).obj
    (limitArtinSchreierSheaf p ell hne (kloostermanPhaseFunction p))

/-- The actual short complex after the original extension by zero. -/
def kloostermanBocksteinExtendedSequence (n : ℕ) :
    ShortComplex (Sheaf (kloostermanCompactificationScheme p).smallEtaleTopology
      (ModuleCat.{0} (TorsionCoefficientLimit p ell))) :=
  (limitArtinSchreierBocksteinSequence p ell hne (kloostermanPhaseFunction p) n).map
    (kloostermanPhaseExtensionByZero p (TorsionCoefficientLimit p ell))

/-- The proved exactness of the actual j! preserves the actual coefficient sequence. -/
theorem kloostermanBocksteinExtendedSequence_shortExact (n : ℕ) :
    (kloostermanBocksteinExtendedSequence p ell hne n).ShortExact :=
  (limitArtinSchreierBocksteinSequence_shortExact p ell hne
    (kloostermanPhaseFunction p) n).map_of_exact
      (kloostermanPhaseExtensionByZero p (TorsionCoefficientLimit p ell))

/-- The ordinary derived reduction is the actual derived functor applied
to the original finite coefficient map. -/
def kloostermanBocksteinReduction (d n : ℕ) :
    kloostermanLimitDerivedImage p ell hne d ⟶
      (kloostermanTorsionDerivedTower p ell hne d).obj (op n) :=
  (kloostermanCompactifiedDerivedImage p (TorsionCoefficientLimit p ell) d).map
    (limitArtinSchreierReduction p ell hne (kloostermanPhaseFunction p) n)

/-- The canonical connecting morphism for the original extended coefficient sequence. -/
def kloostermanBocksteinConnecting (d n : ℕ) :
    (kloostermanTorsionDerivedTower p ell hne d).obj (op n) ⟶
      kloostermanLimitDerivedImage p ell hne (d + 1) :=
  rightDerivedConnectingHom
    (EtaleDirectImage.functor (kloostermanCompactificationProjection p)
      (TorsionCoefficientLimit p ell))
    (kloostermanBocksteinExtendedSequence_shortExact p ell hne n) d

/-- The original derived first arrow is still multiplication by the same integer. -/
theorem kloostermanBockstein_derived_scalar (d n : ℕ) :
    ((kloostermanBocksteinExtendedSequence p ell hne n).map
      ((EtaleDirectImage.functor (kloostermanCompactificationProjection p)
        (TorsionCoefficientLimit p ell)).rightDerived d)).f =
      (ell ^ (n + 1)) • (𝟙 (kloostermanLimitDerivedImage p ell hne d)) := by
  change ((EtaleDirectImage.functor (kloostermanCompactificationProjection p)
    (TorsionCoefficientLimit p ell)).rightDerived d).map
      ((kloostermanPhaseExtensionByZero p (TorsionCoefficientLimit p ell)).map
        ((ell ^ (n + 1)) •
          (𝟙 (limitArtinSchreierSheaf p ell hne (kloostermanPhaseFunction p))))) = _
  rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rfl

/-- Multiplication by the stated ell power composes to zero with the original reduction. -/
theorem kloostermanBockstein_scalar_comp_reduction (d n : ℕ) :
    ((ell ^ (n + 1)) • (𝟙 (kloostermanLimitDerivedImage p ell hne d))) ≫
      kloostermanBocksteinReduction p ell hne d n = 0 := by
  have h := ((kloostermanBocksteinExtendedSequence p ell hne n).map
    ((EtaleDirectImage.functor (kloostermanCompactificationProjection p)
      (TorsionCoefficientLimit p ell)).rightDerived d)).zero
  rw [kloostermanBockstein_derived_scalar] at h
  exact h

/-- The original reduction composes to zero with the canonical connecting morphism. -/
theorem kloostermanBockstein_reduction_comp_connecting (d n : ℕ) :
    kloostermanBocksteinReduction p ell hne d n ≫
      kloostermanBocksteinConnecting p ell hne d n = 0 :=
  comp_rightDerivedConnectingHom
    (EtaleDirectImage.functor (kloostermanCompactificationProjection p)
      (TorsionCoefficientLimit p ell))
    (kloostermanBocksteinExtendedSequence_shortExact p ell hne n) d

/-- The canonical connecting morphism lands in the kernel of the stated ell power. -/
theorem kloostermanBockstein_connecting_comp_scalar (d n : ℕ) :
    kloostermanBocksteinConnecting p ell hne d n ≫
      ((ell ^ (n + 1)) • (𝟙 (kloostermanLimitDerivedImage p ell hne (d + 1)))) = 0 := by
  have h := rightDerivedConnectingHom_comp
    (EtaleDirectImage.functor (kloostermanCompactificationProjection p)
      (TorsionCoefficientLimit p ell))
    (kloostermanBocksteinExtendedSequence_shortExact p ell hne n) d
  change kloostermanBocksteinConnecting p ell hne d n ≫
    ((kloostermanBocksteinExtendedSequence p ell hne n).map
      ((EtaleDirectImage.functor (kloostermanCompactificationProjection p)
        (TorsionCoefficientLimit p ell)).rightDerived (d + 1))).f = 0 at h
  rw [kloostermanBockstein_derived_scalar] at h
  exact h

/-- Exactness at the ordinary derived source uses the actual scalar and original reduction. -/
theorem kloostermanBockstein_exact_source (d n : ℕ) :
    (ShortComplex.mk
      ((ell ^ (n + 1)) • (𝟙 (kloostermanLimitDerivedImage p ell hne d)))
      (kloostermanBocksteinReduction p ell hne d n)
      (kloostermanBockstein_scalar_comp_reduction p ell hne d n)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    (rightDerivedLongExact_exact₂
      (EtaleDirectImage.functor (kloostermanCompactificationProjection p)
        (TorsionCoefficientLimit p ell))
      (kloostermanBocksteinExtendedSequence_shortExact p ell hne n) d)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp only [Iso.refl_hom, comp_id, id_comp]
    exact (kloostermanBockstein_derived_scalar p ell hne d n).symm
  · simp only [Iso.refl_hom, comp_id, id_comp]
    rfl

/-- Exactness at the actual finite torsion tower object. -/
theorem kloostermanBockstein_exact_torsion (d n : ℕ) :
    (ShortComplex.mk (kloostermanBocksteinReduction p ell hne d n)
      (kloostermanBocksteinConnecting p ell hne d n)
      (kloostermanBockstein_reduction_comp_connecting p ell hne d n)).Exact :=
  rightDerivedLongExact_exact₃
    (EtaleDirectImage.functor (kloostermanCompactificationProjection p)
      (TorsionCoefficientLimit p ell))
    (kloostermanBocksteinExtendedSequence_shortExact p ell hne n) d

/-- Exactness at the next ordinary derived source identifies the actual torsion obstruction. -/
theorem kloostermanBockstein_exact_next (d n : ℕ) :
    (ShortComplex.mk (kloostermanBocksteinConnecting p ell hne d n)
      ((ell ^ (n + 1)) • (𝟙 (kloostermanLimitDerivedImage p ell hne (d + 1))))
      (kloostermanBockstein_connecting_comp_scalar p ell hne d n)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    (rightDerivedLongExact_exact₁
      (EtaleDirectImage.functor (kloostermanCompactificationProjection p)
        (TorsionCoefficientLimit p ell))
      (kloostermanBocksteinExtendedSequence_shortExact p ell hne n) d)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp only [Iso.refl_hom, comp_id, id_comp]
    rfl
  · simp only [Iso.refl_hom, comp_id, id_comp]
    exact (kloostermanBockstein_derived_scalar p ell hne (d + 1) n).symm

#print axioms kloostermanLimitDerivedImage
#print axioms kloostermanBocksteinExtendedSequence
#print axioms kloostermanBocksteinExtendedSequence_shortExact
#print axioms kloostermanBocksteinReduction
#print axioms kloostermanBocksteinConnecting
#print axioms kloostermanBockstein_derived_scalar
#print axioms kloostermanBockstein_scalar_comp_reduction
#print axioms kloostermanBockstein_reduction_comp_connecting
#print axioms kloostermanBockstein_connecting_comp_scalar
#print axioms kloostermanBockstein_exact_source
#print axioms kloostermanBockstein_exact_torsion
#print axioms kloostermanBockstein_exact_next

end PrimeGap182.TypeIII
