import TypeIIIKloostermanBockstein
import TypeIIIKloostermanFiniteCoefficientTransitions

/-!
# The coefficient exact sequence on the original finite derived images

The actual coefficient-comparison isomorphisms identify the torsion term
of the proved Bockstein sequence with the derived image computed in its
original finite coefficient category. The reduction and connecting maps
below use those original comparisons, and all three consecutive triples
are exact. Reduction is compatible with the independently constructed
finite-category transition maps.

The other terms remain ordinary derived images of the discrete limit
coefficient sheaf. This result neither identifies them with adic
cohomology nor asserts that their inverse limit commutes with cohomology.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry Opposite

attribute [local instance] kloostermanPhaseRing_charP HasDerivedCategory.standard

variable (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell)

/-- The original derived reduction, followed by the inverse of the
original finite-category coefficient comparison. -/
def kloostermanFiniteBocksteinReduction (d n : ℕ) :
    kloostermanLimitDerivedImage p ell hne d ⟶
      kloostermanFiniteCoefficientRestrictedDerivedImage p ell hne d n :=
  kloostermanBocksteinReduction p ell hne d n ≫
    (kloostermanFiniteCoefficientToTowerIso p ell hne d n).inv

/-- The original finite-category comparison followed by the canonical
connecting map of the actual coefficient short exact sequence. -/
def kloostermanFiniteBocksteinConnecting (d n : ℕ) :
    kloostermanFiniteCoefficientRestrictedDerivedImage p ell hne d n ⟶
      kloostermanLimitDerivedImage p ell hne (d + 1) :=
  (kloostermanFiniteCoefficientToTowerIso p ell hne d n).hom ≫
    kloostermanBocksteinConnecting p ell hne d n

/-- The comparison sends the finite-category reduction to the original
common-coefficient derived reduction. -/
theorem kloostermanFiniteBocksteinReduction_toTower (d n : ℕ) :
    kloostermanFiniteBocksteinReduction p ell hne d n ≫
        (kloostermanFiniteCoefficientToTowerIso p ell hne d n).hom =
      kloostermanBocksteinReduction p ell hne d n := by
  simp only [kloostermanFiniteBocksteinReduction, assoc, Iso.inv_hom_id, comp_id]

/-- The inverse comparison retains the original connecting map. -/
theorem kloostermanFiniteBocksteinConnecting_fromTower (d n : ℕ) :
    (kloostermanFiniteCoefficientToTowerIso p ell hne d n).inv ≫
        kloostermanFiniteBocksteinConnecting p ell hne d n =
      kloostermanBocksteinConnecting p ell hne d n := by
  simp only [kloostermanFiniteBocksteinConnecting, Iso.inv_hom_id_assoc]

/-- The actual scalar composes to zero with reduction into the original
finite-category derived image. -/
theorem kloostermanFiniteBockstein_scalar_comp_reduction (d n : ℕ) :
    ((ell ^ (n + 1)) • (𝟙 (kloostermanLimitDerivedImage p ell hne d))) ≫
      kloostermanFiniteBocksteinReduction p ell hne d n = 0 := by
  rw [kloostermanFiniteBocksteinReduction, ← assoc,
    kloostermanBockstein_scalar_comp_reduction, zero_comp]

/-- The finite-category reduction composes to zero with its canonical
connecting map. -/
theorem kloostermanFiniteBockstein_reduction_comp_connecting (d n : ℕ) :
    kloostermanFiniteBocksteinReduction p ell hne d n ≫
      kloostermanFiniteBocksteinConnecting p ell hne d n = 0 := by
  rw [kloostermanFiniteBocksteinReduction, assoc,
    kloostermanFiniteBocksteinConnecting_fromTower,
    kloostermanBockstein_reduction_comp_connecting]

/-- The connecting map into the next ordinary derived image is killed
by the original coefficient power. -/
theorem kloostermanFiniteBockstein_connecting_comp_scalar (d n : ℕ) :
    kloostermanFiniteBocksteinConnecting p ell hne d n ≫
      ((ell ^ (n + 1)) • (𝟙 (kloostermanLimitDerivedImage p ell hne (d + 1)))) = 0 := by
  rw [kloostermanFiniteBocksteinConnecting, assoc,
    kloostermanBockstein_connecting_comp_scalar, comp_zero]

/-- Exactness at the ordinary source, with reduction into the actual
finite-category derived image. -/
theorem kloostermanFiniteBockstein_exact_source (d n : ℕ) :
    (ShortComplex.mk
      ((ell ^ (n + 1)) • (𝟙 (kloostermanLimitDerivedImage p ell hne d)))
      (kloostermanFiniteBocksteinReduction p ell hne d n)
      (kloostermanFiniteBockstein_scalar_comp_reduction p ell hne d n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (kloostermanBockstein_exact_source p ell hne d n)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (kloostermanFiniteCoefficientToTowerIso p ell hne d n).symm ?_ ?_
  · simp only [Iso.refl_hom, id_comp, comp_id]
  · simp only [Iso.refl_hom, Iso.symm_hom, id_comp,
      kloostermanFiniteBocksteinReduction]

/-- Exactness at the original finite-category derived image. -/
theorem kloostermanFiniteBockstein_exact_torsion (d n : ℕ) :
    (ShortComplex.mk (kloostermanFiniteBocksteinReduction p ell hne d n)
      (kloostermanFiniteBocksteinConnecting p ell hne d n)
      (kloostermanFiniteBockstein_reduction_comp_connecting p ell hne d n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (kloostermanBockstein_exact_torsion p ell hne d n)
  refine ShortComplex.isoMk (Iso.refl _)
    (kloostermanFiniteCoefficientToTowerIso p ell hne d n).symm (Iso.refl _) ?_ ?_
  · simp only [Iso.refl_hom, Iso.symm_hom, id_comp,
      kloostermanFiniteBocksteinReduction]
  · simp only [Iso.refl_hom, Iso.symm_hom, comp_id]
    exact kloostermanFiniteBocksteinConnecting_fromTower p ell hne d n

/-- Exactness at the next ordinary source, retaining the actual
finite-category connecting morphism. -/
theorem kloostermanFiniteBockstein_exact_next (d n : ℕ) :
    (ShortComplex.mk (kloostermanFiniteBocksteinConnecting p ell hne d n)
      ((ell ^ (n + 1)) • (𝟙 (kloostermanLimitDerivedImage p ell hne (d + 1))))
      (kloostermanFiniteBockstein_connecting_comp_scalar p ell hne d n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (kloostermanBockstein_exact_next p ell hne d n)
  refine ShortComplex.isoMk
    (kloostermanFiniteCoefficientToTowerIso p ell hne d n).symm
    (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp only [Iso.refl_hom, Iso.symm_hom, comp_id]
    exact kloostermanFiniteBocksteinConnecting_fromTower p ell hne d n
  · simp only [Iso.refl_hom, id_comp, comp_id]

/-- Reduction from the original discrete limit sheaf respects every
independently defined finite-category derived transition. -/
theorem kloostermanFiniteBocksteinReduction_comp (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    kloostermanFiniteBocksteinReduction p ell hne d n ≫
        kloostermanFiniteCoefficientRestrictedReduction p ell hne d hmn =
      kloostermanFiniteBocksteinReduction p ell hne d m := by
  apply (Iso.cancel_iso_hom_right _ _
    (kloostermanFiniteCoefficientToTowerIso p ell hne d m)).mp
  rw [assoc, kloostermanFiniteCoefficientRestrictedReduction_toTower,
    ← assoc, kloostermanFiniteBocksteinReduction_toTower,
    kloostermanFiniteBocksteinReduction_toTower]
  change (kloostermanCompactifiedDerivedImage p (TorsionCoefficientLimit p ell) d).map
      (limitArtinSchreierReduction p ell hne (kloostermanPhaseFunction p) n) ≫
      (kloostermanCompactifiedDerivedImage p (TorsionCoefficientLimit p ell) d).map
        (torsionArtinSchreierLimitModuleReduction p ell hne
          (kloostermanPhaseFunction p) hmn) =
    (kloostermanCompactifiedDerivedImage p (TorsionCoefficientLimit p ell) d).map
      (limitArtinSchreierReduction p ell hne (kloostermanPhaseFunction p) m)
  rw [← CategoryTheory.Functor.map_comp, limitArtinSchreierReduction_comp]

#print axioms kloostermanFiniteBocksteinReduction
#print axioms kloostermanFiniteBocksteinConnecting
#print axioms kloostermanFiniteBocksteinReduction_toTower
#print axioms kloostermanFiniteBocksteinConnecting_fromTower
#print axioms kloostermanFiniteBockstein_scalar_comp_reduction
#print axioms kloostermanFiniteBockstein_reduction_comp_connecting
#print axioms kloostermanFiniteBockstein_connecting_comp_scalar
#print axioms kloostermanFiniteBockstein_exact_source
#print axioms kloostermanFiniteBockstein_exact_torsion
#print axioms kloostermanFiniteBockstein_exact_next
#print axioms kloostermanFiniteBocksteinReduction_comp

end PrimeGap182.TypeIII
