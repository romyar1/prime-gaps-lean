import TypeIIIEtaleDerivedImageTower
import TypeIIIKloostermanDerivedLimit
import TypeIIIKloostermanFiniteCoefficientTransitions

/-!
# The actual cohomology towers of the full Kloosterman derived object

The full derived direct image of the original extended coefficient tower
has the previously constructed finite-coefficient systems as its
cohomology towers.  This comparison includes their independently defined
reduction maps.  The full derived object is retained as the input to the
derived inverse limit; no cohomology--limit interchange is asserted.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category AlgebraicGeometry Opposite

attribute [local instance] HasDerivedCategory.standard

variable (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell)

/-- The full original derived direct image in the actual tower category. -/
def kloostermanFullDerivedTower :
    DerivedCategory.Plus
      (EtaleSheafTower.Tower (Spec (.of (Polynomial (ZMod p))))
        (TorsionCoefficientLimit p ell)) :=
  (EtaleTowerDirectImage.functor (kloostermanCompactificationProjection p)
    (TorsionCoefficientLimit p ell)).rightDerivedFunctorPlus.obj
      (kloostermanExtendedTowerSingle p ell hne)

/-- This full object, before taking any cohomology, is the input to the
original derived limit in the existing interchange construction. -/
theorem kloostermanDerivedTowerLimit_eq_full :
    kloostermanDerivedTowerLimit p ell hne =
      (EtaleSheafTower.derivedPlus (Spec (.of (Polynomial (ZMod p))))
        (TorsionCoefficientLimit p ell)).obj (kloostermanFullDerivedTower p ell hne) := rfl

/-- The degree-d cohomology object is itself an actual tower of sheaves. -/
def kloostermanFullDerivedTowerCohomology (d : ℕ) :
    EtaleSheafTower.Tower (Spec (.of (Polynomial (ZMod p))))
      (TorsionCoefficientLimit p ell) :=
  (DerivedCategory.Plus.homologyFunctor
    (EtaleSheafTower.Tower (Spec (.of (Polynomial (ZMod p))))
      (TorsionCoefficientLimit p ell)) (d : ℤ)).obj
        (kloostermanFullDerivedTower p ell hne)

/-- The actual cohomology tower is the original common-coefficient tower,
via the original evaluation and derived-unit comparisons. -/
def kloostermanFullDerivedTowerCohomologyIso (d : ℕ) :
    kloostermanFullDerivedTowerCohomology p ell hne d ≅
      kloostermanTorsionDerivedTower p ell hne d :=
  (EtaleDerivedImageTower.cohomologyIso (kloostermanCompactificationProjection p)
    (TorsionCoefficientLimit p ell) d).app (kloostermanTorsionExtendedTower p ell hne)

/-- The cohomology tower also identifies with the original independently
constructed finite-category derived system, including its original maps. -/
def kloostermanFullDerivedTowerFiniteCohomologyIso (d : ℕ) :
    kloostermanFullDerivedTowerCohomology p ell hne d ≅
      kloostermanFiniteCoefficientDerivedTower p ell hne d :=
  kloostermanFullDerivedTowerCohomologyIso p ell hne d ≪≫
    (kloostermanFiniteCoefficientDerivedTowerIso p ell hne d).symm

/-- The finite-category identification retains the original coefficient
comparison to the original common-coefficient tower. -/
theorem kloostermanFullDerivedTowerFiniteCohomologyIso_toTower (d : ℕ) :
    (kloostermanFullDerivedTowerFiniteCohomologyIso p ell hne d).hom ≫
        (kloostermanFiniteCoefficientDerivedTowerIso p ell hne d).hom =
      (kloostermanFullDerivedTowerCohomologyIso p ell hne d).hom := by
  simp only [kloostermanFullDerivedTowerFiniteCohomologyIso, Iso.trans_hom,
    Iso.symm_hom, assoc, Iso.inv_hom_id, comp_id]

/-- Every actual cohomology transition is intertwined with the independently
defined finite-category reduction under the same comparison. -/
theorem kloostermanFullDerivedTowerFiniteCohomologyIso_transition (d : ℕ)
    {m n : ℕ} (hmn : m ≤ n) :
    (kloostermanFullDerivedTowerCohomology p ell hne d).map (homOfLE hmn).op ≫
        (kloostermanFullDerivedTowerFiniteCohomologyIso p ell hne d).hom.app (op m) =
      (kloostermanFullDerivedTowerFiniteCohomologyIso p ell hne d).hom.app (op n) ≫
        kloostermanFiniteCoefficientRestrictedReduction p ell hne d hmn :=
  (kloostermanFullDerivedTowerFiniteCohomologyIso p ell hne d).hom.naturality
    (homOfLE hmn).op

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.kloostermanFullDerivedTower
#print axioms PrimeGap182.TypeIII.kloostermanDerivedTowerLimit_eq_full
#print axioms PrimeGap182.TypeIII.kloostermanFullDerivedTowerCohomology
#print axioms PrimeGap182.TypeIII.kloostermanFullDerivedTowerCohomologyIso
#print axioms PrimeGap182.TypeIII.kloostermanFullDerivedTowerFiniteCohomologyIso
#print axioms PrimeGap182.TypeIII.kloostermanFullDerivedTowerFiniteCohomologyIso_toTower
#print axioms PrimeGap182.TypeIII.kloostermanFullDerivedTowerFiniteCohomologyIso_transition
