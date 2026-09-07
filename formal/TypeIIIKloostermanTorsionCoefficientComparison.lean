import TypeIIIEtaleCompactSupportCoefficientRestriction
import TypeIIIKloostermanTorsionDerivedTower

/-!
# Actual finite-coefficient derived images of the original phase family

The original open immersion into the proper projective-plane model and
its original derived direct-image functor satisfy the proved coefficient
restriction comparison.  Its component and degree-zero formulas retain
the original derived coefficient map and the original extension map.

At every finite torsion level, apply that original functor in the actual
finite coefficient category to the original finite-level phase sheaf.
Restricting its coefficients along the actual limit-ring projection
identifies it with the corresponding object of the already constructed
common-coefficient tower.  This is a levelwise comparison of ordinary
derived functors, not an inverse-limit or adic-cohomology assertion.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry Opposite

section ArbitraryCoefficients

variable (p : ℕ) {E E' : Type} [Ring E] [Ring E'] (r : E →+* E')

/-- The original compactified Kloosterman derived-image functor
commutes with arbitrary restriction of coefficient rings. -/
def kloostermanCompactifiedCoefficientIso (d : ℕ) :
    kloostermanCompactifiedDerivedImage p E' d ⋙
        EtaleCoefficientRestriction.functor (Spec (.of (Polynomial (ZMod p)))) r ≅
      EtaleCoefficientRestriction.functor (kloostermanPhaseScheme p) r ⋙
        kloostermanCompactifiedDerivedImage p E d :=
  EtaleCompactSupportCoefficientRestriction.iso (kloostermanCompactificationProjection p)
    (kloostermanCompactificationEtaleObject p) r d

/-- Its component is the original derived coefficient map on the
original phase extension, followed by the original extension comparison. -/
theorem kloostermanCompactifiedCoefficientIso_hom_app (d : ℕ)
    (F : Sheaf (kloostermanPhaseScheme p).smallEtaleTopology (ModuleCat.{0} E')) :
    (kloostermanCompactifiedCoefficientIso p r d).hom.app F =
      (EtaleCoefficientRestriction.derivedDirectImageMap
          (kloostermanCompactificationProjection p) r d).app
          ((kloostermanPhaseExtensionByZero p E').obj F) ≫
        (EtaleDerivedDirectImage.functor (kloostermanCompactificationProjection p) E d).map
          ((EtaleExtensionCoefficientRestriction.iso (kloostermanCompactificationScheme p)
            (kloostermanCompactificationEtaleObject p) r).hom.app F) :=
  EtaleCompactSupportCoefficientRestriction.iso_hom_app (kloostermanCompactificationProjection p)
    (kloostermanCompactificationEtaleObject p) r d F

/-- The ordinary comparison on the unchanged proper model and open immersion. -/
def kloostermanCompactifiedCoefficientOrdinaryIso :
    (kloostermanPhaseExtensionByZero p E' ⋙
        EtaleDirectImage.functor (kloostermanCompactificationProjection p) E') ⋙
        EtaleCoefficientRestriction.functor (Spec (.of (Polynomial (ZMod p)))) r ≅
      EtaleCoefficientRestriction.functor (kloostermanPhaseScheme p) r ⋙
        (kloostermanPhaseExtensionByZero p E ⋙
          EtaleDirectImage.functor (kloostermanCompactificationProjection p) E) :=
  EtaleCompactSupportCoefficientRestriction.ordinaryIso (kloostermanCompactificationProjection p)
    (kloostermanCompactificationEtaleObject p) r

/-- The actual degree-zero comparison commutes with the unchanged
canonical zero-degree isomorphisms and their original augmentations. -/
theorem kloostermanCompactifiedCoefficientIso_zero :
    Functor.whiskerRight (kloostermanCompactifiedDerivedImage_zeroIso p E').inv
        (EtaleCoefficientRestriction.functor (Spec (.of (Polynomial (ZMod p)))) r) ≫
        (kloostermanCompactifiedCoefficientIso p r 0).hom =
      (kloostermanCompactifiedCoefficientOrdinaryIso p r).hom ≫
        Functor.whiskerLeft (EtaleCoefficientRestriction.functor (kloostermanPhaseScheme p) r)
          (kloostermanCompactifiedDerivedImage_zeroIso p E).inv :=
  EtaleCompactSupportCoefficientRestriction.iso_zero (kloostermanCompactificationProjection p)
    (kloostermanCompactificationEtaleObject p) r

end ArbitraryCoefficients

section FiniteCoefficients

attribute [local instance] kloostermanPhaseRing_charP

variable (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell)

/-- The actual derived image computed in the original finite
coefficient category, on the original finite-level phase sheaf. -/
def kloostermanFiniteCoefficientDerivedImage (d n : ℕ) :
    Sheaf (Spec (.of (Polynomial (ZMod p)))).smallEtaleTopology
      (ModuleCat.{0} (TorsionCoefficientRing p ell n)) :=
  (kloostermanCompactifiedDerivedImage p (TorsionCoefficientRing p ell n) d).obj
    (torsionArtinSchreierSheaf p ell hne n (kloostermanPhaseFunction p))

/-- This object literally applies the original higher direct image
to the original finite-coefficient extension by zero. -/
theorem kloostermanFiniteCoefficientDerivedImage_eq (d n : ℕ) :
    kloostermanFiniteCoefficientDerivedImage p ell hne d n =
      (EtaleDerivedDirectImage.functor (kloostermanCompactificationProjection p)
        (TorsionCoefficientRing p ell n) d).obj
        ((kloostermanPhaseExtensionByZero p (TorsionCoefficientRing p ell n)).obj
          (torsionArtinSchreierSheaf p ell hne n (kloostermanPhaseFunction p))) := rfl

/-- Restriction along the actual coefficient projection identifies
the finite-category derived image with the original common-coefficient
tower object, without replacing either original object. -/
def kloostermanFiniteCoefficientToTowerIso (d n : ℕ) :
    (EtaleCoefficientRestriction.functor (Spec (.of (Polynomial (ZMod p))))
        (torsionCoefficientLimitProjection p ell n)).obj
        (kloostermanFiniteCoefficientDerivedImage p ell hne d n) ≅
      (kloostermanTorsionDerivedTower p ell hne d).obj (op n) :=
  (kloostermanCompactifiedCoefficientIso p (torsionCoefficientLimitProjection p ell n) d).app
    (torsionArtinSchreierSheaf p ell hne n (kloostermanPhaseFunction p))

/-- The levelwise forward map is the same proved coefficient comparison
evaluated on the original finite-level phase sheaf. -/
theorem kloostermanFiniteCoefficientToTowerIso_hom (d n : ℕ) :
    (kloostermanFiniteCoefficientToTowerIso p ell hne d n).hom =
      (kloostermanCompactifiedCoefficientIso p (torsionCoefficientLimitProjection p ell n) d).hom.app
        (torsionArtinSchreierSheaf p ell hne n (kloostermanPhaseFunction p)) := rfl

/-- Expanded completely, the levelwise map retains the original
derived coefficient map and the original extension coefficient map. -/
theorem kloostermanFiniteCoefficientToTowerIso_hom_original (d n : ℕ) :
    (kloostermanFiniteCoefficientToTowerIso p ell hne d n).hom =
      (EtaleCoefficientRestriction.derivedDirectImageMap
          (kloostermanCompactificationProjection p)
          (torsionCoefficientLimitProjection p ell n) d).app
          ((kloostermanPhaseExtensionByZero p (TorsionCoefficientRing p ell n)).obj
            (torsionArtinSchreierSheaf p ell hne n (kloostermanPhaseFunction p))) ≫
        (EtaleDerivedDirectImage.functor (kloostermanCompactificationProjection p)
          (TorsionCoefficientLimit p ell) d).map
          ((EtaleExtensionCoefficientRestriction.iso (kloostermanCompactificationScheme p)
            (kloostermanCompactificationEtaleObject p)
            (torsionCoefficientLimitProjection p ell n)).hom.app
              (torsionArtinSchreierSheaf p ell hne n (kloostermanPhaseFunction p))) :=
  kloostermanCompactifiedCoefficientIso_hom_app p (torsionCoefficientLimitProjection p ell n) d
    (torsionArtinSchreierSheaf p ell hne n (kloostermanPhaseFunction p))

/-- At each finite level, the comparison to the original tower
intertwines the original zero-degree augmentations in both coefficient categories. -/
theorem kloostermanFiniteCoefficientToTowerIso_zero (n : ℕ) :
    (EtaleCoefficientRestriction.functor (Spec (.of (Polynomial (ZMod p))))
        (torsionCoefficientLimitProjection p ell n)).map
        ((kloostermanCompactifiedDerivedImage_zeroIso p (TorsionCoefficientRing p ell n)).inv.app
          (torsionArtinSchreierSheaf p ell hne n (kloostermanPhaseFunction p))) ≫
        (kloostermanFiniteCoefficientToTowerIso p ell hne 0 n).hom =
      (kloostermanCompactifiedCoefficientOrdinaryIso p
          (torsionCoefficientLimitProjection p ell n)).hom.app
          (torsionArtinSchreierSheaf p ell hne n (kloostermanPhaseFunction p)) ≫
        (kloostermanCompactifiedDerivedImage_zeroIso p (TorsionCoefficientLimit p ell)).inv.app
          (torsionArtinSchreierLimitModuleSheaf p ell hne (kloostermanPhaseFunction p) n) :=
  NatTrans.congr_app
    (kloostermanCompactifiedCoefficientIso_zero p (torsionCoefficientLimitProjection p ell n))
    (torsionArtinSchreierSheaf p ell hne n (kloostermanPhaseFunction p))

end FiniteCoefficients

#print axioms kloostermanCompactifiedCoefficientIso
#print axioms kloostermanCompactifiedCoefficientIso_hom_app
#print axioms kloostermanCompactifiedCoefficientOrdinaryIso
#print axioms kloostermanCompactifiedCoefficientIso_zero
#print axioms kloostermanFiniteCoefficientDerivedImage
#print axioms kloostermanFiniteCoefficientDerivedImage_eq
#print axioms kloostermanFiniteCoefficientToTowerIso
#print axioms kloostermanFiniteCoefficientToTowerIso_hom
#print axioms kloostermanFiniteCoefficientToTowerIso_hom_original
#print axioms kloostermanFiniteCoefficientToTowerIso_zero

end PrimeGap182.TypeIII
