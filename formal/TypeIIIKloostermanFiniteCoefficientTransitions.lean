import TypeIIIKloostermanTorsionCoefficientComparison
import TypeIIIEtaleCoefficientRestrictionComposition
import TypeIIIEtaleCompactSupportCoefficientComposition
import TypeIIITorsionArtinSchreierReductionComparison

/-!
# Transitions of the actual finite-coefficient derived images

The transition from level n to level m is defined in the level-n
coefficient category by applying the original derived-image functor to
the original finite sheaf reduction and then using the inverse of the
original coefficient comparison.  Restriction to the common coefficient
ring uses its original projection-composition isomorphism.

These definitions retain the actual finite-category derived objects.
The transition is not defined by transport from the common-coefficient
tower.  The original coefficient comparisons intertwine these
independently defined maps with the existing tower.  Their proved
compatibility gives the functor laws and an isomorphism of the two
ordinary sheaf-valued inverse systems, in every degree.

No passage of cohomology through an inverse limit, adic-cohomology
comparison, concentration, or finiteness assertion is made.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry Opposite

attribute [local instance] kloostermanPhaseRing_charP

variable (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell)

/-- The actual finite-category derived image, restricted along the
original projection from the coefficient limit ring. -/
def kloostermanFiniteCoefficientRestrictedDerivedImage (d n : ℕ) :
    Sheaf (Spec (.of (Polynomial (ZMod p)))).smallEtaleTopology
      (ModuleCat.{0} (TorsionCoefficientLimit p ell)) :=
  (EtaleCoefficientRestriction.functor (Spec (.of (Polynomial (ZMod p))))
    (torsionCoefficientLimitProjection p ell n)).obj
      (kloostermanFiniteCoefficientDerivedImage p ell hne d n)

/-- The transition is defined from the original finite sheaf reduction
by the original finite-category derived functor and coefficient map. -/
def kloostermanFiniteCoefficientReduction (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    kloostermanFiniteCoefficientDerivedImage p ell hne d n ⟶
      (EtaleCoefficientRestriction.functor (Spec (.of (Polynomial (ZMod p))))
        (torsionCoefficientReduce p ell hmn)).obj
          (kloostermanFiniteCoefficientDerivedImage p ell hne d m) :=
  (kloostermanCompactifiedDerivedImage p (TorsionCoefficientRing p ell n) d).map
      (torsionArtinSchreierReduction p ell hne (kloostermanPhaseFunction p) hmn) ≫
    (kloostermanCompactifiedCoefficientIso p (torsionCoefficientReduce p ell hmn) d).inv.app
      (torsionArtinSchreierSheaf p ell hne m (kloostermanPhaseFunction p))

/-- The same independently defined transition in the common
coefficient category, using the original projection compatibility. -/
def kloostermanFiniteCoefficientRestrictedReduction (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    kloostermanFiniteCoefficientRestrictedDerivedImage p ell hne d n ⟶
      kloostermanFiniteCoefficientRestrictedDerivedImage p ell hne d m :=
  (EtaleCoefficientRestriction.functor (Spec (.of (Polynomial (ZMod p))))
      (torsionCoefficientLimitProjection p ell n)).map
      (kloostermanFiniteCoefficientReduction p ell hne d hmn) ≫
    (EtaleCoefficientRestriction.compIso' (Spec (.of (Polynomial (ZMod p))))
      (torsionCoefficientLimitProjection p ell n) (torsionCoefficientReduce p ell hmn)
      (torsionCoefficientLimitProjection p ell m)
      (torsionCoefficientLimitProjection_compatible p ell hmn).symm).inv.app
        (kloostermanFiniteCoefficientDerivedImage p ell hne d m)

/-- The original levelwise comparison respects the independently
defined finite-category transition and the original common-coefficient
sheaf reduction, after the original derived functor is applied. -/
theorem kloostermanFiniteCoefficientRestrictedReduction_toTower
    (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    kloostermanFiniteCoefficientRestrictedReduction p ell hne d hmn ≫
        (kloostermanFiniteCoefficientToTowerIso p ell hne d m).hom =
      (kloostermanFiniteCoefficientToTowerIso p ell hne d n).hom ≫
        (kloostermanCompactifiedDerivedImage p (TorsionCoefficientLimit p ell) d).map
          (torsionArtinSchreierLimitModuleReduction p ell hne (kloostermanPhaseFunction p) hmn) := by
  have hcomp := EtaleCompactSupportCoefficientRestriction.iso_inv_comp'_hom
    (kloostermanCompactificationProjection p) (kloostermanCompactificationEtaleObject p)
    (torsionCoefficientLimitProjection p ell n) (torsionCoefficientReduce p ell hmn)
    (torsionCoefficientLimitProjection p ell m)
    (torsionCoefficientLimitProjection_compatible p ell hmn).symm d
    (torsionArtinSchreierSheaf p ell hne m (kloostermanPhaseFunction p))
  have hnat := (kloostermanCompactifiedCoefficientIso p
    (torsionCoefficientLimitProjection p ell n) d).hom.naturality
      (torsionArtinSchreierReduction p ell hne (kloostermanPhaseFunction p) hmn)
  rw [kloostermanFiniteCoefficientRestrictedReduction, kloostermanFiniteCoefficientReduction,
    Functor.map_comp]
  simp only [assoc]
  erw [hcomp]
  rw [← assoc]
  erw [hnat]
  rw [assoc]
  change (kloostermanFiniteCoefficientToTowerIso p ell hne d n).hom ≫
      (kloostermanCompactifiedDerivedImage p (TorsionCoefficientLimit p ell) d).map
        ((EtaleCoefficientRestriction.functor (kloostermanPhaseScheme p)
          (torsionCoefficientLimitProjection p ell n)).map
            (torsionArtinSchreierReduction p ell hne (kloostermanPhaseFunction p) hmn)) ≫
      (kloostermanCompactifiedDerivedImage p (TorsionCoefficientLimit p ell) d).map
        ((EtaleCoefficientRestriction.compIso' (kloostermanPhaseScheme p)
          (torsionCoefficientLimitProjection p ell n) (torsionCoefficientReduce p ell hmn)
          (torsionCoefficientLimitProjection p ell m)
          (torsionCoefficientLimitProjection_compatible p ell hmn).symm).inv.app
            (torsionArtinSchreierSheaf p ell hne m (kloostermanPhaseFunction p))) = _
  rw [← Functor.map_comp,
    ← torsionArtinSchreierLimitModuleReduction_eq_restrictScalars]

/-- The independently defined transition from a level to itself is
the identity on its actual restricted finite-category derived object. -/
theorem kloostermanFiniteCoefficientRestrictedReduction_refl (d n : ℕ) :
    kloostermanFiniteCoefficientRestrictedReduction p ell hne d (le_refl n) =
      𝟙 (kloostermanFiniteCoefficientRestrictedDerivedImage p ell hne d n) := by
  apply (Iso.cancel_iso_hom_right _ _ (kloostermanFiniteCoefficientToTowerIso p ell hne d n)).mp
  rw [kloostermanFiniteCoefficientRestrictedReduction_toTower,
    torsionArtinSchreierLimitModuleReduction_refl]
  erw [CategoryTheory.Functor.map_id, comp_id]

/-- Successive independently defined transitions compose to the
direct transition; the original common-coefficient maps detect the equality. -/
theorem kloostermanFiniteCoefficientRestrictedReduction_comp (d : ℕ) {k m n : ℕ}
    (hkm : k ≤ m) (hmn : m ≤ n) :
    kloostermanFiniteCoefficientRestrictedReduction p ell hne d hmn ≫
        kloostermanFiniteCoefficientRestrictedReduction p ell hne d hkm =
      kloostermanFiniteCoefficientRestrictedReduction p ell hne d (hkm.trans hmn) := by
  apply (Iso.cancel_iso_hom_right _ _ (kloostermanFiniteCoefficientToTowerIso p ell hne d k)).mp
  rw [assoc, kloostermanFiniteCoefficientRestrictedReduction_toTower p ell hne d hkm,
    ← assoc, kloostermanFiniteCoefficientRestrictedReduction_toTower p ell hne d hmn,
    assoc, ← Functor.map_comp, torsionArtinSchreierLimitModuleReduction_comp,
    kloostermanFiniteCoefficientRestrictedReduction_toTower]

/-- The actual derived images computed in their finite coefficient
categories, with the independently defined transitions, form an inverse
system after the original restrictions to the common coefficient ring. -/
def kloostermanFiniteCoefficientDerivedTower (d : ℕ) :
    ℕᵒᵖ ⥤ Sheaf (Spec (.of (Polynomial (ZMod p)))).smallEtaleTopology
      (ModuleCat.{0} (TorsionCoefficientLimit p ell)) where
  obj n := kloostermanFiniteCoefficientRestrictedDerivedImage p ell hne d n.unop
  map g := kloostermanFiniteCoefficientRestrictedReduction p ell hne d (leOfHom g.unop)
  map_id n := kloostermanFiniteCoefficientRestrictedReduction_refl p ell hne d n.unop
  map_comp g h := (kloostermanFiniteCoefficientRestrictedReduction_comp p ell hne d
    (leOfHom h.unop) (leOfHom g.unop)).symm

/-- The original levelwise isomorphisms are an isomorphism of the
actual inverse systems, including every original reduction map. -/
def kloostermanFiniteCoefficientDerivedTowerIso (d : ℕ) :
    kloostermanFiniteCoefficientDerivedTower p ell hne d ≅
      kloostermanTorsionDerivedTower p ell hne d :=
  NatIso.ofComponents (fun n => kloostermanFiniteCoefficientToTowerIso p ell hne d n.unop)
    (by
      intro n m g
      exact kloostermanFiniteCoefficientRestrictedReduction_toTower p ell hne d (leOfHom g.unop))

/-- Each component is precisely the original finite-category comparison. -/
theorem kloostermanFiniteCoefficientDerivedTowerIso_app (d n : ℕ) :
    (kloostermanFiniteCoefficientDerivedTowerIso p ell hne d).app (op n) =
      kloostermanFiniteCoefficientToTowerIso p ell hne d n := rfl

#print axioms kloostermanFiniteCoefficientRestrictedDerivedImage
#print axioms kloostermanFiniteCoefficientReduction
#print axioms kloostermanFiniteCoefficientRestrictedReduction
#print axioms kloostermanFiniteCoefficientRestrictedReduction_toTower
#print axioms kloostermanFiniteCoefficientRestrictedReduction_refl
#print axioms kloostermanFiniteCoefficientRestrictedReduction_comp
#print axioms kloostermanFiniteCoefficientDerivedTower
#print axioms kloostermanFiniteCoefficientDerivedTowerIso
#print axioms kloostermanFiniteCoefficientDerivedTowerIso_app

end PrimeGap182.TypeIII
