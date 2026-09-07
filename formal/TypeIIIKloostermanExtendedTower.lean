import TypeIIIKloostermanTorsionDerivedTower
import TypeIIIEtaleExtensionCoefficientComposition
import TypeIIITorsionArtinSchreierReductionComparison

/-!
# The actual extended Kloosterman coefficient tower

The original finite phase sheaves, restricted to the common coefficient
limit ring, are first extended by zero to the original proper model.
This gives a tower in the actual sheaf category on that model, before
any injective resolution or derived inverse limit is taken.

Its transitions are the original reductions mapped by the original
extension functor. Extension computed in each finite coefficient category
gives an isomorphic tower after restriction to the common ring. Those
finite-category transitions are defined independently from the original
reduction and the original extension coefficient comparison.

Postcomposition with each existing ordinary higher direct image recovers
the already constructed degreewise tower. This is functor composition,
not an identification of the right derived functor of q_* composed with
j! with the right derived functor of their composite. No limit, derived
limit, or adic-cohomology comparison is asserted.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry Opposite

attribute [local instance] kloostermanPhaseRing_charP

variable (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell)

/-- The original common-coefficient phase tower extended to the actual proper model. -/
def kloostermanTorsionExtendedTower :
    ℕᵒᵖ ⥤ Sheaf (kloostermanCompactificationScheme p).smallEtaleTopology
      (ModuleCat.{0} (TorsionCoefficientLimit p ell)) :=
  torsionArtinSchreierLimitModuleTower p ell hne (kloostermanPhaseFunction p) ⋙
    kloostermanPhaseExtensionByZero p (TorsionCoefficientLimit p ell)

/-- Every level is the original extension of the original common-coefficient sheaf. -/
theorem kloostermanTorsionExtendedTower_obj (n : ℕ) :
    (kloostermanTorsionExtendedTower p ell hne).obj (op n) =
      (kloostermanPhaseExtensionByZero p (TorsionCoefficientLimit p ell)).obj
        (torsionArtinSchreierLimitModuleSheaf p ell hne (kloostermanPhaseFunction p) n) := rfl

/-- Each transition maps the original reduction by the same extension functor. -/
theorem kloostermanTorsionExtendedTower_map {m n : ℕ} (hmn : m ≤ n) :
    (kloostermanTorsionExtendedTower p ell hne).map (homOfLE hmn).op =
      (kloostermanPhaseExtensionByZero p (TorsionCoefficientLimit p ell)).map
        (torsionArtinSchreierLimitModuleReduction p ell hne (kloostermanPhaseFunction p) hmn) := rfl

/-- The original torsion exponent survives actual extension by zero. -/
theorem kloostermanTorsionExtendedTower_nsmul_id (n : ℕ) :
    (ell ^ (n + 1)) • (𝟙 ((kloostermanTorsionExtendedTower p ell hne).obj (op n))) = 0 := by
  let F := kloostermanPhaseExtensionByZero p (TorsionCoefficientLimit p ell)
  have h := congrArg F.map
    (torsionArtinSchreierLimitModuleSheaf_nsmul_id p ell hne (kloostermanPhaseFunction p) n)
  rw [Functor.map_nsmul, F.map_id, Functor.map_zero] at h
  exact h

/-- Postcomposition by the existing ordinary higher direct image is exactly the old tower. -/
theorem kloostermanTorsionExtendedTower_postcomposeDerived (d : ℕ) :
    kloostermanTorsionExtendedTower p ell hne ⋙
        EtaleDerivedDirectImage.functor (kloostermanCompactificationProjection p)
          (TorsionCoefficientLimit p ell) d =
      kloostermanTorsionDerivedTower p ell hne d := rfl

/-- Applying the same extension to the original coefficient cone gives an actual cone. -/
def kloostermanLimitExtendedCone : Cone (kloostermanTorsionExtendedTower p ell hne) :=
  (kloostermanPhaseExtensionByZero p (TorsionCoefficientLimit p ell)).mapCone
    (limitArtinSchreierCone p ell hne (kloostermanPhaseFunction p))

/-- The vertex is the original limit-coefficient character sheaf extended by zero. -/
theorem kloostermanLimitExtendedCone_pt :
    (kloostermanLimitExtendedCone p ell hne).pt =
      (kloostermanPhaseExtensionByZero p (TorsionCoefficientLimit p ell)).obj
        (limitArtinSchreierSheaf p ell hne (kloostermanPhaseFunction p)) := rfl

/-- The cone maps are the extensions of the original maps to finite coefficients. -/
theorem kloostermanLimitExtendedCone_π_app (n : ℕ) :
    (kloostermanLimitExtendedCone p ell hne).π.app (op n) =
      (kloostermanPhaseExtensionByZero p (TorsionCoefficientLimit p ell)).map
        (limitArtinSchreierReduction p ell hne (kloostermanPhaseFunction p) n) := rfl

/-- Extension of the original level-n phase sheaf in its actual finite coefficient category. -/
def kloostermanFiniteCoefficientExtension (n : ℕ) :
    Sheaf (kloostermanCompactificationScheme p).smallEtaleTopology
      (ModuleCat.{0} (TorsionCoefficientRing p ell n)) :=
  (kloostermanPhaseExtensionByZero p (TorsionCoefficientRing p ell n)).obj
    (torsionArtinSchreierSheaf p ell hne n (kloostermanPhaseFunction p))

/-- The actual finite-category extension, restricted along the original limit projection. -/
def kloostermanFiniteCoefficientRestrictedExtension (n : ℕ) :
    Sheaf (kloostermanCompactificationScheme p).smallEtaleTopology
      (ModuleCat.{0} (TorsionCoefficientLimit p ell)) :=
  (EtaleCoefficientRestriction.functor (kloostermanCompactificationScheme p)
    (torsionCoefficientLimitProjection p ell n)).obj
      (kloostermanFiniteCoefficientExtension p ell hne n)

/-- The original extension coefficient comparison identifies the two actual extended levels. -/
def kloostermanFiniteCoefficientExtensionToTowerIso (n : ℕ) :
    kloostermanFiniteCoefficientRestrictedExtension p ell hne n ≅
      (kloostermanTorsionExtendedTower p ell hne).obj (op n) :=
  (EtaleExtensionCoefficientRestriction.iso (kloostermanCompactificationScheme p)
    (kloostermanCompactificationEtaleObject p)
    (torsionCoefficientLimitProjection p ell n)).app
      (torsionArtinSchreierSheaf p ell hne n (kloostermanPhaseFunction p))

/-- The forward map is the unchanged extension coefficient comparison. -/
theorem kloostermanFiniteCoefficientExtensionToTowerIso_hom (n : ℕ) :
    (kloostermanFiniteCoefficientExtensionToTowerIso p ell hne n).hom =
      (EtaleExtensionCoefficientRestriction.iso (kloostermanCompactificationScheme p)
        (kloostermanCompactificationEtaleObject p)
        (torsionCoefficientLimitProjection p ell n)).hom.app
          (torsionArtinSchreierSheaf p ell hne n (kloostermanPhaseFunction p)) := rfl

/-- The finite-category transition uses the original reduction and the original inverse comparison. -/
def kloostermanFiniteCoefficientExtendedReduction {m n : ℕ} (hmn : m ≤ n) :
    kloostermanFiniteCoefficientExtension p ell hne n ⟶
      (EtaleCoefficientRestriction.functor (kloostermanCompactificationScheme p)
        (torsionCoefficientReduce p ell hmn)).obj
          (kloostermanFiniteCoefficientExtension p ell hne m) :=
  (kloostermanPhaseExtensionByZero p (TorsionCoefficientRing p ell n)).map
      (torsionArtinSchreierReduction p ell hne (kloostermanPhaseFunction p) hmn) ≫
    (EtaleExtensionCoefficientRestriction.iso (kloostermanCompactificationScheme p)
      (kloostermanCompactificationEtaleObject p)
      (torsionCoefficientReduce p ell hmn)).inv.app
        (torsionArtinSchreierSheaf p ell hne m (kloostermanPhaseFunction p))

/-- Restrict the independently defined finite transition using the original scalar comparison. -/
def kloostermanFiniteCoefficientRestrictedExtendedReduction {m n : ℕ} (hmn : m ≤ n) :
    kloostermanFiniteCoefficientRestrictedExtension p ell hne n ⟶
      kloostermanFiniteCoefficientRestrictedExtension p ell hne m :=
  (EtaleCoefficientRestriction.functor (kloostermanCompactificationScheme p)
      (torsionCoefficientLimitProjection p ell n)).map
      (kloostermanFiniteCoefficientExtendedReduction p ell hne hmn) ≫
    (EtaleCoefficientRestriction.compIso' (kloostermanCompactificationScheme p)
      (torsionCoefficientLimitProjection p ell n) (torsionCoefficientReduce p ell hmn)
      (torsionCoefficientLimitProjection p ell m)
      (torsionCoefficientLimitProjection_compatible p ell hmn).symm).inv.app
        (kloostermanFiniteCoefficientExtension p ell hne m)

/-- The original comparison intertwines the independently defined transition with the actual tower. -/
theorem kloostermanFiniteCoefficientRestrictedExtendedReduction_toTower
    {m n : ℕ} (hmn : m ≤ n) :
    kloostermanFiniteCoefficientRestrictedExtendedReduction p ell hne hmn ≫
        (kloostermanFiniteCoefficientExtensionToTowerIso p ell hne m).hom =
      (kloostermanFiniteCoefficientExtensionToTowerIso p ell hne n).hom ≫
        (kloostermanPhaseExtensionByZero p (TorsionCoefficientLimit p ell)).map
          (torsionArtinSchreierLimitModuleReduction p ell hne (kloostermanPhaseFunction p) hmn) := by
  let S := kloostermanCompactificationScheme p
  let U := kloostermanCompactificationEtaleObject p
  let f := torsionCoefficientLimitProjection p ell n
  let g := torsionCoefficientReduce p ell hmn
  let gf := torsionCoefficientLimitProjection p ell m
  let hgf := (torsionCoefficientLimitProjection_compatible p ell hmn).symm
  let F := torsionArtinSchreierSheaf p ell hne m (kloostermanPhaseFunction p)
  let eA := (EtaleCoefficientRestriction.compIso' S f g gf hgf).app
    ((EtaleExtensionByZero.functor S U (TorsionCoefficientRing p ell m)).obj F)
  let eB := (EtaleCoefficientRestriction.functor S f).mapIso
    ((EtaleExtensionCoefficientRestriction.iso S U g).app F)
  let eC := (EtaleExtensionCoefficientRestriction.iso S U f).app
    ((EtaleCoefficientRestriction.functor U.left g).obj F)
  let eD := (EtaleExtensionCoefficientRestriction.iso S U gf).app F
  let eE := (EtaleExtensionByZero.functor S U (TorsionCoefficientLimit p ell)).mapIso
    ((EtaleCoefficientRestriction.compIso' U.left f g gf hgf).app F)
  have h : eA.hom ≫ eB.hom ≫ eC.hom = eD.hom ≫ eE.hom :=
    EtaleExtensionCoefficientRestriction.iso_comp' S U f g gf hgf F
  have h' := congrArg (fun z => eB.inv ≫ eA.inv ≫ z ≫ eE.inv) h
  simp only [assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, comp_id] at h'
  have hcomp := h'.symm
  have hnat := (EtaleExtensionCoefficientRestriction.iso S U f).hom.naturality
    (torsionArtinSchreierReduction p ell hne (kloostermanPhaseFunction p) hmn)
  rw [kloostermanFiniteCoefficientRestrictedExtendedReduction,
    kloostermanFiniteCoefficientExtendedReduction, Functor.map_comp]
  simp only [assoc]
  erw [hcomp]
  rw [← assoc]
  erw [hnat]
  rw [assoc]
  change (kloostermanFiniteCoefficientExtensionToTowerIso p ell hne n).hom ≫
      (kloostermanPhaseExtensionByZero p (TorsionCoefficientLimit p ell)).map
        ((EtaleCoefficientRestriction.functor (kloostermanPhaseScheme p)
          (torsionCoefficientLimitProjection p ell n)).map
            (torsionArtinSchreierReduction p ell hne (kloostermanPhaseFunction p) hmn)) ≫
      (kloostermanPhaseExtensionByZero p (TorsionCoefficientLimit p ell)).map
        ((EtaleCoefficientRestriction.compIso' (kloostermanPhaseScheme p)
          (torsionCoefficientLimitProjection p ell n) (torsionCoefficientReduce p ell hmn)
          (torsionCoefficientLimitProjection p ell m)
          (torsionCoefficientLimitProjection_compatible p ell hmn).symm).inv.app
            (torsionArtinSchreierSheaf p ell hne m (kloostermanPhaseFunction p))) = _
  rw [← Functor.map_comp, ← torsionArtinSchreierLimitModuleReduction_eq_restrictScalars]

/-- The independently defined common-coefficient identity transition is the actual identity. -/
theorem kloostermanFiniteCoefficientRestrictedExtendedReduction_refl (n : ℕ) :
    kloostermanFiniteCoefficientRestrictedExtendedReduction p ell hne (le_refl n) =
      𝟙 (kloostermanFiniteCoefficientRestrictedExtension p ell hne n) := by
  apply (Iso.cancel_iso_hom_right _ _
    (kloostermanFiniteCoefficientExtensionToTowerIso p ell hne n)).mp
  rw [kloostermanFiniteCoefficientRestrictedExtendedReduction_toTower,
    torsionArtinSchreierLimitModuleReduction_refl]
  erw [CategoryTheory.Functor.map_id, comp_id]

/-- Successive independently defined finite transitions agree with the direct transition. -/
theorem kloostermanFiniteCoefficientRestrictedExtendedReduction_comp {k m n : ℕ}
    (hkm : k ≤ m) (hmn : m ≤ n) :
    kloostermanFiniteCoefficientRestrictedExtendedReduction p ell hne hmn ≫
        kloostermanFiniteCoefficientRestrictedExtendedReduction p ell hne hkm =
      kloostermanFiniteCoefficientRestrictedExtendedReduction p ell hne (hkm.trans hmn) := by
  apply (Iso.cancel_iso_hom_right _ _
    (kloostermanFiniteCoefficientExtensionToTowerIso p ell hne k)).mp
  rw [assoc, kloostermanFiniteCoefficientRestrictedExtendedReduction_toTower p ell hne hkm,
    ← assoc, kloostermanFiniteCoefficientRestrictedExtendedReduction_toTower p ell hne hmn,
    assoc, ← Functor.map_comp, torsionArtinSchreierLimitModuleReduction_comp,
    kloostermanFiniteCoefficientRestrictedExtendedReduction_toTower]

/-- The independently extended finite-category objects and reductions form an actual tower. -/
def kloostermanFiniteCoefficientExtendedTower :
    ℕᵒᵖ ⥤ Sheaf (kloostermanCompactificationScheme p).smallEtaleTopology
      (ModuleCat.{0} (TorsionCoefficientLimit p ell)) where
  obj n := kloostermanFiniteCoefficientRestrictedExtension p ell hne n.unop
  map g := kloostermanFiniteCoefficientRestrictedExtendedReduction p ell hne (leOfHom g.unop)
  map_id n := kloostermanFiniteCoefficientRestrictedExtendedReduction_refl p ell hne n.unop
  map_comp g h := (kloostermanFiniteCoefficientRestrictedExtendedReduction_comp p ell hne
    (leOfHom h.unop) (leOfHom g.unop)).symm

/-- The unchanged coefficient comparisons identify the two actual extended towers. -/
def kloostermanFiniteCoefficientExtendedTowerIso :
    kloostermanFiniteCoefficientExtendedTower p ell hne ≅
      kloostermanTorsionExtendedTower p ell hne :=
  NatIso.ofComponents
    (fun n => kloostermanFiniteCoefficientExtensionToTowerIso p ell hne n.unop)
    (by
      intro n m g
      exact kloostermanFiniteCoefficientRestrictedExtendedReduction_toTower
        p ell hne (leOfHom g.unop))

/-- The tower comparison retains the original levelwise comparison. -/
theorem kloostermanFiniteCoefficientExtendedTowerIso_app (n : ℕ) :
    (kloostermanFiniteCoefficientExtendedTowerIso p ell hne).app (op n) =
      kloostermanFiniteCoefficientExtensionToTowerIso p ell hne n := rfl

#print axioms kloostermanTorsionExtendedTower
#print axioms kloostermanTorsionExtendedTower_obj
#print axioms kloostermanTorsionExtendedTower_map
#print axioms kloostermanTorsionExtendedTower_nsmul_id
#print axioms kloostermanTorsionExtendedTower_postcomposeDerived
#print axioms kloostermanLimitExtendedCone
#print axioms kloostermanLimitExtendedCone_pt
#print axioms kloostermanLimitExtendedCone_π_app
#print axioms kloostermanFiniteCoefficientExtension
#print axioms kloostermanFiniteCoefficientRestrictedExtension
#print axioms kloostermanFiniteCoefficientExtensionToTowerIso
#print axioms kloostermanFiniteCoefficientExtensionToTowerIso_hom
#print axioms kloostermanFiniteCoefficientExtendedReduction
#print axioms kloostermanFiniteCoefficientRestrictedExtendedReduction
#print axioms kloostermanFiniteCoefficientRestrictedExtendedReduction_toTower
#print axioms kloostermanFiniteCoefficientRestrictedExtendedReduction_refl
#print axioms kloostermanFiniteCoefficientRestrictedExtendedReduction_comp
#print axioms kloostermanFiniteCoefficientExtendedTower
#print axioms kloostermanFiniteCoefficientExtendedTowerIso
#print axioms kloostermanFiniteCoefficientExtendedTowerIso_app

end PrimeGap182.TypeIII
