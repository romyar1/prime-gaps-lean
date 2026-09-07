import TypeIIIKloostermanFiberCompactification
import TypeIIIEtaleGeometricFiberCohomology
import TypeIIIEtaleCompactSupportBaseChange

/-!
# The original relative Kloosterman image maps to cohomology of its actual fiber

The original geometric stalk and the actual cohomology on the proper
fiber are the two endpoints of the existing compact-support base-change
map after taking global sections over the separably closed field.

The source and target isomorphisms are already proved.  The comparison
between them is the original derived base-change map, followed by the
proved compatibility of extension by zero with inverse image.  The
component and transport identities record these exact constructions.
No invertibility of this geometric-point base-change map is asserted.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable (p : ℕ) {Ω : Type} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ Spec (.of (Polynomial (ZMod p)))) (E : Type) [Ring E]

/-- The actual pullback-section source of the fixed-family map is its original geometric stalk. -/
def kloostermanFiberBaseChangeSourceIso (n : ℕ) :
    (kloostermanCompactifiedDerivedImage p E n ⋙ EtaleInverseImage.functor s E) ⋙
        EtaleCohomology.sections (Spec (.of Ω)) E ≅
      kloostermanCompactifiedDerivedImage p E n ⋙
        (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{0} E) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (kloostermanCompactifiedDerivedImage p E n)
      (EtaleGeometricFiberCohomology.pullbackSectionsIso s E)

/-- The target's actual global sections are cohomology of the actual extension on the proper fiber. -/
def kloostermanFiberBaseChangeTargetIso (n : ℕ) :
    EtaleCompactSupportBaseChange.targetFunctor (kloostermanCompactificationProjection p)
        (kloostermanCompactificationOpenImmersion p) s E n ⋙
        EtaleCohomology.sections (Spec (.of Ω)) E ≅
      kloostermanFiberCompactCohomology p s E n :=
  Functor.isoWhiskerLeft (kloostermanFiberPhaseExtension p s E)
    (EtaleGeometricFiberCohomology.closedBaseIso
      (kloostermanCompactificationFiberProjection p s) E n)

/-- The actual stalk-to-fiber-cohomology map for the unchanged compactified phase family. -/
def kloostermanFiberBaseChange (n : ℕ) :
    kloostermanCompactifiedDerivedImage p E n ⋙
        (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{0} E) ⟶
      kloostermanFiberCompactCohomology p s E n :=
  (kloostermanFiberBaseChangeSourceIso p s E n).inv ≫
    Functor.whiskerRight (kloostermanCompactSupportBaseChange p s E n)
      (EtaleCohomology.sections (Spec (.of Ω)) E) ≫
    (kloostermanFiberBaseChangeTargetIso p s E n).hom

/-- The new endpoints transport precisely the existing compact-support base-change map. -/
theorem kloostermanFiberBaseChange_transport (n : ℕ) :
    (kloostermanFiberBaseChangeSourceIso p s E n).hom ≫
        kloostermanFiberBaseChange p s E n =
      Functor.whiskerRight (kloostermanCompactSupportBaseChange p s E n)
          (EtaleCohomology.sections (Spec (.of Ω)) E) ≫
        (kloostermanFiberBaseChangeTargetIso p s E n).hom := by
  simp only [kloostermanFiberBaseChange, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- On each original phase sheaf, apply the actual geometric-stalk comparison,
the original compact-support comparison, and the proved cohomology comparison. -/
theorem kloostermanFiberBaseChange_app (n : ℕ)
    (F : Sheaf (kloostermanPhaseScheme p).smallEtaleTopology (ModuleCat.{0} E)) :
    (kloostermanFiberBaseChange p s E n).app F =
      (EtaleGeometricFiberCohomology.pullbackSectionsIso s E).inv.app
          ((kloostermanCompactifiedDerivedImage p E n).obj F) ≫
        (EtaleCohomology.sections (Spec (.of Ω)) E).map
          ((kloostermanCompactSupportBaseChange p s E n).app F) ≫
        (EtaleGeometricFiberCohomology.closedBaseIso
          (kloostermanCompactificationFiberProjection p s) E n).hom.app
            ((kloostermanFiberPhaseExtension p s E).obj F) := by
  change ((_ ≫ 𝟙 _) ≫ _ ≫ _) = _
  rw [Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Expanding the actual compact-support comparison retains the original derived
base-change component on the original extension by zero. -/
theorem kloostermanFiberBaseChange_app_original (n : ℕ)
    (F : Sheaf (kloostermanPhaseScheme p).smallEtaleTopology (ModuleCat.{0} E)) :
    (kloostermanFiberBaseChange p s E n).app F =
      (EtaleGeometricFiberCohomology.pullbackSectionsIso s E).inv.app
          ((kloostermanCompactifiedDerivedImage p E n).obj F) ≫
        (EtaleCohomology.sections (Spec (.of Ω)) E).map
          ((kloostermanCompactifiedDerivedBaseChange p s E n).app F) ≫
        (EtaleCohomology.sections (Spec (.of Ω)) E).map
          ((EtaleDerivedDirectImage.functor
            (kloostermanCompactificationFiberProjection p s) E n).map
              ((kloostermanFiberPhaseExtensionIso p s E).hom.app F)) ≫
        (EtaleGeometricFiberCohomology.closedBaseIso
          (kloostermanCompactificationFiberProjection p s) E n).hom.app
            ((kloostermanFiberPhaseExtension p s E).obj F) := by
  rw [kloostermanFiberBaseChange_app, kloostermanCompactSupportBaseChange_app,
    Functor.map_comp, Category.assoc]
  rfl

#print axioms kloostermanFiberBaseChangeSourceIso
#print axioms kloostermanFiberBaseChangeTargetIso
#print axioms kloostermanFiberBaseChange
#print axioms kloostermanFiberBaseChange_transport
#print axioms kloostermanFiberBaseChange_app
#print axioms kloostermanFiberBaseChange_app_original

end PrimeGap182.TypeIII
