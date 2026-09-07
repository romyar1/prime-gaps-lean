import TypeIIIEtaleGeometricFiberCohomology
import TypeIIIEtaleDerivedBaseChangeZero

/-!
# Degree zero of the actual geometric-fiber comparison

The ordinary geometric stalk-to-fiber-sections map is constructed from
the existing ordinary pullback mate and the proved stalk and sections
comparisons.  The full transported derived map in degree zero
intertwines this ordinary map with the canonical zero isomorphisms on
both its source and target.

This is a compatibility of the actual maps.  It does not assert that
either base-change map is invertible.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleGeometricFiberCohomology

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  {X S : Scheme.{u}} (q : X ⟶ S) (s : Spec (.of Ω) ⟶ S)
  (E : Type u) [Ring E]

/-- The source of the original ordinary comparison becomes the actual geometric stalk. -/
def ordinarySourceIso :
    (EtaleDirectImage.functor q E ⋙ EtaleInverseImage.functor s E) ⋙
        EtaleCohomology.sections (Spec (.of Ω)) E ≅
      EtaleDirectImage.functor q E ⋙
        (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} E) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (EtaleDirectImage.functor q E) (pullbackSectionsIso s E)

/-- The ordinary target is global sections of the actual pulled-back sheaf on the fiber. -/
def ordinaryTargetIso :
    (EtaleInverseImage.functor (pullback.fst q s) E ⋙
        EtaleDirectImage.functor (pullback.snd q s) E) ⋙
        EtaleCohomology.sections (Spec (.of Ω)) E ≅
      EtaleInverseImage.functor (pullback.fst q s) E ⋙
        EtaleCohomology.sections (pullback q s) E :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (EtaleInverseImage.functor (pullback.fst q s) E)
      (EtaleCohomology.directImageIso (pullback.snd q s) E)

/-- The same ordinary pullback mate, expressed between the actual geometric stalk
and actual sections on the literal geometric fiber. -/
def ordinaryBaseChangeMap :
    EtaleDirectImage.functor q E ⋙
        (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} E) ⟶
      EtaleInverseImage.functor (pullback.fst q s) E ⋙
        EtaleCohomology.sections (pullback q s) E :=
  (ordinarySourceIso q s E).inv ≫
    Functor.whiskerRight (EtaleInverseImage.pullbackBaseChangeMap q s E)
      (EtaleCohomology.sections (Spec (.of Ω)) E) ≫
    (ordinaryTargetIso q s E).hom

/-- Transport recovers the original ordinary mate after actual global sections. -/
theorem ordinaryBaseChangeMap_transport :
    (ordinarySourceIso q s E).hom ≫ ordinaryBaseChangeMap q s E =
      Functor.whiskerRight (EtaleInverseImage.pullbackBaseChangeMap q s E)
          (EtaleCohomology.sections (Spec (.of Ω)) E) ≫
        (ordinaryTargetIso q s E).hom := by
  simp only [ordinaryBaseChangeMap, Iso.hom_inv_id_assoc]

/-- The ordinary component is the original stalk comparison, original ordinary mate,
and original direct-image comparison for sections. -/
theorem ordinaryBaseChangeMap_app
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) :
    (ordinaryBaseChangeMap q s E).app F =
      (pullbackSectionsIso s E).inv.app ((EtaleDirectImage.functor q E).obj F) ≫
        (EtaleCohomology.sections (Spec (.of Ω)) E).map
          ((EtaleInverseImage.pullbackBaseChangeMap q s E).app F) ≫
        (EtaleCohomology.directImageIso (pullback.snd q s) E).hom.app
          ((EtaleInverseImage.functor (pullback.fst q s) E).obj F) := by
  simp only [ordinaryBaseChangeMap, ordinarySourceIso, ordinaryTargetIso,
    Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, id_comp, comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The full geometric-fiber comparison in degree zero commutes with
the canonical maps from original direct image and original fiber sections. -/
theorem baseChangeMap_zero :
    Functor.whiskerRight (EtaleDerivedDirectImage.zeroIso q E).inv
        ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} E)) ≫
        baseChangeMap q s E 0 =
      ordinaryBaseChangeMap q s E ≫
        Functor.whiskerLeft (EtaleInverseImage.functor (pullback.fst q s) E)
          (EtaleCohomology.zeroIso (pullback q s) E).inv := by
  apply NatTrans.ext
  funext F
  have hsource := (pullbackSectionsIso s E).inv.naturality
    ((EtaleDerivedDirectImage.zeroIso q E).inv.app F)
  simp only [Functor.comp_map] at hsource
  have hderived := NatTrans.congr_app
    (EtaleDerivedBaseChange.baseChangeMap_zero q s (pullback.snd q s)
      (pullback.fst q s) (pullback.condition (f := q) (g := s)) E) F
  change (EtaleInverseImage.functor s E).map ((EtaleDerivedDirectImage.zeroIso q E).inv.app F) ≫
      (EtaleDerivedBaseChange.pullbackBaseChangeMap q s E 0).app F =
    (EtaleInverseImage.pullbackBaseChangeMap q s E).app F ≫
      (EtaleDerivedDirectImage.zeroIso (pullback.snd q s) E).inv.app
        ((EtaleInverseImage.functor (pullback.fst q s) E).obj F) at hderived
  have hcohom := NatTrans.congr_app (closedBaseIso_zero (pullback.snd q s) E)
    ((EtaleInverseImage.functor (pullback.fst q s) E).obj F)
  change (EtaleCohomology.sections (Spec (.of Ω)) E).map
      ((EtaleDerivedDirectImage.zeroIso (pullback.snd q s) E).inv.app
        ((EtaleInverseImage.functor (pullback.fst q s) E).obj F)) ≫
      (closedBaseIso (pullback.snd q s) E 0).hom.app
        ((EtaleInverseImage.functor (pullback.fst q s) E).obj F) =
    (EtaleCohomology.directImageIso (pullback.snd q s) E).hom.app
        ((EtaleInverseImage.functor (pullback.fst q s) E).obj F) ≫
      (EtaleCohomology.zeroIso (pullback q s) E).inv.app
        ((EtaleInverseImage.functor (pullback.fst q s) E).obj F) at hcohom
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    baseChangeMap_app, ordinaryBaseChangeMap_app, assoc]
  rw [← assoc, hsource, assoc]
  rw [← (EtaleCohomology.sections (Spec (.of Ω)) E).map_comp_assoc,
    hderived, Functor.map_comp, assoc, hcohom]

set_option backward.isDefEq.respectTransparency false in
/-- Under the canonical zero isomorphisms, the full transported derived map
is exactly the original ordinary geometric stalk-to-fiber-sections map. -/
theorem baseChangeMap_zero_eq :
    baseChangeMap q s E 0 =
      Functor.whiskerRight (EtaleDerivedDirectImage.zeroIso q E).hom
          ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} E)) ≫
        ordinaryBaseChangeMap q s E ≫
        Functor.whiskerLeft (EtaleInverseImage.functor (pullback.fst q s) E)
          (EtaleCohomology.zeroIso (pullback q s) E).inv := by
  let Z := Functor.isoWhiskerRight (EtaleDerivedDirectImage.zeroIso q E)
    ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} E))
  rw [← cancel_epi Z.inv]
  change Z.inv ≫ baseChangeMap q s E 0 = Z.inv ≫ Z.hom ≫ _
  rw [Iso.inv_hom_id_assoc]
  exact baseChangeMap_zero q s E
#print axioms ordinarySourceIso
#print axioms ordinaryTargetIso
#print axioms ordinaryBaseChangeMap
#print axioms ordinaryBaseChangeMap_transport
#print axioms ordinaryBaseChangeMap_app
#print axioms baseChangeMap_zero
#print axioms baseChangeMap_zero_eq

end PrimeGap182.TypeIII.EtaleGeometricFiberCohomology
