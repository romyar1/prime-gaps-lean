import TypeIIIEtaleCohomology
import TypeIIIEtaleClosedFieldSections
import TypeIIIEtaleDerivedBaseChange
import TypeIIIRightDerivedPostcompose

/-!
# The cohomological target of geometric-point base change

Over a separably closed field, the proved exactness of actual global
sections identifies global sections of Rⁿq_* with the actual étale
cohomology of the source.  The degree-zero comparison retains the
original resolution augmentations and the actual direct-image section
comparison.

For any scheme morphism and geometric point of its base, the existing
derived base-change map is transported through this isomorphism and
the original inverse-image stalk isomorphism.  Its target is cohomology
of the literal geometric fiber with the actual pulled-back sheaf.
Invertibility of this base-change map is not asserted.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleGeometricFiberCohomology

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

section ClosedBase

variable {X : Scheme.{u}} (q : X ⟶ Spec (.of Ω)) (E : Type u) [Ring E]

/-- Actual global sections of derived direct image over the closed field
are the actual étale cohomology of the source. -/
def closedBaseIso (n : ℕ) :
    EtaleDerivedDirectImage.functor q E n ⋙
        EtaleCohomology.sections (Spec (.of Ω)) E ≅
      EtaleCohomology.functor X E n := by
  let : (EtaleCohomology.sections (Spec (.of Ω)) E).PreservesHomology :=
    EtaleClosedFieldSections.sections_preservesHomology Ω E
  exact rightDerivedPostcomposeIso (EtaleDirectImage.functor q E)
    (EtaleCohomology.sections X E) (EtaleCohomology.sections (Spec (.of Ω)) E)
    (EtaleCohomology.directImageIso q E) n

/-- Equivalently, the original identity geometric stalk of Rⁿq_*
is the actual cohomology of its source. -/
def closedBaseStalkIso (n : ℕ) :
    EtaleDerivedDirectImage.functor q E n ⋙
        (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber (A := ModuleCat.{u} E) ≅
      EtaleCohomology.functor X E n :=
  Functor.isoWhiskerLeft (EtaleDerivedDirectImage.functor q E n)
      (EtaleClosedFieldSections.stalkIso Ω E) ≪≫
    closedBaseIso q E n

/-- At degree zero this isomorphism intertwines the original augmentation maps. -/
theorem closedBaseIso_zero :
    Functor.whiskerRight (EtaleDerivedDirectImage.zeroIso q E).inv
        (EtaleCohomology.sections (Spec (.of Ω)) E) ≫ (closedBaseIso q E 0).hom =
      (EtaleCohomology.directImageIso q E).hom ≫ (EtaleCohomology.zeroIso X E).inv := by
  let : (EtaleCohomology.sections (Spec (.of Ω)) E).PreservesHomology :=
    EtaleClosedFieldSections.sections_preservesHomology Ω E
  exact rightDerivedPostcomposeIso_zero (EtaleDirectImage.functor q E)
    (EtaleCohomology.sections X E) (EtaleCohomology.sections (Spec (.of Ω)) E)
    (EtaleCohomology.directImageIso q E)

/-- The degree-zero isomorphism is precisely the original direct-image section comparison
through the canonical degree-zero identifications. -/
theorem closedBaseIso_zero_eq :
    (closedBaseIso q E 0).hom =
      Functor.whiskerRight (EtaleDerivedDirectImage.zeroIso q E).hom
          (EtaleCohomology.sections (Spec (.of Ω)) E) ≫
        (EtaleCohomology.directImageIso q E).hom ≫ (EtaleCohomology.zeroIso X E).inv := by
  let Z := Functor.isoWhiskerRight (EtaleDerivedDirectImage.zeroIso q E)
    (EtaleCohomology.sections (Spec (.of Ω)) E)
  rw [← cancel_epi Z.inv]
  change Z.inv ≫ (closedBaseIso q E 0).hom = Z.inv ≫ Z.hom ≫ _
  rw [Iso.inv_hom_id_assoc]
  exact closedBaseIso_zero q E

end ClosedBase

section GeometricPoint

variable {S : Scheme.{u}} (s : Spec (.of Ω) ⟶ S) (E : Type u) [Ring E]

/-- Pullback to the geometric point followed by its actual global sections
is the original geometric stalk on the base. -/
def pullbackSectionsIso :
    EtaleInverseImage.functor s E ⋙ EtaleCohomology.sections (Spec (.of Ω)) E ≅
      (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} E) := by
  let e : EtaleInverseImage.functor s E ⋙
        (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber (A := ModuleCat.{u} E) ≅
      (Scheme.pointSmallEtale s).sheafFiber := by
    simpa only [id_comp] using EtaleInverseImage.stalkIso s E (𝟙 (Spec (.of Ω)))
  exact Functor.isoWhiskerLeft (EtaleInverseImage.functor s E)
      (EtaleClosedFieldSections.stalkIso Ω E).symm ≪≫ e

end GeometricPoint

section FiberComparison

variable {X S : Scheme.{u}} (q : X ⟶ S) (s : Spec (.of Ω) ⟶ S)
  (E : Type u) [Ring E]

/-- The source of the original derived comparison, after actual global sections,
is the geometric stalk of derived direct image. -/
def sourceIso (n : ℕ) :
    (EtaleDerivedDirectImage.functor q E n ⋙ EtaleInverseImage.functor s E) ⋙
        EtaleCohomology.sections (Spec (.of Ω)) E ≅
      EtaleDerivedDirectImage.functor q E n ⋙
        (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} E) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (EtaleDerivedDirectImage.functor q E n) (pullbackSectionsIso s E)

/-- The target of the same comparison is actual cohomology on the literal
geometric fiber, with the actual inverse-image sheaf. -/
def targetIso (n : ℕ) :
    (EtaleInverseImage.functor (pullback.fst q s) E ⋙
        EtaleDerivedDirectImage.functor (pullback.snd q s) E n) ⋙
        EtaleCohomology.sections (Spec (.of Ω)) E ≅
      EtaleInverseImage.functor (pullback.fst q s) E ⋙
        EtaleCohomology.functor (pullback q s) E n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (EtaleInverseImage.functor (pullback.fst q s) E)
      (closedBaseIso (pullback.snd q s) E n)

/-- The original geometric-point base-change map, expressed as a map
from the actual stalk to actual fiber cohomology. -/
def baseChangeMap (n : ℕ) :
    EtaleDerivedDirectImage.functor q E n ⋙
        (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} E) ⟶
      EtaleInverseImage.functor (pullback.fst q s) E ⋙
        EtaleCohomology.functor (pullback q s) E n :=
  (sourceIso q s E n).inv ≫
    Functor.whiskerRight (EtaleDerivedBaseChange.pullbackBaseChangeMap q s E n)
      (EtaleCohomology.sections (Spec (.of Ω)) E) ≫
    (targetIso q s E n).hom

/-- The comparison is transported from the existing derived base-change map,
with no replacement of its underlying resolution construction. -/
theorem baseChangeMap_transport (n : ℕ) :
    (sourceIso q s E n).hom ≫ baseChangeMap q s E n =
      Functor.whiskerRight (EtaleDerivedBaseChange.pullbackBaseChangeMap q s E n)
          (EtaleCohomology.sections (Spec (.of Ω)) E) ≫
        (targetIso q s E n).hom := by
  simp only [baseChangeMap, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- At a sheaf, the map uses the original geometric stalk comparison,
the actual derived pullback component, and the proved fiber-cohomology isomorphism. -/
theorem baseChangeMap_app (n : ℕ)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) :
    (baseChangeMap q s E n).app F =
      (pullbackSectionsIso s E).inv.app ((EtaleDerivedDirectImage.functor q E n).obj F) ≫
        (EtaleCohomology.sections (Spec (.of Ω)) E).map
          ((EtaleDerivedBaseChange.pullbackBaseChangeMap q s E n).app F) ≫
        (closedBaseIso (pullback.snd q s) E n).hom.app
          ((EtaleInverseImage.functor (pullback.fst q s) E).obj F) := by
  change ((_ ≫ 𝟙 _) ≫ _ ≫ (𝟙 _ ≫ _)) = _
  simp only [id_comp, comp_id]
  rfl

end FiberComparison

#print axioms closedBaseIso
#print axioms closedBaseStalkIso
#print axioms closedBaseIso_zero
#print axioms closedBaseIso_zero_eq
#print axioms pullbackSectionsIso
#print axioms sourceIso
#print axioms targetIso
#print axioms baseChangeMap
#print axioms baseChangeMap_transport
#print axioms baseChangeMap_app

end PrimeGap182.TypeIII.EtaleGeometricFiberCohomology
