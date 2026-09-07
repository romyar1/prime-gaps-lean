import TypeIIIDerivedBaseChangeZero
import TypeIIIEtaleDerivedBaseChange

/-!
# Degree zero of actual étale derived base change

Under the canonical identifications of zeroth derived direct image with
direct image, the constructed derived morphism is exactly the original
ordinary unit-square-counit mate. All hypotheses of the generic
augmentation comparison are supplied by the proved étale functors.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleDerivedBaseChange

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry

variable {X' X S' S : Scheme.{u}} (q : X ⟶ S) (g : S' ⟶ S)
  (q' : X' ⟶ S') (g' : X' ⟶ X) (h : g' ≫ q = q' ≫ g) (E : Type u) [Ring E]

/-- The canonical maps to zeroth derived direct image commute with the actual ordinary mate. -/
theorem baseChangeMap_zero :
    Functor.whiskerRight (EtaleDerivedDirectImage.zeroIso q E).inv
        (EtaleInverseImage.functor g E) ≫ baseChangeMap q g q' g' h E 0 =
      EtaleInverseImage.baseChangeMap q g q' g' h E ≫
        Functor.whiskerLeft (EtaleInverseImage.functor g' E)
          (EtaleDerivedDirectImage.zeroIso q' E).inv :=
  derivedBaseChangeMap_zero (EtaleDirectImage.functor q E)
    (EtaleDirectImage.functor q' E) (EtaleInverseImage.functor g' E)
    (EtaleInverseImage.functor g E) (EtaleInverseImage.baseChangeMap q g q' g' h E)

/-- The degree-zero derived morphism is the original ordinary map through the canonical isos. -/
theorem baseChangeMap_zero_eq :
    baseChangeMap q g q' g' h E 0 =
      Functor.whiskerRight (EtaleDerivedDirectImage.zeroIso q E).hom
        (EtaleInverseImage.functor g E) ≫
      EtaleInverseImage.baseChangeMap q g q' g' h E ≫
        Functor.whiskerLeft (EtaleInverseImage.functor g' E)
          (EtaleDerivedDirectImage.zeroIso q' E).inv := by
  let Z := Functor.isoWhiskerRight (EtaleDerivedDirectImage.zeroIso q E)
    (EtaleInverseImage.functor g E)
  rw [← cancel_epi Z.inv]
  change Z.inv ≫ baseChangeMap q g q' g' h E 0 = Z.inv ≫ Z.hom ≫ _
  rw [Iso.inv_hom_id_assoc]
  exact baseChangeMap_zero q g q' g' h E

#print axioms baseChangeMap_zero
#print axioms baseChangeMap_zero_eq

end PrimeGap182.TypeIII.EtaleDerivedBaseChange
