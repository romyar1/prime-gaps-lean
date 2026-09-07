import TypeIIISheafTowerEvaluation
import TypeIIIRightDerivedPlusComparison

/-!
# Cohomology of the original derived direct image of a tower

The original evaluation comparison is natural both in the tower and in
its index.  It therefore identifies the right derived functor of the
pointwise direct image with the tower obtained by applying the original
ordinary higher direct image at each level.

The existing comparison between ordinary right derived functors and
bounded below derived-category cohomology then identifies the cohomology
towers of the full derived object.  This statement retains every original
transition.  It neither takes an inverse limit nor interchanges a limit
with cohomology.
-/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII.EtaleDerivedImageTower

open CategoryTheory CategoryTheory.Category AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (q : X ⟶ S) (E : Type u) [Ring E]

/-- Apply the original ordinary higher direct image at every level of a tower. -/
def pointwise (d : ℕ) : EtaleSheafTower.Tower X E ⥤ EtaleSheafTower.Tower S E :=
  (Functor.whiskeringRight ℕᵒᵖ
    (Sheaf X.smallEtaleTopology (ModuleCat.{u} E))
    (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))).obj
      ((EtaleDirectImage.functor q E).rightDerived d)

/-- The actual higher direct image in the tower category is the original
levelwise higher direct image, including the original transition maps. -/
def iso (d : ℕ) :
    (EtaleTowerDirectImage.functor q E).rightDerived d ≅ pointwise q E d :=
  NatIso.ofComponents
    (fun T => NatIso.ofComponents
      (fun n => (EtaleSheafTowerEvaluation.evaluationBaseChangeIso q E n.unop d).app T)
      (by
        intro n m a
        exact EtaleSheafTowerEvaluation.evaluationBaseChangeIso_index_naturality
          q E d a T))
    (by
      intro T T' f
      apply NatTrans.ext
      funext n
      exact (EtaleSheafTowerEvaluation.evaluationBaseChangeIso q E n.unop d).hom.naturality f)

/-- Every component is the original evaluation base-change comparison. -/
theorem iso_hom_app_app (d : ℕ) (T : EtaleSheafTower.Tower X E) (n : ℕᵒᵖ) :
    ((iso q E d).hom.app T).app n =
      (EtaleSheafTowerEvaluation.evaluationBaseChangeIso q E n.unop d).hom.app T := rfl

/-- The cohomology of the full original derived tower is the ordinary tower
of higher direct images, with all coefficient transitions retained. -/
def cohomologyIso (d : ℕ) :
    DerivedCategory.Plus.singleFunctor (EtaleSheafTower.Tower X E) 0 ⋙
        (EtaleTowerDirectImage.functor q E).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor (EtaleSheafTower.Tower S E) (d : ℤ) ≅
      pointwise q E d :=
  (rightDerivedPlusComparisonIso (EtaleTowerDirectImage.functor q E) d).symm ≪≫ iso q E d

/-- The cohomology isomorphism is normalized by the existing resolution/unit
comparison and the original evaluation comparison. -/
theorem cohomologyIso_hom_fac (d : ℕ) :
    (rightDerivedPlusComparisonIso (EtaleTowerDirectImage.functor q E) d).hom ≫
        (cohomologyIso q E d).hom = (iso q E d).hom := by
  simp only [cohomologyIso, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

end PrimeGap182.TypeIII.EtaleDerivedImageTower

#print axioms PrimeGap182.TypeIII.EtaleDerivedImageTower.pointwise
#print axioms PrimeGap182.TypeIII.EtaleDerivedImageTower.iso
#print axioms PrimeGap182.TypeIII.EtaleDerivedImageTower.iso_hom_app_app
#print axioms PrimeGap182.TypeIII.EtaleDerivedImageTower.cohomologyIso
#print axioms PrimeGap182.TypeIII.EtaleDerivedImageTower.cohomologyIso_hom_fac
