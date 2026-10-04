import TypeIIIParabolicBaseChange

/-!
# Transport the original parabolic image along input isomorphisms

Compact and ordinary cohomology are functors, and forgetting supports is
natural. These general laws construct the comparison on the original
cohomology objects and hence on their images. Both original image maps
are retained. No image or family identification is supplied as a premise.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.CohomologyInputTransport

open PublishedPhysicalConstruction

universe u v w z
variable {Input : Type u} [Category.{v} Input]
  {C : Type w} [Category.{z} C]
  (H : CohomologyData Input C)

/-- A functorial realization of the original cohomology data and its
support-forgetting map, for all inputs and their morphisms. -/
structure FunctorialCohomology where
  compact : Input ⥤ C
  ordinary : Input ⥤ C
  compactObject : ∀ A, compact.obj A ≅ H.compact A
  ordinaryObject : ∀ A, ordinary.obj A ≅ H.ordinary A
  support : compact ⟶ ordinary
  comparison : ∀ A,
    (compactObject A).hom ≫ H.comparison A = support.app A ≫ (ordinaryObject A).hom

variable (R : FunctorialCohomology H)

/-- Transport on the original compact cohomology objects. -/
def compactIso {A B : Input} (e : A ≅ B) : H.compact A ≅ H.compact B :=
  (R.compactObject A).symm ≪≫ R.compact.mapIso e ≪≫ R.compactObject B

/-- Transport on the original ordinary cohomology objects. -/
def ordinaryIso {A B : Input} (e : A ≅ B) : H.ordinary A ≅ H.ordinary B :=
  (R.ordinaryObject A).symm ≪≫ R.ordinary.mapIso e ≪≫ R.ordinaryObject B

/-- Naturality supplies the square for the original support map. -/
theorem comparison_natural {A B : Input} (e : A ≅ B) :
    (compactIso H R e).hom ≫ H.comparison B =
      H.comparison A ≫ (ordinaryIso H R e).hom := by
  apply (cancel_epi (R.compactObject A).hom).mp
  simp only [compactIso, ordinaryIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_assoc]
  calc
    R.compact.map e.hom ≫ (R.compactObject B).hom ≫ H.comparison B =
        R.compact.map e.hom ≫ R.support.app B ≫ (R.ordinaryObject B).hom := by
      rw [R.comparison B]
    _ = R.support.app A ≫ R.ordinary.map e.hom ≫ (R.ordinaryObject B).hom := by
      rw [← Category.assoc, R.support.naturality, Category.assoc]
    _ = (R.compactObject A).hom ≫ H.comparison A ≫ (R.ordinaryObject A).inv ≫
        R.ordinary.map e.hom ≫ (R.ordinaryObject B).hom := by
      rw [← Category.assoc (R.compactObject A).hom (H.comparison A), R.comparison A]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]


/-- Isomorphism of the literal cohomology arrows. -/
def comparisonArrowIso {A B : Input} (e : A ≅ B) :
    Arrow.mk (H.comparison A) ≅ Arrow.mk (H.comparison B) :=
  Arrow.isoMk (compactIso H R e) (ordinaryIso H R e) (comparison_natural H R e)

variable [Abelian C]

/-- The original parabolic image is transported by image functoriality. -/
def parabolicInputIso {A B : Input} (e : A ≅ B) :
    parabolicCore H A ≅ parabolicCore H B :=
  Abelian.im.mapIso (comparisonArrowIso H R e)

theorem parabolicInputIso_toOrdinary {A B : Input} (e : A ≅ B) :
    (parabolicInputIso H R e).hom ≫ Abelian.image.ι (H.comparison B) =
      Abelian.image.ι (H.comparison A) ≫ (ordinaryIso H R e).hom := by
  change kernel.lift _ _ _ ≫ kernel.ι _ = _
  exact kernel.lift_ι _ _ _

theorem fromCompact_parabolicInputIso {A B : Input} (e : A ≅ B) :
    Abelian.factorThruImage (H.comparison A) ≫ (parabolicInputIso H R e).hom =
      (compactIso H R e).hom ≫ Abelian.factorThruImage (H.comparison B) := by
  apply (cancel_mono (Abelian.image.ι (H.comparison B))).mp
  rw [Category.assoc, parabolicInputIso_toOrdinary, ← Category.assoc,
    Abelian.image.fac, Category.assoc, Abelian.image.fac, comparison_natural]

end PrimeGap182.TypeIII.CohomologyInputTransport

#print axioms PrimeGap182.TypeIII.CohomologyInputTransport.compactIso
#print axioms PrimeGap182.TypeIII.CohomologyInputTransport.ordinaryIso
#print axioms PrimeGap182.TypeIII.CohomologyInputTransport.comparison_natural
#print axioms PrimeGap182.TypeIII.CohomologyInputTransport.comparisonArrowIso
#print axioms PrimeGap182.TypeIII.CohomologyInputTransport.parabolicInputIso
#print axioms PrimeGap182.TypeIII.CohomologyInputTransport.parabolicInputIso_toOrdinary
#print axioms PrimeGap182.TypeIII.CohomologyInputTransport.fromCompact_parabolicInputIso
