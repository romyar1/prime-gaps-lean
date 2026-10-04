import TypeIIIPublishedPhysicalConstruction

/-!
# Base change of the original parabolic image

Exact pullback and compatible base-change isomorphisms for compact and
ordinary cohomology induce an isomorphism of the original parabolic
images. This constructs the image comparison; it does not assume one.
Both canonical maps are preserved, and compatible actions commute with
the resulting isomorphism.

The general compact/ordinary base-change theorems, exactness of pullback,
and compatibility with the support-forgetting map remain explicit inputs.
They are applied here to arbitrary inputs, not a finished Type III family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.ParabolicBaseChange

open PublishedPhysicalConstruction

universe u v w z a b
variable {Input : Type u} {Input' : Type v}
  {C : Type w} [Category.{a} C] [Abelian C]
  {C' : Type z} [Category.{b} C'] [Abelian C']
  (H : CohomologyData Input C) (H' : CohomologyData Input' C')
  (B : C ⥤ C') (pull : Input → Input')

/-- General base-change maps and their compatibility with forgetting
supports, for every curve input. No parabolic image is part of the data. -/
structure CohomologyBaseChange where
  compact : ∀ A, B.obj (H.compact A) ≅ H'.compact (pull A)
  ordinary : ∀ A, B.obj (H.ordinary A) ≅ H'.ordinary (pull A)
  comparison : ∀ A,
    (compact A).hom ≫ H'.comparison (pull A) = B.map (H.comparison A) ≫ (ordinary A).hom

variable (R : CohomologyBaseChange H H' B pull)

/-- Base change compares the two original cohomology arrows. -/
def comparisonArrowIso (A : Input) :
    Arrow.mk (B.map (H.comparison A)) ≅ Arrow.mk (H'.comparison (pull A)) :=
  Arrow.isoMk (R.compact A) (R.ordinary A) (R.comparison A)

variable [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B]

/-- The parabolic image comparison is constructed by image functoriality
and Mathlib's preservation of abelian images by exact functors. -/
def parabolicBaseChangeIso (A : Input) :
    B.obj (parabolicCore H A) ≅ parabolicCore H' (pull A) :=
  Abelian.PreservesImage.iso B (H.comparison A) ≪≫
    Abelian.im.mapIso (comparisonArrowIso H H' B pull R A)

/-- Preserve the inclusion into the original ordinary cohomology. -/
theorem parabolicBaseChangeIso_toOrdinary (A : Input) :
    (parabolicBaseChangeIso H H' B pull R A).hom ≫ Abelian.image.ι (H'.comparison (pull A)) =
      B.map (Abelian.image.ι (H.comparison A)) ≫ (R.ordinary A).hom := by
  have him : (Abelian.im.mapIso (comparisonArrowIso H H' B pull R A)).hom ≫
      Abelian.image.ι (H'.comparison (pull A)) =
      Abelian.image.ι (B.map (H.comparison A)) ≫ (R.ordinary A).hom := by
    change kernel.lift _ _ _ ≫ kernel.ι _ = _
    exact kernel.lift_ι _ _ _
  change ((Abelian.PreservesImage.iso B (H.comparison A)).hom ≫
    (Abelian.im.mapIso (comparisonArrowIso H H' B pull R A)).hom) ≫ _ = _
  rw [Category.assoc, him, ← Category.assoc, Abelian.PreservesImage.iso_hom_ι]

/-- Preserve the original quotient out of compact cohomology. -/
theorem fromCompact_parabolicBaseChangeIso (A : Input) :
    B.map (Abelian.factorThruImage (H.comparison A)) ≫ (parabolicBaseChangeIso H H' B pull R A).hom =
      (R.compact A).hom ≫ Abelian.factorThruImage (H'.comparison (pull A)) := by
  apply (cancel_mono (Abelian.image.ι (H'.comparison (pull A)))).mp
  rw [Category.assoc, parabolicBaseChangeIso_toOrdinary, ← Category.assoc,
    ← B.map_comp, Abelian.image.fac, Category.assoc, Abelian.image.fac, R.comparison]

/-- The constructed comparison commutes with arbitrary compatible
actions. Inertia and arithmetic operators are particular applications. -/
theorem parabolicBaseChangeIso_natural (A : Input)
    (a : B.obj (H.compact A) ⟶ B.obj (H.compact A))
    (b : B.obj (parabolicCore H A) ⟶ B.obj (parabolicCore H A))
    (a' : H'.compact (pull A) ⟶ H'.compact (pull A))
    (b' : parabolicCore H' (pull A) ⟶ parabolicCore H' (pull A))
    (hab : a ≫ B.map (Abelian.factorThruImage (H.comparison A)) =
      B.map (Abelian.factorThruImage (H.comparison A)) ≫ b)
    (hab' : a' ≫ Abelian.factorThruImage (H'.comparison (pull A)) =
      Abelian.factorThruImage (H'.comparison (pull A)) ≫ b')
    (ha : a ≫ (R.compact A).hom = (R.compact A).hom ≫ a') :
    b ≫ (parabolicBaseChangeIso H H' B pull R A).hom =
      (parabolicBaseChangeIso H H' B pull R A).hom ≫ b' := by
  apply (cancel_epi (B.map (Abelian.factorThruImage (H.comparison A)))).mp
  rw [← Category.assoc, ← hab, Category.assoc, fromCompact_parabolicBaseChangeIso,
    ← Category.assoc, ha, Category.assoc, hab', ← Category.assoc,
    ← fromCompact_parabolicBaseChangeIso, Category.assoc]

end PrimeGap182.TypeIII.ParabolicBaseChange

#print axioms PrimeGap182.TypeIII.ParabolicBaseChange.comparisonArrowIso
#print axioms PrimeGap182.TypeIII.ParabolicBaseChange.parabolicBaseChangeIso
#print axioms PrimeGap182.TypeIII.ParabolicBaseChange.parabolicBaseChangeIso_toOrdinary
#print axioms PrimeGap182.TypeIII.ParabolicBaseChange.fromCompact_parabolicBaseChangeIso
#print axioms PrimeGap182.TypeIII.ParabolicBaseChange.parabolicBaseChangeIso_natural
