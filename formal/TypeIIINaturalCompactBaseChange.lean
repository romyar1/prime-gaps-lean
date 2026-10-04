import TypeIIISharedCohomology
import TypeIIIPublishedCohomologyFunctor

/-!
# Compact base change from a single natural comparison

The general compact base-change theorem supplies a natural isomorphism
between the actual degree-one functors. Its components give the former
objectwise comparisons, including the comparison on the dual source.
Naturality retains their compatibility with all original morphisms.

This is the general Rf! base-change input, after degree-one cohomology
and exact inverse image (Laumon §0.5, SGA 4 XVII). The existing lisse
dual/Tate comparison remains explicit. No ordinary base-change theorem
or compact-pairing compatibility is introduced here.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.NaturalCompactBaseChange
open PublishedPhysicalConstruction SharedCohomology PublishedCohomologyFunctor

universe u v w z a b c d e
variable {Input : Type u} [Category.{v} Input]
  {Input' : Type w} [Category.{z} Input']
  {C : Type a} [Category.{b} C] {C' : Type c} [Category.{d} C']
  (H : PublishedCohomologyFunctor.Data Input C)
  (H' : PublishedCohomologyFunctor.Data Input' C')
  (P : ParameterData C) (DT : Cᵒᵖ ⥤ C) (DT' : C'ᵒᵖ ⥤ C')
  (B : C ⥤ C') (pull : Input ⥤ Input')

/-- General compact base change on the already selected functors, with
the unchanged lissity guard for parameter dual/Tate base change. -/
structure Data where
  compact : H.compact ⋙ B ≅ pull ⋙ H'.compact
  dualTate : ∀ V, P.Lisse V →
    (B.obj (DT.obj (Opposite.op V)) ≅ DT'.obj (Opposite.op (B.obj V)))

variable {H H' P DT DT' B pull} (M : Data H H' P DT DT' B pull)

/-- The same component is used for every occurrence of this input. -/
def Data.compactIso (A : Input) :
    B.obj (H.cohomology.compact A) ≅ H'.cohomology.compact (pull.obj A) :=
  M.compact.app A

theorem Data.compact_natural {A C : Input} (f : A ⟶ C) :
    B.map (H.compact.map f) ≫ (M.compactIso C).hom =
      (M.compactIso A).hom ≫ H'.compact.map (pull.map f) :=
  M.compact.hom.naturality f

/-- The inverse comparison also uses these same morphisms. -/
theorem Data.compact_inv_natural {A C : Input} (f : A ⟶ C) :
    H'.compact.map (pull.map f) ≫ (M.compactIso C).inv =
      (M.compactIso A).inv ≫ B.map (H.compact.map f) :=
  M.compact.inv.naturality f

variable {Point : Type e} (D : CurveData Input Point)
  [Abelian C] [Abelian C']

/-- Apply the general natural comparison to the old guarded interface.
The compact component needs no lissity restriction; the downstream
duality construction retains its original guards. -/
def Data.comparisons :
    BaseChangeComparisons (D := D) (H := H.cohomology) DT P
      H'.cohomology DT' B pull where
  compact A _ := M.compactIso A
  dualTate := M.dualTate

end PrimeGap182.TypeIII.NaturalCompactBaseChange

#print axioms PrimeGap182.TypeIII.NaturalCompactBaseChange.Data.compactIso
#print axioms PrimeGap182.TypeIII.NaturalCompactBaseChange.Data.compact_natural
#print axioms PrimeGap182.TypeIII.NaturalCompactBaseChange.Data.compact_inv_natural
#print axioms PrimeGap182.TypeIII.NaturalCompactBaseChange.Data.comparisons
