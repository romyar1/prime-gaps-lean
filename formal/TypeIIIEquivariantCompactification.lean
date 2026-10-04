import TypeIIIFourierStalkInertia

/-!
# A shared representation-valued compactification diagram

Affine and projective cohomology, and their comparison maps, are taken in
the same inertia representation category as the compact cohomology stalk.
Forgetting the action constructs the existing compactification diagram.
Its affine inertia action and compact-map compatibility are then derived,
not separately supplied. The outgoing geometric-point H1 map is zero.

The general geometric cohomology functors and their canonical maps remain
published inputs. Localization exactness remains separate. No completed
family comparison, rank, or Fourier estimate is a field of this diagram.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.EquivariantCompactification

open PublishedPhysicalConstruction BoundaryFromSourceModels MiddleFromLocalization
open FourierStalkInertia

universe u v a b c d

variable {Input : Type u} [Category.{c} Input] {Point : Type v}
  {C : Type} [Category.{d} C] [Abelian C]
  {G : Type c} [Group G]
  {D : CurveData Input Point} {H : CohomologyData Input C}
  (J : C ⥤ FDRep ℂ G)
  {BS : BoundarySequence D H (J ⋙ forgetInertia G)}
  {G0 : Type a} [Group G0] {Ginf : Type b} [Group Ginf]
  (Z : RestrictionData (G0 := G0) (Ginf := Ginf) D H (J ⋙ forgetInertia G) BS)

/-- General cohomology and localization maps before forgetting inertia.
The boundary input has no outer-inertia structure, since the comparison
proof only uses its underlying map and the positive-slope vanishing. -/
structure Data where
  affine : Input ⥤ FDRep ℂ G
  projective : Input ⥤ FDRep ℂ G
  fromCompact : ∀ A, J.obj (H.compact A) ⟶ affine.obj A
  toProjective : affine ⟶ projective
  leray : ∀ A, projective.obj A ⟶ J.obj (H.ordinary A)
  fromInfinity : ∀ A, invariantModule (Z.infinity A) ⟶
    (affine ⋙ forgetInertia G).obj A

variable (S : Data J Z)

/-- Construct the original linear diagram using these exact maps. -/
def Data.compactification : CompactificationData Z where
  affine := S.affine ⋙ forgetInertia G
  projective := S.projective ⋙ forgetInertia G
  fromCompact A := (forgetInertia G).map (S.fromCompact A)
  toProjective A := (forgetInertia G).map (S.toProjective.app A)
  leray A := (forgetInertia G).map (S.leray A)
  fromInfinity := S.fromInfinity
  toZero _ := 0

/-- The action is read from the shared affine cohomology functor. -/
def Data.inertia : FunctorInertia S.compactification.affine G :=
  FunctorInertia.ofFDRepFunctor S.affine

omit [Abelian C] in
/-- Compatibility follows from the original comparison being a morphism
of representations; it is not an additional family or naturality premise. -/
theorem Data.localizationInertia :
    LocalizationInertia Z S.compactification (FunctorInertia.ofFDRepFunctor J) S.inertia := by
  constructor
  intro A s
  exact congrArg (fun f => f.hom.hom) ((S.fromCompact A).comm s)

end PrimeGap182.TypeIII.EquivariantCompactification

#print axioms PrimeGap182.TypeIII.EquivariantCompactification.Data.compactification
#print axioms PrimeGap182.TypeIII.EquivariantCompactification.Data.inertia
#print axioms PrimeGap182.TypeIII.EquivariantCompactification.Data.localizationInertia
