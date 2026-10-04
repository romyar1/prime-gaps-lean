import TypeIIICohomologyInputTransport
import TypeIIIEquivariantCompactification

/-!
# Cohomology objects and localization from the same general functors

The published framework supplies R1 f!, R1 f* and their natural support
map. We read the old object-level cohomology record from those functors,
so its functorial realization has identity object comparisons. The same
functors are the endpoints of the localization and Leray transformations.

The general localization corollary used below is for every lisse input:
the zero-localization map is surjective since a geometric point has H1=0;
the infinity localization is exact; the Leray edge map is injective; and
their composite is the original support map. These are explicit published
laws, not a constructed adic cohomology theory or a family-specific image
comparison. See Milne, Lectures on Etale Cohomology, 12.7 and 18.3(a).
https://www.jmilne.org/math/CourseNotes/LEC.pdf
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.PublishedCohomologyFunctor

open PublishedPhysicalConstruction CohomologyInputTransport
open BoundaryFromSourceModels MiddleFromLocalization FourierStalkInertia

universe u v w z a b

/-- The actual degree-one functors and the natural support-forgetting map. -/
structure Data (Input : Type u) [Category.{v} Input] (C : Type w) [Category.{z} C] where
  compact : Input ⥤ C
  ordinary : Input ⥤ C
  support : compact ⟶ ordinary

variable {Input : Type u} [Category.{v} Input] {C : Type w} [Category.{z} C]
  (H : Data Input C)

/-- Ordinary cohomology and support map on an already fixed compact
functor, supplied by extension by zero in the generic application. -/
structure OrdinaryData (compact : Input ⥤ C) where
  ordinary : Input ⥤ C
  support : compact ⟶ ordinary

/-- The old cohomology interface uses the fixed compact functor. -/
abbrev OrdinaryData.data {compact : Input ⥤ C} (O : OrdinaryData compact) : Data Input C where
  compact := compact
  ordinary := O.ordinary
  support := O.support

def Data.cohomology : CohomologyData Input C where
  compact := H.compact.obj
  ordinary := H.ordinary.obj
  comparison := H.support.app

/-- No second cohomology realization or object isomorphisms are supplied. -/
def Data.functorial : FunctorialCohomology H.cohomology where
  compact := H.compact
  ordinary := H.ordinary
  compactObject A := Iso.refl _
  ordinaryObject A := Iso.refl _
  support := H.support
  comparison A := by simp [Data.cohomology]

section Localization
variable {Input : Type u} [Category.{v} Input] {Point : Type w}
  {C : Type} [Category.{z} C] [Abelian C]
  (H : Data Input C) {G : Type v} [Group G] (J : C ⥤ FDRep ℂ G)
  {D : CurveData Input Point}
  {BS : BoundarySequence D H.cohomology (J ⋙ forgetInertia G)}
  {G0 : Type a} [Group G0] {Ginf : Type b} [Group Ginf]
  (Z : RestrictionData (G0 := G0) (Ginf := Ginf) D H.cohomology
    (J ⋙ forgetInertia G) BS)

/-- The canonical maps are natural transformations between the same
cohomology functors, before passing to individual objects or forgetting inertia. -/
structure LocalizationData where
  affine : Input ⥤ FDRep ℂ G
  projective : Input ⥤ FDRep ℂ G
  fromCompact : H.compact ⋙ J ⟶ affine
  toProjective : affine ⟶ projective
  leray : projective ⟶ H.ordinary ⋙ J
  fromInfinity : ∀ A, invariantModule (Z.infinity A) ⟶
    (affine ⋙ forgetInertia G).obj A

/-- Localization maps with their affine term fixed in advance by the
same extension and compact cohomology used by the Fourier comparison. -/
structure LocalizationMaps (affine : Input ⥤ FDRep ℂ G)
    (fromCompact : H.compact ⋙ J ⟶ affine) where
  projective : Input ⥤ FDRep ℂ G
  toProjective : affine ⟶ projective
  leray : projective ⟶ H.ordinary ⋙ J
  fromInfinity : ∀ A, invariantModule (Z.infinity A) ⟶
    (affine ⋙ forgetInertia G).obj A

variable {H J Z}

/-- Assemble localization with the already selected affine functor. -/
abbrev LocalizationMaps.localization {affine : Input ⥤ FDRep ℂ G}
    {fromCompact : H.compact ⋙ J ⟶ affine}
    (M : LocalizationMaps H J Z affine fromCompact) : LocalizationData H J Z where
  affine := affine
  projective := M.projective
  fromCompact := fromCompact
  toProjective := M.toProjective
  leray := M.leray
  fromInfinity := M.fromInfinity

variable (L : LocalizationData H J Z)

def LocalizationData.equivariant : EquivariantCompactification.Data J Z where
  affine := L.affine
  projective := L.projective
  fromCompact A := L.fromCompact.app A
  toProjective := L.toProjective
  leray A := L.leray.app A
  fromInfinity := L.fromInfinity

/-- Published general localization and Leray statements, on these exact
natural maps. No rank, phase set or Type III input occurs in these laws. -/
structure OtherLocalizationRules : Prop where
  comparison : ∀ A, D.Lisse A →
    L.fromCompact.app A ≫ L.toProjective.app A ≫ L.leray.app A = J.map (H.support.app A)
  infinityExact : ∀ A, D.Lisse A →
    LinearMap.range (L.fromInfinity A).hom =
      LinearMap.ker ((forgetInertia G).map (L.toProjective.app A)).hom
  lerayInjective : ∀ A, D.Lisse A →
    Function.Injective ((forgetInertia G).map (L.leray.app A)).hom

/-- The zero-localization consequence is separated from the other general
laws so it can be derived from compact exactness and point vanishing. -/
structure LocalizationRules : Prop extends OtherLocalizationRules L where
  zeroSurjective : ∀ A, D.Lisse A →
    Function.Surjective ((forgetInertia G).map (L.fromCompact.app A)).hom

variable {L} (R : LocalizationRules L)

omit [Abelian C] in
include R in
/-- Construct the original localization rules by forgetting the same
representation maps and identifying the outgoing point map with zero. -/
theorem LocalizationRules.compactificationRules :
    CompactificationRules Z L.equivariant.compactification where
  comparison A hA := by
    change (forgetInertia G).map (L.fromCompact.app A) ≫
      (forgetInertia G).map (L.toProjective.app A) ≫
      (forgetInertia G).map (L.leray.app A) =
        (forgetInertia G).map (J.map (H.support.app A))
    rw [← Functor.map_comp, ← Functor.map_comp, R.comparison A hA]
  zero_exact A hA := by
    change LinearMap.range ((forgetInertia G).map (L.fromCompact.app A)).hom =
      LinearMap.ker (0 : _ →ₗ[ℂ] _)
    rw [LinearMap.ker_zero]
    exact LinearMap.range_eq_top.mpr (R.zeroSurjective A hA)
  infinity_exact := R.infinityExact
  leray_injective := R.lerayInjective

end Localization
end PrimeGap182.TypeIII.PublishedCohomologyFunctor

#print axioms PrimeGap182.TypeIII.PublishedCohomologyFunctor.Data.cohomology
#print axioms PrimeGap182.TypeIII.PublishedCohomologyFunctor.Data.functorial
#print axioms PrimeGap182.TypeIII.PublishedCohomologyFunctor.LocalizationData.equivariant
#print axioms PrimeGap182.TypeIII.PublishedCohomologyFunctor.LocalizationRules.compactificationRules

#print axioms PrimeGap182.TypeIII.PublishedCohomologyFunctor.LocalizationMaps.localization

#print axioms PrimeGap182.TypeIII.PublishedCohomologyFunctor.OrdinaryData.data
