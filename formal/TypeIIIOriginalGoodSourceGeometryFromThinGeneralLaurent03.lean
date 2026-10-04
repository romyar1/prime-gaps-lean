import TypeIIISourceCurveBaseChange
import TypeIIISourceProjectionForQST
import TypeIIICoherentSourceGlobalCohomologyFromGuardedLaurent04
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Thin actual Laurent-coordinate application of GENERAL projective-line geometry

Only elementary affine ring/scheme coordinate theorems and geometry records
are retained from the archived adapters. No native finite-lattice, arithmetic
Euler or aggregate source-lissity import is used. The identity Laurent chart
and its projection square are proved below on the original source schemes.

The one all-fields/all-Laurent-chart standard P1 geometry law is fixed before
K and every sheaf. It constructs the independently good geometry needed by
GC04, with actual positive/inverse charts and finite-flat 0/infinity boundary.
It contains no ULA, conductor, cohomology, lissity or endpoint conclusion.
This staged conditional application does not reconstruct projective schemes
or assert goodness of an arbitrary retained compactification.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.OriginalGoodSourceGeometryFromThinGeneralLaurent03
open ExactInverseImagesToDerived QSTCompactBridgeFromCompactifiedDerivedPushforward
open FullFourierCoreFromNativeBoundedOperations
open QSTDualityBridgesFromSmoothLisseVerdier
open CoherentSourceGlobalCohomologyFromGuardedLaurent04

/-- Actual coordinates of ANY integral relative Laurent curve. -/
structure LaurentCurveChart (K : Type) [Field K] {X Y : Scheme} (f : X ⟶ Y) where
  R : Type
  [ring : CommRing R]
  [domain : IsDomain R]
  [algebra : Algebra K R]
  sourceIso : X ≅ Spec (.of (LaurentPolynomial R))
  baseIso : Y ≅ Spec (.of R)
  projection_square : sourceIso.hom ≫
    Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : R →+* LaurentPolynomial R)) =
      f ≫ baseIso.hom

attribute [instance] LaurentCurveChart.ring LaurentCurveChart.domain LaurentCurveChart.algebra


/-- A good P1-type geometry witness has actual positive and inverse charts,
proper smooth relative dimension one, and actual finite-flat closed boundary.
It contains no sheaf, lissity, ULA, cohomology or desired-result clause. -/
structure GoodGeometryFrame (K : Type) [Field K] {X Y : Scheme}
    (PX : FieldPresentation K X) (PY : FieldPresentation K Y) (f : X ⟶ Y)
    (chart : LaurentCurveChart K f) where
  compactification : CompactificationOver K PX PY f
  [smoothOne : SmoothOfRelativeDimension 1 compactification.properMorphism]
  boundary : Scheme
  boundaryEmbedding : boundary ⟶ compactification.middle
  [boundaryClosed : IsClosedImmersion boundaryEmbedding]
  [boundaryFinite : IsFinite (boundaryEmbedding ≫ compactification.properMorphism)]
  [boundaryFlat : Flat (boundaryEmbedding ≫ compactification.properMorphism)]
  boundary_complement : Set.range boundaryEmbedding.base =
    (Set.range compactification.openMorphism.base)ᶜ
  zeroChart : Spec (.of (Polynomial chart.R)) ⟶ compactification.middle
  infinityChart : Spec (.of (Polynomial chart.R)) ⟶ compactification.middle
  [zeroOpen : IsOpenImmersion zeroChart]
  [infinityOpen : IsOpenImmersion infinityChart]
  positive_chart : chart.sourceIso.hom ≫
    Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial chart.R →+* LaurentPolynomial chart.R)) ≫
      zeroChart = compactification.openMorphism
  inverse_chart : chart.sourceIso.hom ≫
    Spec.map (CommRingCat.ofHom (LaurentPolynomial.invert (R := chart.R)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial chart.R →+* LaurentPolynomial chart.R)) ≫
        infinityChart = compactification.openMorphism
  zero_over : zeroChart ≫ compactification.properMorphism =
    Spec.map (CommRingCat.ofHom (Polynomial.C : chart.R →+* Polynomial chart.R)) ≫ chart.baseIso.inv
  infinity_over : infinityChart ≫ compactification.properMorphism =
    Spec.map (CommRingCat.ofHom (Polynomial.C : chart.R →+* Polynomial chart.R)) ≫ chart.baseIso.inv
  zero_infinity_disjoint : Disjoint
    (Set.range (chart.baseIso.hom ≫
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : chart.R))) ≫ zeroChart).base)
    (Set.range (chart.baseIso.hom ≫
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : chart.R))) ≫ infinityChart).base)
  boundary_labels : Set.range boundaryEmbedding.base =
    Set.range (chart.baseIso.hom ≫
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : chart.R))) ≫ zeroChart).base ∪
    Set.range (chart.baseIso.hom ≫
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : chart.R))) ≫ infinityChart).base

attribute [instance] GoodGeometryFrame.smoothOne GoodGeometryFrame.boundaryClosed
  GoodGeometryFrame.boundaryFinite GoodGeometryFrame.boundaryFlat
  GoodGeometryFrame.zeroOpen GoodGeometryFrame.infinityOpen

/-- Uniform geometric construction before any prime or coefficient object.
The presentations give a finite-type field base, hence the published excellent
Noetherian hypothesis. The chosen geometry is never an arbitrary Nagata middle. -/
abbrev UniversalGoodLaurentGeometry :=
  ∀ (K : Type) [Field K] (_h2 : (2 : K) ≠ 0) {X Y : Scheme}
    (PX : FieldPresentation K X) (PY : FieldPresentation K Y) (f : X ⟶ Y)
    (chart : LaurentCurveChart K f)
    (_over : f ≫ PY.structureMorphism = PX.structureMorphism),
    GoodGeometryFrame K PX PY f chart


section ActualSourceCoordinates

variable (K : Type) [Field K]

/-- Identity base change of the original projection gives an actual source isomorphism. -/
theorem sourceMap_identity_isIso : IsIso
    (Spec.map (CommRingCat.ofHom
      (SourceCurveBaseChange.sourceMap K (AlgHom.id K (PhysicalTorusMorphism.TorusRing K))).toRingHom)) := by
  let : IsIso (Spec.map (CommRingCat.ofHom
      (AlgHom.id K (PhysicalTorusMorphism.TorusRing K)).toRingHom)) := by
    change IsIso (Spec.map (𝟙 _))
    rw [Spec.map_id]
    infer_instance
  exact (SourceCurveBaseChange.sourceSquare_isPullback K
    (AlgHom.id K (PhysicalTorusMorphism.TorusRing K))).isIso_fst_of_isIso

/-- The actual identity base-change isomorphism, preserving positive x. -/
def originalSourceIso : StartingSourceMaps.sourceScheme K ≅
    Spec (.of (LaurentPolynomial (PhysicalTorusMorphism.TorusRing K))) := by
  letI := sourceMap_identity_isIso K
  exact (asIso (Spec.map (CommRingCat.ofHom
    (SourceCurveBaseChange.sourceMap K (AlgHom.id K (PhysicalTorusMorphism.TorusRing K))).toRingHom))).symm

/-- Original positive x and both parameter coordinates give the Laurent chart. -/
def sourceChart : LaurentCurveChart K (SourceProjectionForQST.projection K) where
  R := PhysicalTorusMorphism.TorusRing K
  ring := inferInstance
  domain := inferInstance
  algebra := inferInstance
  sourceIso := originalSourceIso K
  baseIso := Iso.refl _
  projection_square := by
    let s := Spec.map (CommRingCat.ofHom
      (SourceCurveBaseChange.sourceMap K (AlgHom.id K (PhysicalTorusMorphism.TorusRing K))).toRingHom)
    let := sourceMap_identity_isIso K
    have h := (SourceCurveBaseChange.sourceSquare_isPullback K
      (AlgHom.id K (PhysicalTorusMorphism.TorusRing K))).w
    change s ≫ SourceProjectionForQST.projection K =
      Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : PhysicalTorusMorphism.TorusRing K →+*
        LaurentPolynomial (PhysicalTorusMorphism.TorusRing K))) ≫ Spec.map (𝟙 _) at h
    rw [Spec.map_id, Category.comp_id] at h
    change inv s ≫ _ = SourceProjectionForQST.projection K ≫ 𝟙 _
    rw [← h, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp, Category.comp_id]

variable (geometry : QSTDualityBridgesFromSmoothLisseVerdier.LaurentTorusGeometry)

/-- The actual source projection respects the SAME original field presentations. -/
theorem source_over : SourceProjectionForQST.projection K ≫
    (QSTDualityBridgesFromSmoothLisseVerdier.torusPresentation geometry K).structureMorphism =
      (QSTDualityBridgesFromSmoothLisseVerdier.sourcePresentation geometry K).structureMorphism := by
  change Spec.map (CommRingCat.ofHom (SourceProjectionForQST.projectionHom K).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (PhysicalTorusMorphism.TorusRing K))) =
      Spec.map (CommRingCat.ofHom (algebraMap K (StartingSourceMaps.SourceRing K)))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (SourceProjectionForQST.projectionHom K).commutes c


end ActualSourceCoordinates

variable (geometry : LaurentTorusGeometry)
  (standardP1 : UniversalGoodLaurentGeometry)
  (K : Type) [Field K] (h2 : (2 : K) ≠ 0)

include geometry standardP1 K h2

/-- Specialize the all-Laurent-chart geometry theorem on the actual
source iso, original field presentations and proved projection square. -/
def computedGoodSourceGeometry : GoodSourceGeometry K := by
  let chart := sourceChart K
  let PX := sourcePresentation geometry K
  let PY := torusPresentation geometry K
  let good := standardP1 K h2 PX PY (SourceProjectionForQST.projection K)
    chart (source_over K geometry)
  exact {
    source := PX
    target := PY
    factor := good.compactification
    coordinateIso := originalSourceIso K
    projection_square := by
      simpa only [chart, sourceChart, Iso.refl_hom, Category.comp_id] using chart.projection_square
    boundary := good.boundary
    boundaryEmbedding := good.boundaryEmbedding
    boundary_complement := good.boundary_complement
    zeroChart := good.zeroChart
    infinityChart := good.infinityChart
    positive_chart := good.positive_chart
    inverse_chart := good.inverse_chart
    zero_over := by
      simpa only [chart, sourceChart, Iso.refl_inv, Category.comp_id] using good.zero_over
    infinity_over := by
      simpa only [chart, sourceChart, Iso.refl_inv, Category.comp_id] using good.infinity_over
    zero_infinity_disjoint := by
      simpa only [chart, sourceChart, Iso.refl_hom, Category.id_comp] using good.zero_infinity_disjoint
    boundary_labels := by
      simpa only [chart, sourceChart, Iso.refl_hom, Category.id_comp] using good.boundary_labels }

/-- The coordinate identification is the existing actual source chart,
not a new selected scheme identification. -/
theorem coordinateIso_is_original :
    (computedGoodSourceGeometry geometry standardP1 K h2).coordinateIso = originalSourceIso K := rfl

end PrimeGap182.TypeIII.OriginalGoodSourceGeometryFromThinGeneralLaurent03

#print axioms PrimeGap182.TypeIII.OriginalGoodSourceGeometryFromThinGeneralLaurent03.computedGoodSourceGeometry
#print axioms PrimeGap182.TypeIII.OriginalGoodSourceGeometryFromThinGeneralLaurent03.coordinateIso_is_original
