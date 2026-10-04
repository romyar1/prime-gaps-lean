import TypeIIILocalFourierFromASPullbacks
import TypeIIIFullFourierKernelCoordinates

/-!
# Full perverse Fourier origin from the original AS kernel

This is a categorical application of explicit published general theorems.
It does not instantiate a common adic realization or the full Type III input
family. The defining transform and its cycle comparison are constructed below.

Q is the continuous constructible two-adic perverse category on the full
source affine line, with its actual generic-infinity functor. The output is
the corresponding perverse category on the full target affine line.
The inverse images include constant-field extension to PhaseField K.
The same original canonical nontrivial-character AS line object is used in
the full-plane kernel and in the already constructed local AS operation.
Interpreting these categories and operations in that common theory remains
an explicit framework obligation; the categorical types alone do not prove it.

The published-comparison parameters below explicitly require ell=2 != p and
finite or algebraically closed constants. These are perfect-field cases of
Laumon's scope and satisfy his additional hypothesis (0.6). They apply to
every Q object before any Type III family is selected; no purity or slope
guard is imposed. The infinity admissibility guard is retained explicitly.

The full transform is source inverse image on A^2, tensor with AS(xy),
compact pushforward along y, shift [1], then perverse degree zero. The explicit general
perverse-exactness comparison identifies the entire derived transform with
the fully faithful realization of this perverse object. It is never defined
on the punctured chart. The perverse cycle comparison uses the same ambient
degree-minus-one cycle functor. Laumon 1.3.2.3 supplies perverse exactness.

Two separate published comparisons are retained. Laumon 2.3.2.1(iii) compares
global cycles with cycles of the compactified kernel. Its all-finite-point
extension is stated explicitly, including a lisse target origin: section
2.3.2 selects s' in S', whereas proper cycle base change and the finite-chart
local acyclicity used in its proof give this extension. Singularity is not
assumed automatically. Laumon 2.4.2.1(ii) then uses the actual generic source
infinity identification with V[1] and the [2] shift to identify degree -1
compactified cycles with degree 1 local cycles. This comparison uses the
restricted FULL kernel, before the checked AS coordinate comparison.

The compactification functor includes target henselian inverse image and
source extension by zero to the proper source line. Its cycle operation is
H^-1 Phi of the shifted complex at (infinity, geometric generic target 0).
The local kernel restriction henselizes only after the algebraic chart and
source inversion; it extends by zero across source pi=0 only. Target y=0
remains included. No ramified-normalization cycle theorem is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace PrimeGap182.TypeIII.FourierOriginFromASKernel
open PublishedPhaseApplication PublishedLocalConstruction SourceInverseImageSystem
open FiniteOriginFromRestriction NearbyFromStalkPullback TensorListRepresentation

universe mu t u v q w

variable (K : Type) [Field K]

/-- The actual first projection of the full affine plane. -/
def sourceMorphism : FullFourierKernelCoordinates.planeScheme K ⟶
    LocalFourierKernelCoordinates.affineLine K :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.aeval (fun _ : Fin 1 => MvPolynomial.X (0 : Fin 2)) :
      MvPolynomial (Fin 1) K →ₐ[K] MvPolynomial (Fin 2) K).toRingHom)

variable {K} (B : System.{0,mu} K)
  {I : Type t} [Group I] {G : Type mu} [Group G]
  (S : LocalFourierFromASPullbacks.Inputs.{mu,t,u,v} K I G (B.Obj .line))
  (as : B.Obj .line) (J : B.Obj .parameter ⥤ FDRep ℂ G)
  {Q : Type q} [Category.{w} Q] (perverseInfinity : Q ⥤ FDRep ℂ I)

/-- Common full-plane, compactification and cycle operations. These are
general framework data, not a preselected Fourier transform or kernel. -/
structure Data (perverseInfinity : Q ⥤ FDRep ℂ I) where
  SourceAmbient : Type u
  [sourceAmbientCategory : Category.{v} SourceAmbient]
  sourceRealization : Q ⥤ SourceAmbient
  sourceRealizationFullyFaithful : sourceRealization.FullyFaithful
  Plane : Type u
  [planeCategory : Category.{v} Plane]
  [planeMonoidal : MonoidalCategory Plane]
  TargetAmbient : Type u
  [targetAmbientCategory : Category.{v} TargetAmbient]
  Output : Type q
  [outputCategory : Category.{w} Output]
  sourcePullback : (FullFourierKernelCoordinates.planeScheme (PhaseField K) ⟶
    LocalFourierKernelCoordinates.affineLine (PhaseField K)) → SourceAmbient ⥤ Plane
  phasePullback : (FullFourierKernelCoordinates.planeScheme (PhaseField K) ⟶
    LocalFourierKernelCoordinates.affineLine (PhaseField K)) → B.Obj .line ⥤ Plane
  compactPushforward : (FullFourierKernelCoordinates.planeScheme (PhaseField K) ⟶
    LocalFourierKernelCoordinates.affineLine (PhaseField K)) → Plane ⥤ TargetAmbient
  shiftOne : TargetAmbient ⥤ TargetAmbient
  perverseZero : TargetAmbient ⥤ Output
  perverseRealization : Output ⥤ TargetAmbient
  perverseRealizationFullyFaithful : perverseRealization.FullyFaithful
  ambientMinusOneCycles : TargetAmbient ⥤ FDRep ℂ S.Raw
  GenericAmbient : Type u
  [genericAmbientCategory : Category.{v} GenericAmbient]
  ambientInfinityRestriction : SourceAmbient ⥤ GenericAmbient
  embedShiftOne : (show ObjectProperty (FDRep ℂ I) from S.Admissible).FullSubcategory ⥤
    GenericAmbient
  restriction : Output ⥤ B.Obj .parameter
  stalk : NearbyFromStalkPullback.StalkPullback B (S.operationData as).data J
  cycles : FourierOriginFromGlobalCycles.Cycles B (S.operationData as).data
    Output restriction stalk.raw
  chartPullback : Plane ⥤ S.Open
  chartComposition : ∀ f, phasePullback f ⋙ chartPullback ≅
    S.phasePullback (FullFourierKernelCoordinates.chartMorphism (PhaseField K) ≫ f)
  Compactified : Type u
  [compactifiedCategory : Category.{v} Compactified]
  compactify : Plane ⥤ Compactified
  compactifiedMinusOneCycles : Compactified ⥤ FDRep ℂ S.Raw

attribute [instance] Data.sourceAmbientCategory Data.planeCategory Data.planeMonoidal Data.targetAmbientCategory
  Data.outputCategory Data.compactifiedCategory Data.genericAmbientCategory

variable {B S as J perverseInfinity} (D : Data B S as J perverseInfinity)

/-- Unshifted inverse image of the same realized perverse source object. -/
abbrev Data.perversePullback
    (f : FullFourierKernelCoordinates.planeScheme (PhaseField K) ⟶
      LocalFourierKernelCoordinates.affineLine (PhaseField K)) : Q ⥤ D.Plane :=
  D.sourceRealization ⋙ D.sourcePullback f

/-- Actual generic infinity inverse image of that same source realization. -/
abbrev Data.genericInfinityRestriction : Q ⥤ D.GenericAmbient :=
  D.sourceRealization ⋙ D.ambientInfinityRestriction

/-- The full AS object is an actual pullback along positive xy on A^2. -/
abbrev Data.fullAS : D.Plane :=
  (D.phasePullback (FullFourierKernelCoordinates.kernelMorphism (PhaseField K))).obj as

/-- The unshifted positive-AS kernel operation on all derived source objects. -/
abbrev Data.sourceKernel : D.SourceAmbient ⥤ D.Plane :=
  D.sourcePullback (sourceMorphism (PhaseField K)) ⋙ tensorRight D.fullAS

abbrev Data.fullKernel : Q ⥤ D.Plane := D.sourceRealization ⋙ D.sourceKernel

/-- The full compact-pushforward kernel transform, with the [1] shift. -/
abbrev Data.derivedTransform : Q ⥤ D.TargetAmbient :=
  D.fullKernel ⋙ D.compactPushforward
    (FullFourierKernelCoordinates.targetMorphism (PhaseField K)) ⋙ D.shiftOne

/-- Source x=0 and target y=0 are included in this defining composite. -/
abbrev Data.transform : Q ⥤ D.Output := D.derivedTransform ⋙ D.perverseZero

abbrev Data.compactifiedCycles : Q ⥤ FDRep ℂ S.Raw :=
  D.fullKernel ⋙ D.compactify ⋙ D.compactifiedMinusOneCycles

/-- Restrict the full-plane kernel before henselization and source extension. -/
abbrev Data.extendedFullKernel : S.Product :=
  S.extendKernel.obj (S.coordinateRestriction.obj (D.chartPullback.obj D.fullAS))

/-- Apply the general compositor to the actual full-plane chart identity,
then the checked original-AS source-inversion comparison. -/
def Data.fullLocalKernelComparison : D.extendedFullKernel ≅ (S.operationData as).kernel := by
  have e := D.chartComposition (FullFourierKernelCoordinates.kernelMorphism (PhaseField K))
  rw [FullFourierKernelCoordinates.chart_kernelMorphism] at e
  exact S.extendKernel.mapIso (S.coordinateRestriction.mapIso (e.app as)) ≪≫
    S.globalKernelComparison as

abbrev Data.localPoleSource (_D : Data B S as J perverseInfinity)
    (h : ∀ P, S.Admissible (perverseInfinity.obj P)) : Q ⥤ S.Product :=
  (show ObjectProperty (FDRep ℂ I) from S.Admissible).lift perverseInfinity h ⋙
    S.zeroExtend ⋙ S.pull

/-- The exact admissible generic representation lifted to V[1]. The generic
ambient category includes the common coefficient realization; no functor
from arbitrary complex representations into adic sheaves is asserted. -/
abbrev Data.realizedInfinity
    (h : ∀ P, S.Admissible (perverseInfinity.obj P)) : Q ⥤ D.GenericAmbient :=
  (show ObjectProperty (FDRep ℂ I) from S.Admissible).lift perverseInfinity h ⋙
    D.embedShiftOne

abbrev Data.localCyclesThroughFullKernel
    (h : ∀ P, S.Admissible (perverseInfinity.obj P)) : Q ⥤ FDRep ℂ S.Raw :=
  D.localPoleSource h ⋙ tensorRight D.extendedFullKernel ⋙ S.firstCycles

/-- Explicit general published laws on the defining composites above.
`as` is the same original canonical nontrivial-character AS object when this
application is used in the root. Q and Output are the actual common perverse
hearts. The derived-category realization is fully faithful, and the generic
comparison uses actual nu_infinity inverse image and V[1]. These are common
framework interpretations, not consequences of arbitrary category names.

The proper-cycle law is stated on the full derived kernel transform, at
finite target zero whether it is lisse or singular. This is the extension
of Laumon 2.3.2.1(iii) obtained from proper cycle base change and finite-chart
local acyclicity in its proof. The generic-infinity law, 2.4.2.1(ii), accepts
its actual V[1] premise, then performs the [2]/degree-one conversion prior
to replacing the restricted full kernel. Neither law assumes the completed
stationary-phase comparison. -/
structure PublishedComparisons (p : ℕ) [Fact p.Prime] [CharP K p]
    (_ell_ne_p : 2 ≠ p) (_constantScope : Finite K ∨ IsAlgClosed K) where
  infinityAdmissible : ∀ P, S.Admissible (perverseInfinity.obj P)
  genericInfinityIdentification : D.genericInfinityRestriction ≅
    D.realizedInfinity infinityAdmissible
  perverseFourierExactness : D.derivedTransform ≅ D.transform ⋙ D.perverseRealization
  perverseCycleComparison : D.perverseRealization ⋙ D.ambientMinusOneCycles ≅
    D.cycles.vanishing
  properCyclesAllFiniteOrigin : D.derivedTransform ⋙ D.ambientMinusOneCycles ≅
    D.compactifiedCycles
  genericInfinityCyclesShiftTwo : ∀ (h : ∀ P, S.Admissible (perverseInfinity.obj P)),
    (D.genericInfinityRestriction ≅ D.realizedInfinity h) →
      (D.compactifiedCycles ≅ D.localCyclesThroughFullKernel h)

variable {p : ℕ} [Fact p.Prime] [CharP K p]
  {ell_ne_p : 2 ≠ p} {constantScope : Finite K ∨ IsAlgClosed K}
  (Laws : PublishedComparisons D p ell_ne_p constantScope)

/-- First identify the cycles of the same perverse realization with the
ambient derived cycles, then apply proper cycle base change. -/
def globalCyclesComparison : D.transform ⋙ D.cycles.vanishing ≅ D.compactifiedCycles :=
  (Functor.isoWhiskerLeft D.transform Laws.perverseCycleComparison.symm) ≪≫
    (Functor.isoWhiskerRight Laws.perverseFourierExactness.symm D.ambientMinusOneCycles) ≪≫
      Laws.properCyclesAllFiniteOrigin

/-- The general proper-cycle application retains every original input map. -/
theorem globalCyclesComparison_natural {P R : Q} (f : P ⟶ R) :
    (D.transform ⋙ D.cycles.vanishing).map f ≫
        (globalCyclesComparison D Laws).hom.app R =
      (globalCyclesComparison D Laws).hom.app P ≫ D.compactifiedCycles.map f :=
  (globalCyclesComparison D Laws).hom.naturality f

/-- The checked fixed-kernel map is natural after tensoring and R^1 Phi. -/
def Data.fullLocalCyclesComparison
    (h : ∀ P, S.Admissible (perverseInfinity.obj P)) :
    D.localCyclesThroughFullKernel h ≅
      D.localPoleSource h ⋙ tensorRight (S.operationData as).kernel ⋙ S.firstCycles :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (D.localPoleSource h)
      ((tensoringRight S.Product).mapIso D.fullLocalKernelComparison)) S.firstCycles

/-- Apply the infinity theorem with its actual generic-restriction premise,
then the checked tensor-kernel map. This is a natural comparison, rather
than independently selected objectwise representation equivalences. -/
def stationaryPhaseComparison : D.transform ⋙ D.cycles.vanishing ≅
    D.localPoleSource Laws.infinityAdmissible ⋙
      tensorRight (S.operationData as).kernel ⋙ S.firstCycles :=
  globalCyclesComparison D Laws ≪≫
    Laws.genericInfinityCyclesShiftTwo Laws.infinityAdmissible
      Laws.genericInfinityIdentification ≪≫
        D.fullLocalCyclesComparison Laws.infinityAdmissible

/-- The resulting stationary-phase map is natural for all source morphisms. -/
theorem stationaryPhaseComparison_natural {P R : Q} (f : P ⟶ R) :
    (D.transform ⋙ D.cycles.vanishing).map f ≫
        (stationaryPhaseComparison D Laws).hom.app R =
      (stationaryPhaseComparison D Laws).hom.app P ≫
        (D.localPoleSource Laws.infinityAdmissible ⋙
          tensorRight (S.operationData as).kernel ⋙ S.firstCycles).map f :=
  (stationaryPhaseComparison D Laws).hom.naturality f

/-- The old representation comparison is the component of this natural iso. -/
def stationaryPhase (P : Q) : Representation.Equiv
    (D.cycles.vanishing.obj (D.transform.obj P)).ρ
    ((S.operationData as).data.unscaled.obj
      (perverseInfinity.obj P) (Laws.infinityAdmissible P)).ρ :=
  equivOfIso ((stationaryPhaseComparison D Laws).app P)

/-- Any other perverse lift of the full derived transform is canonically
isomorphic to this one. Full faithfulness rules out invisible punctual
additions in the perverse realization. -/
def perverseLiftComparison (F : Q ⥤ D.Output)
    (e : D.derivedTransform ≅ F ⋙ D.perverseRealization) : D.transform ≅ F := by
  letI := D.perverseRealizationFullyFaithful.full
  letI := D.perverseRealizationFullyFaithful.faithful
  exact Functor.fullyFaithfulCancelRight D.perverseRealization
    (Laws.perverseFourierExactness.symm ≪≫ e)

/-- Supply only the old origin component; the whole residual Inputs family
is not taken as a premise. This constructor uses the constructed full transform and derived comparison. -/
def originInputs : FourierOriginFromGlobalCycles.Inputs B (S.operationData as).data
    J perverseInfinity where
  Output := D.Output
  outputCategory := D.outputCategory
  transform := D.transform
  restriction := D.restriction
  stalk := D.stalk
  cycles := D.cycles
  infinity_admissible := Laws.infinityAdmissible
  stationaryPhase := stationaryPhase D Laws

/-- The old interface uses the constructed full-plane transform verbatim. -/
theorem originInputs_transform : (originInputs D Laws).transform = D.transform := rfl

end PrimeGap182.TypeIII.FourierOriginFromASKernel

#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.sourceMorphism
#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.Data.fullAS
#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.Data.fullKernel
#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.Data.derivedTransform
#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.Data.transform
#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.Data.compactifiedCycles
#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.Data.extendedFullKernel
#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.Data.fullLocalKernelComparison
#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.Data.localPoleSource
#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.Data.realizedInfinity
#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.Data.localCyclesThroughFullKernel
#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.globalCyclesComparison
#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.globalCyclesComparison_natural
#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.Data.fullLocalCyclesComparison
#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.stationaryPhaseComparison
#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.stationaryPhaseComparison_natural
#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.stationaryPhase
#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.perverseLiftComparison
#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.originInputs
#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.originInputs_transform

#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.Data.perversePullback
#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.Data.genericInfinityRestriction
#print axioms PrimeGap182.TypeIII.FourierOriginFromASKernel.Data.sourceKernel
