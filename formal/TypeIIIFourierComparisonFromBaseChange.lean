import TypeIIIFourierNormalizationMaps
import TypeIIISourceInverseImageSystem
import TypeIIITensorListRepresentation

/-!
# Fourier comparison from the universal kernel and compact base change

Laumon 1.2.1.1 defines the Fourier transform using the pairing xi*x.
Compact base change and the projection formula for the lisse AS kernel
give the general comparisons below, before choosing any Kloosterman
object, angular ratio or radial scale. Applying them at xi=T^2/a uses
the proved Cartesian square, fixed x-projection and kernel identity.

The comparisons are isomorphisms of representations. Thus the final
linear comparison and its inertia equivariance are the same map. The
cohomology and Fourier laws remain explicit published inputs.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.FourierComparisonFromBaseChange

open SourceInverseImageSystem FourierNormalizationMaps GenericCurvePullback
open FourierSourceMaps GenericSourceSpecialization PublishedPhaseApplication
open PublishedPhysicalConstruction PublishedLocalConstruction TensorListRepresentation

universe mu q v t
variable {K : Type} [Field K] (B : System.{0,mu} K)
  {Point : Type v} (D : CurveData (B.Obj .genericCurve) Point)
  (tensor : ∀ A C, D.tensor A C ≅ A ⊗ C) (as : B.Obj .line)

def universalInput (A : B.Obj .localCurve) : B.Obj .genericCurve :=
  D.tensor ((B.pull (X := .genericCurve) (Y := .localCurve) (projectionMorphism K)).obj A)
    ((B.pull (X := .genericCurve) (Y := .line) (universalKernelMorphism K)).obj as)

/-- The inverse image of the universal Fourier input has the literal
normalized kernel and the same local source, including all tensor maps. -/
def normalizedInputIso (s : (PhaseField K)ˣ) (A : B.Obj .localCurve) :
    (B.pull (X := .genericCurve) (Y := .genericCurve) (curveMorphism K s)).obj
      (universalInput B D as A) ≅
    D.tensor ((B.pull (X := .genericCurve) (Y := .localCurve) (projectionMorphism K)).obj A)
      ((B.pull (X := .genericCurve) (Y := .line) (additiveMorphism K s)).obj as) := by
  let pull := B.pull (X := .genericCurve) (Y := .genericCurve) (curveMorphism K s)
  letI : pull.Monoidal := B.pullMonoidal (X := .genericCurve) (Y := .genericCurve) (curveMorphism K s)
  let eA := B.composition (X := .genericCurve) (Y := .genericCurve) (Z := .localCurve)
    (curveMorphism K s) (projectionMorphism K) ≪≫
    eqToIso (congrArg (fun f => B.pull (X := .genericCurve) (Y := .localCurve) f)
      (curve_projection K s))
  let eAS := B.composition (X := .genericCurve) (Y := .genericCurve) (Z := .line)
    (curveMorphism K s) (universalKernelMorphism K) ≪≫
    eqToIso (congrArg (fun f => B.pull (X := .genericCurve) (Y := .line) f)
      (curve_kernel K s))
  exact pull.mapIso (tensor _ _) ≪≫ (Functor.Monoidal.μIso pull _ _).symm ≪≫
    tensorIso (eA.app A) (eAS.app as) ≪≫ (tensor _ _).symm

variable {Q : Type q} {Outer : Type mu} [Group Outer] {I : Type t} [Group I]
  {LF : LocalFourierData K ℂ I Outer}
  (J : B.Obj .parameter ⥤ FDRep ℂ Outer) (middle : B.Obj .localCurve → Q)
  (FO : FiniteOriginData Q LF) (affine : B.Obj .genericCurve ⥤ FDRep ℂ Outer)

/-- General Fourier/cohomology comparisons on this common background.
`compactMiddle` means H_c^1 on A1 after ordinary extension across x=0.
The base-change law is scoped to the external local source and the lisse
universal AS kernel; it asserts nothing about arbitrary moving boundary
singularities. The nearby comparison uses the identical radial pullback.
No correlation, rank-six statement or Type III estimate is an input. -/
structure Inputs where
  fourier : Q → B.Obj .parameter
  compactMiddle : B.Obj .genericCurve ⥤ B.Obj .parameter
  fiber : ∀ A, J.obj (compactMiddle.obj A) ≅ affine.obj A
  definition : ∀ A, fourier (middle A) ≅ compactMiddle.obj (universalInput B D as A)
  baseChange : ∀ (f : parameterScheme K ⟶ parameterScheme K)
    (g : genericScheme K ⟶ genericScheme K),
    IsPullback g (genericProjection K) (genericProjection K) f →
    g ≫ projectionMorphism K = projectionMorphism K → ∀ A,
    (B.pull (X := .parameter) (Y := .parameter) f).obj
      (compactMiddle.obj (universalInput B D as A)) ≅
      compactMiddle.obj ((B.pull (X := .genericCurve) (Y := .genericCurve) g).obj
        (universalInput B D as A))
  nearby : ∀ (s : PhaseField K) (hs : s ≠ 0) P,
    FO.origin s hs P ≅ J.obj
      ((B.pull (X := .parameter) (Y := .parameter) (frequencyMorphism K (Units.mk0 s hs))).obj
        (fourier P))

variable {B D as J middle FO affine}
variable (S : Inputs B D as J middle FO affine)

/-- Apply the published comparisons to the proved normalization square,
then identify its pulled kernel using inverse-image composition. -/
def Inputs.comparisonIso (s : PhaseField K) (hs : s ≠ 0) (A : B.Obj .localCurve) :
    FO.origin s hs (middle A) ≅ affine.obj
      (D.tensor ((B.pull (X := .genericCurve) (Y := .localCurve) (projectionMorphism K)).obj A)
        ((B.pull (X := .genericCurve) (Y := .line) (additiveMorphism K (Units.mk0 s hs))).obj as)) :=
  S.nearby s hs (middle A) ≪≫
    J.mapIso ((B.pull (X := .parameter) (Y := .parameter)
      (frequencyMorphism K (Units.mk0 s hs))).mapIso (S.definition A)) ≪≫
    J.mapIso (S.baseChange _ _ (normalizationSquare_isPullback K (Units.mk0 s hs))
      (curve_projection K (Units.mk0 s hs)) A) ≪≫
    J.mapIso (S.compactMiddle.mapIso (normalizedInputIso B D tensor as (Units.mk0 s hs) A)) ≪≫
    S.fiber _

def Inputs.comparison (s : PhaseField K) (hs : s ≠ 0) (A : B.Obj .localCurve) :=
  equivOfIso (S.comparisonIso tensor s hs A)

end PrimeGap182.TypeIII.FourierComparisonFromBaseChange

#print axioms PrimeGap182.TypeIII.FourierComparisonFromBaseChange.normalizedInputIso
#print axioms PrimeGap182.TypeIII.FourierComparisonFromBaseChange.Inputs.comparisonIso
#print axioms PrimeGap182.TypeIII.FourierComparisonFromBaseChange.Inputs.comparison
