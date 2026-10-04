import TypeIIIUniformComplexityFromCommonRealization
import TypeIIIOriginRealizationFromExactInverseImages
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-!
# Native QST inverse images and ordinary realization from the same extension

ONE exact ordinary extension includes the literal original B categories,
the QST plane and the native origin indices. Both QST torus embedding
indices use the SAME ordinary category and standard derived localization.
The origin system is a restriction of that extension, not another choice.

QST objects are an admissible full subcategory of the actual standard
derived category. The bounded-constructible interpretation and its general
closure hypotheses remain explicit: QST is not asserted on all unbounded
complexes. Derived pullback, shifts, ordinary cohomology, the degree-zero
original realizations and their pullback comparisons are constructed.
Other six-functor/perverse/class/complexity background remains general data
on these fixed native objects; no whole CommonRealization or Inputs is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical ZeroObject MonoidalCategory

namespace PrimeGap182.TypeIII.QSTRealizationFromExactInverseImages

open ExactInverseImagesToDerived

universe v w ii jj h hh

section Reindex
variable {I : Type ii} {J : Type jj} {X : I → Scheme} {C : I → Type v}
  [∀ i, Category.{w} (C i)] [∀ i, Abelian (C i)]
  (A : OrdinarySystem X C) (r : J → I) (Y : J → Scheme)
  (e : ∀ j, Y j = X (r j))

/-- Reindex by actual scheme equalities. The maps are conjugated only by
these equality identifications; the ordinary object types remain literal. -/
def reindexMap {i j : J} (f : Y i ⟶ Y j) : X (r i) ⟶ X (r j) :=
  eqToHom (e i).symm ≫ f ≫ eqToHom (e j)

theorem reindexMap_id (i : J) : reindexMap r Y e (𝟙 (Y i)) = 𝟙 (X (r i)) := by
  simp [reindexMap]

theorem reindexMap_comp {i j k : J} (f : Y i ⟶ Y j) (g : Y j ⟶ Y k) :
    reindexMap r Y e f ≫ reindexMap r Y e g = reindexMap r Y e (f ≫ g) := by
  simp [reindexMap, Category.assoc]

def ordinaryReindex : OrdinarySystem Y (fun j => C (r j)) where
  pull f := A.pull (reindexMap r Y e f)
  identity i := eqToIso (congrArg (fun f => A.pull f) (reindexMap_id r Y e i)) ≪≫ A.identity _
  composition f g := A.composition (reindexMap r Y e f) (reindexMap r Y e g) ≪≫
    eqToIso (congrArg (fun t => A.pull t) (reindexMap_comp r Y e f g))

end Reindex

section CommonExtension
variable {K : Type} [Field K] (B : SourceInverseImageSystem.System.{v,w} K)
  {J : Type} (extraScheme : J → Scheme) (extraObj : J → Type v)
  [∀ j, Category.{w} (extraObj j)] [∀ j, Abelian (extraObj j)]

/-- Gm and both torus embeddings use ORIGINAL B indices. Only the plane
requires an extra index. No replacement source-line category is selected. -/
def qstIndex (plane : J) : UniformComplexityFromCommonRealization.Space → SourceInverseImageSystem.Space K ⊕ J
  | .gm => Sum.inl (.arithmetic K)
  | .line => Sum.inl .line
  | .source => Sum.inl .source
  | .torus4 | .torus2 => Sum.inl .torus
  | .plane => Sum.inr plane

variable (plane : J) (hPlane : extraScheme plane = UniformComplexityFromCommonRealization.affinePlane K)

include hPlane in
theorem qstScheme (i : UniformComplexityFromCommonRealization.Space) :
    UniformComplexityFromCommonRealization.scheme K i = extensionScheme extraScheme (qstIndex (K := K) plane i) := by
  cases i <;> first | rfl | exact hPlane.symm

abbrev qstObjects (i : UniformComplexityFromCommonRealization.Space) := extensionObjects B extraObj (qstIndex (K := K) plane i)

variable (A : OrdinarySystem (extensionScheme extraScheme) (extensionObjects B extraObj))

def qstSystem : OrdinarySystem (UniformComplexityFromCommonRealization.scheme K) (qstObjects B extraObj plane) :=
  ordinaryReindex A (qstIndex (K := K) plane) (UniformComplexityFromCommonRealization.scheme K) (qstScheme (K := K) extraScheme plane hPlane)

/-- The native origin factory must consume this restriction of the SAME
ordinary extension. Its ordinary categories are literal extraObj values. -/
def originSystem {k : Type} [Field k] (originIndex : OriginRealizationFromExactInverseImages.Index → J)
    (hOrigin : ∀ i, extraScheme (originIndex i) = OriginRealizationFromExactInverseImages.scheme k i) :
    OrdinarySystem (OriginRealizationFromExactInverseImages.scheme k) (fun i => extraObj (originIndex i)) :=
  ordinaryReindex A (fun i => Sum.inr (originIndex i)) (OriginRealizationFromExactInverseImages.scheme k)
    (fun i => (hOrigin i).symm)

local instance qstLocalizations :
    ∀ i, HasDerivedCategory.{max v w} (qstObjects B extraObj plane i) :=
  fun _i => HasDerivedCategory.standard _

abbrev NativeDerived (i : UniformComplexityFromCommonRealization.Space) :=
  DerivedCategory (qstObjects B extraObj plane i)

def nativeDegreeZero (i : UniformComplexityFromCommonRealization.Space) : qstObjects B extraObj plane i ⥤ NativeDerived B extraObj plane i :=
  (qstSystem B extraScheme extraObj plane hPlane A).degreeZero i

def nativePull {i j : UniformComplexityFromCommonRealization.Space} (f : UniformComplexityFromCommonRealization.scheme K i ⟶ UniformComplexityFromCommonRealization.scheme K j) :
    NativeDerived B extraObj plane j ⥤ NativeDerived B extraObj plane i :=
  (qstSystem B extraScheme extraObj plane hPlane A).derivedPull f

def nativeOrdinary (i : UniformComplexityFromCommonRealization.Space) (n : ℤ) :
    NativeDerived B extraObj plane i ⥤ NativeDerived B extraObj plane i :=
  DerivedCategory.homologyFunctor (qstObjects B extraObj plane i) n ⋙
    nativeDegreeZero B extraScheme extraObj plane hPlane A i

variable {extraScheme extraObj plane hPlane A}

theorem sameTorusCategory :
    NativeDerived B extraObj plane .torus2 = NativeDerived B extraObj plane .torus4 := rfl

theorem sameSourceLineCategory : NativeDerived B extraObj plane .line =
    letI := HasDerivedCategory.standard (B.Obj .line)
    DerivedCategory (B.Obj .line) := rfl

theorem sameSourceLineDegreeZero :
    nativeDegreeZero B extraScheme extraObj plane hPlane A .line =
      letI := HasDerivedCategory.standard (B.Obj .line)
      DerivedCategory.singleFunctor (B.Obj .line) 0 := rfl

variable (R : OriginalPullAgreement B extraScheme extraObj A)

include R in
theorem sourceOrdinaryAgreement (f : SourceInverseImageSystem.scheme K .source ⟶ SourceInverseImageSystem.scheme K .line) :
    (qstSystem B extraScheme extraObj plane hPlane A).pull (i := .source) (j := .line) f =
      B.pull (X := .source) (Y := .line) f := by
  change A.pull (i := Sum.inl .source) (j := Sum.inl .line) _ = _
  simpa [reindexMap, qstScheme, qstIndex] using R.pull f

include R in
theorem torusOrdinaryAgreement (f : SourceInverseImageSystem.scheme K .torus ⟶ SourceInverseImageSystem.scheme K .torus) :
    (qstSystem B extraScheme extraObj plane hPlane A).pull (i := .torus4) (j := .torus4) f =
      B.pull (X := .torus) (Y := .torus) f := by
  change A.pull (i := Sum.inl .torus) (j := Sum.inl .torus) _ = _
  simpa [reindexMap, qstScheme, qstIndex] using R.pull f

/-- General exact inverse image / ordinary derived cohomology comparison
is constructed by the native factory, for EVERY map and EVERY degree. -/
def ordinaryPullIso {i j : UniformComplexityFromCommonRealization.Space} (f : UniformComplexityFromCommonRealization.scheme K i ⟶ UniformComplexityFromCommonRealization.scheme K j) (n : ℤ) :
    nativePull B extraScheme extraObj plane hPlane A f ⋙
      DerivedCategory.homologyFunctor (qstObjects B extraObj plane i) n ≅
    DerivedCategory.homologyFunctor (qstObjects B extraObj plane j) n ⋙
      (qstSystem B extraScheme extraObj plane hPlane A).pull f :=
  OriginRealizationFromExactInverseImages.exactDerivedCohomology ((qstSystem B extraScheme extraObj plane hPlane A).pull f) n

section Admissible
variable (extraScheme extraObj plane hPlane A)

/-- The general bounded-constructible interpretation remains required.
The predicate is on the ACTUAL native derived objects. These closure laws
do not contain specialized source/parameter estimates or realization isos. -/
structure Admissibility where
  property : ∀ i, ObjectProperty (NativeDerived B extraObj plane i)
  [containsZero : ∀ i, (property i).ContainsZero]
  [closedIso : ∀ i, (property i).IsClosedUnderIsomorphisms]
  degreeZero : ∀ i A0, property i ((nativeDegreeZero B extraScheme extraObj plane hPlane A i).obj A0)
  shift : ∀ i X, property i X → ∀ n : ℤ, property i ((shiftFunctor _ n).obj X)
  ordinary : ∀ i X, property i X → ∀ n : ℤ,
    property i ((nativeOrdinary B extraScheme extraObj plane hPlane A i n).obj X)
  pull : ∀ i j (f : UniformComplexityFromCommonRealization.scheme K i ⟶ UniformComplexityFromCommonRealization.scheme K j) X,
    property j X → property i ((nativePull B extraScheme extraObj plane hPlane A f).obj X)

attribute [instance] Admissibility.containsZero Admissibility.closedIso
variable {extraScheme extraObj plane hPlane A}
  (T : Admissibility B extraScheme extraObj plane hPlane A)

abbrev Obj (i : UniformComplexityFromCommonRealization.Space) := (T.property i).FullSubcategory

def degreeZero (i : UniformComplexityFromCommonRealization.Space) : qstObjects B extraObj plane i ⥤ Obj B T i :=
  (T.property i).lift (nativeDegreeZero B extraScheme extraObj plane hPlane A i) (T.degreeZero i)

def pull {i j : UniformComplexityFromCommonRealization.Space} (f : UniformComplexityFromCommonRealization.scheme K i ⟶ UniformComplexityFromCommonRealization.scheme K j) : Obj B T j ⥤ Obj B T i :=
  (T.property i).lift ((T.property j).ι ⋙ nativePull B extraScheme extraObj plane hPlane A f)
    (fun X => T.pull i j f X.obj X.property)

def shift (i : UniformComplexityFromCommonRealization.Space) (n : ℤ) : Obj B T i ⥤ Obj B T i :=
  (T.property i).lift ((T.property i).ι ⋙ shiftFunctor _ n)
    (fun X => T.shift i X.obj X.property n)

def ordinary (i : UniformComplexityFromCommonRealization.Space) (n : ℤ) : Obj B T i ⥤ Obj B T i :=
  (T.property i).lift ((T.property i).ι ⋙ nativeOrdinary B extraScheme extraObj plane hPlane A i n)
    (fun X => T.ordinary i X.obj X.property n)

/-- Lift the canonical degree-zero pullback comparison, preserving its
actual underlying derived isomorphism and every original ordinary map. -/
def degreeZeroPullIso {i j : UniformComplexityFromCommonRealization.Space} (f : UniformComplexityFromCommonRealization.scheme K i ⟶ UniformComplexityFromCommonRealization.scheme K j) :
    degreeZero B T j ⋙ pull B T f ≅
      (qstSystem B extraScheme extraObj plane hPlane A).pull f ⋙ degreeZero B T i :=
  NatIso.ofComponents (fun X => (T.property i).isoMk
    (((qstSystem B extraScheme extraObj plane hPlane A).degreeZeroPullback f).app X))
    (by intro X Y f; apply ObjectProperty.hom_ext; exact
      ((qstSystem B extraScheme extraObj plane hPlane A).degreeZeroPullback _).hom.naturality f)

def sourcePullIso (R : OriginalPullAgreement B extraScheme extraObj A)
    (f : SourceInverseImageSystem.scheme K .source ⟶ SourceInverseImageSystem.scheme K .line) (X : B.Obj .line) :
    (degreeZero B T .source).obj ((B.pull (X := .source) (Y := .line) f).obj X) ≅
      (pull B T (i := .source) (j := .line) f).obj ((degreeZero B T .line).obj X) := by
  have e := (degreeZeroPullIso B T (i := .source) (j := .line) f).app X
  rw [sourceOrdinaryAgreement B R f] at e
  exact e.symm

def torusPullIso (R : OriginalPullAgreement B extraScheme extraObj A)
    (f : SourceInverseImageSystem.scheme K .torus ⟶ SourceInverseImageSystem.scheme K .torus) (X : B.Obj .torus) :
    (degreeZero B T .torus4).obj ((B.pull (X := .torus) (Y := .torus) f).obj X) ≅
      (pull B T (i := .torus4) (j := .torus4) f).obj ((degreeZero B T .torus4).obj X) := by
  have e := (degreeZeroPullIso B T (i := .torus4) (j := .torus4) f).app X
  rw [torusOrdinaryAgreement B R f] at e
  exact e.symm

/-- Ordinary cohomology, re-embedded in degree zero, commutes with the
SAME native inverse image at every degree. No comparison law is supplied. -/
def admissibleOrdinaryPullIso {i j : UniformComplexityFromCommonRealization.Space}
    (f : UniformComplexityFromCommonRealization.scheme K i ⟶
      UniformComplexityFromCommonRealization.scheme K j) (n : ℤ) (X : Obj B T j) :
    (ordinary B T i n).obj ((pull B T f).obj X) ≅
      (pull B T f).obj ((ordinary B T j n).obj X) :=
  (T.property i).isoMk
    ((nativeDegreeZero B extraScheme extraObj plane hPlane A i).mapIso
      ((ordinaryPullIso B (extraScheme := extraScheme) (extraObj := extraObj)
        (plane := plane) (hPlane := hPlane) (A := A) f n).app X.obj) ≪≫
      (((qstSystem B extraScheme extraObj plane hPlane A).degreeZeroPullback f).app
        ((DerivedCategory.homologyFunctor (qstObjects B extraObj plane j) n).obj X.obj)).symm)

/-- Remaining GENERAL operations on the fixed native admissible objects.
This record has no alternate Obj, category, inverse image, shift, ordinary
cohomology or original source/parameter realization choice. It contains
none of the thirteen target inequalities or whole CommonRealization. -/
structure Background where
  complexity : ∀ i, Obj B T i → ℕ
  /-- Defined by isomorphism to the unit after the SAME geometric realization. -/
  GeometricConstantRankOne : ∀ i, Obj B T i → Prop
  embeddingComplexity : UniformComplexityFromCommonRealization.Space → ℕ
  mapComplexity : ∀ {i j}, (UniformComplexityFromCommonRealization.scheme K i ⟶
    UniformComplexityFromCommonRealization.scheme K j) → ℕ
  tensor : ∀ i, Obj B T i → Obj B T i → Obj B T i
  unit : ∀ i, Obj B T i
  tensorIso : ∀ i {X X' Y Y' : Obj B T i}, (X ≅ X') → (Y ≅ Y') →
    (tensor i X Y ≅ tensor i X' Y')
  tensorUnit : ∀ i X, tensor i (unit i) X ≅ X
  twist : ∀ i, Obj B T i → ℤ → Obj B T i
  verdier : ∀ i, Obj B T i → Obj B T i
  push : ∀ {i j}, (UniformComplexityFromCommonRealization.scheme K i ⟶
    UniformComplexityFromCommonRealization.scheme K j) → Obj B T i → Obj B T j
  Perv : UniformComplexityFromCommonRealization.Space → Type h
  [perverseCategory : ∀ i, Category.{hh} (Perv i)]
  [perverseAbelian : ∀ i, Abelian (Perv i)]
  perverse : ∀ i, Perv i ⥤ Obj B T i
  openZero : ∀ {i j}, (UniformComplexityFromCommonRealization.scheme K i ⟶
    UniformComplexityFromCommonRealization.scheme K j) → Perv i ⥤ Perv j
  openDirect : ∀ {i j}, (UniformComplexityFromCommonRealization.scheme K i ⟶
    UniformComplexityFromCommonRealization.scheme K j) → Perv i ⥤ Perv j
  openSupport : ∀ {i j} (f : UniformComplexityFromCommonRealization.scheme K i ⟶
    UniformComplexityFromCommonRealization.scheme K j), openZero f ⟶ openDirect f
  Induced : ∀ {i j}, (UniformComplexityFromCommonRealization.scheme K i ⟶
    UniformComplexityFromCommonRealization.scheme K j) → Prop
  gmGenericFiber : Obj B T .gm → ModuleCat.{0} ℂ
  [gmGenericFinite : ∀ X, FiniteDimensional ℂ (gmGenericFiber X)]
  affineZero : Obj B T .gm → Obj B T .line
  affineMiddle : Obj B T .gm → Obj B T .line
  Hypergeometric : Obj B T .gm → ℕ → Prop
  NontrivialArtinSchreier : Obj B T .line → Prop

attribute [instance] Background.perverseCategory Background.perverseAbelian Background.gmGenericFinite

variable (F : Background B T)

/-- QST's underlying category and native operations are constructed;
general published background is constrained to these exact objects. -/
def model : UniformComplexityFromCommonRealization.GeometricModel.{max v w,max v w,h,hh} K where
  Obj := Obj B T
  category _i := inferInstance
  zeroObject _i := inferInstance
  complexity := F.complexity
  GeometricConstantRankOne := F.GeometricConstantRankOne
  embeddingComplexity := F.embeddingComplexity
  mapComplexity := F.mapComplexity
  tensor := F.tensor
  unit := F.unit
  tensorIso := F.tensorIso
  tensorUnit := F.tensorUnit
  shift i X n := (shift B T i n).obj X
  twist := F.twist
  verdier := F.verdier
  ordinary i X n := (ordinary B T i n).obj X
  pull f X := (pull B T f).obj X
  push := F.push
  Perv := F.Perv
  perverseCategory := F.perverseCategory
  perverseAbelian := F.perverseAbelian
  perverse := F.perverse
  openZero := F.openZero
  openDirect := F.openDirect
  openSupport := F.openSupport
  Induced := F.Induced
  gmGenericFiber := F.gmGenericFiber
  gmGenericFinite := F.gmGenericFinite
  affineZero := F.affineZero
  affineMiddle := F.affineMiddle
  Hypergeometric := F.Hypergeometric
  NontrivialArtinSchreier := F.NontrivialArtinSchreier

def lineRealization : B.Obj .line → (model B T F).Obj .line :=
  (degreeZero B T .line).obj

def sourceRealization : B.Obj .source → (model B T F).Obj .source :=
  (degreeZero B T .source).obj

def torusRealization : B.Obj .torus → (model B T F).Obj .torus4 :=
  (degreeZero B T .torus4).obj

def modelSourcePullIso (R : OriginalPullAgreement B extraScheme extraObj A)
    (f : SourceInverseImageSystem.scheme K .source ⟶ SourceInverseImageSystem.scheme K .line)
    (X : B.Obj .line) :
    sourceRealization B T F ((B.pull (X := .source) (Y := .line) f).obj X) ≅
      (model B T F).pull (i := .source) (j := .line) f (lineRealization B T F X) :=
  sourcePullIso B T R f X

def modelTorusPullIso (R : OriginalPullAgreement B extraScheme extraObj A)
    (f : SourceInverseImageSystem.scheme K .torus ⟶ SourceInverseImageSystem.scheme K .torus)
    (X : B.Obj .torus) :
    torusRealization B T F ((B.pull (X := .torus) (Y := .torus) f).obj X) ≅
      (model B T F).pull (i := .torus4) (j := .torus4) f (torusRealization B T F X) :=
  torusPullIso B T R f X

end Admissible
end CommonExtension

section OriginalAssembly
open PublishedPhysicalConstruction PublishedPolynomialComplexity PublishedSupportRules
  StartingSourceComplexity StartingSourceMaps SourceInverseImageSystem

universe q pt
variable {p : ℕ} [Fact p.Prime] (B : System.{v,w} (ZMod p))
  {J : Type} {extraScheme : J → Scheme} {extraObj : J → Type v}
  [∀ j, Category.{w} (extraObj j)] [∀ j, Abelian (extraObj j)]
  {plane : J} {hPlane : extraScheme plane = UniformComplexityFromCommonRealization.affinePlane (ZMod p)}
  {A : OrdinarySystem (extensionScheme extraScheme) (extensionObjects B extraObj)}
  (T : Admissibility B extraScheme extraObj plane hPlane A)
  (F : Background.{v,w,h,hh} B T)
  {Point : Type pt} (D : CurveData (B.Obj .source) Point)
  (H : CohomologyData (B.Obj .source) (B.Obj .torus))
  (P : ParameterData (B.Obj .torus))
  {Surface : Type q}
  {SD : SurfaceData (AlgebraicClosure (ZMod p)) Surface}
  (R : RationalStalkRealization p SD)
  (E : IntermediateExtensionFromImage.Data R (B.Obj .torus))
  (signLine : B.Obj .torus) (SC : PrimitiveClasses (B.Obj .line))
  (ci : B.Obj .source → ℕ) (cp : B.Obj .torus → ℕ) (cl : B.Obj .line → ℕ)
  (cm : TorusMorphismComplexity (ZMod p)) (cs : MorphismComplexity (ZMod p))

local notation "G" => model B T F
local notation "LS" => lineRealization B T F
local notation "SS" => sourceRealization B T F
local notation "TS" => torusRealization B T F

/-- Precisely the remaining common-realization premises on FIXED native
objects. There is no alternate line/source/torus realization, no supplied
source_pull or torus_pull, no whole CommonRealization and no target bound.
These thirty fields include the three exact plane-functor instances. -/
structure Assembly where
  line_complexity : ∀ X, cl X = (model B T F).complexity .line (LS X)
  source_complexity : ∀ X, ci X = (model B T F).complexity .source (SS X)
  torus_complexity : ∀ X, cp X = (model B T F).complexity .torus4 (TS X)
  source_map : ∀ f, cs f = (model B T F).mapComplexity (i := .source) (j := .line) f
  torus_map : ∀ f, cm f = (model B T F).mapComplexity (i := .torus4) (j := .torus4) f
  source_dual : ∀ X, D.Lisse X → (SS (D.dual X) ≅
    (model B T F).twist .source ((model B T F).shift .source ((model B T F).verdier .source (SS X)) (-6)) (-3))
  source_tensor : ∀ X Y, SS (D.tensor X Y) ≅ (model B T F).tensor .source (SS X) (SS Y)
  compact : ∀ X, D.Lisse X → (TS (H.compact X) ≅
    (model B T F).ordinary .torus4 ((model B T F).push (i := .source) (j := .torus4)
      (SourceProjectionForQST.projection (ZMod p)) (SS X)) 1)
  sign_geometrically_constant_rank_one :
    (model B T F).GeometricConstantRankOne .torus4 (TS signLine)
  signed : ∀ X, TS (P.signed X) ≅ (model B T F).tensor .torus4 (TS signLine) (TS X)
  torus_dual : ∀ X, P.Lisse X → (TS (P.dualTateMinusOne X) ≅
    (model B T F).twist .torus4 ((model B T F).shift .torus4 ((model B T F).verdier .torus4 (TS X)) (-4)) (-3))
  torus_tensor : ∀ X Y, TS (X ⊗ Y) ≅ (model B T F).tensor .torus4 (TS X) (TS Y)
  torus_unit : TS (𝟙_ (B.Obj .torus)) ≅ (model B T F).unit .torus4
  lissePerverse : B.Obj .torus ⥤ (model B T F).Perv .torus4
  lisse_shift : ∀ X, P.Lisse X → (((model B T F).perverse .torus4).obj (lissePerverse.obj X) ≅
    (model B T F).shift .torus4 (TS X) 2)
  lisse_image : ∀ X Y (f : X ⟶ Y), P.Lisse X → P.Lisse Y →
    ((model B T F).shift .torus4 (TS (Abelian.image f)) 2 ≅
      ((model B T F).perverse .torus4).obj (Abelian.image (lissePerverse.map f)))
  openRealization : E.Open ⥤ (model B T F).Perv .torus2
  planeRealization : E.Plane ⥤ (model B T F).Perv .plane
  [planeAdditive : planeRealization.Additive]
  [planeLimits : PreservesFiniteLimits planeRealization]
  [planeColimits : PreservesFiniteColimits planeRealization]
  plane_complexity : ∀ X, SD.complexity (E.geometric X) =
    (model B T F).complexity .plane (((model B T F).perverse .plane).obj (planeRealization.obj X))
  zero : E.extensionByZero ⋙ planeRealization ≅ openRealization ⋙
    (model B T F).openZero (i := .torus2) (j := .plane) (UniformComplexityFromCommonRealization.torusOpen (ZMod p))
  direct : E.directImage ⋙ planeRealization ≅ openRealization ⋙
    (model B T F).openDirect (i := .torus2) (j := .plane) (UniformComplexityFromCommonRealization.torusOpen (ZMod p))
  support : ∀ X, planeRealization.map (E.support.app X) ≫ (direct.app X).hom =
    (zero.app X).hom ≫ ((model B T F).openSupport (i := .torus2) (j := .plane)
      (UniformComplexityFromCommonRealization.torusOpen (ZMod p))).app (openRealization.obj X)
  open_shift : ∀ X, P.Lisse X →
    (((model B T F).perverse .torus2).obj (openRealization.obj (E.perverseShift.obj X)) ≅
      (model B T F).shift .torus2 ((model B T F).pull (i := .torus2) (j := .torus4)
        (𝟙 (PhysicalTorusMorphism.torusScheme (ZMod p))) (TS X)) 2)
  openImmersion : IsOpenImmersion (UniformComplexityFromCommonRealization.torusOpen (ZMod p))
  inducedEmbedding : (model B T F).Induced (i := .torus2) (j := .plane)
    (UniformComplexityFromCommonRealization.torusOpen (ZMod p))
  hypergeometric : ∀ X r, SC.Hypergeometric X r → ∃ X0 : (model B T F).Obj .gm,
    (model B T F).Hypergeometric X0 r ∧
      (Nonempty (LS X ≅ (model B T F).affineZero X0) ∨ Nonempty (LS X ≅ (model B T F).affineMiddle X0))
  artinSchreier : ∀ X, SC.NontrivialArtinSchreier X → (model B T F).NontrivialArtinSchreier (LS X)

attribute [instance] Assembly.planeAdditive Assembly.planeLimits Assembly.planeColimits

variable {B T F D H P R E signLine SC ci cp cl cm cs}
  (S : Assembly B T F D H P R E signLine SC ci cp cl cm cs)

/-- The five omitted fields are constructed from the SAME ordinary
extension and original agreement; the thirty residual premises remain
explicit. This result can feed the existing QB/QS theorem applications. -/
def Assembly.commonRealization (agreement : OriginalPullAgreement B extraScheme extraObj A) :
    UniformComplexityFromCommonRealization.CommonRealization B D H P R E signLine SC ci cp cl cm cs G where
  line := LS
  source := SS
  torus := TS
  line_complexity := S.line_complexity
  source_complexity := S.source_complexity
  torus_complexity := S.torus_complexity
  source_map := S.source_map
  torus_map := S.torus_map
  source_dual := S.source_dual
  source_tensor := S.source_tensor
  source_pull := modelSourcePullIso B T F agreement
  compact := S.compact
  sign_geometrically_constant_rank_one := S.sign_geometrically_constant_rank_one
  signed := S.signed
  torus_pull := modelTorusPullIso B T F agreement
  torus_dual := S.torus_dual
  torus_tensor := S.torus_tensor
  torus_unit := S.torus_unit
  lissePerverse := S.lissePerverse
  lisse_shift := S.lisse_shift
  lisse_image := S.lisse_image
  openRealization := S.openRealization
  plane := S.planeRealization
  planeAdditive := S.planeAdditive
  planeLimits := S.planeLimits
  planeColimits := S.planeColimits
  plane_complexity := S.plane_complexity
  zero := S.zero
  direct := S.direct
  support := S.support
  open_shift := S.open_shift
  openImmersion := S.openImmersion
  inducedEmbedding := S.inducedEmbedding
  hypergeometric := S.hypergeometric
  artinSchreier := S.artinSchreier

end OriginalAssembly

end PrimeGap182.TypeIII.QSTRealizationFromExactInverseImages

#print axioms PrimeGap182.TypeIII.QSTRealizationFromExactInverseImages.ordinaryReindex
#print axioms PrimeGap182.TypeIII.QSTRealizationFromExactInverseImages.originSystem
#print axioms PrimeGap182.TypeIII.QSTRealizationFromExactInverseImages.ordinaryPullIso
#print axioms PrimeGap182.TypeIII.QSTRealizationFromExactInverseImages.sourcePullIso
#print axioms PrimeGap182.TypeIII.QSTRealizationFromExactInverseImages.torusPullIso
#print axioms PrimeGap182.TypeIII.QSTRealizationFromExactInverseImages.admissibleOrdinaryPullIso
#print axioms PrimeGap182.TypeIII.QSTRealizationFromExactInverseImages.model
#print axioms PrimeGap182.TypeIII.QSTRealizationFromExactInverseImages.modelSourcePullIso
#print axioms PrimeGap182.TypeIII.QSTRealizationFromExactInverseImages.modelTorusPullIso
#print axioms PrimeGap182.TypeIII.QSTRealizationFromExactInverseImages.Assembly.commonRealization
