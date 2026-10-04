import TypeIIIUniversalBoundedInverseImagesFromExactSystem
import TypeIIIPublishedCohomologyFunctor
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The compact QST dictionary from one compactified derived pushforward

All ordinary categories and their standard derived localizations are fixed
before the prime. General open-extension, open-derived-direct-image and
proper-derived-direct-image functors are supplied only on separated finite
type schemes over one field with 2 invertible. Their bounded domains are
literal standard bounded full subcategories. No ordinary `f!` is derived.

A map is used only with an actual quasi-compact open / proper factorization,
including the same-field squares. Compact pushforward is the composite
`Rp_* j_!`; ordinary pushforward is `Rp_* Rj_*`; support comes from the SAME
natural transformation `j_! → Rj_*`. Their degree-one cohomology functors
construct the original cohomology data and the compact QST comparison.

SGA 4 XVII 5.1.8 defines the compactified derived operation; Definition
5.1.9(ii) defines `R^q f! = H^q Rf!`. Remark 5.1.9.1 explicitly warns that
`Rf!` is not the right derived functor of an ordinary `f!`. The literal SGA
statements concern torsion coefficients. Continuous constructible two-adic
realization, bounded preservation over finite type fields, independence of
compactification and the six-functor identifications remain general data.
No adic category or complete compatible Type III family is constructed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace PrimeGap182.TypeIII.QSTCompactBridgeFromCompactifiedDerivedPushforward
open ExactInverseImagesToDerived CanonicalPrimeFramework
open QSTRealizationFromExactInverseImages

universe mu

/-- A precise finite type, separated field domain, rather than all schemes. -/
structure FieldPresentation (K : Type) [Field K] (X : Scheme.{0}) where
  structureMorphism : X ⟶ Spec (.of K)
  [locallyFiniteType : LocallyOfFiniteType structureMorphism]
  [quasiCompact : QuasiCompact structureMorphism]
  [separated : IsSeparated structureMorphism]

attribute [instance] FieldPresentation.locallyFiniteType
  FieldPresentation.quasiCompact FieldPresentation.separated

/-- An actual compactification, with all three schemes over the SAME field.
The characteristic guard is the invertibility condition for two-adic use. -/
structure Compactification {X Y : Scheme.{0}} (f : X ⟶ Y) where
  K : Type
  [field : Field K]
  two_ne_zero : (2 : K) ≠ 0
  compactified : Scheme.{0}
  source : FieldPresentation K X
  middle : FieldPresentation K compactified
  target : FieldPresentation K Y
  openMorphism : X ⟶ compactified
  properMorphism : compactified ⟶ Y
  [openImmersion : IsOpenImmersion openMorphism]
  [openQuasiCompact : QuasiCompact openMorphism]
  [proper : IsProper properMorphism]
  open_over : openMorphism ≫ middle.structureMorphism = source.structureMorphism
  proper_over : properMorphism ≫ target.structureMorphism = middle.structureMorphism
  factorization : openMorphism ≫ properMorphism = f

attribute [instance] Compactification.field Compactification.openImmersion
  Compactification.openQuasiCompact Compactification.proper

variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)]
  [∀ X, Abelian (C X)]
local instance allSchemeLocalizations : ∀ X : Scheme,
    HasDerivedCategory.{mu} (C X) := fun _ => HasDerivedCategory.standard _

/-- The existing literal standard bounded derived category. -/
abbrev Bounded (X : Scheme.{0}) :=
  (QSTAdmissibilityFromBoundedDerived.boundedProperty (C X)).FullSubcategory

/-- General bounded six-functor realization on the guarded field domain.
The three operators and open support map are universal before any prime,
source family, compactification or selected object is chosen. -/
structure Operations where
  openBang : ∀ (K : Type) [Field K], (2 : K) ≠ 0 →
    ∀ {X Y : Scheme} (PX : FieldPresentation K X) (PY : FieldPresentation K Y)
      (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j],
      j ≫ PY.structureMorphism = PX.structureMorphism → Bounded C X ⥤ Bounded C Y
  openPush : ∀ (K : Type) [Field K], (2 : K) ≠ 0 →
    ∀ {X Y : Scheme} (PX : FieldPresentation K X) (PY : FieldPresentation K Y)
      (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j],
      j ≫ PY.structureMorphism = PX.structureMorphism → Bounded C X ⥤ Bounded C Y
  openSupport : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    {X Y : Scheme} (PX : FieldPresentation K X) (PY : FieldPresentation K Y)
      (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
      (baseSquare : j ≫ PY.structureMorphism = PX.structureMorphism),
      openBang K h2 PX PY j baseSquare ⟶ openPush K h2 PX PY j baseSquare
  properPush : ∀ (K : Type) [Field K], (2 : K) ≠ 0 →
    ∀ {X Y : Scheme} (PX : FieldPresentation K X) (PY : FieldPresentation K Y)
      (g : X ⟶ Y) [IsProper g],
      g ≫ PY.structureMorphism = PX.structureMorphism → Bounded C X ⥤ Bounded C Y

variable (O : Operations C) {X Y : Scheme.{0}} {f : X ⟶ Y}
  (c : Compactification f)

/-- Compactified DERIVED pushforward, not `mapDerivedCategory` of ordinary f!. -/
def derivedBang : Bounded C X ⥤ Bounded C Y :=
  O.openBang c.K c.two_ne_zero c.source c.middle c.openMorphism c.open_over ⋙
    O.properPush c.K c.two_ne_zero c.middle c.target c.properMorphism c.proper_over

/-- The SAME compactification also defines ordinary derived direct image. -/
def derivedPush : Bounded C X ⥤ Bounded C Y :=
  O.openPush c.K c.two_ne_zero c.source c.middle c.openMorphism c.open_over ⋙
    O.properPush c.K c.two_ne_zero c.middle c.target c.properMorphism c.proper_over

/-- Support-forgetting uses the same open support map and proper pushforward. -/
def derivedSupport : derivedBang C O c ⟶ derivedPush C O c :=
  Functor.whiskerRight (O.openSupport c.K c.two_ne_zero c.source c.middle
    c.openMorphism c.open_over)
    (O.properPush c.K c.two_ne_zero c.middle c.target c.properMorphism c.proper_over)

/-- Ordinary degree zero included in the literal standard bounded category. -/
def boundedDegreeZero (X : Scheme.{0}) : C X ⥤ Bounded C X :=
  (QSTAdmissibilityFromBoundedDerived.boundedProperty (C X)).lift
    (DerivedCategory.singleFunctor (C X) (0 : ℤ))
    (QSTAdmissibilityFromBoundedDerived.single_bounded (C X) 0)

/-- Actual ordinary H^n of the SAME standard derived category. -/
def cohomology (Y : Scheme.{0}) (n : ℤ) : Bounded C Y ⥤ C Y :=
  (QSTAdmissibilityFromBoundedDerived.boundedProperty (C Y)).ι ⋙
    DerivedCategory.homologyFunctor (C Y) n

/-- Both ordinary cohomology functors and their support map from one operation. -/
def cohomologyData (n : ℤ) : PublishedCohomologyFunctor.Data (C X) (C Y) where
  compact := boundedDegreeZero C X ⋙ derivedBang C O c ⋙ cohomology C Y n
  ordinary := boundedDegreeZero C X ⋙ derivedPush C O c ⋙ cohomology C Y n
  support := Functor.whiskerLeft (boundedDegreeZero C X)
    (Functor.whiskerRight (derivedSupport C O c) (cohomology C Y n))

/-- The generic dictionary is degree-zero H^n of the same derived object. -/
def cohomologyComparison (n : ℤ) (A : C X) :
    (boundedDegreeZero C Y).obj ((cohomologyData C O c n).compact.obj A) ≅
      ((cohomology C Y n) ⋙ boundedDegreeZero C Y).obj
        ((derivedBang C O c).obj ((boundedDegreeZero C X).obj A)) := Iso.refl _

/-- The support map has no second choice at the cohomology level. -/
theorem cohomologyData_support (n : ℤ) (A : C X) :
    (cohomologyData C O c n).support.app A =
      (cohomology C Y n).map
        ((derivedSupport C O c).app ((boundedDegreeZero C X).obj A)) := rfl

section CanonicalQST
variable [∀ X, MonoidalCategory (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  [∀ {X Y : Scheme} (g : X ⟶ Y), (U.pull g).Monoidal]
  (p : ℕ) [Fact p.Prime]
local instance commonLocalizations : ∀ i,
    HasDerivedCategory.{mu} (extensionObjects (primeSource C U p) (extraOrdinary C p) i) :=
  fun _ => HasDerivedCategory.standard _

/-- Restrict Bang to the literal six-space QST domain, with a certificate for f. -/
def qstPush {i j : UniformComplexityFromCommonRealization.Space}
    (g : UniformComplexityFromCommonRealization.scheme (ZMod p) i ⟶
      UniformComplexityFromCommonRealization.scheme (ZMod p) j)
    (cg : Compactification g) :
    Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) i ⥤
      Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) j := by
  cases i <;> cases j <;> exact derivedBang C O cg

/-- A total Background.push restriction requires certificates only for maps
between these SIX fixed presentations, not for all scheme morphisms. -/
def qstPushOperation
    (certificates : ∀ {i j : UniformComplexityFromCommonRealization.Space}
      (_g : UniformComplexityFromCommonRealization.scheme (ZMod p) i ⟶
        UniformComplexityFromCommonRealization.scheme (ZMod p) j), Compactification _g) :
    ∀ {i j : UniformComplexityFromCommonRealization.Space}
      (_g : UniformComplexityFromCommonRealization.scheme (ZMod p) i ⟶
        UniformComplexityFromCommonRealization.scheme (ZMod p) j),
      Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) i →
        Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) j :=
  fun g => (qstPush C O U p g (certificates g)).obj

/-- R^1 π! and R^1 π* for the ORIGINAL actual source projection. -/
def sourceCohomology (cπ : Compactification (SourceProjectionForQST.projection (ZMod p))) :
    PublishedCohomologyFunctor.Data ((primeSource C U p).Obj .source)
      ((primeSource C U p).Obj .torus) :=
  cohomologyData C O cπ 1

/-- The exact original compact dictionary, for ALL ordinary inputs.
No selected comparison, lisse input or Type III target bound is a premise. -/
def compactBridge (cπ : Compactification (SourceProjectionForQST.projection (ZMod p)))
    (A : (primeSource C U p).Obj .source) :
    (degreeZero (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p)
      .torus4).obj ((sourceCohomology C O U p cπ).cohomology.compact A) ≅
    (ordinary (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p)
      .torus4 1).obj
      ((qstPush C O U p (i := .source) (j := .torus4)
        (SourceProjectionForQST.projection (ZMod p)) cπ).obj
        ((degreeZero (primeSource C U p)
          (QSTPerverseBackgroundFromUniversalHeart.domain C U p) .source).obj A)) :=
  Iso.refl _

end CanonicalQST
end PrimeGap182.TypeIII.QSTCompactBridgeFromCompactifiedDerivedPushforward
