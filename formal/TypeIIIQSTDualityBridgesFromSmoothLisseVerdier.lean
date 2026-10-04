import TypeIIIQSTCompactBridgeFromCompactifiedDerivedPushforward
import TypeIIISourcePurityFromStalks
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Two QST dual dictionaries from general smooth lisse Verdier duality

The ordinary tensor dual is internal Hom into the SAME ordinary unit.
Ordinary dual(-1) is that dual followed by tensoring with the SAME Tate(-1)
line. General bounded Verdier and Tate functors, global ordinary lissity,
and their ALL-field/ALL-object comparisons are fixed before the prime.

SGA 4 XVIII 3.2.5 identifies smooth exceptional pullback with (d)[2d].
Together with lisse internal-Hom concentration (3.2.6) and Verdier's
internal-Hom definition this yields the smooth lisse duality corollary
used here. The literal SGA statements have torsion coefficients; 3.2.6
as printed uses an algebraically closed field. The arithmetic-field
continuous constructible two-adic corollary and its identification with
these standard derived categories remain explicit general parameters.

Actual global Gm^3 and Gm^2 structure maps have dimensions 3 and 2.
Universal ALL-field geometry certificates supply their smooth dimensions
and compactifications; no selected-prime geometry equality is supplied.
The old relative-curve Lisse predicate is explicitly replaced by the
universal GLOBAL-source predicate when using bindSourceLisse. No claim
is made that a merely fibrewise lisse source satisfies this theorem.
No Background, Inputs, selected dual comparison or adic foundations are
assumed or constructed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.QSTDualityBridgesFromSmoothLisseVerdier
open ExactInverseImagesToDerived CanonicalPrimeFramework
open QSTRealizationFromExactInverseImages
open QSTCompactBridgeFromCompactifiedDerivedPushforward

universe mu pt

/-- Literal coefficient structural map of the original global source. -/
def sourceStructure (K : Type) [Field K] :
    StartingSourceMaps.sourceScheme K ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (StartingSourceMaps.SourceRing K)))

/-- Literal coefficient structural map of the original parameter torus. -/
def torusStructure (K : Type) [Field K] :
    PhysicalTorusMorphism.torusScheme K ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (PhysicalTorusMorphism.TorusRing K)))

/-- Standard Laurent-torus geometry, universally before prime selection.
No sheaf comparison or selected Type III equality is a field. -/
structure LaurentTorusGeometry where
  sourceSmooth : ∀ (K : Type) [Field K], SmoothOfRelativeDimension 3 (sourceStructure K)
  torusSmooth : ∀ (K : Type) [Field K], SmoothOfRelativeDimension 2 (torusStructure K)
  sourceCompactification : ∀ (K : Type) [Field K], (2 : K) ≠ 0 →
    Compactification (sourceStructure K)
  torusCompactification : ∀ (K : Type) [Field K], (2 : K) ≠ 0 →
    Compactification (torusStructure K)

variable (geometry : LaurentTorusGeometry)

/-- The exact source dimension gives its finite type field presentation. -/
def sourcePresentation (K : Type) [Field K] :
    FieldPresentation K (StartingSourceMaps.sourceScheme K) := by
  letI := geometry.sourceSmooth K
  letI : Smooth (sourceStructure K) := SmoothOfRelativeDimension.smooth 3 _
  exact { structureMorphism := sourceStructure K }

/-- The exact torus dimension gives its finite type field presentation. -/
def torusPresentation (K : Type) [Field K] :
    FieldPresentation K (PhysicalTorusMorphism.torusScheme K) := by
  letI := geometry.torusSmooth K
  letI : Smooth (torusStructure K) := SmoothOfRelativeDimension.smooth 2 _
  exact { structureMorphism := torusStructure K }

variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)]
  [∀ X, Abelian (C X)] [∀ X, MonoidalCategory (C X)]
  [∀ X, MonoidalClosed (C X)]
local instance allSchemeLocalizations : ∀ X : Scheme,
    HasDerivedCategory.{mu} (C X) := fun _ => HasDerivedCategory.standard _

/-- Genuine ordinary tensor dual; no arbitrary contravariant functor. -/
def ordinaryDual (X : Scheme) : (C X)ᵒᵖ ⥤ C X :=
  MonoidalClosed.internalHom ⋙ (CategoryTheory.evaluation (C X) (C X)).obj (𝟙_ (C X))

/-- Actual standard bounded shift, at every scheme. -/
def boundedShift (X : Scheme) (n : ℤ) : Bounded C X ⥤ Bounded C X :=
  (QSTAdmissibilityFromBoundedDerived.boundedProperty (C X)).lift
    ((QSTAdmissibilityFromBoundedDerived.boundedProperty (C X)).ι ⋙ shiftFunctor _ n)
    (fun A => QSTAdmissibilityFromBoundedDerived.shift_bounded (C X) A.obj A.property n)

/-- General operations on the SAME categories, before any prime or source.
Tate-line interpretation is used only where 2 is invertible. -/
structure Operations where
  globalLisse : ∀ X, C X → Prop
  line : ∀ X, ℤ → C X
  tate : ∀ X, ℤ → Bounded C X ⥤ Bounded C X
  verdier : ∀ X, (Bounded C X)ᵒᵖ ⥤ Bounded C X

variable (O : Operations C)

/-- Ordinary Tate is tensor with the SAME supplied coefficient line. -/
def ordinaryTate (X : Scheme) (n : ℤ) : C X ⥤ C X := MonoidalCategory.tensorLeft (O.line X n)

/-- Literal ordinary dual followed by actual tensor with Tate(-1). -/
def ordinaryDualTateMinusOne (X : Scheme) : (C X)ᵒᵖ ⥤ C X :=
  ordinaryDual C X ⋙ ordinaryTate C O X (-1)

/-- Precisely universal field-domain laws, not selected QST dictionaries.
The final field is the arithmetic/adically realized smooth lisse corollary,
including the exceptional-pullback and internal-Hom identifications. -/
structure PublishedLaws where
  degreeZeroTate : ∀ (K : Type) [Field K], (2 : K) ≠ 0 →
    ∀ {X : Scheme} (_PX : FieldPresentation K X) (n : ℤ),
      ordinaryTate C O X n ⋙ boundedDegreeZero C X ≅
        boundedDegreeZero C X ⋙ O.tate X n
  tateAdd : ∀ (K : Type) [Field K], (2 : K) ≠ 0 →
    ∀ {X : Scheme} (_PX : FieldPresentation K X) (m n : ℤ),
      O.tate X m ⋙ O.tate X n ≅ O.tate X (m + n)
  smoothLisseDual : ∀ (K : Type) [Field K] (_h2 : (2 : K) ≠ 0)
    {X : Scheme} (PX : FieldPresentation K X) (d : ℕ)
    [SmoothOfRelativeDimension d PX.structureMorphism]
    (_compactification : Compactification PX.structureMorphism) (A : C X),
    O.globalLisse X A →
      ((boundedDegreeZero C X).obj ((ordinaryDual C X).obj (Opposite.op A)) ≅
        (O.tate X (-(d : ℤ))).obj
          ((boundedShift C X (-2 * (d : ℤ))).obj
            ((O.verdier X).obj (Opposite.op ((boundedDegreeZero C X).obj A)))))

variable (L : PublishedLaws C O)

/-- ALL smooth global lisse inputs, additionally twisted by ANY integer t. -/
def smoothLisseDualTate (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    {X : Scheme} (PX : FieldPresentation K X) (d : ℕ)
    [SmoothOfRelativeDimension d PX.structureMorphism]
    (c : Compactification PX.structureMorphism) (A : C X)
    (hA : O.globalLisse X A) (t : ℤ) :
    (boundedDegreeZero C X).obj
      ((ordinaryTate C O X t).obj ((ordinaryDual C X).obj (Opposite.op A))) ≅
      (O.tate X (-(d : ℤ) + t)).obj
        ((boundedShift C X (-2 * (d : ℤ))).obj
          ((O.verdier X).obj (Opposite.op ((boundedDegreeZero C X).obj A)))) :=
  (L.degreeZeroTate K h2 PX t).app ((ordinaryDual C X).obj (Opposite.op A)) ≪≫
    (O.tate X t).mapIso (L.smoothLisseDual K h2 PX d c A hA) ≪≫
    (L.tateAdd K h2 PX (-(d : ℤ)) t).app
      ((boundedShift C X (-2 * (d : ℤ))).obj
        ((O.verdier X).obj (Opposite.op ((boundedDegreeZero C X).obj A))))

/-- Only global source lissity is replaced; the original numerical
observables stay fixed. The old relative-only guard is not silently used. -/
def bindSourceLisse (K : Type) [Field K] {Point : Type pt}
    (observables : SourcePurityFromStalks.Observables
      (C (StartingSourceMaps.sourceScheme K)) Point) :
    SourcePurityFromStalks.Observables (C (StartingSourceMaps.sourceScheme K)) Point :=
  { observables with Lisse := O.globalLisse (StartingSourceMaps.sourceScheme K) }

section CanonicalQST
variable (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  [∀ {X Y : Scheme} (g : X ⟶ Y), (U.pull g).Monoidal]
  (p : ℕ) [Fact p.Prime]
local instance commonLocalizations : ∀ i,
    HasDerivedCategory.{mu} (extensionObjects (primeSource C U p) (extraOrdinary C p) i) :=
  fun _ => HasDerivedCategory.standard _

/-- The original source dual functor is computed from universal internal Hom. -/
def sourceDualFunctor : ((primeSource C U p).Obj .source)ᵒᵖ ⥤
    (primeSource C U p).Obj .source := ordinaryDual C (StartingSourceMaps.sourceScheme (ZMod p))

/-- The original parameter dual(-1) is computed from the same line tensor. -/
def torusDualTateFunctor : ((primeSource C U p).Obj .torus)ᵒᵖ ⥤
    (primeSource C U p).Obj .torus :=
  ordinaryDualTateMinusOne C O (PhysicalTorusMorphism.torusScheme (ZMod p))

/-- The Background.twist field is a literal universal Tate restriction. -/
def qstTwist (i : UniformComplexityFromCommonRealization.Space)
    (A : Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) i)
    (n : ℤ) : Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) i := by
  cases i <;> exact (O.tate _ n).obj A

/-- The Background.verdier field is a literal universal contravariant restriction. -/
def qstVerdier (i : UniformComplexityFromCommonRealization.Space)
    (A : Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) i) :
    Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) i := by
  cases i <;> exact (O.verdier _).obj (Opposite.op A)

/-- Exact source [-6](-3), for the true global-source lisse guard. -/
def sourceDualBridge (h2 : (2 : ZMod p) ≠ 0)
    (A : (primeSource C U p).Obj .source)
    (hA : O.globalLisse (StartingSourceMaps.sourceScheme (ZMod p)) A) :
    (degreeZero (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p)
      .source).obj ((sourceDualFunctor C U p).obj (Opposite.op A)) ≅
      qstTwist C O U p .source
        ((shift (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p)
          .source (-6)).obj
            (qstVerdier C O U p .source
              ((degreeZero (primeSource C U p)
                (QSTPerverseBackgroundFromUniversalHeart.domain C U p) .source).obj A))) (-3) := by
  letI : SmoothOfRelativeDimension 3 (sourcePresentation geometry (ZMod p)).structureMorphism := by
    change SmoothOfRelativeDimension 3 (sourceStructure (ZMod p))
    exact geometry.sourceSmooth (ZMod p)
  exact L.smoothLisseDual (ZMod p) h2 (sourcePresentation geometry (ZMod p)) 3
    (geometry.sourceCompactification (ZMod p) h2) A hA

/-- Exact parameter dual(-1) [-4](-3), on the original parameter torus. -/
def torusDualBridge (h2 : (2 : ZMod p) ≠ 0)
    (A : (primeSource C U p).Obj .torus)
    (hA : O.globalLisse (PhysicalTorusMorphism.torusScheme (ZMod p)) A) :
    (degreeZero (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p)
      .torus4).obj ((torusDualTateFunctor C O U p).obj (Opposite.op A)) ≅
      qstTwist C O U p .torus4
        ((shift (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p)
          .torus4 (-4)).obj
            (qstVerdier C O U p .torus4
              ((degreeZero (primeSource C U p)
                (QSTPerverseBackgroundFromUniversalHeart.domain C U p) .torus4).obj A))) (-3) := by
  letI : SmoothOfRelativeDimension 2 (torusPresentation geometry (ZMod p)).structureMorphism := by
    change SmoothOfRelativeDimension 2 (torusStructure (ZMod p))
    exact geometry.torusSmooth (ZMod p)
  exact smoothLisseDualTate C O L (ZMod p) h2 (torusPresentation geometry (ZMod p)) 2
    (geometry.torusCompactification (ZMod p) h2) A hA (-1)

end CanonicalQST
end PrimeGap182.TypeIII.QSTDualityBridgesFromSmoothLisseVerdier
